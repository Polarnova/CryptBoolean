/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.LinearStructureSpectrum

/-!
# Carlet Chapter 4 derivative bounds for nonlinearity

The raw hyperplane Walsh identity gives Carlet's autocorrelation upper bound for nonlinearity.
The derivative weight inequality gives Relation (37).
-/

open Finset
open scoped BigOperators BooleanCube NNReal

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance derivativeNonlinearitySubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

/-- The least absolute autocorrelation at a nonzero direction. In dimension zero the empty
family is assigned the value zero. -/
noncomputable def minimumAutocorrelationMagnitude (f : BooleanFunction n) : ℝ :=
  let directions := Finset.univ.erase (0 : FABL.F₂Cube n)
  if h : directions.Nonempty then
    directions.inf' h fun e ↦ |autocorrelation f e|
  else 0

private theorem exists_walshCharacter_mul_eq_abs
    (e : FABL.F₂Cube n) (he : e ≠ 0) (t : ℝ) :
    ∃ a : FABL.F₂Cube n, FABL.vectorWalshCharacter a e * t = |t| := by
  by_cases ht : 0 ≤ t
  · exact ⟨0, by simp [abs_of_nonneg ht]⟩
  · have htneg : t < 0 := lt_of_not_ge ht
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    have hi' : e i ≠ 0 := by simpa using hi
    have hei : e i = 1 := Fin.eq_one_of_ne_zero (e i) hi'
    let a : FABL.F₂Cube n := Pi.single i 1
    have hcharacter : FABL.vectorWalshCharacter a e = -1 := by
      rw [FABL.vectorWalshCharacter_apply]
      have hdot : FABL.f₂DotProduct a e = 1 := by
        simp [a, FABL.f₂DotProduct, single_dotProduct, hei]
      rw [hdot, FABL.binarySign_one]
    refine ⟨a, ?_⟩
    rw [hcharacter, abs_of_neg htneg]
    ring

private theorem abs_walshTransform_le_maxWalshMagnitude
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    |(walshTransform f a : ℝ)| ≤ (maxWalshMagnitude f : ℝ) := by
  have hnat : (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
    rw [maxWalshMagnitude]
    exact Finset.le_sup' (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ a)
  have hcast : ((walshTransform f a).natAbs : ℝ) ≤ (maxWalshMagnitude f : ℝ) := by
    exact_mod_cast hnat
  simpa using hcast

private theorem two_pow_add_abs_autocorrelation_le_maxWalshMagnitude_sq
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (he : e ≠ 0) :
    (2 : ℝ) ^ n + |autocorrelation f e| ≤ (maxWalshMagnitude f : ℝ) ^ 2 := by
  obtain ⟨a, ha⟩ :=
    exists_walshCharacter_mul_eq_abs e he (autocorrelation f e)
  have hsum := sum_walshTransform_sq_hyperplane_coset f e a he
  rw [ha] at hsum
  have hmaxNonneg : 0 ≤ (maxWalshMagnitude f : ℝ) := by positivity
  have hterm (u : walshHyperplane e) :
      (walshTransform f (a + u.1) : ℝ) ^ 2 ≤
        (maxWalshMagnitude f : ℝ) ^ 2 := by
    have habs := abs_walshTransform_le_maxWalshMagnitude f (a + u.1)
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (walshTransform f (a + u.1) : ℝ)) hmaxNonneg).mpr habs
    simpa only [sq_abs] using hsquare
  have hsumLe :
      (∑ u : walshHyperplane e,
          (walshTransform f (a + u.1) : ℝ) ^ 2) ≤
        ∑ _u : walshHyperplane e, (maxWalshMagnitude f : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro u _hu
    exact hterm u
  have hcard : Fintype.card (walshHyperplane e) = 2 ^ (n - 1) := by
    rw [← Nat.card_eq_fintype_card, natCard_walshHyperplane e he]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard] at hsumLe
  push_cast at hsumLe
  have hpositive : 0 < (2 : ℝ) ^ (n - 1) := by positivity
  nlinarith

/-- Adding a function with constant derivative changes autocorrelation in that direction only by
the sign of the derivative constant. -/
theorem autocorrelation_add_of_isLinearStructure
    (f g : BooleanFunction n) {e : FABL.F₂Cube n} {ε : FABL.𝔽₂}
    (hg : ∀ x, FABL.booleanDerivative g e x = ε) :
    autocorrelation (f + g) e = (bitSignInt ε : ℝ) * autocorrelation f e := by
  classical
  unfold autocorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  unfold realSignView FABL.realSignEncodedFunction FABL.signEncodedFunction
  rw [show FABL.booleanDerivative (f + g) e x =
      FABL.booleanDerivative f e x + ε by
    rw [booleanDerivative_add]
    exact congrArg (FABL.booleanDerivative f e x + ·) (hg x)]
  rw [FABL.signValue_signEncode_eq_binarySign,
    FABL.signValue_signEncode_eq_binarySign, AddChar.map_add_eq_mul,
    bitSignInt_cast]
  ring

/-- Adding a function with constant derivative preserves the autocorrelation magnitude in that
direction. -/
theorem abs_autocorrelation_add_of_isLinearStructure
    (f g : BooleanFunction n) {e : FABL.F₂Cube n} {ε : FABL.𝔽₂}
    (hg : ∀ x, FABL.booleanDerivative g e x = ε) :
    |autocorrelation (f + g) e| = |autocorrelation f e| := by
  rw [autocorrelation_add_of_isLinearStructure f g hg, abs_mul]
  have hsign : |(bitSignInt ε : ℝ)| = 1 := by
    rw [bitSignInt_cast]
    rcases FABL.signValue_eq_neg_one_or_one (FABL.signEncode ε) with h | h <;>
      rw [FABL.signValue_signEncode_eq_binarySign] at h <;> rw [h] <;> norm_num
  rw [hsign, one_mul]

/-- In positive dimension Carlet's absolute indicator is attained at a nonzero direction. -/
theorem exists_abs_autocorrelation_eq_absoluteIndicator
    (hn : 0 < n) (f : BooleanFunction n) :
    ∃ e : FABL.F₂Cube n, e ≠ 0 ∧
      |autocorrelation f e| = absoluteIndicator f := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let d : FABL.F₂Cube n := Pi.single i 1
  have hd : d ≠ 0 := by
    intro hzero
    have hi := congrFun hzero i
    simp [d] at hi
  let directions := Finset.univ.erase (0 : FABL.F₂Cube n)
  have hnonempty : directions.Nonempty :=
    ⟨d, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ d⟩⟩
  obtain ⟨e, he, hmaximum⟩ := Finset.exists_mem_eq_sup directions hnonempty
    (fun d ↦ Real.toNNReal |autocorrelation f d|)
  refine ⟨e, (Finset.mem_erase.mp he).1, ?_⟩
  have hmaximumReal := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hmaximum
  simpa [absoluteIndicator, directions] using hmaximumReal.symm

/-- Carlet's upper derivative bound: the largest nonzero autocorrelation magnitude improves the
universal upper bound on raw nonlinearity. -/
theorem nonlinearity_cast_le_autocorrelation_upper_bound
    (f : BooleanFunction n) (hn : 0 < n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ (n - 1) -
        Real.sqrt ((2 : ℝ) ^ n + absoluteIndicator f) / 2 := by
  obtain ⟨e, he, hmaximum⟩ :=
    exists_abs_autocorrelation_eq_absoluteIndicator hn f
  have hsquare :=
    two_pow_add_abs_autocorrelation_le_maxWalshMagnitude_sq f e he
  rw [hmaximum] at hsquare
  have hsqrt :
      Real.sqrt ((2 : ℝ) ^ n + absoluteIndicator f) ≤
        (maxWalshMagnitude f : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsquare⟩
  have hpow : (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ (n - 1) := by
    have hpowsucc : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by congr 1; omega
        _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
    rw [hpowsucc]
    ring
  rw [nonlinearity_cast_eq_relation_35, hpow]
  linarith

private theorem nonzeroDirections_nonempty
    (f : BooleanFunction n) (hn : 0 < n) :
    (Finset.univ.erase (0 : FABL.F₂Cube n)).Nonempty := by
  obtain ⟨e, he, _hmaximum⟩ :=
    exists_abs_autocorrelation_eq_absoluteIndicator hn f
  exact ⟨e, Finset.mem_erase.mpr ⟨he, Finset.mem_univ e⟩⟩

private theorem exists_abs_autocorrelation_eq_minimumAutocorrelationMagnitude
    (f : BooleanFunction n) (hn : 0 < n) :
    ∃ e : FABL.F₂Cube n, e ≠ 0 ∧
      |autocorrelation f e| = minimumAutocorrelationMagnitude f := by
  classical
  let directions := Finset.univ.erase (0 : FABL.F₂Cube n)
  have hnonempty : directions.Nonempty := by
    simpa [directions] using nonzeroDirections_nonempty f hn
  obtain ⟨e, he, hminimum⟩ := Finset.exists_mem_eq_inf' hnonempty
    (fun d ↦ |autocorrelation f d|)
  refine ⟨e, (Finset.mem_erase.mp he).1, ?_⟩
  rw [minimumAutocorrelationMagnitude, dif_pos hnonempty]
  exact hminimum.symm

private theorem derivative_affineFunction
    (b : FABL.𝔽₂) (a e : FABL.F₂Cube n) :
    ∀ x, FABL.booleanDerivative (FABL.affineFunction b a) e x =
      FABL.f₂DotProduct a e := by
  intro x
  simp only [FABL.booleanDerivative, FABL.affineFunction, FABL.f₂DotProduct,
    dotProduct_add]
  calc
    b + dotProduct a x + (b + (dotProduct a x + dotProduct a e)) =
        (b + b) + (dotProduct a x + dotProduct a x) + dotProduct a e := by
      abel
    _ = dotProduct a e := by
      rw [ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]

private theorem autocorrelation_lower_bound_le_hammingDistance_affineFunction
    (f : BooleanFunction n) (e : FABL.F₂Cube n)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    ((2 : ℝ) ^ n - |autocorrelation f e|) / 4 ≤
      (hammingDistance f (FABL.affineFunction b a) : ℝ) := by
  let g := FABL.affineFunction b a
  have hweight := hammingWeight_booleanDerivative_le_two_mul (f + g) e
  rw [← hammingDistance_eq_hammingWeight_add] at hweight
  have hweightReal :
      (hammingWeight (FABL.booleanDerivative (f + g) e) : ℝ) ≤
        2 * (hammingDistance f g : ℝ) := by
    exact_mod_cast hweight
  have hauto := autocorrelation_eq_two_pow_sub_two_derivative_weight (f + g) e
  have habs : |autocorrelation (f + g) e| = |autocorrelation f e| :=
    abs_autocorrelation_add_of_isLinearStructure f g
      (derivative_affineFunction b a e)
  have hautoLe : autocorrelation (f + g) e ≤ |autocorrelation f e| := by
    calc
      autocorrelation (f + g) e ≤ |autocorrelation (f + g) e| := le_abs_self _
      _ = |autocorrelation f e| := habs
  dsimp [g] at hweightReal hauto hautoLe ⊢
  nlinarith

private theorem autocorrelation_lower_bound_le_nonlinearity
    (f : BooleanFunction n) (e : FABL.F₂Cube n) :
    ((2 : ℝ) ^ n - |autocorrelation f e|) / 4 ≤ (nonlinearity f : ℝ) := by
  classical
  obtain ⟨p, _hp, hminimum⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun q ↦ hammingDistance f (FABL.affineFunction q.1 q.2))
  have hminimum' :
      nonlinearity f = hammingDistance f (FABL.affineFunction p.1 p.2) := by
    simpa [nonlinearity] using hminimum
  rw [hminimum']
  exact autocorrelation_lower_bound_le_hammingDistance_affineFunction f e p.1 p.2

/-- Carlet Relation (37): the least nonzero autocorrelation magnitude gives a lower bound on raw
nonlinearity. The real exponent preserves the printed power in every positive dimension. -/
theorem relation_37_nonlinearity_lower_bound
    (f : BooleanFunction n) (hn : 0 < n) :
    (2 : ℝ) ^ ((n : ℝ) - 2) - minimumAutocorrelationMagnitude f / 4 ≤
      (nonlinearity f : ℝ) := by
  obtain ⟨e, _he, hminimum⟩ :=
    exists_abs_autocorrelation_eq_minimumAutocorrelationMagnitude f hn
  have hlower := autocorrelation_lower_bound_le_nonlinearity f e
  rw [hminimum] at hlower
  have hpow : (2 : ℝ) ^ ((n : ℝ) - 2) = (2 : ℝ) ^ n / 4 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    norm_num
  rw [hpow]
  linarith

end CryptBoolean
