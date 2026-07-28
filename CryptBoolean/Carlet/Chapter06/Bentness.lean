/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.DistanceToLinearStructures
public import CryptBoolean.Carlet.Chapter04.PropagationCriteria
public import CryptBoolean.Carlet.Chapter05.QuadraticValues

/-!
# Bent Boolean functions

Carlet Definition 7 and Theorem 8: distance, spectrum, affine invariance, and derivatives.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Every raw Walsh coefficient of a bent Boolean function has magnitude `2^(n/2)`. -/
theorem natAbs_walshTransform_eq_two_pow_half_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) (a : FABL.F₂Cube n) :
    (walshTransform f a).natAbs = 2 ^ (n / 2) := by
  have hn := even_of_isBent f hf
  have hflat := (hasFlatWalshSpectrum_iff_isBent f).2 hf a
  rw [sqrt_two_pow_eq_pow_half hn] at hflat
  apply Nat.cast_injective (R := ℝ)
  simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat]
    using hflat

/-- The maximum raw Walsh magnitude of a bent function is `2^(n/2)`. -/
theorem maxWalshMagnitude_eq_two_pow_half_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) :
    maxWalshMagnitude f = 2 ^ (n / 2) := by
  unfold maxWalshMagnitude
  simp_rw [natAbs_walshTransform_eq_two_pow_half_of_isBent f hf]
  simp

/-- In positive even dimension, a bent function attains Carlet's integral
nonlinearity value `2^(n-1)-2^(n/2-1)`. -/
theorem nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) (hn : 2 ≤ n) :
    nonlinearity f = 2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  have heven := even_of_isBent f hf
  have hhalf : 1 ≤ n / 2 := by
    rcases heven with ⟨k, hk⟩
    omega
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  rw [maxWalshMagnitude_eq_two_pow_half_of_isBent f hf] at hrelation
  have hnPow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  have hhalfPow : 2 ^ (n / 2) = 2 * 2 ^ (n / 2 - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n / 2 ≠ 0)
    rw [hm]
    simp [pow_succ, Nat.mul_comm]
  rw [hnPow, hhalfPow] at hrelation
  omega

/-- Bentness is equivalent to the exact raw Walsh magnitude at every frequency. -/
theorem isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
    (f : BooleanFunction n) :
    IsBent f ↔ ∀ a, (walshTransform f a).natAbs = 2 ^ (n / 2) := by
  constructor
  · intro hf a
    exact natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a
  · intro h
    apply (hasFlatWalshSpectrum_iff_isBent f).1
    have hn : Even n := by
      have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
      have hsum :
          (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) =
            (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ 2 := by
        calc
          (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) =
              ∑ _a : FABL.F₂Cube n, ((2 : ℝ) ^ (n / 2)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            have ha : |(walshTransform f a : ℝ)| =
                (2 : ℝ) ^ (n / 2) := by
              have haCast := congrArg (fun k : ℕ ↦ (k : ℝ)) (h a)
              simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
                Nat.cast_ofNat] using haCast
            rw [← sq_abs, ha]
          _ = (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
              nsmul_eq_mul]
            norm_num
      rw [hsum] at hparseval
      have hsquares : ((2 : ℝ) ^ (n / 2)) ^ 2 = (2 : ℝ) ^ n := by
        apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0)
        calc
          (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ 2 =
              ((2 : ℝ) ^ n) ^ 2 := hparseval
          _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by ring
      have hsquaresNat : ((2 : ℕ) ^ (n / 2)) ^ 2 = 2 ^ n := by
        exact_mod_cast hsquares
      have hnEq : 2 * (n / 2) = n := by
        apply Nat.pow_right_injective (by omega : 2 ≤ 2)
        calc
          2 ^ (2 * (n / 2)) = ((2 : ℕ) ^ (n / 2)) ^ 2 := by
            rw [Nat.mul_comm, pow_mul]
          _ = 2 ^ n := hsquaresNat
      exact ⟨n / 2, by omega⟩
    intro a
    rw [sqrt_two_pow_eq_pow_half hn]
    have haCast := congrArg (fun k : ℕ ↦ (k : ℝ)) (h a)
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
      Nat.cast_ofNat] using haCast

/-- Adding an affine Boolean function preserves bentness. -/
theorem isBent_add_affineFunction_iff
    (f : BooleanFunction n) (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    IsBent (f + FABL.affineFunction b a) ↔ IsBent f := by
  rw [← nonlinearity_cast_eq_relation_36_iff_isBent,
    ← nonlinearity_cast_eq_relation_36_iff_isBent,
    nonlinearity_add_affineFunction]

/-- Precomposition by an affine automorphism preserves bentness. -/
theorem isBent_comp_affineEquiv_iff
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    IsBent (f ∘ L) ↔ IsBent f := by
  rw [← nonlinearity_cast_eq_relation_36_iff_isBent,
    ← nonlinearity_cast_eq_relation_36_iff_isBent,
    nonlinearity_comp_affineEquiv]

/-- Every affine distance from a bent function differs from half the cube size by
`2^(n/2-1)`. -/
theorem abs_hammingDistance_affine_sub_half_of_isBent
    (f : BooleanFunction n) (hf : IsBent f)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    |(hammingDistance f (FABL.affineFunction b a) : ℝ) -
        (2 : ℝ) ^ n / 2| = (2 : ℝ) ^ (n / 2) / 2 := by
  rw [hammingDistance_cast_affineFunction_eq]
  have hwalsh : |(walshTransform f a : ℝ)| = (2 : ℝ) ^ (n / 2) := by
    have hwalshCast := congrArg (fun k : ℕ ↦ (k : ℝ))
      (natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a)
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
      Nat.cast_ofNat] using hwalshCast
  have hsign : |(bitSignInt b : ℝ)| = 1 := by
    have hsignNat : (bitSignInt b).natAbs = 1 := by
      rw [bitSignInt_eq_if_one]
      split <;> simp
    have hsignCast := congrArg (fun k : ℕ ↦ (k : ℝ)) hsignNat
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_one] using hsignCast
  rw [sub_sub_cancel_left, abs_neg, abs_div, abs_mul, hsign, one_mul,
    hwalsh]
  norm_num

/-- Carlet Theorem 8: a Boolean function is bent exactly when every nonzero
directional derivative is balanced. -/
theorem isBent_iff_forall_nonzero_derivative_isBalanced
    (f : BooleanFunction n) :
    IsBent f ↔
      ∀ a : FABL.F₂Cube n, a ≠ 0 →
        IsBalanced (FABL.booleanDerivative f a) := by
  rw [← absoluteIndicator_eq_zero_iff_isBent]
  constructor
  · intro habsolute a ha
    apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).2
    have hle := abs_autocorrelation_le_absoluteIndicator f ha
    rw [habsolute] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro h
    unfold absoluteIndicator
    apply NNReal.coe_eq_zero.mpr
    rw [Finset.sup_eq_zero]
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    have hzero :=
      (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).1 (h a hne)
    rw [hzero, abs_zero, Real.toNNReal_zero]

/-- Carlet's `PC(n)` formulation of Theorem 8. -/
theorem isBent_iff_satisfiesPropagationCriterion_dimension
    (f : BooleanFunction n) :
    IsBent f ↔ SatisfiesPropagationCriterion n f := by
  rw [isBent_iff_forall_nonzero_derivative_isBalanced,
    SatisfiesPropagationCriterion, SatisfiesPropagationCriterionOn]
  constructor
  · intro h a ha
    exact h a ha.1
  · intro h a ha
    have hcard : (FABL.f₂Support a).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (FABL.f₂Support a))
    exact h a ⟨ha, hcard⟩

end CryptBoolean
