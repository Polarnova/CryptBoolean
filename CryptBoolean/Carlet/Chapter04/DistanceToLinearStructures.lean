/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.DerivativeNonlinearity
public import CryptBoolean.Carlet.Chapter04.LinearStructures

/-!
# Carlet Chapter 4 distance to linear structures

The distance to linear structures is the least raw Hamming distance to a Boolean function with a
nonzero constant-derivative direction. Its exact value is determined by the largest nontrivial
autocorrelation magnitude.
-/

open Finset
open scoped BigOperators BooleanCube NNReal

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A Boolean function admits a nonzero linear structure. -/
def HasNonzeroLinearStructure (g : BooleanFunction n) : Prop :=
  ∃ e : FABL.F₂Cube n, e ≠ 0 ∧ IsLinearStructure g e

private noncomputable instance hasNonzeroLinearStructureDecidable :
    DecidablePred (HasNonzeroLinearStructure (n := n)) :=
  Classical.decPred _

private theorem exists_nonzero_direction (hn : 0 < n) :
    ∃ e : FABL.F₂Cube n, e ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨Pi.single i 1, ?_⟩
  intro h
  have hi := congrFun h i
  simp at hi

private theorem nonempty_hasNonzeroLinearStructure (hn : 0 < n) :
    (Finset.univ.filter (HasNonzeroLinearStructure (n := n))).Nonempty := by
  classical
  obtain ⟨e, he⟩ := exists_nonzero_direction hn
  refine ⟨(0 : BooleanFunction n), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  refine ⟨e, he, 0, ?_⟩
  intro x
  simp [FABL.booleanDerivative]

/-- The least raw Hamming distance to a Boolean function admitting a nonzero linear structure.
The zero-dimensional empty-family value is defined to be zero. -/
noncomputable def distanceToLinearStructures (f : BooleanFunction n) : ℕ :=
  by
    classical
    exact
      if h : (Finset.univ.filter (HasNonzeroLinearStructure (n := n))).Nonempty then
        (Finset.univ.filter (HasNonzeroLinearStructure (n := n))).inf' h
          (hammingDistance f)
      else 0

/-- The distance to linear structures is bounded by the distance to every function with a
nonzero linear structure. -/
theorem distanceToLinearStructures_le_hammingDistance
    (hn : 0 < n) (f g : BooleanFunction n) (hg : HasNonzeroLinearStructure g) :
    distanceToLinearStructures f ≤ hammingDistance f g := by
  classical
  rw [distanceToLinearStructures, dif_pos (nonempty_hasNonzeroLinearStructure hn)]
  exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)

/-- The nearest function with a nonzero linear structure exists in every positive dimension. -/
theorem exists_hammingDistance_eq_distanceToLinearStructures
    (hn : 0 < n) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, HasNonzeroLinearStructure g ∧
      hammingDistance f g = distanceToLinearStructures f := by
  classical
  let s := Finset.univ.filter (HasNonzeroLinearStructure (n := n))
  have hs : s.Nonempty := nonempty_hasNonzeroLinearStructure hn
  obtain ⟨g, hg, hmin⟩ := Finset.exists_mem_eq_inf' hs (hammingDistance f)
  refine ⟨g, (Finset.mem_filter.mp hg).2, ?_⟩
  rw [distanceToLinearStructures, dif_pos hs]
  exact hmin.symm

private noncomputable instance cubeLinearOrder : LinearOrder (FABL.F₂Cube n) :=
  (Trunc.out (Fintype.truncEquivFin (FABL.F₂Cube n))).linearOrder

private noncomputable def repairDerivative
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (ε : FABL.𝔽₂) : BooleanFunction n :=
  fun x ↦ if x < x + e then f x else f (x + e) + ε

private theorem add_direction_twice (x e : FABL.F₂Cube n) :
    (x + e) + e = x := by
  calc
    (x + e) + e = x + (e + e) := add_assoc _ _ _
    _ = x := by rw [ZModModule.add_self, add_zero]

private theorem add_direction_ne (x : FABL.F₂Cube n) {e : FABL.F₂Cube n}
    (he : e ≠ 0) : x + e ≠ x := by
  intro h
  apply he
  apply add_left_cancel (a := x)
  simpa using h

private theorem repairDerivative_pair
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0)
    (ε : FABL.𝔽₂) (x : FABL.F₂Cube n) :
    repairDerivative f e ε x + repairDerivative f e ε (x + e) = ε := by
  classical
  have hcycle := add_direction_twice x e
  have hne := add_direction_ne x he
  by_cases hlt : x < x + e
  · have hnlt : ¬ x + e < (x + e) + e := by
      rw [hcycle]
      exact not_lt_of_ge hlt.le
    rw [repairDerivative, if_pos hlt, repairDerivative, if_neg hnlt, hcycle]
    calc
      f x + (f x + ε) = (f x + f x) + ε := by abel
      _ = ε := by rw [ZModModule.add_self, zero_add]
  · have hrev : x + e < x := lt_of_le_of_ne (le_of_not_gt hlt) hne
    have hrevCycle : x + e < (x + e) + e := by simpa [hcycle] using hrev
    rw [repairDerivative, if_neg hlt, repairDerivative, if_pos hrevCycle]
    calc
      f (x + e) + ε + f (x + e) = (f (x + e) + f (x + e)) + ε := by abel
      _ = ε := by rw [ZModModule.add_self, zero_add]

private theorem isLinearStructure_repairDerivative
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0) (ε : FABL.𝔽₂) :
    IsLinearStructure (repairDerivative f e ε) e := by
  refine ⟨ε, ?_⟩
  intro x
  exact repairDerivative_pair f he ε x

private theorem repairDerivative_error_pair
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0)
    (ε : FABL.𝔽₂) (x : FABL.F₂Cube n) :
    (if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) +
        (if (f + repairDerivative f e ε) (x + e) = 1 then (1 : ℕ) else 0) =
      if (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε) :
          BooleanFunction n) x = 1 then 1 else 0 := by
  classical
  have hcycle := add_direction_twice x e
  have hne := add_direction_ne x he
  by_cases hlt : x < x + e
  · have hnlt : ¬ x + e < (x + e) + e := by
      rw [hcycle]
      exact not_lt_of_ge hlt.le
    have hxzero : (f + repairDerivative f e ε) x = 0 := by
      simp only [Pi.add_apply, repairDerivative, if_pos hlt]
      exact ZModModule.add_self (f x)
    have hyerror : (f + repairDerivative f e ε) (x + e) =
        (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε) :
          BooleanFunction n) x := by
      rw [Pi.add_apply, repairDerivative, if_neg hnlt, hcycle]
      simp only [Pi.add_apply, FABL.booleanDerivative]
      abel
    rw [hxzero, hyerror]
    simp
  · have hrev : x + e < x := lt_of_le_of_ne (le_of_not_gt hlt) hne
    have hrevCycle : x + e < (x + e) + e := by simpa [hcycle] using hrev
    have hxerror : (f + repairDerivative f e ε) x =
        (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε) :
          BooleanFunction n) x := by
      rw [Pi.add_apply, repairDerivative, if_neg hlt]
      simp only [Pi.add_apply, FABL.booleanDerivative]
      abel
    have hyzero : (f + repairDerivative f e ε) (x + e) = 0 := by
      rw [Pi.add_apply, repairDerivative, if_pos hrevCycle]
      exact ZModModule.add_self (f (x + e))
    rw [hxerror, hyzero]
    simp

private theorem two_mul_hammingDistance_repairDerivative
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0) (ε : FABL.𝔽₂) :
    2 * hammingDistance f (repairDerivative f e ε) =
      hammingWeight (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε)) := by
  classical
  rw [hammingDistance_eq_hammingWeight_add,
    hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  simp only [support, FABL.f₂OneSupport, Finset.card_filter]
  change
    2 * ∑ x, (if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) =
      ∑ x, (if (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε) :
        BooleanFunction n) x = 1 then (1 : ℕ) else 0)
  rw [two_mul]
  calc
    (∑ x, if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) +
        ∑ x, (if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) =
        (∑ x, if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) +
          ∑ x, (if (f + repairDerivative f e ε) (x + e) = 1 then
            (1 : ℕ) else 0) := by
      congr 1
      calc
        ∑ x, (if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) =
            ∑ x, (if (f + repairDerivative f e ε) ((Equiv.addRight e) x) = 1 then
              (1 : ℕ) else 0) :=
          (Equiv.sum_comp (Equiv.addRight e)
            (fun x ↦ if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0)).symm
        _ = ∑ x, (if (f + repairDerivative f e ε) (x + e) = 1 then
              (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rfl
    _ = ∑ x, ((if (f + repairDerivative f e ε) x = 1 then (1 : ℕ) else 0) +
        if (f + repairDerivative f e ε) (x + e) = 1 then (1 : ℕ) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ x, (if (FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ ε) :
          BooleanFunction n) x = 1 then
          (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      exact repairDerivative_error_pair f he ε x

/-- Every nonzero autocorrelation magnitude is bounded by Carlet's absolute indicator. -/
theorem abs_autocorrelation_le_absoluteIndicator
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0) :
    |autocorrelation f e| ≤ absoluteIndicator f := by
  have hle : Real.toNNReal |autocorrelation f e| ≤
      (Finset.univ.erase (0 : FABL.F₂Cube n)).sup
        (fun d ↦ Real.toNNReal |autocorrelation f d|) :=
    Finset.le_sup (f := fun d ↦ Real.toNNReal |autocorrelation f d|)
      (Finset.mem_erase.mpr ⟨he, Finset.mem_univ e⟩)
  unfold absoluteIndicator
  calc
    |autocorrelation f e| = (Real.toNNReal |autocorrelation f e| : ℝ) := by
      exact (Real.coe_toNNReal _ (abs_nonneg _)).symm
    _ ≤ (((Finset.univ.erase (0 : FABL.F₂Cube n)).sup
        (fun d ↦ Real.toNNReal |autocorrelation f d|) : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.mpr hle

private theorem distance_lower_bound_of_hasNonzeroLinearStructure
    (f g : BooleanFunction n) (hg : HasNonzeroLinearStructure g) :
    ((2 : ℝ) ^ n - absoluteIndicator f) / 4 ≤ hammingDistance f g := by
  obtain ⟨e, he, ε, hε⟩ := hg
  have hweight := hammingWeight_booleanDerivative_le_two_mul (f + g) e
  rw [← hammingDistance_eq_hammingWeight_add] at hweight
  have hweightReal :
      (hammingWeight (FABL.booleanDerivative (f + g) e) : ℝ) ≤
        2 * (hammingDistance f g : ℝ) := by
    exact_mod_cast hweight
  have hauto := autocorrelation_eq_two_pow_sub_two_derivative_weight (f + g) e
  have habs : |autocorrelation (f + g) e| = |autocorrelation f e| :=
    abs_autocorrelation_add_of_isLinearStructure f g hε
  have hindicator := abs_autocorrelation_le_absoluteIndicator f he
  have hautoLe : autocorrelation (f + g) e ≤ absoluteIndicator f := by
    calc
      autocorrelation (f + g) e ≤ |autocorrelation (f + g) e| := le_abs_self _
      _ = |autocorrelation f e| := habs
      _ ≤ absoluteIndicator f := hindicator
  linarith

private theorem hasNonzeroLinearStructure_repairDerivative
    (f : BooleanFunction n) {e : FABL.F₂Cube n} (he : e ≠ 0) (ε : FABL.𝔽₂) :
    HasNonzeroLinearStructure (repairDerivative f e ε) :=
  ⟨e, he, isLinearStructure_repairDerivative f he ε⟩

private theorem exists_repairDerivative_at_absoluteIndicator
    (hn : 0 < n) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, HasNonzeroLinearStructure g ∧
      (hammingDistance f g : ℝ) =
        ((2 : ℝ) ^ n - absoluteIndicator f) / 4 := by
  obtain ⟨e, he, hmax⟩ := exists_abs_autocorrelation_eq_absoluteIndicator hn f
  by_cases hnonneg : 0 ≤ autocorrelation f e
  · let g := repairDerivative f e 0
    refine ⟨g, hasNonzeroLinearStructure_repairDerivative f he 0, ?_⟩
    have hrepair := two_mul_hammingDistance_repairDerivative f he 0
    have hauto := autocorrelation_eq_two_pow_sub_two_derivative_weight f e
    have habs : |autocorrelation f e| = autocorrelation f e := abs_of_nonneg hnonneg
    have hrepairReal :
        2 * (hammingDistance f g : ℝ) =
          (hammingWeight (FABL.booleanDerivative f e +
            (fun _ : FABL.F₂Cube n ↦ (0 : FABL.𝔽₂))) : ℝ) := by
      exact_mod_cast hrepair
    have hzeroFunction : FABL.booleanDerivative f e +
        (fun _ : FABL.F₂Cube n ↦ (0 : FABL.𝔽₂)) = FABL.booleanDerivative f e := by
      funext x
      simp
    rw [hzeroFunction] at hrepairReal
    rw [← hmax, habs]
    linarith
  · have hneg : autocorrelation f e < 0 := lt_of_not_ge hnonneg
    let g := repairDerivative f e 1
    refine ⟨g, hasNonzeroLinearStructure_repairDerivative f he 1, ?_⟩
    have hrepair := two_mul_hammingDistance_repairDerivative f he 1
    have hautoRepair := autocorrelation_eq_two_pow_sub_two_derivative_weight (f + g) e
    have hderivative : FABL.booleanDerivative (f + g) e =
        FABL.booleanDerivative f e + (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂)) := by
      funext x
      rw [booleanDerivative_add]
      simp only [Pi.add_apply]
      change FABL.booleanDerivative f e x +
          (repairDerivative f e 1 x + repairDerivative f e 1 (x + e)) =
        FABL.booleanDerivative f e x + 1
      rw [repairDerivative_pair f he 1 x]
    have hautoSign : autocorrelation (f + g) e = -autocorrelation f e := by
      have hmul := autocorrelation_add_of_isLinearStructure f g
        (repairDerivative_pair f he 1)
      simpa [bitSignInt] using hmul
    have hrepairReal :
        2 * (hammingDistance f g : ℝ) =
          (hammingWeight (FABL.booleanDerivative f e +
            (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂))) : ℝ) := by
      exact_mod_cast hrepair
    rw [hderivative] at hautoRepair
    have habs : |autocorrelation f e| = -autocorrelation f e := abs_of_neg hneg
    rw [← hmax, habs]
    linarith

/-- Carlet's exact formula for the distance to functions admitting a nonzero linear structure. -/
theorem distanceToLinearStructures_cast_eq
    (hn : 2 ≤ n) (f : BooleanFunction n) :
    (distanceToLinearStructures f : ℝ) =
      (2 : ℝ) ^ n / 4 - absoluteIndicator f / 4 := by
  have hnpos : 0 < n := by omega
  obtain ⟨gmin, hgmin, hmin⟩ :=
    exists_hammingDistance_eq_distanceToLinearStructures hnpos f
  obtain ⟨grepair, hgrepair, hrepair⟩ :=
    exists_repairDerivative_at_absoluteIndicator hnpos f
  apply le_antisymm
  · calc
      (distanceToLinearStructures f : ℝ) ≤ (hammingDistance f grepair : ℝ) := by
        exact_mod_cast distanceToLinearStructures_le_hammingDistance hnpos f grepair hgrepair
      _ = ((2 : ℝ) ^ n - absoluteIndicator f) / 4 := hrepair
      _ = (2 : ℝ) ^ n / 4 - absoluteIndicator f / 4 := by ring
  · rw [← hmin]
    have hlower := distance_lower_bound_of_hasNonzeroLinearStructure f gmin hgmin
    linarith

/-- Distance to linear structures is no larger than ordinary nonlinearity. -/
theorem distanceToLinearStructures_le_nonlinearity
    (hn : 2 ≤ n) (f : BooleanFunction n) :
    distanceToLinearStructures f ≤ nonlinearity f := by
  classical
  unfold nonlinearity
  apply Finset.le_inf'
  intro p _hp
  apply distanceToLinearStructures_le_hammingDistance (by omega) f
  obtain ⟨e, he⟩ := exists_nonzero_direction (by omega : 0 < n)
  refine ⟨e, he, FABL.f₂DotProduct p.2 e, ?_⟩
  intro x
  have hzero := ZModModule.add_self (p.1 + FABL.f₂DotProduct p.2 x)
  have hzero' : p.1 + p.2 ⬝ᵥ x + (p.1 + p.2 ⬝ᵥ x) = 0 := by
    simpa [FABL.f₂DotProduct] using hzero
  simp only [FABL.booleanDerivative, FABL.affineFunction, FABL.f₂DotProduct,
    dotProduct_add]
  calc
    p.1 + p.2 ⬝ᵥ x + (p.1 + (p.2 ⬝ᵥ x + p.2 ⬝ᵥ e)) =
        (p.1 + p.2 ⬝ᵥ x + (p.1 + p.2 ⬝ᵥ x)) + p.2 ⬝ᵥ e := by abel
    _ = p.2 ⬝ᵥ e := by rw [hzero', zero_add]

/-- Every Boolean function is at distance at most `2^(n-2)` from a function with a nonzero
linear structure. -/
theorem distanceToLinearStructures_le_two_pow
    (hn : 2 ≤ n) (f : BooleanFunction n) :
    distanceToLinearStructures f ≤ 2 ^ (n - 2) := by
  have hreal : (distanceToLinearStructures f : ℝ) ≤ (2 ^ (n - 2) : ℕ) := by
    rw [distanceToLinearStructures_cast_eq hn]
    push_cast
    have hnonneg : 0 ≤ absoluteIndicator f := by
      unfold absoluteIndicator
      positivity
    have hpow : ((2 : ℝ) ^ (n - 2)) = (2 : ℝ) ^ n / 4 := by
      have h := pow_sub_mul_pow (2 : ℝ) (by omega : 2 ≤ n)
      calc
        (2 : ℝ) ^ (n - 2) = ((2 : ℝ) ^ (n - 2) * 4) / 4 := by ring
        _ = (2 : ℝ) ^ n / 4 := by norm_num at h ⊢; nlinarith
    rw [hpow]
    linarith
  exact_mod_cast hreal

/-- Vanishing nontrivial autocorrelation is equivalent to bentness. -/
theorem absoluteIndicator_eq_zero_iff_isBent
    (f : BooleanFunction n) : absoluteIndicator f = 0 ↔ IsBent f := by
  constructor
  · intro habsolute
    apply (hasFlatWalshSpectrum_iff_isBent f).1
    intro a
    have hzero (e : FABL.F₂Cube n) (he : e ≠ 0) : autocorrelation f e = 0 := by
      have habs := abs_autocorrelation_le_absoluteIndicator f he
      rw [habsolute] at habs
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have hsquare : (walshTransform f a : ℝ) ^ 2 = (2 : ℝ) ^ n := by
      rw [← rawFourierTransform_autocorrelation]
      unfold rawFourierTransform
      calc
        ∑ x, autocorrelation f x * FABL.vectorWalshCharacter a x =
            autocorrelation f 0 * FABL.vectorWalshCharacter a 0 := by
          apply Finset.sum_eq_single 0
          · intro e _ he
            rw [hzero e he, zero_mul]
          · simp
        _ = (2 : ℝ) ^ n := by rw [autocorrelation_zero]; simp
    have hsqrt := congrArg Real.sqrt hsquare
    rw [Real.sqrt_sq_eq_abs] at hsqrt
    exact hsqrt
  · intro hbent
    have hflat := (hasFlatWalshSpectrum_iff_isBent f).2 hbent
    have htransform : rawFourierTransform (autocorrelation f) =
        fun _ : FABL.F₂Cube n ↦ (2 : ℝ) ^ n := by
      funext a
      rw [rawFourierTransform_autocorrelation]
      calc
        (walshTransform f a : ℝ) ^ 2 = |(walshTransform f a : ℝ)| ^ 2 :=
          (sq_abs _).symm
        _ = Real.sqrt ((2 : ℝ) ^ n) ^ 2 := by rw [hflat a]
        _ = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
    have hzero (e : FABL.F₂Cube n) (he : e ≠ 0) : autocorrelation f e = 0 := by
      have hexpect := FABL.expect_vectorWalshCharacter e
      rw [if_neg he, Fintype.expect_eq_sum_div_card] at hexpect
      have hsum : ∑ x, FABL.vectorWalshCharacter e x = 0 := by
        have hcard : (Fintype.card (FABL.F₂Cube n) : ℝ) ≠ 0 := by positivity
        exact (div_eq_zero_iff.mp hexpect).resolve_right hcard
      have hconstant :
          rawFourierTransform (fun _ : FABL.F₂Cube n ↦ (2 : ℝ) ^ n) e = 0 := by
        unfold rawFourierTransform
        calc
          ∑ x, (2 : ℝ) ^ n * FABL.vectorWalshCharacter e x =
              (2 : ℝ) ^ n * ∑ x, FABL.vectorWalshCharacter e x := by
            rw [Finset.mul_sum]
          _ = 0 := by rw [hsum, mul_zero]
      have hinvolution := rawFourierTransform_involution (autocorrelation f) e
      rw [htransform, hconstant] at hinvolution
      have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      nlinarith
    unfold absoluteIndicator
    apply NNReal.coe_eq_zero.mpr
    rw [Finset.sup_eq_zero]
    intro e he
    rw [hzero e (Finset.mem_erase.mp he).1, abs_zero, Real.toNNReal_zero]

/-- The universal `2^(n-2)` bound is attained exactly by bent Boolean functions. -/
theorem distanceToLinearStructures_eq_two_pow_iff_isBent
    (hn : 2 ≤ n) (f : BooleanFunction n) :
    distanceToLinearStructures f = 2 ^ (n - 2) ↔ IsBent f := by
  rw [← Nat.cast_inj (R := ℝ), distanceToLinearStructures_cast_eq hn]
  have hpow : ((2 : ℝ) ^ (n - 2)) = (2 : ℝ) ^ n / 4 := by
    have h := pow_sub_mul_pow (2 : ℝ) (by omega : 2 ≤ n)
    calc
      (2 : ℝ) ^ (n - 2) = ((2 : ℝ) ^ (n - 2) * 4) / 4 := by ring
      _ = (2 : ℝ) ^ n / 4 := by norm_num at h ⊢; nlinarith
  push_cast
  rw [hpow]
  have hzero : (2 : ℝ) ^ n / 4 - absoluteIndicator f / 4 =
      (2 : ℝ) ^ n / 4 ↔ absoluteIndicator f = 0 := by
    constructor
    · intro h
      linarith
    · intro h
      rw [h]
      ring
  rw [hzero]
  exact absoluteIndicator_eq_zero_iff_isBent f

end CryptBoolean
