/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderJuntaDistance
public import CryptBoolean.Carlet.Chapter04.Resiliency
public import FABL.Chapter06.Pseudorandomness.RestrictionMeanVariance

/-!
# Carlet Chapter 4 maximum correlation

Maximum correlation with functions depending on a prescribed coordinate set,
its restriction formula, and the Walsh-square bounds in Relation (40).
-/

open Finset Set
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Sign choices indexed by assignments to the coordinates in `I`.  FABL's
restriction convention makes these the fixed coordinates of the free set `Iᶜ`. -/
abbrev CoordinateSignChoice (I : Finset (Fin n)) :=
  FABL.FixedSignCube Iᶜ → FABL.Sign

/-- The Boolean function depending on `I` induced by one sign choice for each
assignment to those coordinates. -/
def coordinateBooleanFunction (I : Finset (Fin n))
    (g : CoordinateSignChoice I) : BooleanFunction n :=
  fun x ↦ FABL.binarySignEquiv.symm
    (g ((FABL.signCubeSplitEquiv Iᶜ (FABL.binaryCubeSignEquiv n x)).2))

/-- Every function represented by `coordinateBooleanFunction I` depends only
on the coordinates in `I`. -/
theorem coordinateBooleanFunction_dependsOn (I : Finset (Fin n))
    (g : CoordinateSignChoice I) :
    DependsOn (coordinateBooleanFunction I g) (I : Set (Fin n)) := by
  intro x y hxy
  apply FABL.binarySignEquiv.injective
  simp only [coordinateBooleanFunction, FABL.binarySignEquiv.apply_symm_apply]
  congr 1
  funext i
  have hiI : (i : Fin n) ∈ I := by
    simpa using i.property
  exact congrArg FABL.binarySignEquiv (hxy i hiI)

/-- The coordinate-sign representation is exactly the class of Boolean
functions depending only on `I`. -/
theorem exists_coordinateSignChoice_iff_dependsOn
    (I : Finset (Fin n)) (g : BooleanFunction n) :
    (∃ q : CoordinateSignChoice I, coordinateBooleanFunction I q = g) ↔
      DependsOn g (I : Set (Fin n)) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact coordinateBooleanFunction_dependsOn I q
  · intro hdepends
    let q : CoordinateSignChoice I := fun z ↦
      FABL.signEncode
        (g ((FABL.binaryCubeSignEquiv n).symm
          (FABL.combineSignCube Iᶜ (fun _ ↦ 1) z)))
    refine ⟨q, funext fun x ↦ ?_⟩
    let s : {−1,1}^[n] := FABL.binaryCubeSignEquiv n x
    let z : FABL.FixedSignCube Iᶜ :=
      ((FABL.signCubeSplitEquiv Iᶜ) s).2
    let x₀ : FABL.F₂Cube n :=
      (FABL.binaryCubeSignEquiv n).symm
        (FABL.combineSignCube Iᶜ (fun _ ↦ 1) z)
    have hx₀x : ∀ i ∈ (I : Set (Fin n)), x₀ i = x i := by
      intro i hiI
      have hiFixed : i ∉ Iᶜ := by simpa using hiI
      apply FABL.binarySignEquiv.injective
      change FABL.signEncode (x₀ i) = FABL.signEncode (x i)
      rw [← FABL.binaryCubeSignEquiv_apply,
        ← FABL.binaryCubeSignEquiv_apply]
      have hx₀sign : FABL.binaryCubeSignEquiv n x₀ =
          FABL.combineSignCube Iᶜ (fun _ ↦ 1) z := by
        dsimp [x₀]
        exact (FABL.binaryCubeSignEquiv n).apply_symm_apply _
      rw [hx₀sign]
      rw [show FABL.combineSignCube Iᶜ (fun _ ↦ 1) z i =
          z ⟨i, hiFixed⟩ by
        exact FABL.combineSignCube_apply_fixed Iᶜ (fun _ ↦ 1) z
          ⟨i, hiFixed⟩]
      have hreconstruct :
          FABL.combineSignCube Iᶜ
              ((FABL.signCubeSplitEquiv Iᶜ s).1)
              ((FABL.signCubeSplitEquiv Iᶜ s).2) = s :=
        (FABL.signCubeSplitEquiv Iᶜ).symm_apply_apply s
      have hi := congrFun hreconstruct i
      rw [show FABL.combineSignCube Iᶜ
          ((FABL.signCubeSplitEquiv Iᶜ s).1)
          ((FABL.signCubeSplitEquiv Iᶜ s).2) i =
          ((FABL.signCubeSplitEquiv Iᶜ s).2) ⟨i, hiFixed⟩ by
        exact FABL.combineSignCube_apply_fixed Iᶜ
          ((FABL.signCubeSplitEquiv Iᶜ s).1)
          ((FABL.signCubeSplitEquiv Iᶜ s).2) ⟨i, hiFixed⟩] at hi
      exact hi
    have hg : g x₀ = g x := hdepends hx₀x
    change FABL.binarySignEquiv.symm
        (FABL.signEncode (g x₀)) = g x
    rw [show FABL.signEncode (g x₀) = FABL.binarySignEquiv (g x₀) by rfl,
      FABL.binarySignEquiv.symm_apply_apply, hg]

/-- A normalized correlation, with Carlet's raw zero-frequency Walsh sum made
explicit before division by the cube cardinality. -/
noncomputable def normalizedCorrelation
    (f g : BooleanFunction n) : ℝ :=
  (walshTransform (f + g) 0 : ℝ) / (2 : ℝ) ^ n

/-- Normalized correlation is one minus twice relative Hamming distance. -/
theorem normalizedCorrelation_eq_one_sub_two_mul_hammingDistance
    (f g : BooleanFunction n) :
    normalizedCorrelation f g =
      1 - 2 * (hammingDistance f g : ℝ) / (2 : ℝ) ^ n := by
  rw [normalizedCorrelation, walshTransform_zero_eq_two_pow_sub_two_weight,
    ← hammingDistance_eq_hammingWeight_add]
  push_cast
  field_simp

/-- Carlet's `BF_{I,n}` distance: minimum raw Hamming distance to a Boolean
function depending only on the coordinates in `I`. -/
noncomputable def distanceToCoordinateFunctions
    (f : BooleanFunction n) (I : Finset (Fin n)) : ℕ :=
  (Finset.univ : Finset (CoordinateSignChoice I)).inf'
    Finset.univ_nonempty fun g ↦
      hammingDistance f (coordinateBooleanFunction I g)

/-- Carlet's maximum correlation `C_f(I)`, as the maximum normalized raw
correlation with a Boolean function depending only on `I`. -/
noncomputable def maximumCorrelation
    (f : BooleanFunction n) (I : Finset (Fin n)) : ℝ :=
  (Finset.univ : Finset (CoordinateSignChoice I)).sup'
    Finset.univ_nonempty fun g ↦
      normalizedCorrelation f (coordinateBooleanFunction I g)

/-- The source distance formula `d_H(f,BF_{I,n}) = 2^(n-1)(1-C_f(I))`,
written as `2^n / 2` so that it also has the intended meaning at `n = 0`. -/
theorem distanceToCoordinateFunctions_cast_eq
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    (distanceToCoordinateFunctions f I : ℝ) =
      (2 : ℝ) ^ n / 2 * (1 - maximumCorrelation f I) := by
  classical
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  apply le_antisymm
  · have hmaximum :
        maximumCorrelation f I ≤
          1 - 2 * (distanceToCoordinateFunctions f I : ℝ) /
            (2 : ℝ) ^ n := by
      unfold maximumCorrelation
      apply Finset.sup'_le Finset.univ_nonempty
      intro g _hg
      rw [normalizedCorrelation_eq_one_sub_two_mul_hammingDistance]
      have hdist := Finset.inf'_le
        (fun q : CoordinateSignChoice I ↦
          hammingDistance f (coordinateBooleanFunction I q))
        (Finset.mem_univ g)
      have hdistReal :
          (distanceToCoordinateFunctions f I : ℝ) ≤
            (hammingDistance f (coordinateBooleanFunction I g) : ℝ) := by
        exact_mod_cast hdist
      have hscaled :=
        (div_le_div_iff_of_pos_right hpow).mpr
          (mul_le_mul_of_nonneg_left hdistReal (by norm_num : (0 : ℝ) ≤ 2))
      linarith
    calc
      (distanceToCoordinateFunctions f I : ℝ) =
          (2 : ℝ) ^ n / 2 *
            (1 - (1 - 2 * (distanceToCoordinateFunctions f I : ℝ) /
              (2 : ℝ) ^ n)) := by
        field_simp
        ring
      _ ≤ (2 : ℝ) ^ n / 2 * (1 - maximumCorrelation f I) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hmaximum 1) (by positivity)
  · obtain ⟨g, _hg, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (CoordinateSignChoice I)))
      Finset.univ_nonempty
      (fun g ↦ hammingDistance f (coordinateBooleanFunction I g))
    have hmin' : distanceToCoordinateFunctions f I =
        hammingDistance f (coordinateBooleanFunction I g) := by
      simpa [distanceToCoordinateFunctions] using hmin
    have hsup := Finset.le_sup'
      (fun q : CoordinateSignChoice I ↦
        normalizedCorrelation f (coordinateBooleanFunction I q))
      (Finset.mem_univ g)
    have hsup' :
        normalizedCorrelation f (coordinateBooleanFunction I g) ≤
          maximumCorrelation f I := by
      simpa [maximumCorrelation] using hsup
    rw [normalizedCorrelation_eq_one_sub_two_mul_hammingDistance,
      ← hmin'] at hsup'
    calc
      (2 : ℝ) ^ n / 2 * (1 - maximumCorrelation f I) ≤
          (2 : ℝ) ^ n / 2 *
            (1 - (1 - 2 * (distanceToCoordinateFunctions f I : ℝ) /
              (2 : ℝ) ^ n)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hsup' 1) (by positivity)
      _ = (distanceToCoordinateFunctions f I : ℝ) := by
        field_simp
        ring

/-- Distance to functions on a prescribed `r`-coordinate set is at least the
order-`r` nonlinearity. -/
theorem higherOrderNonlinearity_le_distanceToCoordinateFunctions
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    higherOrderNonlinearity I.card f ≤ distanceToCoordinateFunctions f I := by
  classical
  unfold distanceToCoordinateFunctions
  apply Finset.le_inf'
  intro g _hg
  exact higherOrderNonlinearity_le_hammingDistance_of_dependsOn
    I.card f (coordinateBooleanFunction I g) I rfl
      (coordinateBooleanFunction_dependsOn I g)

/-- The normalized absolute imbalance of the restrictions obtained by fixing
the coordinates in `I`. -/
noncomputable def restrictionMaximumCorrelation
    (f : BooleanFunction n) (I : Finset (Fin n)) : ℝ :=
  𝔼 z : FABL.FixedSignCube Iᶜ,
    |FABL.mean
      (FABL.signRestriction (signCubeView f).toReal Iᶜ z)|

private theorem realSignView_coordinateBooleanFunction_add
    (f : BooleanFunction n) (I : Finset (Fin n))
    (g : CoordinateSignChoice I) (x : FABL.F₂Cube n) :
    realSignView (f + coordinateBooleanFunction I g) x =
      realSignView f x *
        FABL.signValue
          (g ((FABL.signCubeSplitEquiv Iᶜ
            (FABL.binaryCubeSignEquiv n x)).2)) := by
  unfold realSignView FABL.realSignEncodedFunction FABL.signEncodedFunction
    coordinateBooleanFunction
  rw [Pi.add_apply, FABL.signEncode_add]
  have hdecode :
      FABL.signEncode
          (FABL.binarySignEquiv.symm
            (g ((FABL.signCubeSplitEquiv Iᶜ
              (FABL.binaryCubeSignEquiv n x)).2))) =
        g ((FABL.signCubeSplitEquiv Iᶜ
          (FABL.binaryCubeSignEquiv n x)).2) := by
    exact FABL.binarySignEquiv.apply_symm_apply _
  rw [hdecode]
  simp [FABL.signValue]

private theorem normalizedCorrelation_coordinateBooleanFunction_eq
    (f : BooleanFunction n) (I : Finset (Fin n))
    (g : CoordinateSignChoice I) :
    normalizedCorrelation f (coordinateBooleanFunction I g) =
      𝔼 z : FABL.FixedSignCube Iᶜ,
        FABL.signValue (g z) *
          FABL.mean
            (FABL.signRestriction (signCubeView f).toReal Iᶜ z) := by
  classical
  rw [normalizedCorrelation,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hpow]
  rw [FABL.vectorFourierCoeff_eq_expect]
  have hcharacter (x : FABL.F₂Cube n) :
      FABL.vectorWalshCharacter 0 x = 1 := by
    rw [FABL.vectorWalshCharacter_apply]
    simp [FABL.f₂DotProduct, dotProduct]
  simp_rw [hcharacter, mul_one]
  let e : FABL.F₂Cube n ≃
      FABL.FreeSignCube Iᶜ × FABL.FixedSignCube Iᶜ :=
    (FABL.binaryCubeSignEquiv n).trans (FABL.signCubeSplitEquiv Iᶜ)
  calc
    (𝔼 x : FABL.F₂Cube n,
        realSignView (f + coordinateBooleanFunction I g) x) =
        𝔼 yz : FABL.FreeSignCube Iᶜ × FABL.FixedSignCube Iᶜ,
          FABL.signValue (g yz.2) *
            (signCubeView f).toReal
              (FABL.combineSignCube Iᶜ yz.1 yz.2) := by
      apply Fintype.expect_equiv e
      intro x
      rw [realSignView_coordinateBooleanFunction_add]
      change realSignView f x * FABL.signValue (g (e x).2) =
        FABL.signValue (g (e x).2) *
          (signCubeView f).toReal
            (FABL.combineSignCube Iᶜ (e x).1 (e x).2)
      rw [mul_comm]
      congr 1
      rw [signCubeView_toReal]
      change realSignView f x =
        realSignView f
          ((FABL.binaryCubeSignEquiv n).symm
            (FABL.combineSignCube Iᶜ (e x).1 (e x).2))
      congr 1
      apply (FABL.binaryCubeSignEquiv n).injective
      rw [(FABL.binaryCubeSignEquiv n).apply_symm_apply]
      change FABL.binaryCubeSignEquiv n x =
        (FABL.signCubeSplitEquiv Iᶜ).symm
          ((FABL.signCubeSplitEquiv Iᶜ)
            (FABL.binaryCubeSignEquiv n x))
      exact ((FABL.signCubeSplitEquiv Iᶜ).symm_apply_apply _).symm
    _ = 𝔼 z : FABL.FixedSignCube Iᶜ,
          𝔼 y : FABL.FreeSignCube Iᶜ,
            FABL.signValue (g z) *
              (signCubeView f).toReal
                (FABL.combineSignCube Iᶜ y z) := by
      calc
        (𝔼 yz : FABL.FreeSignCube Iᶜ × FABL.FixedSignCube Iᶜ,
            FABL.signValue (g yz.2) *
              (signCubeView f).toReal
                (FABL.combineSignCube Iᶜ yz.1 yz.2)) =
            𝔼 y : FABL.FreeSignCube Iᶜ,
              𝔼 z : FABL.FixedSignCube Iᶜ,
                FABL.signValue (g z) *
                  (signCubeView f).toReal
                    (FABL.combineSignCube Iᶜ y z) := by
          simpa only [Finset.univ_product_univ] using
            (Finset.expect_product'
              (Finset.univ : Finset (FABL.FreeSignCube Iᶜ))
              (Finset.univ : Finset (FABL.FixedSignCube Iᶜ))
              (fun y z ↦ FABL.signValue (g z) *
                (signCubeView f).toReal
                  (FABL.combineSignCube Iᶜ y z)))
        _ = 𝔼 z : FABL.FixedSignCube Iᶜ,
              𝔼 y : FABL.FreeSignCube Iᶜ,
                FABL.signValue (g z) *
                  (signCubeView f).toReal
                    (FABL.combineSignCube Iᶜ y z) :=
          Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 z : FABL.FixedSignCube Iᶜ,
          FABL.signValue (g z) *
            FABL.mean
              (FABL.signRestriction (signCubeView f).toReal Iᶜ z) := by
      apply Finset.expect_congr rfl
      intro z _hz
      rw [← Finset.mul_expect]
      rfl

private noncomputable def maximizingCoordinateSignChoice
    (f : BooleanFunction n) (I : Finset (Fin n)) : CoordinateSignChoice I :=
  fun z ↦
    if 0 ≤ FABL.mean
        (FABL.signRestriction (signCubeView f).toReal Iᶜ z)
    then 1 else -1

private theorem maximizingCoordinateSignChoice_mul_mean
    (f : BooleanFunction n) (I : Finset (Fin n))
    (z : FABL.FixedSignCube Iᶜ) :
    FABL.signValue (maximizingCoordinateSignChoice f I z) *
        FABL.mean (FABL.signRestriction (signCubeView f).toReal Iᶜ z) =
      |FABL.mean
        (FABL.signRestriction (signCubeView f).toReal Iᶜ z)| := by
  by_cases h : 0 ≤ FABL.mean
      (FABL.signRestriction (signCubeView f).toReal Iᶜ z)
  · simp [maximizingCoordinateSignChoice, h, abs_of_nonneg h]
  · have hneg : FABL.mean
        (FABL.signRestriction (signCubeView f).toReal Iᶜ z) < 0 :=
      lt_of_not_ge h
    simp [maximizingCoordinateSignChoice, h, abs_of_neg hneg]

/-- The maximum correlation is the average absolute imbalance of all
restrictions obtained by fixing the coordinates in `I`. -/
theorem maximumCorrelation_eq_restrictionMaximumCorrelation
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    maximumCorrelation f I = restrictionMaximumCorrelation f I := by
  classical
  unfold maximumCorrelation restrictionMaximumCorrelation
  apply le_antisymm
  · apply Finset.sup'_le
    intro g _hg
    rw [normalizedCorrelation_coordinateBooleanFunction_eq]
    apply Finset.expect_le_expect
    intro z _hz
    rcases Int.units_eq_one_or (g z) with hz | hz
    · simp [hz, le_abs_self]
    · simp [hz, neg_le_abs]
  · have hle := Finset.le_sup'
      (fun g : CoordinateSignChoice I ↦
        normalizedCorrelation f (coordinateBooleanFunction I g))
      (Finset.mem_univ (maximizingCoordinateSignChoice f I))
    rw [normalizedCorrelation_coordinateBooleanFunction_eq] at hle
    simpa only [maximizingCoordinateSignChoice_mul_mean] using hle

/-- The unnormalized sign imbalance of the restriction obtained by fixing
the coordinates in `I` to `z`. -/
noncomputable def restrictionRawImbalance
    (f : BooleanFunction n) (I : Finset (Fin n))
    (z : FABL.FixedSignCube Iᶜ) : ℝ :=
  ∑ y : FABL.FreeSignCube Iᶜ,
    (signCubeView f).toReal (FABL.combineSignCube Iᶜ y z)

/-- Carlet's displayed restriction formula:
`C_f(I) = 2⁻ⁿ ∑_z |ℱ(f|_z)|`. -/
theorem maximumCorrelation_eq_sum_abs_restrictionRawImbalance_div_two_pow
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    maximumCorrelation f I =
      (∑ z : FABL.FixedSignCube Iᶜ, |restrictionRawImbalance f I z|) /
        (2 : ℝ) ^ n := by
  classical
  rw [maximumCorrelation_eq_restrictionMaximumCorrelation]
  unfold restrictionMaximumCorrelation restrictionRawImbalance FABL.mean
  simp_rw [Fintype.expect_eq_sum_div_card]
  have hfreePos :
      (0 : ℝ) < Fintype.card (FABL.FreeSignCube Iᶜ) := by positivity
  have hfixedPos :
      (0 : ℝ) < Fintype.card (FABL.FixedSignCube Iᶜ) := by positivity
  have hcard :
      (Fintype.card (FABL.FreeSignCube Iᶜ) : ℝ) *
          Fintype.card (FABL.FixedSignCube Iᶜ) =
        (2 : ℝ) ^ n := by
    have hcardNat := Fintype.card_congr
      ((FABL.binaryCubeSignEquiv n).trans (FABL.signCubeSplitEquiv Iᶜ))
    rw [Fintype.card_prod, card_f₂Cube] at hcardNat
    exact_mod_cast hcardNat.symm
  simp_rw [FABL.signRestriction_apply]
  simp_rw [abs_div, abs_of_pos hfreePos]
  rw [← Finset.sum_div]
  calc
    ((∑ z : FABL.FixedSignCube Iᶜ,
        |∑ y : FABL.FreeSignCube Iᶜ,
          (signCubeView f).toReal (FABL.combineSignCube Iᶜ y z)|) /
          Fintype.card (FABL.FreeSignCube Iᶜ)) /
        Fintype.card (FABL.FixedSignCube Iᶜ) =
      (∑ z : FABL.FixedSignCube Iᶜ,
        |∑ y : FABL.FreeSignCube Iᶜ,
          (signCubeView f).toReal (FABL.combineSignCube Iᶜ y z)|) /
        ((Fintype.card (FABL.FreeSignCube Iᶜ) : ℝ) *
          Fintype.card (FABL.FixedSignCube Iᶜ)) := by
      field_simp
    _ = (∑ z : FABL.FixedSignCube Iᶜ,
          |∑ y : FABL.FreeSignCube Iᶜ,
            (signCubeView f).toReal (FABL.combineSignCube Iᶜ y z)|) /
        (2 : ℝ) ^ n := by rw [hcard]

/-- Maximum correlation vanishes exactly when every restriction obtained by
fixing `I` is balanced. -/
theorem maximumCorrelation_eq_zero_iff_restrictions_balanced
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    maximumCorrelation f I = 0 ↔
      ∀ z : FABL.FixedSignCube Iᶜ,
        FABL.IsBalanced
          (FABL.signRestriction (signCubeView f).toReal Iᶜ z) := by
  rw [maximumCorrelation_eq_restrictionMaximumCorrelation]
  unfold restrictionMaximumCorrelation
  constructor
  · intro h z
    rw [FABL.IsBalanced]
    have hfun :
        (fun z : FABL.FixedSignCube Iᶜ ↦
          |FABL.mean
            (FABL.signRestriction (signCubeView f).toReal Iᶜ z)|) = 0 :=
      (Fintype.expect_eq_zero_iff_of_nonneg
        (fun z ↦ abs_nonneg _)).mp h
    have hz := congrFun hfun z
    exact abs_eq_zero.mp hz
  · intro h
    apply Finset.expect_eq_zero
    intro z _hz
    rw [h z, abs_zero]

/-- The raw Walsh square mass on frequencies supported inside `I`. -/
noncomputable def restrictedWalshSquareSum
    (f : BooleanFunction n) (I : Finset (Fin n)) : ℝ :=
  ∑ u : {u : FABL.F₂Cube n // FABL.f₂Support u ⊆ I},
    (walshTransform f u.1 : ℝ) ^ 2

/-- The subtype-indexed definition is exactly Carlet's displayed filtered
sum over ambient frequencies. -/
theorem restrictedWalshSquareSum_eq_sum_filter
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    restrictedWalshSquareSum f I =
      ∑ u ∈ (Finset.univ.filter
        fun u : FABL.F₂Cube n ↦ FABL.f₂Support u ⊆ I),
        (walshTransform f u : ℝ) ^ 2 := by
  classical
  unfold restrictedWalshSquareSum
  symm
  exact Finset.sum_subtype
    (Finset.univ.filter
      fun u : FABL.F₂Cube n ↦ FABL.f₂Support u ⊆ I)
    (fun u ↦ by simp) (fun u ↦ (walshTransform f u : ℝ) ^ 2)

private theorem liftFixedFrequency_subset_coordinates
    (I : Finset (Fin n)) (T : Finset (FABL.FixedIndex Iᶜ)) :
    FABL.liftFixedFrequency T ⊆ I := by
  intro i hi
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
  simpa using j.property

private theorem fixedFrequencyPart_liftFixedFrequency
    (J : Finset (Fin n)) (T : Finset (FABL.FixedIndex J)) :
    FABL.fixedFrequencyPart J (FABL.liftFixedFrequency T) = T := by
  ext i
  constructor
  · intro hi
    have hilift : (i : Fin n) ∈ FABL.liftFixedFrequency T :=
      (FABL.mem_fixedFrequencyPart J (FABL.liftFixedFrequency T) i).mp hi
    obtain ⟨j, hjT, hji⟩ := Finset.mem_map.mp hilift
    have hji' : j = i := Subtype.ext hji
    simpa [hji'] using hjT
  · intro hi
    apply (FABL.mem_fixedFrequencyPart J (FABL.liftFixedFrequency T) i).mpr
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem liftFixedFrequency_fixedFrequencyPart_eq_of_subset
    (I S : Finset (Fin n)) (hSI : S ⊆ I) :
    FABL.liftFixedFrequency (FABL.fixedFrequencyPart Iᶜ S) = S := by
  have hfree : FABL.freeFrequencyPart Iᶜ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiS : (i : Fin n) ∈ S :=
      (FABL.mem_freeFrequencyPart Iᶜ S i).mp hi
    exact (Finset.mem_compl.mp i.property) (hSI hiS)
  have hsplit :=
    FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart Iᶜ S
  rw [hfree] at hsplit
  simpa [FABL.liftFreeFrequency] using hsplit

private noncomputable def fixedFrequencyEquivSupportedCube
    (I : Finset (Fin n)) :
    Finset (FABL.FixedIndex Iᶜ) ≃
      {u : FABL.F₂Cube n // FABL.f₂Support u ⊆ I} where
  toFun T :=
    ⟨FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T), by
      rw [← FABL.f₂CubeEquivFinset_apply,
        ← FABL.f₂CubeEquivFinset_symm_apply,
        (FABL.f₂CubeEquivFinset n).apply_symm_apply]
      exact liftFixedFrequency_subset_coordinates I T⟩
  invFun u := FABL.fixedFrequencyPart Iᶜ (FABL.f₂Support u.1)
  left_inv T := by
    change FABL.fixedFrequencyPart Iᶜ
      (FABL.f₂Support
        (FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T))) = T
    rw [← FABL.f₂CubeEquivFinset_apply,
      ← FABL.f₂CubeEquivFinset_symm_apply,
      (FABL.f₂CubeEquivFinset n).apply_symm_apply]
    exact fixedFrequencyPart_liftFixedFrequency Iᶜ T
  right_inv u := by
    apply Subtype.ext
    change FABL.f₂CubeOfFinset
      (FABL.liftFixedFrequency
        (FABL.fixedFrequencyPart Iᶜ (FABL.f₂Support u.1))) = u.1
    apply (FABL.f₂CubeEquivFinset n).injective
    change (FABL.f₂CubeEquivFinset n)
        ((FABL.f₂CubeEquivFinset n).symm
          (FABL.liftFixedFrequency
            (FABL.fixedFrequencyPart Iᶜ (FABL.f₂Support u.1)))) =
      (FABL.f₂CubeEquivFinset n) u.1
    rw [(FABL.f₂CubeEquivFinset n).apply_symm_apply,
      FABL.f₂CubeEquivFinset_apply]
    exact liftFixedFrequency_fixedFrequencyPart_eq_of_subset
      I (FABL.f₂Support u.1) u.2

private theorem restrictedWalshSquareSum_eq_sum_fixedFrequency
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    restrictedWalshSquareSum f I =
      ∑ T : Finset (FABL.FixedIndex Iᶜ),
        (walshTransform f
          (FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T)) : ℝ) ^ 2 := by
  classical
  unfold restrictedWalshSquareSum
  symm
  apply Fintype.sum_equiv (fixedFrequencyEquivSupportedCube I)
  intro T
  rfl

private theorem walshTransform_f₂CubeOfFinset_liftFixedFrequency
    (f : BooleanFunction n) (I : Finset (Fin n))
    (T : Finset (FABL.FixedIndex Iᶜ)) :
    (walshTransform f
        (FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T)) : ℝ) =
      (2 : ℝ) ^ n *
        FABL.fourierCoeff (signCubeView f).toReal
          (FABL.liftFixedFrequency T) := by
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
    ← signCubeView_toReal]
  rw [← FABL.f₂CubeEquivFinset_apply,
    ← FABL.f₂CubeEquivFinset_symm_apply,
    (FABL.f₂CubeEquivFinset n).apply_symm_apply]

/-- The Walsh square mass on `I` is the cube-cardinality square times the
second moment of the corresponding restriction imbalances. -/
theorem two_pow_sq_mul_expect_restrictionMean_sq_eq_restrictedWalshSquareSum
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    ((2 : ℝ) ^ n) ^ 2 *
        (𝔼 z : FABL.FixedSignCube Iᶜ,
          FABL.mean
            (FABL.signRestriction (signCubeView f).toReal Iᶜ z) ^ 2) =
      restrictedWalshSquareSum f I := by
  classical
  rw [restrictedWalshSquareSum_eq_sum_fixedFrequency]
  have hmean :
      (𝔼 z : FABL.FixedSignCube Iᶜ,
          FABL.mean
            (FABL.signRestriction (signCubeView f).toReal Iᶜ z) ^ 2) =
        ∑ T : Finset (FABL.FixedIndex Iᶜ),
          FABL.fourierCoeff (signCubeView f).toReal
            (FABL.liftFixedFrequency T) ^ 2 := by
    simp_rw [FABL.mean_signRestriction_eq_restrictionFourierCoeff_empty]
    simpa [FABL.liftFreeFrequency] using
      FABL.expect_sq_restrictionFourierCoeff
        (signCubeView f).toReal Iᶜ
          (∅ : Finset (Iᶜ : Finset (Fin n)))
  rw [hmean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [walshTransform_f₂CubeOfFinset_liftFixedFrequency]
  ring

private theorem expect_abs_le_sqrt_expect_sq
    {X : Type*} [Fintype X] [Nonempty X] (q : X → ℝ) :
    (𝔼 x, |q x|) ≤ Real.sqrt (𝔼 x, q x ^ 2) := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset X) (fun x ↦ |q x|) (fun _ ↦ (1 : ℝ))
  have hsq : (𝔼 x, |q x|) ^ 2 ≤ 𝔼 x, q x ^ 2 := by
    simpa [sq_abs] using hcs
  have hleft : 0 ≤ 𝔼 x, |q x| :=
    Finset.expect_nonneg fun x _ ↦ abs_nonneg (q x)
  have hright : 0 ≤ 𝔼 x, q x ^ 2 :=
    Finset.expect_nonneg fun x _ ↦ sq_nonneg (q x)
  apply (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hright]
  exact hsq

/-- The first inequality in Carlet Relation (40). -/
theorem maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    maximumCorrelation f I ≤
      Real.sqrt (restrictedWalshSquareSum f I) / (2 : ℝ) ^ n := by
  rw [maximumCorrelation_eq_restrictionMaximumCorrelation]
  unfold restrictionMaximumCorrelation
  let q : FABL.FixedSignCube Iᶜ → ℝ := fun z ↦
    FABL.mean (FABL.signRestriction (signCubeView f).toReal Iᶜ z)
  have hcauchy : (𝔼 z, |q z|) ≤ Real.sqrt (𝔼 z, q z ^ 2) :=
    expect_abs_le_sqrt_expect_sq q
  have hscaled :=
    two_pow_sq_mul_expect_restrictionMean_sq_eq_restrictedWalshSquareSum f I
  change ((2 : ℝ) ^ n) ^ 2 * (𝔼 z, q z ^ 2) =
    restrictedWalshSquareSum f I at hscaled
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  apply (le_div_iff₀ hpow).mpr
  calc
    (𝔼 z, |q z|) * (2 : ℝ) ^ n ≤
        Real.sqrt (𝔼 z, q z ^ 2) * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hcauchy hpow.le
    _ = Real.sqrt (restrictedWalshSquareSum f I) := by
      rw [← hscaled, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ n)),
        Real.sqrt_sq_eq_abs, abs_of_pos hpow]
      ring

private theorem walshTransform_abs_le_maxWalshMagnitude
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    |(walshTransform f u : ℝ)| ≤ (maxWalshMagnitude f : ℝ) := by
  have hnat := Finset.le_sup'
    (fun a : FABL.F₂Cube n ↦ (walshTransform f a).natAbs)
    (Finset.mem_univ u)
  change (walshTransform f u).natAbs ≤ maxWalshMagnitude f at hnat
  have hcast : ((walshTransform f u).natAbs : ℝ) ≤
      (maxWalshMagnitude f : ℝ) := by
    exact_mod_cast hnat
  simpa [Nat.cast_natAbs, Int.cast_abs] using hcast

/-- The supported Walsh square mass is at most the number of supported
frequencies times the square of the largest Walsh magnitude. -/
theorem restrictedWalshSquareSum_le_card_mul_maxWalshMagnitude_sq
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    restrictedWalshSquareSum f I ≤
      (2 : ℝ) ^ I.card * (maxWalshMagnitude f : ℝ) ^ 2 := by
  classical
  rw [restrictedWalshSquareSum_eq_sum_fixedFrequency]
  calc
    (∑ T : Finset (FABL.FixedIndex Iᶜ),
        (walshTransform f
          (FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T)) : ℝ) ^ 2) ≤
        ∑ _T : Finset (FABL.FixedIndex Iᶜ),
          (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro T _hT
      have habs := walshTransform_abs_le_maxWalshMagnitude f
        (FABL.f₂CubeOfFinset (FABL.liftFixedFrequency T))
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
      simpa only [sq_abs] using hsquare
    _ = (2 : ℝ) ^ I.card * (maxWalshMagnitude f : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_finset]
      simp [FABL.FixedIndex]

/-- The square-root form of the second inequality in Relation (40). -/
theorem sqrt_restrictedWalshSquareSum_le
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    Real.sqrt (restrictedWalshSquareSum f I) ≤
      Real.sqrt ((2 : ℝ) ^ I.card) * (maxWalshMagnitude f : ℝ) := by
  have hsqrt := Real.sqrt_le_sqrt
    (restrictedWalshSquareSum_le_card_mul_maxWalshMagnitude_sq f I)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ maxWalshMagnitude f)] at hsqrt
  exact hsqrt

/-- Both maximum-correlation bounds in Carlet Relation (40), with the second
one written in its printed real-exponent and nonlinearity form. -/
theorem relation_40_maximumCorrelation_bound
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    maximumCorrelation f I ≤
        Real.sqrt (restrictedWalshSquareSum f I) / (2 : ℝ) ^ n ∧
      maximumCorrelation f I ≤
        (2 : ℝ) ^ (-(n : ℝ) + (I.card : ℝ) / 2) *
          ((2 : ℝ) ^ n - 2 * (nonlinearity f : ℝ)) := by
  refine ⟨maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div f I, ?_⟩
  calc
    maximumCorrelation f I ≤
        Real.sqrt (restrictedWalshSquareSum f I) / (2 : ℝ) ^ n :=
      maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div f I
    _ ≤ (Real.sqrt ((2 : ℝ) ^ I.card) *
          (maxWalshMagnitude f : ℝ)) / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right
        (sqrt_restrictedWalshSquareSum_le f I) (by positivity)
    _ = (2 : ℝ) ^ (-(n : ℝ) + (I.card : ℝ) / 2) *
          ((2 : ℝ) ^ n - 2 * (nonlinearity f : ℝ)) := by
      rw [sqrt_two_pow_eq_rpow]
      have hrelation := congrArg (fun k : ℕ ↦ (k : ℝ))
        (two_mul_nonlinearity_add_maxWalshMagnitude f)
      push_cast at hrelation
      rw [show (maxWalshMagnitude f : ℝ) =
          (2 : ℝ) ^ n - 2 * (nonlinearity f : ℝ) by linarith]
      rw [show -(n : ℝ) + (I.card : ℝ) / 2 =
          (I.card : ℝ) / 2 - (n : ℝ) by ring,
        Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
        Real.rpow_natCast]
      ring

/-- The first equivalent distance bound in Relation (40). -/
theorem distanceToCoordinateFunctions_cast_ge_walshSquare
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    (2 : ℝ) ^ n / 2 -
        Real.sqrt (restrictedWalshSquareSum f I) / 2 ≤
      (distanceToCoordinateFunctions f I : ℝ) := by
  rw [distanceToCoordinateFunctions_cast_eq]
  have hcorrelation :=
    maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div f I
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  calc
    (2 : ℝ) ^ n / 2 -
        Real.sqrt (restrictedWalshSquareSum f I) / 2 =
        (2 : ℝ) ^ n / 2 *
          (1 - Real.sqrt (restrictedWalshSquareSum f I) /
            (2 : ℝ) ^ n) := by
      field_simp
    _ ≤ (2 : ℝ) ^ n / 2 * (1 - maximumCorrelation f I) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left hcorrelation 1) (by positivity)

/-- The second equivalent distance bound in Relation (40). -/
theorem distanceToCoordinateFunctions_cast_ge_maxWalshMagnitude
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    (2 : ℝ) ^ n / 2 -
        (2 : ℝ) ^ ((I.card : ℝ) / 2 - 1) *
          (maxWalshMagnitude f : ℝ) ≤
      (distanceToCoordinateFunctions f I : ℝ) := by
  calc
    (2 : ℝ) ^ n / 2 -
        (2 : ℝ) ^ ((I.card : ℝ) / 2 - 1) *
          (maxWalshMagnitude f : ℝ) =
        (2 : ℝ) ^ n / 2 -
          (Real.sqrt ((2 : ℝ) ^ I.card) *
            (maxWalshMagnitude f : ℝ)) / 2 := by
      rw [sqrt_two_pow_eq_rpow,
        Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    _ ≤ (2 : ℝ) ^ n / 2 -
          Real.sqrt (restrictedWalshSquareSum f I) / 2 := by
      have hsqrt := sqrt_restrictedWalshSquareSum_le f I
      linarith
    _ ≤ (distanceToCoordinateFunctions f I : ℝ) :=
      distanceToCoordinateFunctions_cast_ge_walshSquare f I

end CryptBoolean
