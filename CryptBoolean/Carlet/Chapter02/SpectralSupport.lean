/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Restrictions
public import CryptBoolean.Carlet.Chapter02.NumericalNormalForm
public import CryptBoolean.Carlet.Chapter02.Subspaces

/-!
# Carlet Chapter 2 Fourier-support bounds

Coordinate restrictions, the algebraic-degree lower bound for nonzero Boolean
functions, and the numerical-degree upper bound for pseudo-Boolean functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The support of Carlet's unnormalized Fourier transform. -/
noncomputable def rawFourierSupport (φ : PseudoBooleanFunction n) :
    Finset (FABL.F₂Cube n) :=
  FABL.vectorFourierSupport φ

@[simp] theorem mem_rawFourierSupport (φ : PseudoBooleanFunction n)
    (u : FABL.F₂Cube n) :
    u ∈ rawFourierSupport φ ↔ rawFourierTransform φ u ≠ 0 := by
  rw [rawFourierSupport, FABL.mem_vectorFourierSupport,
    rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  constructor
  · intro h
    exact mul_ne_zero (by positivity) h
  · intro h hzero
    exact h (by rw [hzero, mul_zero])

/-- Raw and normalized Fourier coefficients have exactly the same support. -/
theorem mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero
    (φ : PseudoBooleanFunction n) (u : FABL.F₂Cube n) :
    u ∈ rawFourierSupport φ ↔ FABL.vectorFourierCoeff φ u ≠ 0 := by
  rw [mem_rawFourierSupport, rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  constructor
  · intro h hzero
    exact h (by rw [hzero, mul_zero])
  · intro h
    exact mul_ne_zero (by positivity) h

/-- Carlet's unnormalized Fourier transform on a sign cube with an arbitrary finite
coordinate type. -/
noncomputable def indexedRawFourierTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : FABL.IndexedSignCube ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ x, φ x * FABL.indexedMonomial S x

/-- The support of the unnormalized Fourier transform on an indexed sign cube. -/
noncomputable def indexedRawFourierSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : FABL.IndexedSignCube ι → ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun S ↦ indexedRawFourierTransform φ S ≠ 0

@[simp] theorem mem_indexedRawFourierSupport {ι : Type*} [Fintype ι]
    [DecidableEq ι] (φ : FABL.IndexedSignCube ι → ℝ) (S : Finset ι) :
    S ∈ indexedRawFourierSupport φ ↔ indexedRawFourierTransform φ S ≠ 0 := by
  classical
  simp [indexedRawFourierSupport]

/-- An indexed raw coefficient is the cardinality-scaled normalized coefficient. -/
theorem indexedRawFourierTransform_eq_card_mul_indexedFourierCoeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : FABL.IndexedSignCube ι → ℝ) (S : Finset ι) :
    indexedRawFourierTransform φ S =
      (Fintype.card (FABL.IndexedSignCube ι) : ℝ) * FABL.indexedFourierCoeff φ S := by
  rw [indexedRawFourierTransform, FABL.indexedFourierCoeff,
    Fintype.expect_eq_sum_div_card]
  have hcard : (Fintype.card (FABL.IndexedSignCube ι) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Raw and normalized indexed Fourier coefficients have the same support. -/
theorem mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : FABL.IndexedSignCube ι → ℝ) (S : Finset ι) :
    S ∈ indexedRawFourierSupport φ ↔ FABL.indexedFourierCoeff φ S ≠ 0 := by
  rw [mem_indexedRawFourierSupport,
    indexedRawFourierTransform_eq_card_mul_indexedFourierCoeff]
  constructor
  · intro h hzero
    exact h (by rw [hzero, mul_zero])
  · intro h
    exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) h

/-- Fixing any collection of coordinates cannot increase the number of nonzero raw
Fourier coefficients. -/
theorem card_indexedRawFourierSupport_signRestriction_le
    (φ : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FABL.FixedSignCube J) :
    #(indexedRawFourierSupport (FABL.signRestriction φ J z)) ≤
      #(indexedRawFourierSupport φ) := by
  classical
  let restrictedSupport := indexedRawFourierSupport (FABL.signRestriction φ J z)
  let ambientSupport := indexedRawFourierSupport φ
  have exists_nonzero_extension (S : Finset J) (hS : S ∈ restrictedSupport) :
      ∃ T : Finset (FABL.FixedIndex J),
        FABL.fourierCoeff φ
            (FABL.liftFreeFrequency S ∪ FABL.liftFixedFrequency T) ≠ 0 := by
    have hrestricted :
        FABL.indexedFourierCoeff (FABL.signRestriction φ J z) S ≠ 0 :=
      (mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero
        (FABL.signRestriction φ J z) S).mp hS
    rw [← FABL.restrictionFourierCoeff] at hrestricted
    rw [FABL.restrictionFourierCoeff_eq_sum] at hrestricted
    by_contra hall
    push Not at hall
    apply hrestricted
    apply Finset.sum_eq_zero
    intro T _
    rw [hall T, zero_mul]
  let extensionFrequency : restrictedSupport → Finset (Fin n) := fun S ↦
    FABL.liftFreeFrequency S.1 ∪
      FABL.liftFixedFrequency (Classical.choose (exists_nonzero_extension S.1 S.2))
  have extensionFrequency_mem (S : restrictedSupport) :
      extensionFrequency S ∈ ambientSupport := by
    apply (mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero φ _).mpr
    simpa only [FABL.indexedFourierCoeff_fin_eq_fourierCoeff] using
      Classical.choose_spec (exists_nonzero_extension S.1 S.2)
  let extension : restrictedSupport → ambientSupport := fun S ↦
    ⟨extensionFrequency S, extensionFrequency_mem S⟩
  have extension_injective : Function.Injective extension := by
    intro S₁ S₂ h
    apply Subtype.ext
    apply Finset.ext
    intro i
    have hambient : extensionFrequency S₁ = extensionFrequency S₂ :=
      congrArg Subtype.val h
    have hmem := congrArg
      (fun U : Finset (Fin n) ↦ ((i : Fin n) ∈ U)) hambient
    simpa [extensionFrequency, FABL.liftFreeFrequency, FABL.liftFixedFrequency,
      i.property] using hmem
  change #restrictedSupport ≤ #ambientSupport
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective extension extension_injective

/-- The vector-indexed raw support and the finite-subset-indexed raw support have the same
cardinality under the canonical binary/sign representation bridge. -/
theorem card_indexedRawFourierSupport_binaryFunctionOnSignCube
    (φ : PseudoBooleanFunction n) :
    #(indexedRawFourierSupport (FABL.binaryFunctionOnSignCube φ)) =
      #(rawFourierSupport φ) := by
  classical
  symm
  apply Finset.card_bij (fun u _ ↦ FABL.f₂Support u)
  · intro u hu
    apply (mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero _ _).mpr
    rw [FABL.indexedFourierCoeff_fin_eq_fourierCoeff]
    rw [← FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact (mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero φ u).mp hu
  · intro u₁ hu₁ u₂ hu₂ hsupport
    exact (FABL.f₂CubeEquivFinset n).injective hsupport
  · intro S hS
    refine ⟨FABL.f₂CubeOfFinset S, ?_, ?_⟩
    · apply (mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero φ _).mpr
      rw [FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
      have hsupport : FABL.f₂Support (FABL.f₂CubeOfFinset S) = S :=
        (FABL.f₂CubeEquivFinset n).right_inv S
      rw [hsupport]
      rw [← FABL.indexedFourierCoeff_fin_eq_fourierCoeff]
      exact (mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero _ S).mp hS
    · exact (FABL.f₂CubeEquivFinset n).right_inv S

/-- Carlet's coordinate-restriction bound, stated through the canonical binary/sign bridge:
the restricted raw spectrum has no more nonzero coefficients than the ambient raw spectrum. -/
theorem card_rawFourierSupport_coordinateRestriction_le
    (φ : PseudoBooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J) :
    #(indexedRawFourierSupport
        (FABL.signRestriction (FABL.binaryFunctionOnSignCube φ) J z)) ≤
      #(rawFourierSupport φ) := by
  calc
    #(indexedRawFourierSupport
        (FABL.signRestriction (FABL.binaryFunctionOnSignCube φ) J z)) ≤
        #(indexedRawFourierSupport (FABL.binaryFunctionOnSignCube φ)) :=
      card_indexedRawFourierSupport_signRestriction_le
        (FABL.binaryFunctionOnSignCube φ) J z
    _ = #(rawFourierSupport φ) :=
      card_indexedRawFourierSupport_binaryFunctionOnSignCube φ

/-- The `{0,1}`-valued real embedding of a bit-valued Boolean function. -/
def booleanRealEmbedding (f : BooleanFunction n) : PseudoBooleanFunction n :=
  fun x ↦ if f x = 1 then 1 else 0

private def indexedF₂Support {ι : Type*} [Fintype ι]
    (x : ι → FABL.𝔽₂) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ x i ≠ 0

private noncomputable def indexedF₂CubeOfFinset {ι : Type*} [Fintype ι]
    (S : Finset ι) : ι → FABL.𝔽₂ := by
  classical
  exact fun i ↦ if i ∈ S then 1 else 0

private noncomputable def indexedF₂CubeEquivFinset (ι : Type*) [Fintype ι] :
    (ι → FABL.𝔽₂) ≃ Finset ι := by
  classical
  exact
    { toFun := indexedF₂Support
      invFun := indexedF₂CubeOfFinset
      left_inv := fun x ↦ by
        funext i
        by_cases hi : x i = 0
        · simp [indexedF₂Support, indexedF₂CubeOfFinset, hi]
        · have hi_one : x i = 1 := Fin.eq_one_of_ne_zero _ hi
          simp [indexedF₂Support, indexedF₂CubeOfFinset, hi_one]
      right_inv := fun S ↦ by
        ext i
        simp [indexedF₂Support, indexedF₂CubeOfFinset] }

private noncomputable def indexedSignCubeEquivFinset (ι : Type*) [Fintype ι] :
    FABL.IndexedSignCube ι ≃ Finset ι :=
  (Equiv.piCongrRight fun _ ↦ FABL.binarySignEquiv).symm.trans
    (indexedF₂CubeEquivFinset ι)

private noncomputable def freeFrequencyPowersetEquiv (J : Finset (Fin n)) :
    Finset J ≃ ↥J.powerset where
  toFun S := ⟨FABL.liftFreeFrequency S, by
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact hji ▸ j.property⟩
  invFun U := FABL.freeFrequencyPart J U.1
  left_inv S := by
    ext i
    simp [FABL.freeFrequencyPart, FABL.liftFreeFrequency]
  right_inv U := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ J
    · let j : J := ⟨i, hi⟩
      change i ∈ FABL.liftFreeFrequency (FABL.freeFrequencyPart J U.1) ↔ i ∈ U.1
      constructor
      · intro h
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
        have hkj : k = j := Subtype.ext hki
        subst k
        exact (FABL.mem_freeFrequencyPart J U.1 j).mp hk
      · intro h
        apply Finset.mem_map.mpr
        exact ⟨j, (FABL.mem_freeFrequencyPart J U.1 j).mpr h, rfl⟩
    · have hiU : i ∉ U.1 := fun hiU ↦ hi (Finset.mem_powerset.mp U.2 hiU)
      simp [FABL.liftFreeFrequency, hi, hiU]

private def zeroFixedSign (J : Finset (Fin n)) : FABL.FixedSignCube J :=
  fun _ ↦ 1

private theorem binaryPointOfFreeSign_eq_f₂CubeOfFinset
    (J : Finset (Fin n)) (y : FABL.FreeSignCube J) :
    (FABL.binaryCubeSignEquiv n).symm
        (FABL.combineSignCube J y (zeroFixedSign J)) =
      FABL.f₂CubeOfFinset
        (FABL.liftFreeFrequency (indexedSignCubeEquivFinset J y)) := by
  funext i
  by_cases hi : i ∈ J
  · let j : J := ⟨i, hi⟩
    have hcombine : FABL.combineSignCube J y (zeroFixedSign J) i = y j := by
      simpa [j] using FABL.combineSignCube_apply_free J y (zeroFixedSign J) j
    rw [show ((FABL.binaryCubeSignEquiv n).symm
        (FABL.combineSignCube J y (zeroFixedSign J))) i =
        FABL.binarySignEquiv.symm (FABL.combineSignCube J y (zeroFixedSign J) i) by rfl]
    rw [hcombine, FABL.f₂CubeOfFinset_apply]
    change FABL.binarySignEquiv.symm (y j) =
      if i ∈ FABL.liftFreeFrequency (indexedSignCubeEquivFinset J y) then 1 else 0
    have hmem :
        i ∈ FABL.liftFreeFrequency (indexedSignCubeEquivFinset J y) ↔
          FABL.binarySignEquiv.symm (y j) ≠ 0 := by
      change i ∈ FABL.liftFreeFrequency
          (indexedF₂Support ((Equiv.piCongrRight fun _ : J ↦ FABL.binarySignEquiv).symm y)) ↔ _
      constructor
      · intro h
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
        have hkj : k = j := Subtype.ext hki
        subst k
        exact (Finset.mem_filter.mp hk).2
      · intro h
        apply Finset.mem_map.mpr
        refine ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    by_cases hy : FABL.binarySignEquiv.symm (y j) = 0
    · simp [hmem, hy]
    · have hy_one : FABL.binarySignEquiv.symm (y j) = 1 :=
        Fin.eq_one_of_ne_zero _ hy
      simp [hmem, hy_one]
  · let j : FABL.FixedIndex J := ⟨i, hi⟩
    have hcombine : FABL.combineSignCube J y (zeroFixedSign J) i = 1 := by
      simpa [j, zeroFixedSign] using
        FABL.combineSignCube_apply_fixed J y (zeroFixedSign J) j
    rw [show ((FABL.binaryCubeSignEquiv n).symm
        (FABL.combineSignCube J y (zeroFixedSign J))) i =
        FABL.binarySignEquiv.symm (FABL.combineSignCube J y (zeroFixedSign J) i) by rfl]
    rw [hcombine, FABL.f₂CubeOfFinset_apply]
    simp [FABL.binarySignEquiv, FABL.liftFreeFrequency, hi]

private theorem sum_freeSignCube_boolean_eq_anfCoeff
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    (∑ y : FABL.FreeSignCube S,
        f ((FABL.binaryCubeSignEquiv n).symm
          (FABL.combineSignCube S y (zeroFixedSign S)))) = anfCoeff f S := by
  classical
  calc
    (∑ y : FABL.FreeSignCube S,
        f ((FABL.binaryCubeSignEquiv n).symm
          (FABL.combineSignCube S y (zeroFixedSign S)))) =
        ∑ T : Finset S,
          f (FABL.f₂CubeOfFinset (FABL.liftFreeFrequency T)) := by
      apply Fintype.sum_equiv (indexedSignCubeEquivFinset S)
      intro y
      rw [binaryPointOfFreeSign_eq_f₂CubeOfFinset]
    _ = ∑ U : ↥S.powerset, f (FABL.f₂CubeOfFinset U.1) := by
      apply Fintype.sum_equiv (freeFrequencyPowersetEquiv S)
      intro T
      rfl
    _ = ∑ U ∈ S.powerset, f (FABL.f₂CubeOfFinset U) := by
      symm
      exact Finset.sum_subtype S.powerset (fun U ↦ Iff.rfl)
        (fun U ↦ f (FABL.f₂CubeOfFinset U))
    _ = anfCoeff f S := rfl

private def indexedMonomialInt {ι : Type*} (S : Finset ι)
    (x : FABL.IndexedSignCube ι) : ℤ :=
  ∏ i ∈ S, (x i : ℤ)

private theorem indexedMonomialInt_cast
    {ι : Type*} (S : Finset ι) (x : FABL.IndexedSignCube ι) :
    (indexedMonomialInt S x : ℝ) = FABL.indexedMonomial S x := by
  simp [indexedMonomialInt, FABL.indexedMonomial, FABL.signValue]

private theorem indexedMonomialInt_cast_f₂_eq_one
    {ι : Type*} (S : Finset ι) (x : FABL.IndexedSignCube ι) :
    (indexedMonomialInt S x : FABL.𝔽₂) = 1 := by
  rw [indexedMonomialInt, Int.cast_prod]
  apply Finset.prod_eq_one
  intro i hi
  rcases Int.units_eq_one_or (x i) with h | h <;> simp [h]

private theorem indexedRawFourierTransform_booleanRestriction_ne_zero
    (f : BooleanFunction n) (S : Finset (Fin n))
    (hcoeff : anfCoeff f S ≠ 0) (A : Finset S) :
    indexedRawFourierTransform
        (FABL.signRestriction
          (FABL.binaryFunctionOnSignCube (booleanRealEmbedding f)) S (zeroFixedSign S)) A ≠ 0 := by
  classical
  let point : FABL.FreeSignCube S → FABL.F₂Cube n := fun y ↦
    (FABL.binaryCubeSignEquiv n).symm
      (FABL.combineSignCube S y (zeroFixedSign S))
  let z : ℤ := ∑ y : FABL.FreeSignCube S,
    if f (point y) = 1 then indexedMonomialInt A y else 0
  have hrawCast :
      indexedRawFourierTransform
          (FABL.signRestriction
            (FABL.binaryFunctionOnSignCube (booleanRealEmbedding f)) S (zeroFixedSign S)) A =
        (z : ℝ) := by
    rw [indexedRawFourierTransform]
    change (∑ y, _ ) = ((∑ y : FABL.FreeSignCube S,
      if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : ℝ)
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : f (point y) = 1
    · rw [if_pos hy]
      simp only [FABL.signRestriction, FABL.binaryFunctionOnSignCube,
        booleanRealEmbedding, point, hy, if_pos, one_mul]
      exact indexedMonomialInt_cast A y |>.symm
    · rw [if_neg hy]
      simp [FABL.signRestriction, FABL.binaryFunctionOnSignCube,
        booleanRealEmbedding, point, hy]
  intro hzero
  have hzReal : (z : ℝ) = 0 := hrawCast ▸ hzero
  have hz : z = 0 := by exact_mod_cast hzReal
  have hzmod : (z : FABL.𝔽₂) = anfCoeff f S := by
    change ((∑ y : FABL.FreeSignCube S,
      if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : FABL.𝔽₂) = _
    calc
      ((∑ y : FABL.FreeSignCube S,
          if f (point y) = 1 then indexedMonomialInt A y else 0 : ℤ) : FABL.𝔽₂) =
          ∑ y : FABL.FreeSignCube S,
          if f (point y) = 1 then 1 else 0 := by
        rw [Int.cast_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f (point y) = 1
        · simp [hy, indexedMonomialInt_cast_f₂_eq_one]
        · simp [hy]
      _ = ∑ y : FABL.FreeSignCube S, f (point y) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : f (point y) = 1
        · simp [hy]
        · have hy0 : f (point y) = 0 := by
            by_contra h
            exact hy (Fin.eq_one_of_ne_zero _ h)
          simp [hy0]
      _ = anfCoeff f S := sum_freeSignCube_boolean_eq_anfCoeff f S
  have hzcast : (z : FABL.𝔽₂) = 0 := by rw [hz]; rfl
  exact hcoeff (hzmod.symm.trans hzcast)

private theorem card_indexedRawFourierSupport_booleanRestriction_eq_two_pow
    (f : BooleanFunction n) (S : Finset (Fin n)) (hcoeff : anfCoeff f S ≠ 0) :
    #(indexedRawFourierSupport
        (FABL.signRestriction
          (FABL.binaryFunctionOnSignCube (booleanRealEmbedding f)) S (zeroFixedSign S))) =
      2 ^ S.card := by
  classical
  have hall (A : Finset S) :
      indexedRawFourierTransform
          (FABL.signRestriction
            (FABL.binaryFunctionOnSignCube (booleanRealEmbedding f)) S (zeroFixedSign S)) A ≠ 0 :=
    indexedRawFourierTransform_booleanRestriction_ne_zero f S hcoeff A
  rw [indexedRawFourierSupport]
  simp only [hall, ne_eq, not_false_eq_true, Finset.filter_true]
  simp

/-- Carlet's algebraic-degree lower bound: a nonzero Boolean function has at least
`2^d` nonzero raw Fourier coefficients, where `d` is its algebraic degree. -/
theorem two_pow_functionAlgebraicDegree_le_card_rawFourierSupport_booleanRealEmbedding
    (f : BooleanFunction n) (hf : f ≠ 0) :
    2 ^ functionAlgebraicDegree f ≤ #(rawFourierSupport (booleanRealEmbedding f)) := by
  classical
  have hexists : ∃ S : Finset (Fin n), anfCoeff f S ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    funext x
    rw [← congrFun (anfEval_anfCoeff f) x]
    simp [anfEval, h]
  have hsupportNonempty : (anfSupport (anfCoeff f)).Nonempty := by
    obtain ⟨S, hS⟩ := hexists
    exact ⟨S, (mem_anfSupport (anfCoeff f) S).mpr hS⟩
  obtain ⟨S, hSsupport, hdegree⟩ :=
    Finset.exists_mem_eq_sup (anfSupport (anfCoeff f)) hsupportNonempty Finset.card
  have hcoeff : anfCoeff f S ≠ 0 :=
    (mem_anfSupport (anfCoeff f) S).mp hSsupport
  have hfunctionDegree : functionAlgebraicDegree f = S.card := by
    rw [functionAlgebraicDegree, algebraicDegree]
    exact hdegree
  calc
    2 ^ functionAlgebraicDegree f = 2 ^ S.card := by rw [hfunctionDegree]
    _ = #(indexedRawFourierSupport
        (FABL.signRestriction
          (FABL.binaryFunctionOnSignCube (booleanRealEmbedding f)) S (zeroFixedSign S))) :=
      (card_indexedRawFourierSupport_booleanRestriction_eq_two_pow f S hcoeff).symm
    _ ≤ #(rawFourierSupport (booleanRealEmbedding f)) :=
      card_rawFourierSupport_coordinateRestriction_le
        (booleanRealEmbedding f) S (zeroFixedSign S)

/-- The nonzero coefficient support of a numerical normal form. -/
noncomputable def numericalSupport (c : NumericalCoefficients n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ c S ≠ 0

@[simp] theorem mem_numericalSupport (c : NumericalCoefficients n)
    (S : Finset (Fin n)) :
    S ∈ numericalSupport c ↔ c S ≠ 0 := by
  classical
  simp [numericalSupport]

/-- The degree of a numerical normal form, with degree zero for the zero form. -/
noncomputable def numericalDegree (c : NumericalCoefficients n) : ℕ :=
  (numericalSupport c).sup Finset.card

/-- Degree at most `D` is coefficientwise vanishing above `D`. -/
theorem numericalDegree_le_iff (c : NumericalCoefficients n) (D : ℕ) :
    numericalDegree c ≤ D ↔ ∀ S, c S ≠ 0 → S.card ≤ D := by
  classical
  rw [numericalDegree, Finset.sup_le_iff]
  constructor
  · intro h S hS
    exact h S (by simpa using hS)
  · intro h S hS
    exact h S (by simpa using hS)

/-- The numerical degree of a pseudo-Boolean function is the degree of its unique NNF. -/
noncomputable def functionNumericalDegree (φ : PseudoBooleanFunction n) : ℕ :=
  numericalDegree (numericalCoeff φ)

/-- A numerical monomial is the indicator of the coordinate subcube on which its variables
are all one. -/
theorem numericalMonomial_eq_setIndicator_coordinateSubcube
    (S : Finset (Fin n)) :
    numericalMonomial S =
      FABL.setIndicator
        (FABL.F₂DecisionTree.coordinateSubcube S (FABL.f₂CubeOfFinset S) :
          Set (FABL.F₂Cube n)) := by
  classical
  funext x
  by_cases h : ∀ i ∈ S, x i = 1
  · have hx : x ∈ FABL.F₂DecisionTree.coordinateSubcube S (FABL.f₂CubeOfFinset S) := by
      intro i hi
      simpa [FABL.f₂CubeOfFinset_apply, hi] using h i hi
    rw [numericalMonomial]
    have hprod : (∏ i ∈ S, if x i = 1 then (1 : ℝ) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [h i hi]
    rw [hprod]
    simp [FABL.setIndicator, hx]
  · push Not at h
    obtain ⟨i, hiS, hxi⟩ := h
    have hxi0 : x i = 0 := by
      by_contra hzero
      exact hxi (Fin.eq_one_of_ne_zero (x i) hzero)
    have hx : x ∉ FABL.F₂DecisionTree.coordinateSubcube S (FABL.f₂CubeOfFinset S) := by
      intro hx
      have := hx i hiS
      simp [FABL.f₂CubeOfFinset_apply, hiS, hxi0] at this
    rw [numericalMonomial]
    rw [Finset.prod_eq_zero hiS]
    · simp [FABL.setIndicator, hx]
    · simp [hxi0]

/-- A numerical monomial has no Fourier frequency outside its set of variables. -/
theorem f₂Support_subset_of_vectorFourierCoeff_numericalMonomial_ne_zero
    (S : Finset (Fin n)) (u : FABL.F₂Cube n)
    (hu : FABL.vectorFourierCoeff (numericalMonomial S) u ≠ 0) :
    FABL.f₂Support u ⊆ S := by
  rw [numericalMonomial_eq_setIndicator_coordinateSubcube,
    FABL.F₂DecisionTree.coordinateSubcube_eq_binaryAffineSubspace] at hu
  have hperp :
      u ∈ FABL.perpendicularSubspace (FABL.F₂DecisionTree.coordinateZeroSubspace S) :=
    (FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff
      (FABL.F₂DecisionTree.coordinateZeroSubspace S) (FABL.f₂CubeOfFinset S) u).mp hu
  exact FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
    S u hperp

/-- Fourier coefficients commute with the finite numerical-normal-form sum. -/
theorem vectorFourierCoeff_numericalEval
    (c : NumericalCoefficients n) (u : FABL.F₂Cube n) :
    FABL.vectorFourierCoeff (numericalEval c) u =
      ∑ S, c S * FABL.vectorFourierCoeff (numericalMonomial S) u := by
  rw [FABL.vectorFourierCoeff_eq_expect]
  simp_rw [numericalEval, Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  calc
    (𝔼 x, c S * numericalMonomial S x * FABL.vectorWalshCharacter u x) =
        c S * (𝔼 x, numericalMonomial S x * FABL.vectorWalshCharacter u x) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = c S * FABL.vectorFourierCoeff (numericalMonomial S) u := by
      rw [FABL.vectorFourierCoeff_eq_expect]

/-- Numerical degree bounds the Hamming weight of every nonzero Fourier frequency. -/
theorem f₂Support_card_le_functionNumericalDegree_of_mem_rawFourierSupport
    (φ : PseudoBooleanFunction n) (u : FABL.F₂Cube n)
    (hu : u ∈ rawFourierSupport φ) :
    (FABL.f₂Support u).card ≤ functionNumericalDegree φ := by
  rw [mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero] at hu
  rw [← numericalEval_numericalCoeff φ] at hu
  rw [vectorFourierCoeff_numericalEval] at hu
  by_contra hweight
  push Not at hweight
  apply hu
  apply Finset.sum_eq_zero
  intro S _
  by_cases hc : numericalCoeff φ S = 0
  · simp [hc]
  · have hSdegree : S.card ≤ functionNumericalDegree φ :=
      (numericalDegree_le_iff (numericalCoeff φ) (functionNumericalDegree φ)).mp
        le_rfl S hc
    have hcoeff : FABL.vectorFourierCoeff (numericalMonomial S) u = 0 := by
      by_contra hne
      have hsubset :=
        f₂Support_subset_of_vectorFourierCoeff_numericalMonomial_ne_zero S u hne
      have hcard := Finset.card_le_card hsubset
      omega
    simp [hcoeff]

/-- The binary vectors of Hamming weight at most `D` are counted by the lower binomial sum. -/
theorem card_lowWeightInputs (n D : ℕ) :
    #(lowWeightInputs (n := n) D) =
      ∑ i ∈ Finset.range (D + 1), n.choose i := by
  classical
  calc
    #(lowWeightInputs (n := n) D) =
        #((Finset.univ : Finset (Finset (Fin n))).filter fun S ↦ S.card ≤ D) := by
      apply Finset.card_bij (fun u _ ↦ FABL.f₂Support u)
      · intro u hu
        simpa [lowWeightInputs] using hu
      · intro u₁ hu₁ u₂ hu₂ hsupport
        exact (FABL.f₂CubeEquivFinset n).injective hsupport
      · intro S hS
        refine ⟨FABL.f₂CubeOfFinset S, ?_, ?_⟩
        · have hSD : S.card ≤ D := (Finset.mem_filter.mp hS).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          have hsupport : FABL.f₂Support (FABL.f₂CubeOfFinset S) = S :=
            (FABL.f₂CubeEquivFinset n).right_inv S
          rw [hsupport]
          exact hSD
        · exact (FABL.f₂CubeEquivFinset n).right_inv S
    _ = #((Finset.univ : Finset (Fin n)).powerset.filter fun S ↦ S.card ≤ D) := by
      congr 1
    _ = ∑ i ∈ Finset.range (D + 1), n.choose i := by
      simpa using card_powerset_filter_card_le (Finset.univ : Finset (Fin n)) D

/-- Carlet's numerical-degree bound: at most the lower binomial sum of raw Fourier
coefficients are nonzero. -/
theorem card_rawFourierSupport_le_sum_choose_functionNumericalDegree
    (φ : PseudoBooleanFunction n) :
    #(rawFourierSupport φ) ≤
      ∑ i ∈ Finset.range (functionNumericalDegree φ + 1), n.choose i := by
  calc
    #(rawFourierSupport φ) ≤ #(lowWeightInputs (n := n) (functionNumericalDegree φ)) := by
      apply Finset.card_le_card
      intro u hu
      simpa [lowWeightInputs] using
        f₂Support_card_le_functionNumericalDegree_of_mem_rawFourierSupport φ u hu
    _ = _ := card_lowWeightInputs n (functionNumericalDegree φ)

end CryptBoolean
