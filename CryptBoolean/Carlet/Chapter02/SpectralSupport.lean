/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Restrictions
public import CryptBoolean.Carlet.Chapter02.NumericalNormalForm
public import CryptBoolean.Carlet.Chapter02.Subspaces
public import FABL.Chapter06.F₂Polynomials.FourierToF₂Polynomial
public import FABL.Chapter06.F₂Polynomials.SpectralDegree

/-!
# Carlet Chapter 2 Fourier-support bounds

Coordinate restrictions, the algebraic-degree lower bound for nonzero Boolean
functions, and the numerical-degree upper bound for pseudo-Boolean functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

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

/-- Carlet's algebraic-degree lower bound, transported from FABL's canonical normalized
spectral-sparsity theorem to the raw-transform support. -/
theorem two_pow_functionAlgebraicDegree_le_card_rawFourierSupport_booleanRealEmbedding
    (f : BooleanFunction n) (hf : f ≠ 0) :
    2 ^ FABL.functionAlgebraicDegree f ≤
      #(rawFourierSupport (FABL.booleanRealEmbedding f)) := by
  calc
    2 ^ FABL.functionAlgebraicDegree f ≤
        FABL.spectralSparsity (FABL.booleanRealEmbedding f) :=
      FABL.two_pow_functionAlgebraicDegree_le_spectralSparsity_booleanRealEmbedding f hf
    _ = #(rawFourierSupport (FABL.booleanRealEmbedding f)) := by
      rw [FABL.spectralSparsity_eq_card_vectorFourierSupport]
      rfl

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
