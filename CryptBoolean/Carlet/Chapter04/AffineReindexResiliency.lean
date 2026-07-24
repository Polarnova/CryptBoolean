/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Resiliency
public import FABL.Chapter06.Constructions.BentFunctions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Carlet Chapter 4 affine reindexing to first-order resiliency

A basis of zero-Walsh frequencies determines a dual linear change of input
coordinates whose coordinate frequencies all have zero Walsh coefficient.
-/

open Finset Module
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The coordinate map associated with a family of Walsh frequencies. -/
def walshCoordinateLinearMap (u : Fin n → FABL.F₂Cube n) :
    FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun y i := FABL.f₂DotProduct (u i) y
  map_add' y z := by
    funext i
    exact (FABL.f₂DotProductBilin n (u i)).map_add y z
  map_smul' c y := by
    funext i
    exact (FABL.f₂DotProductBilin n (u i)).map_smul c y

/-- A linearly independent full family of Walsh frequencies gives an
injective coordinate map. -/
theorem walshCoordinateLinearMap_injective
    (u : Fin n → FABL.F₂Cube n)
    (hu : LinearIndependent FABL.𝔽₂ u) :
    Function.Injective (walshCoordinateLinearMap u) := by
  intro y z hyz
  have hy : walshCoordinateLinearMap u (y - z) = 0 := by
    rw [(walshCoordinateLinearMap u).map_sub, hyz, sub_self]
  let B : Basis (Fin n) FABL.𝔽₂ (FABL.F₂Cube n) :=
    basisOfLinearIndependentOfCardEqFinrank' u hu (by
      simp [Module.finrank_fintype_fun_eq_card])
  have hfunctional :
      (dotProductEquiv FABL.𝔽₂ (Fin n)) (y - z) = 0 := by
    apply B.ext
    intro i
    change dotProduct (y - z) (B i) = 0
    rw [show B i = u i by simp [B]]
    rw [dotProduct_comm]
    exact congrFun hy i
  have hyzero : y - z = 0 := by
    apply (dotProductEquiv FABL.𝔽₂ (Fin n)).injective
    simpa using hfunctional
  exact sub_eq_zero.mp hyzero

/-- The input reindexing dual to a basis of prescribed Walsh frequencies. -/
noncomputable def walshReindexLinearEquiv
    (u : Fin n → FABL.F₂Cube n)
    (hu : LinearIndependent FABL.𝔽₂ u) :
    FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
  (LinearEquiv.ofInjectiveEndo (walshCoordinateLinearMap u)
    (walshCoordinateLinearMap_injective u hu)).symm

/-- The dual frequency of a standard coordinate under the constructed
reindexing is the prescribed Walsh frequency. -/
theorem bentDualFrequency_walshReindexLinearEquiv_single
    (u : Fin n → FABL.F₂Cube n)
    (hu : LinearIndependent FABL.𝔽₂ u) (i : Fin n) :
    FABL.bentDualFrequency (walshReindexLinearEquiv u hu)
        (FABL.f₂CubeOfFinset {i}) = u i := by
  apply (dotProductEquiv FABL.𝔽₂ (Fin n)).injective
  apply LinearMap.ext
  intro y
  change FABL.f₂DotProduct
      (FABL.bentDualFrequency (walshReindexLinearEquiv u hu)
        (FABL.f₂CubeOfFinset {i})) y =
    FABL.f₂DotProduct (u i) y
  rw [FABL.f₂DotProduct_bentDualFrequency]
  simp [walshReindexLinearEquiv, walshCoordinateLinearMap,
    FABL.f₂DotProduct, FABL.f₂CubeOfFinset_apply, dotProduct]

/-- Raw Walsh coefficients are reindexed by the dual frequency under an
invertible linear change of variables. -/
theorem walshTransform_linearReindex_cast
    (f : BooleanFunction n)
    (M : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (γ : FABL.F₂Cube n) :
    (walshTransform (f ∘ M) γ : ℝ) =
      (walshTransform f (FABL.bentDualFrequency M γ) : ℝ) := by
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  change (2 : ℝ) ^ n *
      FABL.vectorFourierCoeff
        (FABL.bentLinearReindex M (realSignView f)) γ = _
  rw [FABL.vectorFourierCoeff_bentLinearReindex]

/-- The dual reindexing fixes the zero frequency. -/
@[simp] theorem bentDualFrequency_zero
    (M : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    FABL.bentDualFrequency M 0 = 0 := by
  apply (dotProductEquiv FABL.𝔽₂ (Fin n)).injective
  apply LinearMap.ext
  intro y
  change FABL.f₂DotProduct (FABL.bentDualFrequency M 0) y =
    FABL.f₂DotProduct 0 y
  rw [FABL.f₂DotProduct_bentDualFrequency]
  simp [FABL.f₂DotProduct]

/-- Linear input reindexing preserves balancedness. -/
theorem isBalanced_linearReindex
    (f : BooleanFunction n)
    (M : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (hf : IsBalanced f) :
    IsBalanced (f ∘ M) := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero] at hf ⊢
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, walshTransform_linearReindex_cast,
    bentDualFrequency_zero]
  exact_mod_cast hf

/-- Carlet's concluding observation in Chapter 4: a balanced function with
a basis of zero-Walsh frequencies becomes first-order resilient after a
linear input automorphism. -/
theorem exists_linearEquiv_isResilient_one
    (f : BooleanFunction n) (u : Fin n → FABL.F₂Cube n)
    (hu : LinearIndependent FABL.𝔽₂ u)
    (hbalanced : IsBalanced f)
    (hzero : ∀ i, walshTransform f (u i) = 0) :
    ∃ M : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n,
      IsResilient 1 (f ∘ M) := by
  let M := walshReindexLinearEquiv u hu
  refine ⟨M, (isResilient_iff_fabl 1 (f ∘ M)).mpr ?_⟩
  refine ⟨?_, (isBalanced_iff_fabl (f ∘ M)).mp
    (isBalanced_linearReindex f M hbalanced)⟩
  rw [FABL.IsCorrelationImmune, FABL.IsLowDegreeFourierRegular]
  intro S hS hScard
  have hcard : S.card = 1 :=
    Nat.le_antisymm hScard (Finset.card_pos.mpr hS)
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  have hwalsh :
      walshTransform (f ∘ M) (FABL.f₂CubeOfFinset {i}) = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero, walshTransform_linearReindex_cast,
      bentDualFrequency_walshReindexLinearEquiv_single]
    exact_mod_cast hzero i
  have hvector :=
    (walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero
      (f ∘ M) (FABL.f₂CubeOfFinset {i})).mp hwalsh
  have hsupport : FABL.f₂Support (FABL.f₂CubeOfFinset {i}) = {i} :=
    (FABL.f₂CubeEquivFinset n).right_inv {i}
  have hfourier :
      FABL.fourierCoeff (signCubeView (f ∘ M)).toReal {i} = 0 := by
    rw [signCubeView_toReal, ← hsupport]
    exact (FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube
      (realSignView (f ∘ M)) (FABL.f₂CubeOfFinset {i})).symm.trans hvector
  simp [hfourier]

end CryptBoolean
