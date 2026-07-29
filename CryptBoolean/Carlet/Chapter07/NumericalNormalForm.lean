/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierNNF
public import CryptBoolean.Carlet.Chapter05.Affine
public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree

/-!
# Numerical normal form of resilient Boolean functions

Carlet Proposition 32: after adding full parity, resiliency is equivalent to
an upper bound on numerical degree.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The numerical degree of the real Boolean embedding is the Fourier degree
of the corresponding sign-cube view. -/
theorem functionNumericalDegree_booleanRealEmbedding_eq_fourierDegree_signCubeView
    (f : BooleanFunction n) :
    FABL.functionNumericalDegree (FABL.booleanRealEmbedding f) =
      FABL.fourierDegree (signCubeView f).toReal := by
  simpa [FABL.fourierToF₂Polynomial_booleanFunction,
    booleanFunctionF₂Encoding_signCubeView] using
    FABL.functionNumericalDegree_fourierToF₂Polynomial
      (signCubeView f).toReal

/-- A Fourier coefficient of the sign-cube view vanishes exactly when the
raw Walsh coefficient at the corresponding binary frequency vanishes. -/
private theorem fourierCoeff_signCubeView_eq_zero_iff_walshTransform
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    FABL.fourierCoeff (signCubeView f).toReal S = 0 ↔
      walshTransform f (FABL.f₂CubeOfFinset S) = 0 := by
  let u : FABL.F₂Cube n := FABL.f₂CubeOfFinset S
  have hsupport : FABL.f₂Support u = S := by
    exact (FABL.f₂CubeEquivFinset n).right_inv S
  rw [signCubeView_toReal, ← hsupport,
    ← FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
  have hrecover : FABL.f₂CubeOfFinset (FABL.f₂Support u) = u := by
    exact (FABL.f₂CubeEquivFinset n).left_inv u
  rw [hrecover]
  exact (walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero f u).symm

/-- Numerical degree at most `D` is equivalent to vanishing of all raw Walsh
coefficients whose frequencies have weight greater than `D`. -/
theorem functionNumericalDegree_booleanRealEmbedding_le_iff_walshTransform
    (f : BooleanFunction n) (D : ℕ) :
    FABL.functionNumericalDegree (FABL.booleanRealEmbedding f) ≤ D ↔
      ∀ S : Finset (Fin n), D < S.card →
        walshTransform f (FABL.f₂CubeOfFinset S) = 0 := by
  rw [functionNumericalDegree_booleanRealEmbedding_eq_fourierDegree_signCubeView,
    FABL.fourierDegree_le_iff]
  constructor
  · intro h S hcard
    exact (fourierCoeff_signCubeView_eq_zero_iff_walshTransform f S).mp
      (h S hcard)
  · intro h S hcard
    exact (fourierCoeff_signCubeView_eq_zero_iff_walshTransform f S).mpr
      (h S hcard)

/-- Adding full coordinate parity sends the Walsh coefficient indexed by `S`
to the original coefficient indexed by the complementary set. -/
private theorem walshTransform_add_coordinateSum_univ
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    walshTransform
        (f + (FABL.coordinateSum (Finset.univ : Finset (Fin n)) :
          BooleanFunction n))
        (FABL.f₂CubeOfFinset S) =
      walshTransform f (FABL.f₂CubeOfFinset Sᶜ) := by
  classical
  have hparity :
      (FABL.coordinateSum (Finset.univ : Finset (Fin n)) : BooleanFunction n) =
        FABL.affineFunction 0
          (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))) := by
    funext x
    rw [FABL.affineFunction, zero_add,
      FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
    have hsupport :
        FABL.f₂Support
            (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))) =
          Finset.univ :=
      (FABL.f₂CubeEquivFinset n).right_inv Finset.univ
    rw [hsupport]
  have hfrequency :
      FABL.f₂CubeOfFinset S +
          FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n)) =
        FABL.f₂CubeOfFinset Sᶜ := by
    funext i
    by_cases hi : i ∈ S <;> simp [FABL.f₂CubeOfFinset_apply, hi]
  rw [hparity, walshTransform_add_affineFunction, hfrequency]
  norm_num [bitSignInt]

/-- Carlet Proposition 32: for `n > 0` and `m < n`, an `n`-variable
Boolean function is `m`-resilient exactly when adding full coordinate parity
produces a Boolean function whose numerical normal form has degree at most
`n - m - 1`. -/
theorem proposition_32_resilient_iff_functionNumericalDegree_le
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m < n) :
    IsResilient m f ↔
      FABL.functionNumericalDegree
          (FABL.booleanRealEmbedding
            (f + (FABL.coordinateSum (Finset.univ : Finset (Fin n)) :
              BooleanFunction n))) ≤
        n - m - 1 := by
  classical
  rw [theorem_3_resilient_iff_walshTransform_eq_zero m f hn hm,
    functionNumericalDegree_booleanRealEmbedding_le_iff_walshTransform]
  constructor
  · intro h S hlarge
    rw [walshTransform_add_coordinateSum_univ]
    apply h
    have hcard : Sᶜ.card ≤ m := by
      rw [Finset.card_compl, Fintype.card_fin]
      have hSle : S.card ≤ n := by
        simpa using Finset.card_le_univ S
      omega
    have hsupport :
        FABL.f₂Support (FABL.f₂CubeOfFinset Sᶜ) = Sᶜ :=
      (FABL.f₂CubeEquivFinset n).right_inv Sᶜ
    rw [hsupport]
    exact hcard
  · intro h u hsmall
    let S : Finset (Fin n) := (FABL.f₂Support u)ᶜ
    have hsupportLe : (FABL.f₂Support u).card ≤ n := by
      simpa using Finset.card_le_univ (FABL.f₂Support u)
    have hlarge : n - m - 1 < S.card := by
      dsimp [S]
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hzero := h S hlarge
    rw [walshTransform_add_coordinateSum_univ] at hzero
    have hrecover :
        FABL.f₂CubeOfFinset (FABL.f₂Support u) = u := by
      simpa using (FABL.f₂CubeEquivFinset n).left_inv u
    rw [show Sᶜ = FABL.f₂Support u by simp [S], hrecover] at hzero
    exact hzero

end CryptBoolean
