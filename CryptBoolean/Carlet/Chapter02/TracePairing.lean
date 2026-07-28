/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FiniteField
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Binary finite-field trace pairing

The nondegenerate absolute-trace pairing identifies cube linear characters
with finite-field trace characters after a linear choice of coordinates.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

/-- Every linear character of a binary cube has a unique coefficient under the finite-field
trace pairing transported by a linear equivalence. -/
theorem existsUnique_tracePairingCoefficient {n : ℕ}
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (u : FABL.F₂Cube n) :
    ∃! b : BinaryGaloisField n, ∀ x,
      FABL.f₂DotProduct u x = absoluteTrace n (b * theta x) := by
  let ell : BinaryGaloisField n →ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
    ((dotProductEquiv FABL.𝔽₂ (Fin n)) u).comp theta.symm.toLinearMap
  let traceForm := Algebra.traceForm FABL.𝔽₂ (BinaryGaloisField n)
  let traceNondegenerate :=
    traceForm_nondegenerate FABL.𝔽₂ (BinaryGaloisField n)
  let b := (traceForm.toDual traceNondegenerate).symm ell
  refine ⟨b, ?_, ?_⟩
  · intro x
    calc
      FABL.f₂DotProduct u x = ell (theta x) := by
        simp [ell, FABL.f₂DotProduct, dotProductEquiv_apply_apply]
      _ = traceForm b (theta x) := by
        change ell (theta x) =
          traceForm ((traceForm.toDual traceNondegenerate).symm ell) (theta x)
        exact (LinearMap.BilinForm.apply_toDual_symm_apply ell (theta x)).symm
      _ = absoluteTrace n (b * theta x) := by
        rfl
  · intro c hc
    apply (traceForm.toDual traceNondegenerate).injective
    apply LinearMap.ext
    intro y
    calc
      traceForm.toDual traceNondegenerate c y = traceForm c y := rfl
      _ = absoluteTrace n (c * y) := rfl
      _ = FABL.f₂DotProduct u (theta.symm y) := by
        rw [hc (theta.symm y), theta.apply_symm_apply]
      _ = ell y := by
        simp [ell, FABL.f₂DotProduct, dotProductEquiv_apply_apply]
      _ = traceForm.toDual traceNondegenerate b y := by
        change ell y = traceForm.toDual traceNondegenerate
          ((traceForm.toDual traceNondegenerate).symm ell) y
        rw [LinearEquiv.apply_symm_apply]

end CryptBoolean
