/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import FABL.Chapter03.Restrictions

import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Coordinate models of affine-subspace restrictions

Pure coordinate and affine-frequency formulas for restrictions to binary
affine subspaces.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

/-- The restriction to `a + E`, reindexed by binary coordinates on `E`. -/
def coordinateAffineSubspaceRestriction
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) : BooleanFunction k :=
  FABL.affineSubspaceRestriction f E a ∘ e

@[simp] theorem coordinateAffineSubspaceRestriction_apply
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (y : FABL.F₂Cube k) :
    coordinateAffineSubspaceRestriction f E a e y =
      f ((e y).1 + a) :=
  rfl

/-- The coordinate frequency induced by restricting an ambient linear form
to a binary subspace. -/
noncomputable def coordinateRestrictedAffineFrequency
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube n) : FABL.F₂Cube k :=
  (dotProductEquiv FABL.𝔽₂ (Fin k)).symm
    (((dotProductEquiv FABL.𝔽₂ (Fin n)) c).comp
      (E.subtype.comp e.toLinearMap))

@[simp] theorem f₂DotProduct_coordinateRestrictedAffineFrequency
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube n) (y : FABL.F₂Cube k) :
    FABL.f₂DotProduct (coordinateRestrictedAffineFrequency E e c) y =
      FABL.f₂DotProduct c (e y).1 := by
  change dotProduct (coordinateRestrictedAffineFrequency E e c) y =
    dotProduct c (e y).1
  calc
    dotProduct (coordinateRestrictedAffineFrequency E e c) y =
        (dotProductEquiv FABL.𝔽₂ (Fin k)
          (coordinateRestrictedAffineFrequency E e c)) y :=
      (dotProductEquiv_apply_apply FABL.𝔽₂ (Fin k) _ _).symm
    _ = (((dotProductEquiv FABL.𝔽₂ (Fin n)) c).comp
          (E.subtype.comp e.toLinearMap)) y := by
      exact DFunLike.congr_fun
        ((dotProductEquiv FABL.𝔽₂ (Fin k)).apply_symm_apply _) y
    _ = (dotProductEquiv FABL.𝔽₂ (Fin n) c) (e y).1 := rfl
    _ = dotProduct c (e y).1 :=
      dotProductEquiv_apply_apply FABL.𝔽₂ (Fin n) c (e y).1

/-- Restricting an ambient affine function along binary subspace coordinates
produces the corresponding coordinate affine function. -/
theorem affineFunction_coordinateAffineSubspaceRestriction
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (a c : FABL.F₂Cube n) (b : FABL.𝔽₂)
    (y : FABL.F₂Cube k) :
    FABL.affineFunction b c (a + (e y).1) =
      FABL.affineFunction (FABL.affineFunction b c a)
        (coordinateRestrictedAffineFrequency E e c) y := by
  rw [FABL.affineFunction, FABL.affineFunction, FABL.affineFunction,
    f₂DotProduct_coordinateRestrictedAffineFrequency]
  change b + dotProduct c (a + (e y).1) =
    (b + dotProduct c a) + dotProduct c (e y).1
  rw [dotProduct_add]
  ac_rfl

end CryptBoolean
