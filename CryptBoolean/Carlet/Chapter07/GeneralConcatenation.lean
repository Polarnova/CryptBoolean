/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.Concatenation

/-!
# Generalized concatenation

Carlet's finite family form of the concatenation construction.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s m : ℕ}

/-- A family indexed by the second coordinate block defines a Boolean
function on the joined cube. -/
def familyConcatenation
    (f : FABL.F₂Cube s → BooleanFunction r) :
    BooleanFunction (r + s) :=
  fun z ↦
    f ((cubeSplitLinearEquiv r s) z).2
      ((cubeSplitLinearEquiv r s) z).1

@[simp] theorem familyConcatenation_append
    (f : FABL.F₂Cube s → BooleanFunction r)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    familyConcatenation f (Fin.append x y) = f y x := by
  simp [familyConcatenation, cubeSplitLinearEquiv]

@[simp] theorem firstBlockSlice_familyConcatenation
    (f : FABL.F₂Cube s → BooleanFunction r)
    (y : FABL.F₂Cube s) :
    firstBlockSlice (familyConcatenation f) y = f y := by
  funext x
  simp [firstBlockSlice]

/-- The Walsh transform of a generalized concatenation is the signed sum of
the Walsh transforms of its slices. -/
theorem walshTransform_familyConcatenation_append
    (f : FABL.F₂Cube s → BooleanFunction r)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    walshTransform (familyConcatenation f) (Fin.append a b) =
      ∑ y : FABL.F₂Cube s,
        bitSignInt (FABL.f₂DotProduct b y) * walshTransform (f y) a := by
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_append_cast_eq_rawFourierTransform_sliceWalsh,
    rawFourierTransform]
  simp_rw [firstBlockSlice_familyConcatenation,
    FABL.vectorWalshCharacter_apply, ← bitSignInt_cast]
  push_cast
  simp [mul_comm]

/-- A generalized concatenation of `m`-resilient slices is
`m`-resilient. -/
theorem isResilient_familyConcatenation
    (f : FABL.F₂Cube s → BooleanFunction r)
    (hm : m < r) (hf : ∀ y, IsResilient m (f y)) :
    IsResilient m (familyConcatenation f) := by
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    m (familyConcatenation f) (by omega) (by omega)]
  intro u hu
  let p := (Fin.appendEquiv r s).symm u
  have hp : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  have hleft : (FABL.f₂Support p.1).card ≤ m := by
    apply (Nat.le_add_right (FABL.f₂Support p.1).card _).trans
    rw [← card_f₂Support_append, hp]
    exact hu
  rw [← hp, walshTransform_familyConcatenation_append]
  apply Finset.sum_eq_zero
  intro y _hy
  rw [(theorem_3_resilient_iff_walshTransform_eq_zero
    m (f y) (by omega) hm).mp (hf y) p.1 hleft, mul_zero]

end CryptBoolean
