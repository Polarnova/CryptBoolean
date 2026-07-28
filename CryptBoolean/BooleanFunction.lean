/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01
public import FABL.Chapter02
public import FABL.Chapter03
public import FABL.Chapter04

/-!
# Boolean functions and their sign representation

The canonical scalar Boolean-function type and its real sign representation.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- Scalar cryptographic Boolean functions on the additive binary cube. -/
abbrev BooleanFunction (n : ℕ) := FABL.F₂Cube n → FABL.𝔽₂

/-- The real sign view `(-1)^{f(x)}` of a bit-valued Boolean function. -/
abbrev realSignView {n : ℕ} (f : BooleanFunction n) : FABL.F₂Cube n → ℝ :=
  FABL.realSignEncodedFunction f

/-- The canonical linear splitting of a binary cube into two coordinate
blocks. -/
def cubeSplitLinearEquiv (a b : ℕ) :
    FABL.F₂Cube (a + b) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube a × FABL.F₂Cube b) where
  __ := (Fin.appendEquiv a b).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext i <;> rfl

end CryptBoolean
