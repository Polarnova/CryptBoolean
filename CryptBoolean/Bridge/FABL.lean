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
# FABL bridge

Representation and normalization bridges from FABL to cryptographic Boolean functions.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- Scalar cryptographic Boolean functions on the additive binary cube. -/
abbrev BooleanFunction (n : ℕ) := FABL.F₂Cube n → FABL.𝔽₂

/-- The real sign view `(-1)^{f(x)}` of a bit-valued Boolean function. -/
abbrev realSignView {n : ℕ} (f : BooleanFunction n) : FABL.F₂Cube n → ℝ :=
  FABL.realSignEncodedFunction f

end CryptBoolean
