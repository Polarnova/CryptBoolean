/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierOperations
public import FABL.Chapter06.F₂Polynomials.Encoding

/-!
# Partial bent functions

Carlet's two-level Fourier definition on the punctured binary cube.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The raw Fourier transform of the zero-one embedding takes exactly the
levels `level` and `level + 2^(n/2)` on the punctured cube. -/
def HasPartialBentFourierLevels
    (f : BooleanFunction n) (level : ℤ) : Prop :=
  Set.range (fun u : {u : FABL.F₂Cube n // u ≠ 0} ↦
      rawFourierTransform (FABL.booleanRealEmbedding f) u.1) =
    ({(level : ℝ), (level : ℝ) + (2 : ℝ) ^ (n / 2)} : Set ℝ)

/-- A partial bent function has even dimension and exactly two raw Fourier
levels, separated by `2^(n/2)`, on the punctured cube. -/
def IsPartialBent (f : BooleanFunction n) : Prop :=
  Even n ∧ ∃ level : ℤ, HasPartialBentFourierLevels f level

end CryptBoolean
