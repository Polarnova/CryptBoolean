/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.ANFExistence
public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree

/-!
# Carlet Chapter 2 algebraic degree and Hamming distance

FABL Chapter 6 provides the canonical algebraic-degree API. This module retains Carlet's raw
Hamming-distance surface and its exact relation to Hamming weight.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The unnormalized Hamming distance between Boolean functions, reusing Mathlib. -/
abbrev hammingDistance (f g : BooleanFunction n) : ℕ :=
  hammingDist f g

/-- On `GF(2)`, distance is the weight of the pointwise sum. -/
theorem hammingDistance_eq_hammingWeight_add (f g : BooleanFunction n) :
    hammingDistance f g = hammingWeight (f + g) := by
  rw [hammingDistance, hammingDist_eq_hammingNorm]
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.neg_apply, ZMod.neg_eq_self_mod_two]

end CryptBoolean
