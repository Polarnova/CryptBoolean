/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness
public import FABL.Chapter06.F₂Polynomials.BentDegree

/-!
# Algebraic degree of bent functions

Carlet Proposition 18: Rothaus' bound and the two-variable exceptional case.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Carlet Proposition 18: in even dimension at least four, the algebraic
degree of a bent Boolean function is at most half the dimension. -/
theorem functionAlgebraicDegree_le_half_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) (hn : 4 ≤ n) :
    FABL.functionAlgebraicDegree f ≤ n / 2 :=
  FABL.functionAlgebraicDegree_le_half_of_isBent f
    (even_of_isBent f hf) (by omega) hf

/-- Every two-variable bent Boolean function has algebraic degree two. -/
theorem functionAlgebraicDegree_eq_two_of_isBent
    (f : BooleanFunction 2) (hf : IsBent f) :
    FABL.functionAlgebraicDegree f = 2 := by
  apply Nat.le_antisymm (FABL.functionAlgebraicDegree_le_dimension f)
  by_contra hdegree
  have hdegreeOne : FABL.functionAlgebraicDegree f ≤ 1 := by omega
  obtain ⟨b, a, hfa⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one f hdegreeOne
  have hrelation := (nonlinearity_cast_eq_relation_36_iff_isBent f).2 hf
  rw [hfa, nonlinearity_affineFunction] at hrelation
  norm_num at hrelation

end CryptBoolean
