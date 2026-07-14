/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.ANFExistence

/-!
# Carlet Chapter 2 function-level algebraic degree

The canonical ANF turns coefficient-level degree into an invariant of Boolean
functions and supplies the additive laws needed by Reed--Muller theory.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The algebraic degree of a Boolean function, through its unique ANF. -/
noncomputable def functionAlgebraicDegree (f : BooleanFunction n) : ℕ :=
  algebraicDegree (anfCoeff f)

/-- Function-level algebraic degree is bounded by the number of variables. -/
theorem functionAlgebraicDegree_le_dimension (f : BooleanFunction n) :
    functionAlgebraicDegree f ≤ n :=
  algebraicDegree_le_dimension (anfCoeff f)

/-- Degree at most `r` is exactly the coefficientwise vanishing condition above `r`. -/
theorem algebraicDegree_le_iff (c : ANFCoefficients n) (r : ℕ) :
    algebraicDegree c ≤ r ↔ ∀ S, c S ≠ 0 → S.card ≤ r := by
  classical
  rw [algebraicDegree, Finset.sup_le_iff]
  constructor
  · intro h S hS
    exact h S (by simpa [anfSupport] using hS)
  · intro h S hS
    exact h S (by simpa [anfSupport] using hS)

/-- The canonical ANF transform is additive. -/
theorem anfCoeff_add (f g : BooleanFunction n) :
    anfCoeff (f + g) = fun S ↦ anfCoeff f S + anfCoeff g S := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  rw [anfEval_add, anfEval_anfCoeff, anfEval_anfCoeff]
  rfl

/-- The zero Boolean function has the zero canonical ANF. -/
@[simp] theorem anfCoeff_zero :
    anfCoeff (0 : BooleanFunction n) = fun _ ↦ 0 := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  simp

/-- The zero coefficient family has algebraic degree zero. -/
@[simp] theorem algebraicDegree_zero :
    algebraicDegree (fun _ : Finset (Fin n) ↦ 0) = 0 := by
  simp [algebraicDegree, anfSupport]

/-- The zero Boolean function has algebraic degree zero. -/
@[simp] theorem functionAlgebraicDegree_zero :
    functionAlgebraicDegree (0 : BooleanFunction n) = 0 := by
  rw [functionAlgebraicDegree, anfCoeff_zero, algebraicDegree_zero]

/-- Algebraic degree of a coefficient sum is bounded by the maximum of the two degrees. -/
theorem algebraicDegree_add_le_max (c d : ANFCoefficients n) :
    algebraicDegree (fun S ↦ c S + d S) ≤
      max (algebraicDegree c) (algebraicDegree d) := by
  rw [algebraicDegree_le_iff]
  intro S hsum
  have hcd : c S ≠ 0 ∨ d S ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (by rw [h.1, h.2, add_zero])
  cases hcd with
  | inl hc =>
      exact (algebraicDegree_le_iff c _).mp le_rfl S hc |>.trans (Nat.le_max_left _ _)
  | inr hd =>
      exact (algebraicDegree_le_iff d _).mp le_rfl S hd |>.trans (Nat.le_max_right _ _)

/-- Algebraic degree is submaximal under addition of Boolean functions. -/
theorem functionAlgebraicDegree_add_le_max (f g : BooleanFunction n) :
    functionAlgebraicDegree (f + g) ≤
      max (functionAlgebraicDegree f) (functionAlgebraicDegree g) := by
  rw [functionAlgebraicDegree, anfCoeff_add, functionAlgebraicDegree,
    functionAlgebraicDegree]
  exact algebraicDegree_add_le_max (anfCoeff f) (anfCoeff g)

/-- The unnormalized Hamming distance between Boolean functions, reusing Mathlib. -/
def hammingDistance (f g : BooleanFunction n) : ℕ :=
  hammingDist f g

/-- On `GF(2)`, distance is the weight of the pointwise sum. -/
theorem hammingDistance_eq_hammingWeight_add (f g : BooleanFunction n) :
    hammingDistance f g = hammingWeight (f + g) := by
  classical
  rw [hammingDistance, hammingDist, hammingWeight, support]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  have hf : f x = 0 ∨ f x = 1 := by
    by_cases h : f x = 0
    · exact Or.inl h
    · exact Or.inr (Fin.eq_one_of_ne_zero (f x) h)
  have hg : g x = 0 ∨ g x = 1 := by
    by_cases h : g x = 0
    · exact Or.inl h
    · exact Or.inr (Fin.eq_one_of_ne_zero (g x) h)
  constructor
  · intro hne
    rcases hf with hf | hf <;> rcases hg with hg | hg <;> simp_all
  · intro hone
    rcases hf with hf | hf <;> rcases hg with hg | hg <;> simp_all

end CryptBoolean
