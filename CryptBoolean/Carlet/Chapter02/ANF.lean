/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Fourier

/-!
# Carlet Chapter 2 algebraic normal form skeleton

Square-free coefficient families, monomial evaluation, ANF evaluation, algebraic
support, and algebraic degree for scalar Boolean functions over `𝔽₂`.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A square-free algebraic normal form coefficient family over coordinate subsets. -/
abbrev ANFCoefficients (n : ℕ) := Finset (Fin n) → FABL.𝔽₂

/-- The square-free monomial `∏ᵢ∈S xᵢ` over `𝔽₂`. -/
def anfMonomial (S : Finset (Fin n)) (x : FABL.F₂Cube n) : FABL.𝔽₂ :=
  ∏ i ∈ S, x i

/-- Evaluation of a square-free algebraic normal form. -/
def anfEval (c : ANFCoefficients n) (x : FABL.F₂Cube n) : FABL.𝔽₂ :=
  ∑ S, c S * anfMonomial S x

/-- The nonzero coefficient support of an algebraic normal form. -/
def anfSupport (c : ANFCoefficients n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ c S ≠ 0

/-- The algebraic degree of an ANF coefficient family, with degree zero for the zero family. -/
def algebraicDegree (c : ANFCoefficients n) : ℕ :=
  (anfSupport c).sup Finset.card

/-- Membership in ANF support is nonvanishing of the coefficient. -/
@[simp] theorem mem_anfSupport (c : ANFCoefficients n) (S : Finset (Fin n)) :
    S ∈ anfSupport c ↔ c S ≠ 0 := by
  classical
  simp [anfSupport]

/-- The empty ANF monomial evaluates to one. -/
@[simp] theorem anfMonomial_empty (x : FABL.F₂Cube n) :
    anfMonomial ∅ x = 1 := by
  simp [anfMonomial]

/-- The zero coefficient family evaluates to the zero Boolean function. -/
@[simp] theorem anfEval_zero (x : FABL.F₂Cube n) :
    anfEval (fun _ : Finset (Fin n) ↦ 0) x = 0 := by
  simp [anfEval]

/-- ANF evaluation is additive in the coefficient family. -/
theorem anfEval_add (c d : ANFCoefficients n) (x : FABL.F₂Cube n) :
    anfEval (fun S ↦ c S + d S) x = anfEval c x + anfEval d x := by
  classical
  simp [anfEval, add_mul, Finset.sum_add_distrib]

/-- Algebraic degree is bounded by the ambient dimension. -/
theorem algebraicDegree_le_dimension (c : ANFCoefficients n) :
    algebraicDegree c ≤ n := by
  classical
  rw [algebraicDegree]
  apply Finset.sup_le
  intro S _hS
  simpa using (Finset.card_le_univ S)

end CryptBoolean
