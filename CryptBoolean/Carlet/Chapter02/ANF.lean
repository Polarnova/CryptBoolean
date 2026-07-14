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

/-- Products of square-free monomials are indexed by the union of their variables. -/
theorem anfMonomial_mul (S T : Finset (Fin n)) (x : FABL.F₂Cube n) :
    anfMonomial S x * anfMonomial T x = anfMonomial (S ∪ T) x := by
  classical
  rw [anfMonomial, anfMonomial, anfMonomial]
  by_cases h : ∀ i ∈ S ∪ T, x i ≠ 0
  · have hone : ∀ i ∈ S ∪ T, x i = 1 := by
      intro i hi
      exact Fin.eq_one_of_ne_zero (x i) (h i hi)
    rw [Finset.prod_eq_one (fun i hi ↦ hone i (Finset.mem_union_left T hi)),
      Finset.prod_eq_one (fun i hi ↦ hone i (Finset.mem_union_right S hi)),
      Finset.prod_eq_one hone, one_mul]
  · push Not at h
    obtain ⟨i, hi, hxi⟩ := h
    have hunion : ∏ j ∈ S ∪ T, x j = 0 :=
      Finset.prod_eq_zero hi hxi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have hS : ∏ j ∈ S, x j = 0 := Finset.prod_eq_zero hiS hxi
      rw [hS, zero_mul, hunion]
    · have hT : ∏ j ∈ T, x j = 0 := Finset.prod_eq_zero hiT hxi
      rw [hT, mul_zero, hunion]

/-- Multiplication of square-free ANFs, with repeated variables reduced by `xᵢ²=xᵢ`. -/
def anfMul (c d : ANFCoefficients n) : ANFCoefficients n :=
  fun U ↦ ∑ S, ∑ T, if U = S ∪ T then c S * d T else 0

/-- Evaluation of the square-free ANF product is pointwise multiplication. -/
theorem anfEval_anfMul (c d : ANFCoefficients n) (x : FABL.F₂Cube n) :
    anfEval (anfMul c d) x = anfEval c x * anfEval d x := by
  classical
  rw [anfEval, anfEval, anfEval]
  simp only [anfMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (S ∪ T),
    if_pos (Finset.mem_univ (S ∪ T))]
  rw [← anfMonomial_mul]
  ring

/-- Algebraic degree is bounded by the ambient dimension. -/
theorem algebraicDegree_le_dimension (c : ANFCoefficients n) :
    algebraicDegree c ≤ n := by
  classical
  rw [algebraicDegree]
  apply Finset.sup_le
  intro S _hS
  simpa using (Finset.card_le_univ S)

end CryptBoolean
