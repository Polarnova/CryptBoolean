/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.ANFExistence
public import FABL.Chapter06.F₂Polynomials.NumericalNormalForm

/-!
# Carlet Chapter 2 numerical normal form criteria

FABL Chapter 6 owns numerical-normal-form coefficients, evaluation, existence, uniqueness, and the
Möbius coefficient formula. This module retains Carlet Proposition 5's integer-valued and
Boolean-valued criteria.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

/-- A pseudo-Boolean function is integer-valued when each value is the cast of an integer. -/
def IsIntegerValued (φ : PseudoBooleanFunction n) : Prop :=
  ∀ x, ∃ z : ℤ, φ x = (z : ℝ)

/-- A pseudo-Boolean function is Boolean-valued when every value is zero or one. -/
def IsBooleanValued (φ : PseudoBooleanFunction n) : Prop :=
  ∀ x, φ x = 0 ∨ φ x = 1

/-- A finite sum of integer-valued real terms is an integer-valued real number. -/
private theorem exists_intCast_eq_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, ∃ z : ℤ, f i = (z : ℝ)) :
    ∃ z : ℤ, ∑ i ∈ s, f i = (z : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨za, hza⟩ := hf a (Finset.mem_insert_self a s)
      obtain ⟨zs, hzs⟩ := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      refine ⟨za + zs, ?_⟩
      rw [Finset.sum_insert ha, hza, hzs, Int.cast_add]

/-- For an integer `z`, the real number `z²-z` is nonnegative. -/
private theorem sq_sub_self_nonneg_of_eq_intCast {r : ℝ} {z : ℤ}
    (hr : r = (z : ℝ)) : 0 ≤ r ^ 2 - r := by
  rw [hr]
  by_cases hz : z ≤ 0
  · have hzReal : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    nlinarith
  · have hone : (1 : ℤ) ≤ z := by omega
    have honeReal : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hone
    nlinarith

/-- Carlet Proposition 5: an NNF is integer-valued exactly when all coefficients are integers. -/
theorem numericalEval_integerValued_iff (c : NumericalCoefficients n) :
    IsIntegerValued (numericalEval c) ↔
      ∀ S, ∃ z : ℤ, c S = (z : ℝ) := by
  constructor
  · intro h S
    have hc : c = numericalCoeff (numericalEval c) := by
      apply numericalEval_injective
      change numericalEval c = numericalEval (numericalCoeff (numericalEval c))
      exact (numericalEval_numericalCoeff (numericalEval c)).symm
    rw [hc, numericalCoeff_eq_mobius_sum]
    apply exists_intCast_eq_finset_sum
    intro T _
    obtain ⟨z, hz⟩ := h (FABL.f₂CubeOfFinset T)
    refine ⟨(-1 : ℤ) ^ (S.card - T.card) * z, ?_⟩
    rw [hz, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  · intro hc x
    let U := FABL.f₂Support x
    have hx : FABL.f₂CubeOfFinset U = x := by
      simpa [U] using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
    rw [← hx, numericalEval_f₂CubeOfFinset]
    exact exists_intCast_eq_finset_sum U.powerset c (fun S _ ↦ hc S)

/-- Carlet Proposition 5: for integral NNF coefficients, the sum-of-squares identity
characterizes Boolean-valued evaluation. -/
theorem numericalEval_booleanValued_iff_sum_sq_eq_sum (c : NumericalCoefficients n)
    (hc : ∀ S, ∃ z : ℤ, c S = (z : ℝ)) :
    IsBooleanValued (numericalEval c) ↔
      (∑ x, numericalEval c x ^ 2) = ∑ x, numericalEval c x := by
  constructor
  · intro h
    apply Finset.sum_congr rfl
    intro x _
    rcases h x with hx | hx <;> simp [hx]
  · intro hsum
    have hinteger : IsIntegerValued (numericalEval c) :=
      (numericalEval_integerValued_iff c).2 hc
    have hsumzero :
        (∑ x, (numericalEval c x ^ 2 - numericalEval c x)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hnonneg : ∀ x ∈ Finset.univ,
        0 ≤ numericalEval c x ^ 2 - numericalEval c x := by
      intro x _
      obtain ⟨z, hz⟩ := hinteger x
      exact sq_sub_self_nonneg_of_eq_intCast hz
    intro x
    have hxzero : numericalEval c x ^ 2 - numericalEval c x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumzero x (Finset.mem_univ x)
    have hfactor : numericalEval c x * (numericalEval c x - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hx | hx
    · exact Or.inl hx
    · exact Or.inr (sub_eq_zero.mp hx)

end CryptBoolean
