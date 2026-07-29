/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.NonlinearityBounds

/-!
# Nonlinearity at optimal algebraic immunity

Carlet Chapter 9: the parity specializations of Lobanov's bound.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem two_mul_sum_choose_below_middle_even_row (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, Nat.choose (2 * m) i) =
      2 ^ (2 * m) - Nat.choose (2 * m) m := by
  have hreflect := Finset.sum_Ico_reflect
    (fun i ↦ Nat.choose (2 * m) i) 0 (n := 2 * m) (m := m) (by omega)
  have hreflectStart : 2 * m + 1 - m = m + 1 := by omega
  rw [hreflectStart] at hreflect
  have hsymmetry :
      (∑ i ∈ Finset.range m, Nat.choose (2 * m) i) =
        ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), Nat.choose (2 * m) i := by
    rw [Finset.range_eq_Ico]
    calc
      (∑ i ∈ Finset.Ico 0 m, Nat.choose (2 * m) i) =
          ∑ i ∈ Finset.Ico 0 m, Nat.choose (2 * m) (2 * m - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact Nat.choose_symm (by
          have hi' := Finset.mem_Ico.mp hi
          omega)
      _ = ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1),
          Nat.choose (2 * m) i := by simpa using hreflect
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i ↦ Nat.choose (2 * m) i)
    (show m + 1 ≤ 2 * m + 1 by omega)
  rw [Finset.sum_range_succ, hsymmetry, Nat.sum_range_choose] at hsplit
  omega

private theorem two_mul_sum_choose_below_middle_odd_row
    (m : ℕ) (hm : 0 < m) :
    2 * (∑ i ∈ Finset.range (m - 1), Nat.choose (2 * m - 1) i) =
      2 ^ (2 * m - 1) - 2 * Nat.choose (2 * m - 1) (m - 1) := by
  have hdimension : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have hhalf := Nat.sum_range_choose_halfway (m - 1)
  rw [← hdimension] at hhalf
  have hsplit := Finset.sum_range_succ
    (fun i ↦ Nat.choose (2 * m - 1) i) (m - 1)
  have hpower : 2 ^ (2 * m - 1) = 2 * 4 ^ (m - 1) := by
    calc
      2 ^ (2 * m - 1) = 2 ^ (2 * (m - 1) + 1) := by rw [hdimension]
      _ = 2 * 4 ^ (m - 1) := by
        rw [pow_succ', pow_mul]
        norm_num
  rw [hhalf] at hsplit
  rw [hpower]
  omega

/-- Lobanov's lower bound at optimal algebraic immunity in positive even
dimension. -/
theorem nonlinearity_lowerBound_of_even_optimalAlgebraicImmunity
    (f : BooleanFunction n) (hn : 0 < n) (hneven : Even n)
    (hAI : algebraicImmunity f = n / 2) :
    2 ^ (n - 1) - 2 * Nat.choose (n - 1) (n / 2 - 1) ≤
      nonlinearity f := by
  obtain ⟨m, rfl⟩ := hneven
  have hm : 0 < m := by omega
  have hlobanov :=
    two_mul_sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity f
  have hsum := two_mul_sum_choose_below_middle_odd_row m hm
  have hhalf : (m + m) / 2 = m := by omega
  have hdimension : m + m - 1 = 2 * m - 1 := by omega
  rw [hAI, hhalf, hdimension] at hlobanov
  rw [hhalf, hdimension]
  simpa using hsum.symm.le.trans hlobanov

/-- The two central-binomial forms of the even optimal-immunity lower bound
are equal. -/
theorem even_optimalAlgebraicImmunity_lowerBound_eq
    (n : ℕ) (hn : 0 < n) (hneven : Even n) :
    2 ^ (n - 1) - 2 * Nat.choose (n - 1) (n / 2 - 1) =
      2 ^ (n - 1) - Nat.choose n (n / 2) := by
  obtain ⟨m, rfl⟩ := hneven
  have hm : 0 < m := by omega
  have hhalf : (m + m) / 2 = m := by omega
  have hdimension : m + m - 1 = 2 * m - 1 := by omega
  have hdouble : m + m = 2 * m := by omega
  rw [hhalf, hdimension, hdouble]
  have hpascal := Nat.choose_succ_succ (2 * m - 1) (m - 1)
  have hsymmetry := Nat.choose_symm (show m ≤ 2 * m - 1 by omega)
  have hleft : 2 * m - 1 - m = m - 1 := by omega
  rw [hleft] at hsymmetry
  have htop : (2 * m - 1).succ = 2 * m := by omega
  have hbottom : (m - 1).succ = m := by omega
  rw [htop, hbottom, hsymmetry] at hpascal
  omega

/-- Lobanov's even optimal-immunity bound in its central-binomial form. -/
theorem centralBinomial_le_nonlinearity_of_even_optimalAlgebraicImmunity
    (f : BooleanFunction n) (hn : 0 < n) (hneven : Even n)
    (hAI : algebraicImmunity f = n / 2) :
    2 ^ (n - 1) - Nat.choose n (n / 2) ≤ nonlinearity f := by
  rw [← even_optimalAlgebraicImmunity_lowerBound_eq n hn hneven]
  exact nonlinearity_lowerBound_of_even_optimalAlgebraicImmunity
    f hn hneven hAI

/-- Lobanov's lower bound at optimal algebraic immunity in odd dimension. -/
theorem nonlinearity_lowerBound_of_odd_optimalAlgebraicImmunity
    (f : BooleanFunction n) (hnodd : Odd n)
    (hAI : algebraicImmunity f = (n + 1) / 2) :
    2 ^ (n - 1) - Nat.choose (n - 1) ((n - 1) / 2) ≤
      nonlinearity f := by
  obtain ⟨m, rfl⟩ := hnodd
  have hlobanov :=
    two_mul_sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity f
  have hsum := two_mul_sum_choose_below_middle_even_row m
  have hhalf : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have hdimension : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hAI, hhalf, hdimension] at hlobanov
  rw [hdimension]
  simpa using hsum.symm.le.trans hlobanov

end CryptBoolean
