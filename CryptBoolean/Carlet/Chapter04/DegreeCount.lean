/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMuller
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Carlet Chapter 4 degree count

The exact number of Boolean functions of degree at most `n - 2` and the
resulting asymptotic probability of degree at least `n - 1`.
-/

open Finset
open scoped BigOperators BooleanCube Topology

@[expose] public section

namespace CryptBoolean

/-- The low-degree binomial sum omits exactly the last two terms of the
full binomial expansion. -/
theorem sum_choose_le_n_sub_two (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n - 2 + 1), Nat.choose n j) =
      2 ^ n - n - 1 := by
  have hfull := Nat.sum_range_choose n
  have hindex : n + 1 = (n - 1) + 2 := by omega
  rw [hindex, Finset.sum_range_succ, Finset.sum_range_succ] at hfull
  have hpred : Nat.choose n (n - 1) = n := by
    exact (Nat.choose_symm (n := n) (k := 1) (by omega)).trans
      (Nat.choose_one_right n)
  have hself : Nat.choose n (n - 1 + 1) = 1 := by
    rw [show n - 1 + 1 = n by omega, Nat.choose_self]
  rw [hpred, hself] at hfull
  have hrange : n - 2 + 1 = n - 1 := by omega
  rw [hrange]
  omega

/-- The functions of degree at most `n - 2` are exactly the corresponding
Reed--Muller codewords, so their number has the standard dimension formula. -/
theorem card_booleanFunctions_degree_le_n_sub_two (n : ℕ) :
    Nat.card {f : BooleanFunction n //
      FABL.functionAlgebraicDegree f ≤ n - 2} =
        2 ^ (∑ j ∈ Finset.range (n - 2 + 1), Nat.choose n j) := by
  change Nat.card (reedMuller (n - 2) n) = _
  exact reedMuller_card

/-- Carlet's simplified exact count of functions of degree at most `n - 2`. -/
theorem card_booleanFunctions_degree_le_n_sub_two_eq
    (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {f : BooleanFunction n //
      FABL.functionAlgebraicDegree f ≤ n - 2} =
        2 ^ (2 ^ n - n - 1) := by
  rw [card_booleanFunctions_degree_le_n_sub_two,
    sum_choose_le_n_sub_two n hn]

/-- The number of all `n`-variable Boolean functions is `2^(2^n)`. -/
theorem natCard_booleanFunction (n : ℕ) :
    Nat.card (BooleanFunction n) = 2 ^ (2 ^ n) := by
  rw [Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

private noncomputable def highDegreeEquivNotLow (n : ℕ) (hn : 2 ≤ n) :
    {f : BooleanFunction n // n - 1 ≤ FABL.functionAlgebraicDegree f} ≃
      {f : BooleanFunction n //
        ¬ FABL.functionAlgebraicDegree f ≤ n - 2} where
  toFun f := ⟨f.1, by omega⟩
  invFun f := ⟨f.1, by omega⟩
  left_inv f := by rfl
  right_inv f := by rfl

/-- The proportion of `n`-variable Boolean functions having degree at least
`n - 1`. -/
noncomputable def highAlgebraicDegreeProbability (n : ℕ) : ℝ :=
  1 - ((1 : ℝ) / 2) ^ (n + 1)

/-- The displayed probability is the exact uniform counting ratio. -/
theorem highAlgebraicDegreeProbability_eq_card_ratio
    (n : ℕ) (hn : 2 ≤ n) :
    highAlgebraicDegreeProbability n =
      (Nat.card {f : BooleanFunction n //
        n - 1 ≤ FABL.functionAlgebraicDegree f} : ℝ) /
        Nat.card (BooleanFunction n) := by
  have hhigh :
      Nat.card {f : BooleanFunction n //
        n - 1 ≤ FABL.functionAlgebraicDegree f} =
          2 ^ (2 ^ n) - 2 ^ (2 ^ n - n - 1) := by
    rw [Nat.card_congr (highDegreeEquivNotLow n hn)]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [natCard_booleanFunction,
      card_booleanFunctions_degree_le_n_sub_two_eq n hn]
  rw [highAlgebraicDegreeProbability, hhigh,
    natCard_booleanFunction]
  have hexp : 2 ^ n - n - 1 + (n + 1) = 2 ^ n := by
    have := n.lt_two_pow_self
    omega
  have hle : 2 ^ (2 ^ n - n - 1) ≤ 2 ^ (2 ^ n) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.cast_sub hle]
  norm_num [div_pow]
  rw [show (2 : ℝ) ^ (2 ^ n) =
      (2 : ℝ) ^ (2 ^ n - n - 1) * (2 : ℝ) ^ (n + 1) by
        rw [← pow_add, hexp]]
  field_simp

/-- A uniformly chosen Boolean function has degree at least `n - 1` with
probability tending to one. -/
theorem tendsto_highAlgebraicDegreeProbability :
    Filter.Tendsto highAlgebraicDegreeProbability Filter.atTop (𝓝 1) := by
  have hpow :
      Filter.Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n)
        Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hshift :
      Filter.Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ (n + 1))
        Filter.atTop (𝓝 0) := by
    simpa [pow_succ, mul_comm] using hpow.const_mul ((1 : ℝ) / 2)
  unfold highAlgebraicDegreeProbability
  simpa only [sub_zero] using hshift.const_sub 1

end CryptBoolean
