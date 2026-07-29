/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.NonlinearityBounds
public import CryptBoolean.Carlet.Chapter09.PrescribedDegreeAnnihilators

/-!
# Higher-order nonlinearity from algebraic immunity

Carlet Chapter 9: the universal positive-order bound from reference [70].
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem pow_two_mul_sum_choose_le_sum_choose_add
    (m r k : ℕ) :
    2 ^ r * (∑ i ∈ Finset.range k, Nat.choose m i) ≤
      ∑ i ∈ Finset.range (k + r), Nat.choose (m + r) i := by
  induction r with
  | zero => simp
  | succ r ih =>
      let D := ∑ i ∈ Finset.range (k + r), Nat.choose (m + r) i
      have hmono : D ≤
          ∑ i ∈ Finset.range (k + r + 1), Nat.choose (m + r) i :=
        sum_choose_range_mono (m + r) (by omega)
      have hdouble : 2 * D ≤
          ∑ i ∈ Finset.range (k + (r + 1)),
            Nat.choose (m + (r + 1)) i := by
        rw [show m + (r + 1) = (m + r) + 1 by omega,
          show k + (r + 1) = k + r + 1 by omega,
          sum_choose_succ_dimension]
        dsimp [D] at hmono ⊢
        omega
      calc
        2 ^ (r + 1) *
            (∑ i ∈ Finset.range k, Nat.choose m i) =
            2 * (2 ^ r *
              (∑ i ∈ Finset.range k, Nat.choose m i)) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * D := Nat.mul_le_mul_left 2 ih
        _ ≤ _ := hdouble

private theorem two_mul_sum_choose_sub_le_sum_choose
    (n r k : ℕ) (hr : 0 < r) (hrn : r ≤ n) :
    2 * (∑ i ∈ Finset.range k, Nat.choose (n - r) i) ≤
      ∑ i ∈ Finset.range (k + r), Nat.choose n i := by
  have hpow : 2 ≤ 2 ^ r := by
    cases r with
    | zero => omega
    | succ r =>
        rw [pow_succ]
        have hpositive : 0 < 2 ^ r := pow_pos (by omega) r
        omega
  have hadd : n - r + r = n := Nat.sub_add_cancel hrn
  calc
    2 * (∑ i ∈ Finset.range k, Nat.choose (n - r) i) ≤
        2 ^ r * (∑ i ∈ Finset.range k, Nat.choose (n - r) i) :=
      Nat.mul_le_mul_right _ hpow
    _ ≤ ∑ i ∈ Finset.range (k + r),
        Nat.choose ((n - r) + r) i :=
      pow_two_mul_sum_choose_le_sum_choose_add (n - r) r k
    _ = _ := by rw [hadd]

/-- The error set between `f` and `g` splits according to the output of `f`. -/
theorem hammingWeight_add_eq_product_partition
    (f g : BooleanFunction n) :
    hammingWeight (f + g) =
      hammingWeight (f * (g + 1)) + hammingWeight ((f + 1) * g) := by
  let left : BooleanFunction n := f * (g + 1)
  let right : BooleanFunction n := (f + 1) * g
  have hsum : left + right = f + g := by
    dsimp [left, right]
    funext x
    change f x * (g x + 1) + (f x + 1) * g x = f x + g x
    by_cases hf : f x = 0
    · by_cases hg : g x = 0
      · simp [hf, hg]
      · have hgOne : g x = 1 := Fin.eq_one_of_ne_zero _ hg
        simp [hf, hgOne]
    · have hfOne : f x = 1 := Fin.eq_one_of_ne_zero _ hf
      by_cases hg : g x = 0
      · simp [hfOne, hg]
      · have hgOne : g x = 1 := Fin.eq_one_of_ne_zero _ hg
        simp [hfOne, hgOne]
  have hproduct : left * right = 0 := by
    dsimp [left, right]
    calc
      (f * (g + 1)) * ((f + 1) * g) =
          (f * (f + 1)) * (g * (g + 1)) := by ac_rfl
      _ = 0 := by rw [booleanFunction_mul_complement, zero_mul]
  have hinter : support left ∩ support right = ∅ := by
    rw [← support_mul, hproduct]
    ext x
    simp [mem_support]
  have hweight := hammingWeight_add_add_two_mul_card_inter left right
  rw [hinter] at hweight
  simpa [hsum] using hweight

private theorem functionAlgebraicDegree_add_one_le
    (g : BooleanFunction n) (r : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r) :
    FABL.functionAlgebraicDegree (g + 1) ≤ r := by
  exact (FABL.functionAlgebraicDegree_add_le_max g 1).trans (by
    rw [FABL.functionAlgebraicDegree_one]
    exact max_le hdegree (Nat.zero_le r))

private theorem add_one_ne_zero_of_ne_one
    (g : BooleanFunction n) (hne : g ≠ 1) :
    g + 1 ≠ 0 := by
  intro hzero
  apply hne
  calc
    g = (g + 1) + 1 := by
      funext x
      change g x = g x + 1 + 1
      rw [add_assoc, ZModModule.add_self, add_zero]
    _ = 0 + 1 := congrArg (fun q : BooleanFunction n ↦ q + 1) hzero
    _ = 1 := zero_add 1

/-- Carlet's higher-order algebraic-immunity bound: for positive order below
`AI(f)`, the order-`r` nonlinearity is at least twice the Reed–Muller
dimension in `n-r` variables below degree `AI(f)-r`. -/
theorem two_mul_sum_choose_sub_le_higherOrderNonlinearity
    (f : BooleanFunction n) (r : ℕ) (hr : 0 < r)
    (hrAI : r < algebraicImmunity f) :
    2 * (∑ i ∈ Finset.range (algebraicImmunity f - r),
      Nat.choose (n - r) i) ≤ higherOrderNonlinearity r f := by
  obtain ⟨g, hgDegree, hgDistance⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  have hrn : r ≤ n := by
    have hAI := algebraicImmunity_le_ceiling_half f
    omega
  have hconstantBound (c : BooleanFunction n)
      (hc : c = 0 ∨ c = 1) :
      2 * (∑ i ∈ Finset.range (algebraicImmunity f - r),
        Nat.choose (n - r) i) ≤ hammingWeight (f + c) := by
    have hAIc : algebraicImmunity (f + c) = algebraicImmunity f := by
      rcases hc with rfl | rfl
      · rw [add_zero]
      · exact algebraicImmunity_add_constant_one f
    have hweight := sum_choose_below_algebraicImmunity_le_hammingWeight (f + c)
    rw [hAIc] at hweight
    have hcombinatorial := two_mul_sum_choose_sub_le_sum_choose n r
      (algebraicImmunity f - r) hr hrn
    have hindex : algebraicImmunity f - r + r = algebraicImmunity f := by
      omega
    rw [hindex] at hcombinatorial
    exact hcombinatorial.trans hweight
  by_cases hgZero : g = 0
  · calc
      2 * (∑ i ∈ Finset.range (algebraicImmunity f - r),
          Nat.choose (n - r) i) ≤ hammingWeight (f + g) :=
        hconstantBound g (Or.inl hgZero)
      _ = hammingDistance f g :=
        (hammingDistance_eq_hammingWeight_add f g).symm
      _ = higherOrderNonlinearity r f := hgDistance
  · by_cases hgOne : g = 1
    · calc
        2 * (∑ i ∈ Finset.range (algebraicImmunity f - r),
            Nat.choose (n - r) i) ≤ hammingWeight (f + g) :=
          hconstantBound g (Or.inr hgOne)
        _ = hammingDistance f g :=
          (hammingDistance_eq_hammingWeight_add f g).symm
        _ = higherOrderNonlinearity r f := hgDistance
    · have hgComplementNe : g + 1 ≠ 0 :=
        add_one_ne_zero_of_ne_one g hgOne
      have hgComplementDegree : FABL.functionAlgebraicDegree (g + 1) ≤ r :=
        functionAlgebraicDegree_add_one_le g r hgDegree
      have hleft := sum_choose_sub_degree_le_hammingWeight_mul
        f (g + 1) hgComplementNe r hgComplementDegree hrAI
      have hright := sum_choose_sub_degree_le_hammingWeight_mul
        (f + 1) g hgZero r hgDegree (by
          rw [algebraicImmunity_add_constant_one]
          exact hrAI)
      rw [algebraicImmunity_add_constant_one] at hright
      calc
        2 * (∑ i ∈ Finset.range (algebraicImmunity f - r),
            Nat.choose (n - r) i) ≤
            hammingWeight (f * (g + 1)) + hammingWeight ((f + 1) * g) := by
          omega
        _ = hammingWeight (f + g) :=
          (hammingWeight_add_eq_product_partition f g).symm
        _ = hammingDistance f g :=
          (hammingDistance_eq_hammingWeight_add f g).symm
        _ = higherOrderNonlinearity r f := hgDistance


end CryptBoolean
