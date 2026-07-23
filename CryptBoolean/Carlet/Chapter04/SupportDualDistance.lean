/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Resiliency

/-!
# Support dual distance

The character-sum definition of dual distance for arbitrary binary codes and its
specialization to supports of correlation-immune and resilient Boolean functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The character sum of a binary code at a frequency. -/
noncomputable def codeCharacterSum
    (C : Finset (FABL.F₂Cube n)) (u : FABL.F₂Cube n) : ℝ :=
  ∑ x ∈ C, FABL.vectorWalshCharacter u x

/-- An arbitrary binary code has dual distance at least `d` when every nonzero
character of weight below `d` has zero sum over the code. -/
def HasDualDistanceAtLeast
    (C : Finset (FABL.F₂Cube n)) (d : ℕ) : Prop :=
  ∀ u : FABL.F₂Cube n, u ≠ 0 →
    (FABL.f₂Support u).card < d → codeCharacterSum C u = 0

/-- A nontrivial Walsh character sums to zero over the full binary cube. -/
theorem sum_vectorWalshCharacter_eq_zero
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    ∑ x, FABL.vectorWalshCharacter u x = 0 := by
  have h := FABL.expect_vectorWalshCharacter u
  rw [if_neg hu, Fintype.expect_eq_sum_div_card] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by positivity)

/-- At a nonzero frequency, the raw Walsh transform is minus twice the
character sum over the support. -/
theorem walshTransform_cast_eq_neg_two_mul_codeCharacterSum_support
    (f : BooleanFunction n) (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    (walshTransform f u : ℝ) =
      -2 * codeCharacterSum (support f) u := by
  rw [walshTransform_cast_eq_sum_realSignView_mul_character]
  calc
    ∑ x, realSignView f x * FABL.vectorWalshCharacter u x =
        ∑ x, (1 - 2 * (if f x = 1 then (1 : ℝ) else 0)) *
          FABL.vectorWalshCharacter u x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = 1
      · simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, hx]
        ring
      · have hxzero : f x = 0 := by
          by_contra hzero
          exact hx (Fin.eq_one_of_ne_zero (f x) hzero)
        simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, hxzero]
    _ = ∑ x, (FABL.vectorWalshCharacter u x -
          2 * ((if f x = 1 then (1 : ℝ) else 0) *
            FABL.vectorWalshCharacter u x)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, FABL.vectorWalshCharacter u x) -
        2 * ∑ x, (if f x = 1 then (1 : ℝ) else 0) *
          FABL.vectorWalshCharacter u x := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = -2 * ∑ x, (if f x = 1 then (1 : ℝ) else 0) *
          FABL.vectorWalshCharacter u x := by
      rw [sum_vectorWalshCharacter_eq_zero u hu]
      ring
    _ = -2 * codeCharacterSum (support f) u := by
      congr 1
      rw [codeCharacterSum, support, FABL.f₂OneSupport, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = 1 <;> simp [hx]

/-- Carlet's support-dual-distance corollary, correlation-immunity form. -/
theorem isCorrelationImmune_iff_support_hasDualDistanceAtLeast
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m < n) :
    IsCorrelationImmune m f ↔
      HasDualDistanceAtLeast (support f) (m + 1) := by
  rw [theorem_3_correlationImmune_iff_walshTransform_eq_zero m f hn hm]
  constructor
  · intro hwalsh u hu hweight
    have hzero := hwalsh u hu (Nat.lt_succ_iff.mp hweight)
    have hidentity :=
      walshTransform_cast_eq_neg_two_mul_codeCharacterSum_support f u hu
    rw [hzero, Int.cast_zero] at hidentity
    linarith
  · intro hdual u hu hweight
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero,
      walshTransform_cast_eq_neg_two_mul_codeCharacterSum_support f u hu,
      hdual u hu (Nat.lt_succ_iff.mpr hweight), mul_zero]

/-- For a nonempty binary cube, balancedness says exactly that the support has
cardinality `2^(n-1)`. -/
theorem isBalanced_iff_support_card_eq_two_pow_pred
    (f : BooleanFunction n) (hn : 0 < n) :
    IsBalanced f ↔ (support f).card = 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [IsBalanced, hammingWeight_eq_card_support]
  simp only [Nat.succ_sub_one, pow_succ]
  omega

/-- Carlet's support-dual-distance corollary, resilient form: the support has
size `2^(n-1)` and dual distance at least `m+1`. -/
theorem isResilient_iff_support_card_and_hasDualDistanceAtLeast
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m < n) :
    IsResilient m f ↔
      (support f).card = 2 ^ (n - 1) ∧
        HasDualDistanceAtLeast (support f) (m + 1) := by
  rw [IsResilient,
    isCorrelationImmune_iff_support_hasDualDistanceAtLeast m f hn hm,
    isBalanced_iff_support_card_eq_two_pow_pred f hn, and_comm]

end CryptBoolean
