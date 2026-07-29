/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AlgebraicDegree
public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
public import CryptBoolean.Carlet.Chapter04.SupportDualDistance
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Sums with disjoint truth supports

Carlet Section 7.5.2: weight, resiliency, nonlinearity, and algebraic degree
for sums of Boolean functions with disjoint truth supports.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- On disjoint binary truth values, the sign of the sum is the sum of the
two signs minus one. -/
private theorem bitSignInt_add_eq_add_sub_one_of_not_both_one
    (b c : FABL.𝔽₂) (hnotBoth : ¬(b = 1 ∧ c = 1)) :
    bitSignInt (b + c) = bitSignInt b + bitSignInt c - 1 := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · simp [hb, hc, bitSignInt]
    · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
      simp [hb, hcOne, bitSignInt]
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
    by_cases hc : c = 0
    · simp [hbOne, hc, bitSignInt]
    · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
      exact (hnotBoth ⟨hbOne, hcOne⟩).elim

/-- Disjoint truth supports make Hamming weight additive. -/
theorem hammingWeight_add_eq_of_disjoint_truthSupport
    (g h : BooleanFunction n)
    (hdisjoint : Disjoint (support g) (support h)) :
    hammingWeight (g + h) = hammingWeight g + hammingWeight h := by
  have hidentity := hammingWeight_add_add_two_mul_card_inter g h
  have hinter : support g ∩ support h = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
  rw [hinter] at hidentity
  simpa using hidentity

/-- The sum of two functions with disjoint truth supports is balanced exactly
when their weights add to half the cube. -/
theorem isBalanced_add_iff_hammingWeight_add_eq_two_pow_pred
    (g h : BooleanFunction n) (hn : 0 < n)
    (hdisjoint : Disjoint (support g) (support h)) :
    IsBalanced (g + h) ↔
      hammingWeight g + hammingWeight h = 2 ^ (n - 1) := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Nat.succ_sub_one, pow_succ]
    omega
  rw [IsBalanced,
    hammingWeight_add_eq_of_disjoint_truthSupport g h hdisjoint, hpow]
  omega

/-- Away from the zero frequency, the Walsh transform of a sum with disjoint
truth supports is the sum of the two Walsh transforms. -/
theorem walshTransform_add_of_disjoint_truthSupport
    (g h : BooleanFunction n)
    (hdisjoint : Disjoint (support g) (support h))
    (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    walshTransform (g + h) a = walshTransform g a + walshTransform h a := by
  classical
  have hterm (x : FABL.F₂Cube n) :
      walshTerm (g + h) a x =
        walshTerm g a x + walshTerm h a x - walshTerm 0 a x := by
    have hnotBoth : ¬(g x = 1 ∧ h x = 1) := by
      intro hboth
      exact Finset.disjoint_left.mp hdisjoint
        (mem_support g x |>.2 hboth.1) (mem_support h x |>.2 hboth.2)
    have hsign := bitSignInt_add_eq_add_sub_one_of_not_both_one
      (g x) (h x) hnotBoth
    change bitSignInt ((g x + h x) + FABL.f₂DotProduct a x) =
      bitSignInt (g x + FABL.f₂DotProduct a x) +
        bitSignInt (h x + FABL.f₂DotProduct a x) -
          bitSignInt (0 + FABL.f₂DotProduct a x)
    rw [bitSignInt_add (g x + h x), hsign, bitSignInt_add (g x),
      bitSignInt_add (h x), zero_add]
    ring
  have hzero : walshTransform (0 : BooleanFunction n) a = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero,
      walshTransform_cast_eq_neg_two_mul_codeCharacterSum_support _ a ha]
    simp [codeCharacterSum, support, FABL.f₂OneSupport]
  rw [walshTransform, walshTransform, walshTransform]
  calc
    ∑ x, walshTerm (g + h) a x =
        ∑ x, (walshTerm g a x + walshTerm h a x - walshTerm 0 a x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hterm x
    _ = (∑ x, walshTerm g a x) + (∑ x, walshTerm h a x) -
        ∑ x, walshTerm 0 a x := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ x, walshTerm g a x) + ∑ x, walshTerm h a x := by
      have hzero' : (∑ x, walshTerm 0 a x) = 0 := by
        simpa [walshTransform] using hzero
      rw [hzero', sub_zero]

/-- Two correlation-immune functions of the same order whose disjoint-support
sum is balanced yield a resilient function of that order. -/
theorem isResilient_add_of_disjoint_truthSupport
    (g h : BooleanFunction n) (hn : 0 < n) (hm : m < n)
    (hdisjoint : Disjoint (support g) (support h))
    (hg : IsCorrelationImmune m g) (hh : IsCorrelationImmune m h)
    (hbalanced : IsBalanced (g + h)) :
    IsResilient m (g + h) := by
  refine ⟨?_, hbalanced⟩
  apply (theorem_3_correlationImmune_iff_walshTransform_eq_zero
    m (g + h) hn hm).2
  intro a ha hweight
  rw [walshTransform_add_of_disjoint_truthSupport g h hdisjoint a ha,
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m g hn hm).1 hg a ha hweight,
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m h hn hm).1 hh a ha hweight,
    add_zero]

/-- The Walsh maximum of a balanced disjoint-support sum is at most the sum
of the two Walsh maxima. -/
theorem maxWalshMagnitude_add_le_of_disjoint_truthSupport
    (g h : BooleanFunction n)
    (hdisjoint : Disjoint (support g) (support h))
    (hbalanced : IsBalanced (g + h)) :
    maxWalshMagnitude (g + h) ≤
      maxWalshMagnitude g + maxWalshMagnitude h := by
  unfold maxWalshMagnitude
  apply Finset.sup'_le
  intro a _ha
  by_cases ha : a = 0
  · subst a
    rw [(isBalanced_iff_walshTransform_zero_eq_zero (g + h)).1 hbalanced]
    simp
  · rw [walshTransform_add_of_disjoint_truthSupport g h hdisjoint a ha]
    exact (Int.natAbs_add_le _ _).trans
      (Nat.add_le_add
        (walshTransform_natAbs_le_maxWalshMagnitude g a)
        (walshTransform_natAbs_le_maxWalshMagnitude h a))

/-- Division-free form of the nonlinearity lower bound for a balanced sum
with disjoint truth supports. -/
theorem nonlinearity_add_le_two_pow_pred_add_of_disjoint_truthSupport
    (g h : BooleanFunction n) (hn : 0 < n)
    (hdisjoint : Disjoint (support g) (support h))
    (hbalanced : IsBalanced (g + h)) :
    nonlinearity g + nonlinearity h ≤
      2 ^ (n - 1) + nonlinearity (g + h) := by
  have hmax := maxWalshMagnitude_add_le_of_disjoint_truthSupport
    g h hdisjoint hbalanced
  have hsum := two_mul_nonlinearity_add_maxWalshMagnitude (g + h)
  have hg := two_mul_nonlinearity_add_maxWalshMagnitude g
  have hh := two_mul_nonlinearity_add_maxWalshMagnitude h
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [Nat.succ_sub_one, pow_succ]
    omega
  omega

/-- Carlet's nonlinearity lower bound for a balanced sum with disjoint truth
supports. -/
theorem nonlinearity_add_sub_two_pow_pred_le_of_disjoint_truthSupport
    (g h : BooleanFunction n) (hn : 0 < n)
    (hdisjoint : Disjoint (support g) (support h))
    (hbalanced : IsBalanced (g + h)) :
    nonlinearity g + nonlinearity h - 2 ^ (n - 1) ≤
      nonlinearity (g + h) := by
  have hbound :=
    nonlinearity_add_le_two_pow_pred_add_of_disjoint_truthSupport
      g h hn hdisjoint hbalanced
  omega

/-- Algebraic degree is submaximal under a sum with disjoint truth supports. -/
theorem functionAlgebraicDegree_add_le_max_of_disjoint_truthSupport
    (g h : BooleanFunction n)
    (_hdisjoint : Disjoint (support g) (support h)) :
    FABL.functionAlgebraicDegree (g + h) ≤
      max (FABL.functionAlgebraicDegree g)
        (FABL.functionAlgebraicDegree h) :=
  FABL.functionAlgebraicDegree_add_le_max g h

/-- Algebraic-degree equality occurs for a nonzero one-variable summand and
the zero summand, whose truth supports are disjoint. -/
theorem exists_disjoint_truthSupport_functionAlgebraicDegree_add_eq_max :
    ∃ g h : BooleanFunction 1,
      Disjoint (support g) (support h) ∧ g ≠ 0 ∧
        FABL.functionAlgebraicDegree (g + h) =
          max (FABL.functionAlgebraicDegree g)
            (FABL.functionAlgebraicDegree h) := by
  let g : BooleanFunction 1 := fun x ↦ x 0
  refine ⟨g, 0, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.2
    intro x _hx hzero
    have : (0 : BooleanFunction 1) x = 1 := (mem_support _ _).1 hzero
    simp at this
  · intro hzero
    have hvalue := congrFun hzero (fun _ ↦ (1 : FABL.𝔽₂))
    norm_num [g] at hvalue
  · simp

end CryptBoolean
