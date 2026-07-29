/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.ExtremalPropagation
public import CryptBoolean.Carlet.Chapter08.OrderCharacterization

import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
import CryptBoolean.Carlet.Chapter06.Bentness
import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# The zero branch in the extremal order-one classification

The normalized direction with two missing coordinates cannot be a linear
structure of a function satisfying the extremal propagation criterion of
order one in even dimension at least eight.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

@[expose] public section

namespace CryptBoolean

/-- The standard weight-`2k` direction in dimension `2k+2`, with its final
two coordinates equal to zero. -/
def standardPredThreeDirection (k : ℕ) : FABL.F₂Cube (2 * k + 2) :=
  Fin.append (fullDirection (2 * k)) (0 : FABL.F₂Cube 2)

private theorem standardPredThreeDirection_zero
    (k : ℕ) (hk : 1 ≤ k) : standardPredThreeDirection k 0 = 1 := by
  let i : Fin (2 * k) := ⟨0, by omega⟩
  have hzero : (0 : Fin (2 * k + 2)) = Fin.castAdd 2 i := by
    exact Fin.ext rfl
  rw [standardPredThreeDirection, hzero, Fin.append_left]
  simp [fullDirection]

private theorem card_f₂Support_standardPredThreeDirection (k : ℕ) :
    (FABL.f₂Support (standardPredThreeDirection k)).card = 2 * k := by
  rw [standardPredThreeDirection, card_f₂Support_append,
    card_f₂Support_fullDirection]
  have hzero : FABL.f₂Support (0 : FABL.F₂Cube 2) = ∅ := by
    ext i
    simp [FABL.mem_f₂Support]
  rw [hzero]
  simp

private theorem card_f₂Support_finCons_zero
    {m : ℕ} (v : FABL.F₂Cube m) :
    (FABL.f₂Support (Fin.cons 0 v)).card =
      (FABL.f₂Support v).card := by
  simp only [FABL.f₂Support, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp

private theorem f₂Support_add_eq_symmDiff
    {m : ℕ} (a b : FABL.F₂Cube m) :
    FABL.f₂Support (a + b) =
      FABL.f₂Support a ∆ FABL.f₂Support b := by
  ext i
  simp only [FABL.mem_f₂Support, Finset.mem_symmDiff]
  by_cases hai : a i = 0
  · simp [hai]
  · by_cases hbi : b i = 0
    · simp [hai, hbi]
    · have haone : a i = 1 := Fin.eq_one_of_ne_zero _ hai
      have hbone : b i = 1 := Fin.eq_one_of_ne_zero _ hbi
      simp [haone, hbone]

private theorem exists_lowWeight_standardPeriodRepresentative
    (k : ℕ) (hk : 3 ≤ k) (v : FABL.F₂Cube (2 * k + 1)) (hv : v ≠ 0) :
    ∃ u : FABL.F₂Cube (2 * k + 2),
      (u = Fin.cons 0 v ∨
          u = Fin.cons 0 v + standardPredThreeDirection k) ∧
        u ≠ 0 ∧ (FABL.f₂Support u).card ≤ 2 * k - 1 := by
  classical
  let u₀ : FABL.F₂Cube (2 * k + 2) := Fin.cons 0 v
  let A := standardPredThreeDirection k
  have hu₀ne : u₀ ≠ 0 := by
    intro hu₀
    apply hv
    funext i
    have hi := congrFun hu₀ i.succ
    simpa [u₀] using hi
  have hu₀card :
      (FABL.f₂Support u₀).card = (FABL.f₂Support v).card := by
    exact card_f₂Support_finCons_zero v
  by_cases hlow : (FABL.f₂Support u₀).card ≤ 2 * k - 1
  · exact ⟨u₀, Or.inl rfl, hu₀ne, hlow⟩
  · let u₁ := u₀ + A
    have hAzero : A 0 = 1 := by
      exact standardPredThreeDirection_zero k (by omega)
    have hu₁ne : u₁ ≠ 0 := by
      intro hu₁
      have hzero := congrFun hu₁ 0
      simp only [u₁, Pi.add_apply, u₀, Fin.cons_zero, hAzero,
        Pi.zero_apply, zero_add] at hzero
      exact one_ne_zero hzero
    have hAcard : (FABL.f₂Support A).card = 2 * k := by
      exact card_f₂Support_standardPredThreeDirection k
    have hu₀high : 2 * k ≤ (FABL.f₂Support u₀).card := by
      omega
    have hu₀compl : (FABL.f₂Support u₀)ᶜ.card ≤ 2 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hAcompl : (FABL.f₂Support A)ᶜ.card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hAcard]
      omega
    have hsupport :
        FABL.f₂Support u₁ =
          FABL.f₂Support u₀ ∆ FABL.f₂Support A := by
      exact f₂Support_add_eq_symmDiff u₀ A
    have hsubset :
        FABL.f₂Support u₀ ∆ FABL.f₂Support A ⊆
          (FABL.f₂Support u₀)ᶜ ∪ (FABL.f₂Support A)ᶜ := by
      intro i hi
      rcases (Finset.mem_symmDiff.mp hi) with hi | hi
      · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hi.2)
      · exact Finset.mem_union_left _ (Finset.mem_compl.mpr hi.2)
    have hu₁card : (FABL.f₂Support u₁).card ≤ 4 := by
      rw [hsupport]
      calc
        (FABL.f₂Support u₀ ∆ FABL.f₂Support A).card ≤
            ((FABL.f₂Support u₀)ᶜ ∪
              (FABL.f₂Support A)ᶜ).card :=
          Finset.card_le_card hsubset
        _ ≤ (FABL.f₂Support u₀)ᶜ.card +
            (FABL.f₂Support A)ᶜ.card := Finset.card_union_le _ _
        _ ≤ 4 := by omega
    refine ⟨u₁, Or.inr rfl, hu₁ne, ?_⟩
    exact hu₁card.trans (by omega)

private theorem eq_domainTranslate_of_booleanDerivative_eq_zero
    {m : ℕ} (f : BooleanFunction m) (a : FABL.F₂Cube m)
    (hperiod : FABL.booleanDerivative f a = 0) (x : FABL.F₂Cube m) :
    f (x + a) = f x := by
  have hsum := congrFun hperiod x
  change f x + f (x + a) = 0 at hsum
  exact ((eq_neg_of_add_eq_zero_left hsum).trans
    (ZModModule.neg_eq_self (f (x + a)))).symm

private theorem booleanDerivative_domainTranslate_eq_self_of_period
    {m : ℕ} (f : BooleanFunction m) (a u : FABL.F₂Cube m)
    (hperiod : FABL.booleanDerivative f a = 0) (x : FABL.F₂Cube m) :
    FABL.booleanDerivative f u (x + a) = FABL.booleanDerivative f u x := by
  have hfirst := eq_domainTranslate_of_booleanDerivative_eq_zero f a hperiod x
  have hsecond :=
    eq_domainTranslate_of_booleanDerivative_eq_zero f a hperiod (x + u)
  have harg : x + a + u = x + u + a := by abel
  simp only [FABL.booleanDerivative]
  rw [harg, hfirst, hsecond]

private theorem booleanDerivative_add_period_eq
    {m : ℕ} (f : BooleanFunction m) (a u : FABL.F₂Cube m)
    (hperiod : FABL.booleanDerivative f a = 0) :
    FABL.booleanDerivative f (u + a) = FABL.booleanDerivative f u := by
  funext x
  have htranslate :=
    eq_domainTranslate_of_booleanDerivative_eq_zero f a hperiod (x + u)
  have harg : x + (u + a) = x + u + a := by abel
  simp only [FABL.booleanDerivative]
  rw [harg, htranslate]

private theorem isBalanced_firstCoordinateSlice_zero_of_period
    {m : ℕ} (h : BooleanFunction (m + 1)) (a : FABL.F₂Cube (m + 1))
    (ha : a 0 = 1) (hbalanced : IsBalanced h)
    (hperiod : ∀ x, h (x + a) = h x) :
    IsBalanced (firstCoordinateSlice h 0) := by
  have hcons (x : FABL.F₂Cube m) :
      Fin.cons 0 (x + Fin.tail a) + a = Fin.cons 1 x := by
    rw [← Fin.cons_self_tail a]
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [ha]
    · change x j + a j.succ + a j.succ = x j
      rw [add_assoc, ZModModule.add_self, add_zero]
  have hslices :
      firstCoordinateSlice h 1 =
        fun x ↦ firstCoordinateSlice h 0 (x + Fin.tail a) := by
    funext x
    rw [firstCoordinateSlice, firstCoordinateSlice]
    rw [← hcons x, hperiod]
  have hweights :
      hammingWeight (firstCoordinateSlice h 1) =
        hammingWeight (firstCoordinateSlice h 0) := by
    rw [hslices, hammingWeight_translate]
  have hsplit := hammingWeight_firstCoordinateSlices h
  unfold IsBalanced at hbalanced ⊢
  rw [pow_succ] at hbalanced
  omega

/-- In dimension `2k+2` with `k≥3`, the standard weight-`2k` direction
cannot be a linear structure of a function satisfying `PC(2k-1)` of order
one. -/
theorem
    false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_linearStructure
    (k : ℕ) (hk : 3 ≤ k) (f : BooleanFunction (2 * k + 2))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k - 1) 1 f)
    (hperiod : FABL.booleanDerivative f (standardPredThreeDirection k) = 0) :
    False := by
  classical
  let A := standardPredThreeDirection k
  let g : BooleanFunction (2 * k + 1) := firstCoordinateSlice f 0
  have hzero :=
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      (2 * k - 1) 1 f (by omega)).mp hf
  have hgpc : SatisfiesPropagationCriterion (2 * k + 1) g := by
    intro v hv
    obtain ⟨u, huclass, hune, huweight⟩ :=
      exists_lowWeight_standardPeriodRepresentative k hk v hv.1
    have hzeroSupport :
        FABL.f₂Support (0 : FABL.F₂Cube (2 * k + 2)) = ∅ := by
      ext i
      simp [FABL.mem_f₂Support]
    have huWalsh : walshTransform (FABL.booleanDerivative f u) 0 = 0 := by
      apply hzero u 0 huweight
      · rw [hzeroSupport]
        simp
      · intro hpair
        apply hune
        exact congrArg Prod.fst hpair
      · rw [hzeroSupport]
        exact Finset.disjoint_empty_right _
    have hubalanced : IsBalanced (FABL.booleanDerivative f u) :=
      (isBalanced_iff_walshTransform_zero_eq_zero _).mpr huWalsh
    have hAzero : A 0 = 1 := standardPredThreeDirection_zero k (by omega)
    have huderivativePeriod :
        ∀ x, FABL.booleanDerivative f u (x + A) =
          FABL.booleanDerivative f u x := by
      intro x
      exact booleanDerivative_domainTranslate_eq_self_of_period
        f A u hperiod x
    have husliceBalanced :
        IsBalanced (firstCoordinateSlice (FABL.booleanDerivative f u) 0) :=
      isBalanced_firstCoordinateSlice_zero_of_period
        (FABL.booleanDerivative f u) A hAzero hubalanced huderivativePeriod
    have hbaseSlice :
        firstCoordinateSlice
            (FABL.booleanDerivative f (Fin.cons 0 v)) 0 =
          FABL.booleanDerivative g v := by
      funext x
      simp only [firstCoordinateSlice, FABL.booleanDerivative, g]
      congr 1
      apply congrArg f
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · rfl
    have huslice :
        firstCoordinateSlice (FABL.booleanDerivative f u) 0 =
          FABL.booleanDerivative g v := by
      rcases huclass with hu | hu
      · rw [hu]
        exact hbaseSlice
      · rw [hu, booleanDerivative_add_period_eq f A (Fin.cons 0 v) hperiod]
        exact hbaseSlice
    rw [huslice] at husliceBalanced
    exact husliceBalanced
  have hgbent : IsBent g :=
    (isBent_iff_satisfiesPropagationCriterion_dimension g).2 hgpc
  have hgeven := even_of_isBent g hgbent
  rcases hgeven with ⟨r, hr⟩
  omega

end CryptBoolean
