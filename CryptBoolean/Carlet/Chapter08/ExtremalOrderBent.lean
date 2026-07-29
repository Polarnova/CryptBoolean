/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.ExtremalPropagation
public import CryptBoolean.Carlet.Chapter08.OrderCharacterization

import CryptBoolean.Carlet.Chapter07.DirectSum
import CryptBoolean.Carlet.Chapter08.EmbeddedCoordinateRestrictions
import CryptBoolean.Carlet.Chapter08.ExtremalOrderCompleteQuadratic
import CryptBoolean.Carlet.Chapter08.ExtremalOrderPeriod

/-!
# Bentness at propagation order one

Carlet Proposition 4: in even dimension at least eight, `PC(n-3)` of
order one forces bentness.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

private theorem firstBlockSlice_booleanDerivative_append_zero
    (f : BooleanFunction (n + 1)) (a : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    firstBlockSlice
        (FABL.booleanDerivative f
          (Fin.append a (singletonF₂Cube 0)))
        (singletonF₂Cube b) =
      FABL.booleanDerivative
        (firstBlockSlice f (singletonF₂Cube b)) a := by
  funext x
  simp only [firstBlockSlice, FABL.booleanDerivative]
  have hadd :
      Fin.append x (singletonF₂Cube b) +
          Fin.append a (singletonF₂Cube 0) =
        Fin.append (x + a) (singletonF₂Cube b) := by
    rw [← finAppend_add]
    congr 1
    funext i
    fin_cases i
    simp [singletonF₂Cube]
  rw [hadd]

private theorem disjoint_f₂Support_append_zero_zero_append
    (a : FABL.F₂Cube n) (b : FABL.F₂Cube m) :
    Disjoint
      (FABL.f₂Support (Fin.append a (0 : FABL.F₂Cube m)))
      (FABL.f₂Support (Fin.append (0 : FABL.F₂Cube n) b)) := by
  rw [Finset.disjoint_left]
  intro i
  refine Fin.addCases
    (motive := fun q ↦
      q ∈ FABL.f₂Support (Fin.append a (0 : FABL.F₂Cube m)) →
      q ∈ FABL.f₂Support (Fin.append (0 : FABL.F₂Cube n) b) →
      False)
    (fun j hiA hiB ↦ ?_)
    (fun j hiA hiB ↦ ?_) i
  · rw [FABL.mem_f₂Support] at hiB
    exact hiB (by simp)
  · rw [FABL.mem_f₂Support] at hiA
    exact hiA (by simp)

/-- Fixing the last coordinate of a function satisfying `PC(l)` of order one
produces a function satisfying `PC(l)`. -/
theorem satisfiesPropagationCriterion_firstBlockSlice_of_order_one
    (f : BooleanFunction (n + 1)) (l : ℕ) (hparameters : l + 1 ≤ n + 1)
    (hf : SatisfiesPropagationCriterionOfOrder l 1 f) (b : FABL.𝔽₂) :
    SatisfiesPropagationCriterion l
      (firstBlockSlice f (singletonF₂Cube b)) := by
  have hzero :=
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l 1 f hparameters).mp hf
  intro a ha
  apply (isBalanced_iff_walshTransform_zero_eq_zero _).mpr
  let A : FABL.F₂Cube (n + 1) :=
    Fin.append a (singletonF₂Cube 0)
  let B : FABL.F₂Cube (n + 1) :=
    Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 1)
  have hAweight : (FABL.f₂Support A).card ≤ l := by
    change (FABL.f₂Support
      (Fin.append a (singletonF₂Cube 0))).card ≤ l
    rw [card_f₂Support_append]
    have hzeroSupport :
        FABL.f₂Support (singletonF₂Cube 0) = ∅ := by
      ext i
      fin_cases i
      simp [FABL.mem_f₂Support, singletonF₂Cube]
    rw [hzeroSupport, Finset.card_empty, Nat.add_zero]
    exact ha.2
  have hBweight : (FABL.f₂Support B).card ≤ 1 := by
    change (FABL.f₂Support
      (Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 1))).card ≤ 1
    rw [card_f₂Support_append]
    have hzeroSupport :
        FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
      ext i
      simp [FABL.mem_f₂Support]
    have honeSupport :
        (FABL.f₂Support (singletonF₂Cube 1)).card = 1 := by
      have hsupport : FABL.f₂Support (singletonF₂Cube 1) = Finset.univ := by
        ext i
        fin_cases i
        simp [FABL.mem_f₂Support, singletonF₂Cube]
      rw [hsupport]
      simp
    rw [hzeroSupport, Finset.card_empty, Nat.zero_add, honeSupport]
  have hAne : A ≠ 0 := by
    intro hA
    apply ha.1
    funext i
    have hi := congrFun hA (Fin.castAdd 1 i)
    simpa [A] using hi
  have hdisjoint : Disjoint (FABL.f₂Support A) (FABL.f₂Support B) := by
    change Disjoint
      (FABL.f₂Support
        (Fin.append a (0 : FABL.F₂Cube 1)))
      (FABL.f₂Support
        (Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 1)))
    exact disjoint_f₂Support_append_zero_zero_append a (singletonF₂Cube 1)
  have hambientSupportZero :
      FABL.f₂Support (0 : FABL.F₂Cube (n + 1)) = ∅ := by
    ext i
    simp [FABL.mem_f₂Support]
  have hambientZero :
      walshTransform (FABL.booleanDerivative f A) 0 = 0 := by
    apply hzero A 0 hAweight
      (by rw [hambientSupportZero, Finset.card_empty]; omega)
    · intro hpair
      exact hAne (congrArg Prod.fst hpair)
    · rw [hambientSupportZero]
      exact Finset.disjoint_empty_right _
  have hambientLast :
      walshTransform (FABL.booleanDerivative f A) B = 0 := by
    apply hzero A B hAweight hBweight
    · intro hpair
      exact hAne (congrArg Prod.fst hpair)
    · exact hdisjoint
  have hsum := walshTransform_append_singletonF₂Cube
    (FABL.booleanDerivative f A) (0 : FABL.F₂Cube n) 0
  have hdifference := walshTransform_append_singletonF₂Cube
    (FABL.booleanDerivative f A) (0 : FABL.F₂Cube n) 1
  have hsliceZero :
      walshTransform
          (firstBlockSlice
            (FABL.booleanDerivative f A) (singletonF₂Cube 0)) 0 = 0 := by
    simp only [A, B] at hambientZero hambientLast hsum hdifference
    norm_num [bitSignInt] at hsum hdifference
    have hfrequencyZero :
        Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 0) = 0 := by
      funext i
      exact Fin.addCases
        (fun j ↦ by simp [Fin.append])
        (fun j ↦ by simp [Fin.append, singletonF₂Cube]) i
    rw [hfrequencyZero, hambientZero] at hsum
    rw [hambientLast] at hdifference
    change walshTransform
      (firstBlockSlice
        (FABL.booleanDerivative f
          (Fin.append a (singletonF₂Cube 0))) (singletonF₂Cube 0)) 0 = 0
    linarith
  have hsliceOne :
      walshTransform
          (firstBlockSlice
            (FABL.booleanDerivative f A) (singletonF₂Cube 1)) 0 = 0 := by
    simp only [A, B] at hambientZero hambientLast hsum hdifference
    norm_num [bitSignInt] at hsum hdifference
    have hfrequencyZero :
        Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 0) = 0 := by
      funext i
      exact Fin.addCases
        (fun j ↦ by simp [Fin.append])
        (fun j ↦ by simp [Fin.append, singletonF₂Cube]) i
    rw [hfrequencyZero, hambientZero] at hsum
    rw [hambientLast] at hdifference
    change walshTransform
      (firstBlockSlice
        (FABL.booleanDerivative f
          (Fin.append a (singletonF₂Cube 0))) (singletonF₂Cube 1)) 0 = 0
    linarith
  fin_cases b
  · rw [← firstBlockSlice_booleanDerivative_append_zero]
    exact hsliceZero
  · rw [← firstBlockSlice_booleanDerivative_append_zero]
    exact hsliceOne

/-- In odd dimension, the extremal propagation criterion makes every
nonzero derivative either constant or balanced. -/
theorem isLinearStructure_or_isBalanced_of_satisfiesPropagationCriterion_pred_two_odd
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hf : SatisfiesPropagationCriterion (2 * k - 1) f)
    (a : FABL.F₂Cube (2 * k + 1)) (ha : a ≠ 0) :
    IsLinearStructure f a ∨ IsBalanced (FABL.booleanDerivative f a) := by
  rcases
      (satisfiesPropagationCriterion_pred_two_iff_hasUniqueHighWeightLinearStructure
        k hk f).mp hf with
    ⟨q, hqne, hqweight, hqlinear, hbalanced⟩
  by_cases haq : a = q
  · left
    simpa [haq] using hqlinear
  · right
    exact hbalanced a ha haq

/-- Hamming weight splits over the two values of the last coordinate. -/
theorem hammingWeight_eq_add_firstBlockSlices
    (f : BooleanFunction (n + 1)) :
    hammingWeight f =
      hammingWeight (firstBlockSlice f (singletonF₂Cube 0)) +
        hammingWeight (firstBlockSlice f (singletonF₂Cube 1)) := by
  have hsplit := walshTransform_append_singletonF₂Cube
    f (0 : FABL.F₂Cube n) 0
  norm_num [bitSignInt] at hsplit
  have hfrequencyZero :
      Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 0) = 0 := by
    funext i
    exact Fin.addCases
      (fun j ↦ by simp [Fin.append])
      (fun j ↦ by simp [Fin.append, singletonF₂Cube]) i
  rw [hfrequencyZero,
    walshTransform_zero_eq_two_pow_sub_two_weight,
    walshTransform_zero_eq_two_pow_sub_two_weight,
    walshTransform_zero_eq_two_pow_sub_two_weight] at hsplit
  rw [pow_succ] at hsplit
  omega

/-- Balancedness glues across the two values of the last coordinate. -/
theorem isBalanced_of_firstBlockSlices
    (f : BooleanFunction (n + 1))
    (hzero : IsBalanced
      (firstBlockSlice f (singletonF₂Cube 0)))
    (hone : IsBalanced
      (firstBlockSlice f (singletonF₂Cube 1))) :
    IsBalanced f := by
  apply (isBalanced_iff_walshTransform_zero_eq_zero f).mpr
  have hsplit := walshTransform_append_singletonF₂Cube
    f (0 : FABL.F₂Cube n) 0
  norm_num [bitSignInt] at hsplit
  have hfrequencyZero :
      Fin.append (0 : FABL.F₂Cube n) (singletonF₂Cube 0) = 0 := by
    funext i
    exact Fin.addCases
      (fun j ↦ by simp [Fin.append])
      (fun j ↦ by simp [Fin.append, singletonF₂Cube]) i
  rw [hfrequencyZero,
    (isBalanced_iff_walshTransform_zero_eq_zero _).mp hzero,
    (isBalanced_iff_walshTransform_zero_eq_zero _).mp hone,
    add_zero] at hsplit
  exact hsplit

private theorem booleanFunction_eq_one_of_hammingWeight_eq_two_pow
    (f : BooleanFunction n) (hf : hammingWeight f = 2 ^ n) :
    f = 1 := by
  rw [hammingWeight_eq_card_support, ← card_f₂Cube n] at hf
  have hsupport : support f = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [Finset.card_univ]
      exact hf.ge)
  funext x
  exact (mem_support f x).mp (by rw [hsupport]; exact Finset.mem_univ x)

/-- If a balanced function is constant on one last-coordinate slice, it is
the complementary constant on the other slice. -/
theorem firstBlockSlice_eq_complement_of_isBalanced
    (f : BooleanFunction (n + 1)) (hf : IsBalanced f)
    (c : FABL.𝔽₂)
    (hzero : firstBlockSlice f (singletonF₂Cube 0) = fun _ ↦ c) :
    firstBlockSlice f (singletonF₂Cube 1) = fun _ ↦ c + 1 := by
  have hweight := hammingWeight_eq_add_firstBlockSlices f
  have hfweight : hammingWeight f = 2 ^ n := by
    unfold IsBalanced at hf
    rw [pow_succ] at hf
    omega
  by_cases hc : c = 0
  · subst c
    have hleftWeight :
        hammingWeight (firstBlockSlice f (singletonF₂Cube 0)) = 0 := by
      have hconstZero :
          (fun _ : FABL.F₂Cube n ↦ (0 : FABL.𝔽₂)) = 0 := rfl
      rw [hzero, hconstZero]
      simp [hammingWeight]
    have hrightWeight :
        hammingWeight (firstBlockSlice f (singletonF₂Cube 1)) = 2 ^ n := by
      omega
    have hone := booleanFunction_eq_one_of_hammingWeight_eq_two_pow
      (firstBlockSlice f (singletonF₂Cube 1)) hrightWeight
    calc
      firstBlockSlice f (singletonF₂Cube 1) = 1 := hone
      _ = (fun _ : FABL.F₂Cube n ↦ (0 : FABL.𝔽₂) + 1) := by
        funext x
        simp
  · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
    subst c
    have hleftWeight :
        hammingWeight (firstBlockSlice f (singletonF₂Cube 0)) = 2 ^ n := by
      rw [hzero]
      rw [hammingWeight_eq_card_support]
      have hs : support (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂)) =
          Finset.univ := by
        ext x
        simp [mem_support]
      rw [hs, Finset.card_univ, card_f₂Cube]
    have hrightWeight :
        hammingWeight (firstBlockSlice f (singletonF₂Cube 1)) = 0 := by
      omega
    have hrightZero := hammingNorm_eq_zero.mp hrightWeight
    calc
      firstBlockSlice f (singletonF₂Cube 1) = 0 := hrightZero
      _ = (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂) + 1) := by
        funext x
        simp

private theorem f₂DotProduct_coordinateSwapLinearEquiv
    (i j : Fin n) (a x : FABL.F₂Cube n) :
    FABL.f₂DotProduct (coordinateSwapLinearEquiv i j a)
        (coordinateSwapLinearEquiv i j x) =
      FABL.f₂DotProduct a x := by
  simp only [FABL.f₂DotProduct, dotProduct,
    coordinateSwapLinearEquiv_apply]
  exact Equiv.sum_comp (Equiv.swap i j)
    (fun t ↦ a t * x t)

private theorem walshTransform_comp_coordinateSwapLinearEquiv
    (f : BooleanFunction n) (i j : Fin n) (b : FABL.F₂Cube n) :
    walshTransform (f ∘ coordinateSwapLinearEquiv i j) b =
      walshTransform f (coordinateSwapLinearEquiv i j b) := by
  classical
  rw [walshTransform, walshTransform]
  apply Fintype.sum_equiv (coordinateSwapLinearEquiv i j).toEquiv
  intro x
  simp only [walshTerm, Function.comp_apply]
  apply congrArg bitSignInt
  congr 1
  exact (f₂DotProduct_coordinateSwapLinearEquiv i j b x).symm

private theorem card_f₂Support_coordinateSwapLinearEquiv
    (i j : Fin n) (a : FABL.F₂Cube n) :
    (FABL.f₂Support (coordinateSwapLinearEquiv i j a)).card =
      (FABL.f₂Support a).card := by
  simp only [FABL.f₂Support, Finset.card_filter,
    coordinateSwapLinearEquiv_apply]
  exact Equiv.sum_comp (Equiv.swap i j)
    (fun t ↦ if a t ≠ 0 then 1 else 0)

private theorem disjoint_f₂Support_coordinateSwapLinearEquiv
    (i j : Fin n) (a b : FABL.F₂Cube n)
    (hab : Disjoint (FABL.f₂Support a) (FABL.f₂Support b)) :
    Disjoint
      (FABL.f₂Support (coordinateSwapLinearEquiv i j a))
      (FABL.f₂Support (coordinateSwapLinearEquiv i j b)) := by
  rw [Finset.disjoint_left] at hab ⊢
  intro t hta htb
  apply hab
  · rw [FABL.mem_f₂Support] at hta ⊢
    simpa using hta
  · rw [FABL.mem_f₂Support] at htb ⊢
    simpa using htb

private theorem booleanDerivative_comp_coordinateSwapLinearEquiv
    (f : BooleanFunction n) (i j : Fin n) (a : FABL.F₂Cube n) :
    FABL.booleanDerivative (f ∘ coordinateSwapLinearEquiv i j) a =
      FABL.booleanDerivative f (coordinateSwapLinearEquiv i j a) ∘
        coordinateSwapLinearEquiv i j := by
  funext x
  simp only [FABL.booleanDerivative, Function.comp_apply,
    map_add]

private theorem satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv
    (f : BooleanFunction n) (l k : ℕ) (hparameters : l + k ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l k f)
    (i j : Fin n) :
    SatisfiesPropagationCriterionOfOrder l k
      (f ∘ coordinateSwapLinearEquiv i j) := by
  apply
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k (f ∘ coordinateSwapLinearEquiv i j) hparameters).mpr
  have hzero :=
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k f hparameters).mp hf
  intro a b haweight hbweight hab hdisjoint
  rw [booleanDerivative_comp_coordinateSwapLinearEquiv,
    walshTransform_comp_coordinateSwapLinearEquiv]
  apply hzero
  · simpa [card_f₂Support_coordinateSwapLinearEquiv] using haweight
  · simpa [card_f₂Support_coordinateSwapLinearEquiv] using hbweight
  · intro hpair
    apply hab
    apply Prod.ext
    · apply (coordinateSwapLinearEquiv i j).injective
      simpa using congrArg Prod.fst hpair
    · apply (coordinateSwapLinearEquiv i j).injective
      simpa using congrArg Prod.snd hpair
  · exact disjoint_f₂Support_coordinateSwapLinearEquiv i j a b hdisjoint

/-- Permuting two input coordinates preserves every propagation criterion
of order. -/
theorem satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv_iff
    (f : BooleanFunction n) (l k : ℕ) (hparameters : l + k ≤ n)
    (i j : Fin n) :
    SatisfiesPropagationCriterionOfOrder l k
        (f ∘ coordinateSwapLinearEquiv i j) ↔
      SatisfiesPropagationCriterionOfOrder l k f := by
  constructor
  · intro hf
    have htwice :=
      satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv
        (f ∘ coordinateSwapLinearEquiv i j) l k hparameters hf i j
    have hfunction :
        (f ∘ coordinateSwapLinearEquiv i j) ∘
            coordinateSwapLinearEquiv i j = f := by
      funext x
      apply congrArg f
      funext t
      simp only [coordinateSwapLinearEquiv_apply]
      rw [Equiv.swap_apply_self]
    simpa only [hfunction] using htwice
  · intro hf
    exact satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv
      f l k hparameters hf i j

private theorem isBalanced_comp_coordinateSwapLinearEquiv_iff
    (f : BooleanFunction n) (i j : Fin n) :
    IsBalanced (f ∘ coordinateSwapLinearEquiv i j) ↔ IsBalanced f := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero,
    isBalanced_iff_walshTransform_zero_eq_zero,
    walshTransform_comp_coordinateSwapLinearEquiv]
  have hzero :
      coordinateSwapLinearEquiv i j (0 : FABL.F₂Cube n) = 0 := by
    exact (coordinateSwapLinearEquiv i j).map_zero
  rw [hzero]

private theorem exists_constant_firstBlockSlice_of_not_isBalanced
    (f : BooleanFunction (n + 1)) (hf : ¬ IsBalanced f)
    (hdichotomy : ∀ b : FABL.𝔽₂,
      (∃ c : FABL.𝔽₂,
        firstBlockSlice f (singletonF₂Cube b) = fun _ ↦ c) ∨
      IsBalanced (firstBlockSlice f (singletonF₂Cube b))) :
    ∃ b c : FABL.𝔽₂,
      firstBlockSlice f (singletonF₂Cube b) = fun _ ↦ c := by
  rcases hdichotomy 0 with hzero | hzero
  · exact ⟨0, hzero⟩
  · rcases hdichotomy 1 with hone | hone
    · exact ⟨1, hone⟩
    · exact (hf (isBalanced_of_firstBlockSlices f hzero hone)).elim

/-- The product of the last two input coordinates. -/
def lastTwoCoordinateProduct (m : ℕ) : BooleanFunction (m + 2) :=
  fun x ↦ x (Fin.last m).castSucc * x (Fin.last (m + 1))

@[simp] private theorem append_singleton_last
    (x : FABL.F₂Cube m) (b : FABL.𝔽₂) :
    Fin.append x (singletonF₂Cube b) (Fin.last m) = b := by
  change Fin.append x (singletonF₂Cube b) (Fin.natAdd m 0) = b
  exact Fin.append_right x (singletonF₂Cube b) 0

@[simp] private theorem singletonF₂Cube_add
    (a b : FABL.𝔽₂) :
    singletonF₂Cube a + singletonF₂Cube b =
      singletonF₂Cube (a + b) := by
  funext i
  fin_cases i
  simp [singletonF₂Cube]

@[simp] private theorem append_singleton_castSucc
    (x : FABL.F₂Cube m) (b : FABL.𝔽₂) (i : Fin m) :
    Fin.append x (singletonF₂Cube b) i.castSucc = x i := by
  exact Fin.append_left x (singletonF₂Cube b) i

@[simp] private theorem append_singleton_castSucc_last
    (x : FABL.F₂Cube (m + 1)) (b : FABL.𝔽₂) :
    Fin.append x (singletonF₂Cube b) (Fin.last m).castSucc = x (Fin.last m) := by
  exact append_singleton_castSucc x b (Fin.last m)

@[simp] private theorem lastTwoCoordinateProduct_append_zero
    (x : FABL.F₂Cube (m + 1)) :
    lastTwoCoordinateProduct m
      (Fin.append (m := m + 1) (n := 1) x (singletonF₂Cube 0)) = 0 := by
  unfold lastTwoCoordinateProduct
  apply mul_eq_zero_of_right
  exact append_singleton_last x 0

@[simp] private theorem lastTwoCoordinateProduct_append_append
    (x : FABL.F₂Cube m) (b c : FABL.𝔽₂) :
    lastTwoCoordinateProduct m
      (Fin.append (m := m + 1) (n := 1)
        (Fin.append (m := m) (n := 1) x (singletonF₂Cube b))
        (singletonF₂Cube c)) = b * c := by
  unfold lastTwoCoordinateProduct
  rw [append_singleton_castSucc_last, append_singleton_last,
    append_singleton_last]

private theorem coordinateSwap_last_two_append_append
    (x : FABL.F₂Cube m) (b c : FABL.𝔽₂) :
    coordinateSwapLinearEquiv
        (Fin.last m).castSucc (Fin.last (m + 1))
        (Fin.append (m := m + 1) (n := 1)
          (Fin.append (m := m) (n := 1) x (singletonF₂Cube b))
          (singletonF₂Cube c)) =
      Fin.append (m := m + 1) (n := 1)
        (Fin.append (m := m) (n := 1) x (singletonF₂Cube c))
        (singletonF₂Cube b) := by
  funext t
  refine Fin.lastCases ?_ (fun q ↦ ?_) t
  · simp only [coordinateSwapLinearEquiv_apply, Equiv.swap_apply_right]
    rw [append_singleton_castSucc_last, append_singleton_last,
      append_singleton_last]
  · refine Fin.lastCases ?_ (fun r ↦ ?_) q
    · simp only [coordinateSwapLinearEquiv_apply, Equiv.swap_apply_left]
      rw [append_singleton_last, append_singleton_castSucc_last,
        append_singleton_last]
    · simp only [coordinateSwapLinearEquiv_apply]
      have hleft :
          Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))
              r.castSucc.castSucc = r.castSucc.castSucc := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          have h' : r.castSucc = Fin.last m :=
            Fin.castSucc_injective (m + 1) h
          exact Fin.castSucc_ne_last r h'
        · exact Fin.castSucc_ne_last _
      rw [hleft]
      change
        Fin.append (Fin.append x (singletonF₂Cube b)) (singletonF₂Cube c)
            r.castSucc.castSucc =
          Fin.append (Fin.append x (singletonF₂Cube c)) (singletonF₂Cube b)
            r.castSucc.castSucc
      rw [append_singleton_castSucc, append_singleton_castSucc,
        append_singleton_castSucc, append_singleton_castSucc]

private theorem eq_zero_or_eq_lastTwoCoordinateProduct
    (f : BooleanFunction (m + 2))
    (hrowZero :
      firstBlockSlice (n := m + 1) (m := 1) f (singletonF₂Cube 0) = 0)
    (hcolumnZero :
      firstBlockSlice (n := m + 1) (m := 1)
        (f ∘ coordinateSwapLinearEquiv
          (Fin.last m).castSucc (Fin.last (m + 1)))
        (singletonF₂Cube 0) = 0)
    (hrowOne :
      (∃ c : FABL.𝔽₂,
        firstBlockSlice (n := m + 1) (m := 1) f
          (singletonF₂Cube 1) = fun _ ↦ c) ∨
      IsBalanced (firstBlockSlice (n := m + 1) (m := 1) f
        (singletonF₂Cube 1))) :
    f = 0 ∨ f = lastTwoCoordinateProduct m := by
  let rowOne : BooleanFunction (m + 1) :=
    firstBlockSlice (n := m + 1) (m := 1) f (singletonF₂Cube 1)
  have hrowOneColumnZero :
      firstBlockSlice rowOne (singletonF₂Cube 0) = 0 := by
    funext x
    have hx := congrFun hcolumnZero
      (Fin.append x (singletonF₂Cube 1))
    change f
      (coordinateSwapLinearEquiv
        (Fin.last m).castSucc (Fin.last (m + 1))
        (Fin.append (Fin.append x (singletonF₂Cube 1))
          (singletonF₂Cube 0))) = 0 at hx
    change f (Fin.append (m := m + 1) (n := 1)
      (Fin.append (m := m) (n := 1) x (singletonF₂Cube 0))
      (singletonF₂Cube 1)) = 0
    rw [coordinateSwap_last_two_append_append] at hx
    exact hx
  rcases hrowOne with hconstant | hbalanced
  · left
    rcases hconstant with ⟨c, hc⟩
    have hcZero : c = 0 := by
      have hx := congrFun hrowOneColumnZero (0 : FABL.F₂Cube m)
      have hcAt := congrFun hc
        (Fin.append (0 : FABL.F₂Cube m) (singletonF₂Cube 0))
      change rowOne
        (Fin.append (0 : FABL.F₂Cube m) (singletonF₂Cube 0)) = 0 at hx
      change rowOne
        (Fin.append (0 : FABL.F₂Cube m) (singletonF₂Cube 0)) = c at hcAt
      rw [hcAt] at hx
      exact hx
    subst c
    have hrowOneZero :
        firstBlockSlice (n := m + 1) (m := 1) f
          (singletonF₂Cube 1) = 0 := by
      funext z
      exact congrFun hc z
    funext x
    have hx :
        Fin.append (Fin.init x) (singletonF₂Cube (x (Fin.last (m + 1)))) = x := by
      rw [Fin.append_right_eq_snoc]
      exact Fin.snoc_init_self x
    rw [← hx]
    by_cases hlast : x (Fin.last (m + 1)) = 0
    · rw [hlast]
      exact congrFun hrowZero (Fin.init x)
    · have hlastOne : x (Fin.last (m + 1)) = 1 :=
        Fin.eq_one_of_ne_zero _ hlast
      rw [hlastOne]
      exact congrFun hrowOneZero (Fin.init x)
  · right
    have hrowOneColumnOne :=
      firstBlockSlice_eq_complement_of_isBalanced rowOne hbalanced 0
        (by
          funext x
          exact congrFun hrowOneColumnZero x)
    funext x
    have hx :
        Fin.append (Fin.init x) (singletonF₂Cube (x (Fin.last (m + 1)))) = x := by
      rw [Fin.append_right_eq_snoc]
      exact Fin.snoc_init_self x
    rw [← hx]
    by_cases hlast : x (Fin.last (m + 1)) = 0
    · rw [hlast]
      have hvalue := congrFun hrowZero (Fin.init x)
      simp only [Pi.zero_apply] at hvalue
      change f (Fin.append (m := m + 1) (n := 1)
        (Fin.init x) (singletonF₂Cube 0)) = 0 at hvalue
      rw [hvalue]
      exact (lastTwoCoordinateProduct_append_zero (Fin.init x)).symm
    · have hlastOne : x (Fin.last (m + 1)) = 1 :=
        Fin.eq_one_of_ne_zero _ hlast
      rw [hlastOne]
      let y := Fin.init x
      have hy :
          Fin.append (Fin.init y)
              (singletonF₂Cube (y (Fin.last m))) = y := by
        rw [Fin.append_right_eq_snoc]
        exact Fin.snoc_init_self y
      change f (Fin.append (m := m + 1) (n := 1)
          y (singletonF₂Cube 1)) =
        lastTwoCoordinateProduct m
          (Fin.append (m := m + 1) (n := 1)
            y (singletonF₂Cube 1))
      rw [← hy]
      by_cases hpenultimate : y (Fin.last m) = 0
      · rw [hpenultimate]
        have hvalue := congrFun hrowOneColumnZero (Fin.init y)
        simp only [Pi.zero_apply] at hvalue
        change f (Fin.append (m := m + 1) (n := 1)
          (Fin.append (m := m) (n := 1) (Fin.init y)
            (singletonF₂Cube 0)) (singletonF₂Cube 1)) = 0 at hvalue
        rw [hvalue]
        exact (lastTwoCoordinateProduct_append_append
          (Fin.init y) 0 1).symm
      · have hpenultimateOne : y (Fin.last m) = 1 :=
          Fin.eq_one_of_ne_zero _ hpenultimate
        rw [hpenultimateOne]
        have hvalue := congrFun hrowOneColumnOne (Fin.init y)
        simp only [zero_add] at hvalue
        change f (Fin.append (m := m + 1) (n := 1)
          (Fin.append (m := m) (n := 1) (Fin.init y)
            (singletonF₂Cube 1)) (singletonF₂Cube 1)) = 1 at hvalue
        rw [hvalue]
        exact (lastTwoCoordinateProduct_append_append
          (Fin.init y) 1 1).symm

private def directionSliceShearLinearEquiv (r : ℕ) :
    FABL.F₂Cube (r + 3) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (r + 3) where
  toFun x := Fin.append
    (fun i : Fin r ↦ x (Fin.castAdd 3 i) + x (Fin.natAdd r 0))
    (fun j : Fin 3 ↦ x (Fin.natAdd r j))
  invFun x := Fin.append
    (fun i : Fin r ↦ x (Fin.castAdd 3 i) + x (Fin.natAdd r 0))
    (fun j : Fin 3 ↦ x (Fin.natAdd r j))
  left_inv x := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left, Fin.append_right]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp
  right_inv x := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left, Fin.append_right]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Pi.smul_apply, Fin.append_left]
      rw [smul_add]
      simp only [RingHom.id_apply]
    · simp

private def directionSliceCubic (r : ℕ) : BooleanFunction (r + 3) :=
  fun x ↦ x (Fin.natAdd r 0) * x (Fin.natAdd r 1) * x (Fin.natAdd r 2)

private def lastDirectionIndex (r : ℕ) : Fin (r + 4) :=
  ⟨r + 1, by omega⟩

private def precedingDirectionIndex (r : ℕ) : Fin (r + 4) :=
  ⟨r, by omega⟩

private def lastDirectionEmbedding (r : ℕ) : Fin (r + 3) ↪ Fin (r + 4) :=
  (lastDirectionIndex r).succAboveEmb.trans
    (finCongr (by omega)).toEmbedding

private def precedingDirectionEmbedding (r : ℕ) : Fin (r + 3) ↪ Fin (r + 4) :=
  (precedingDirectionIndex r).succAboveEmb.trans
    (finCongr (by omega)).toEmbedding

private def lastDirectionInsertion
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) : FABL.F₂Cube (r + 4) :=
  Fin.append
    (fun i : Fin r ↦ x (Fin.castAdd 3 i))
    ![x (Fin.natAdd r 0), 0, x (Fin.natAdd r 1), x (Fin.natAdd r 2)]

private def precedingDirectionInsertion
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) : FABL.F₂Cube (r + 4) :=
  Fin.append
    (fun i : Fin r ↦ x (Fin.castAdd 3 i))
    ![0, x (Fin.natAdd r 0), x (Fin.natAdd r 1), x (Fin.natAdd r 2)]

private theorem functionExtend_succAbove_apply
    {r : ℕ} (p : Fin (r + 1)) (x : FABL.F₂Cube r) (i : Fin r) :
    Function.extend p.succAbove x 0 (p.succAbove i) = x i := by
  exact Fin.succAbove_right_injective.extend_apply x 0 i

private theorem functionExtend_succAbove_apply_self_zero
    {r : ℕ} (p : Fin (r + 1)) (x : FABL.F₂Cube r) :
    Function.extend p.succAbove x 0 p = 0 := by
  have hnot : ¬ ∃ i, p.succAbove i = p := by
    rintro ⟨i, hi⟩
    exact Fin.succAbove_ne p i hi
  change Function.extend p.succAbove x (fun _ ↦ (0 : FABL.𝔽₂)) p = 0
  rw [Function.extend_apply' x (fun _ ↦ (0 : FABL.𝔽₂)) p hnot]

private theorem functionExtend_lastDirectionEmbedding_zero
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) :
    Function.extend (lastDirectionEmbedding r) x 0 =
      lastDirectionInsertion r x := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [lastDirectionInsertion, Fin.append_left]
    change Function.extend (lastDirectionIndex r).succAbove x 0
      (Fin.castAdd 4 j) = x (Fin.castAdd 3 j)
    rw [show Fin.castAdd 4 j =
        (lastDirectionIndex r).succAbove (Fin.castAdd 3 j) by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · change j.val < r + 1
        omega]
    exact functionExtend_succAbove_apply _ _ _
  · fin_cases j
    · simp only [lastDirectionInsertion, Fin.append_right]
      change Function.extend (lastDirectionIndex r).succAbove x 0
        (Fin.natAdd r (0 : Fin 4)) = x (Fin.natAdd r (0 : Fin 3))
      rw [show Fin.natAdd r (0 : Fin 4) =
          (lastDirectionIndex r).succAbove (Fin.natAdd r (0 : Fin 3)) by
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · change r < r + 1
          omega]
      exact functionExtend_succAbove_apply _ _ _
    · simp only [lastDirectionInsertion, Fin.append_right]
      change Function.extend (lastDirectionIndex r).succAbove x 0
        (Fin.natAdd r (1 : Fin 4)) = 0
      have hindex : Fin.natAdd r (1 : Fin 4) = lastDirectionIndex r := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact functionExtend_succAbove_apply_self_zero _ _
    · simp only [lastDirectionInsertion, Fin.append_right]
      change Function.extend (lastDirectionIndex r).succAbove x 0
        (Fin.natAdd r (2 : Fin 4)) = x (Fin.natAdd r (1 : Fin 3))
      rw [show Fin.natAdd r (2 : Fin 4) =
          (lastDirectionIndex r).succAbove (Fin.natAdd r (1 : Fin 3)) by
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change r + 1 ≤ r + 1
          omega]
      exact functionExtend_succAbove_apply _ _ _
    · simp only [lastDirectionInsertion, Fin.append_right]
      change Function.extend (lastDirectionIndex r).succAbove x 0
        (Fin.natAdd r (3 : Fin 4)) = x (Fin.natAdd r (2 : Fin 3))
      rw [show Fin.natAdd r (3 : Fin 4) =
          (lastDirectionIndex r).succAbove (Fin.natAdd r (2 : Fin 3)) by
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change r + 1 ≤ r + 2
          omega]
      exact functionExtend_succAbove_apply _ _ _

private theorem functionExtend_precedingDirectionEmbedding_zero
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) :
    Function.extend (precedingDirectionEmbedding r) x 0 =
      precedingDirectionInsertion r x := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [precedingDirectionInsertion, Fin.append_left]
    change Function.extend (precedingDirectionIndex r).succAbove x 0
      (Fin.castAdd 4 j) = x (Fin.castAdd 3 j)
    rw [show Fin.castAdd 4 j =
        (precedingDirectionIndex r).succAbove (Fin.castAdd 3 j) by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · change j.val < r
        exact j.isLt]
    exact functionExtend_succAbove_apply _ _ _
  · fin_cases j
    · simp only [precedingDirectionInsertion, Fin.append_right]
      change Function.extend (precedingDirectionIndex r).succAbove x 0
        (Fin.natAdd r (0 : Fin 4)) = 0
      have hindex : Fin.natAdd r (0 : Fin 4) = precedingDirectionIndex r := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact functionExtend_succAbove_apply_self_zero _ _
    · simp only [precedingDirectionInsertion, Fin.append_right]
      change Function.extend (precedingDirectionIndex r).succAbove x 0
        (Fin.natAdd r (1 : Fin 4)) = x (Fin.natAdd r (0 : Fin 3))
      rw [show Fin.natAdd r (1 : Fin 4) =
          (precedingDirectionIndex r).succAbove (Fin.natAdd r (0 : Fin 3)) by
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change r ≤ r
          omega]
      exact functionExtend_succAbove_apply _ _ _
    · simp only [precedingDirectionInsertion, Fin.append_right]
      change Function.extend (precedingDirectionIndex r).succAbove x 0
        (Fin.natAdd r (2 : Fin 4)) = x (Fin.natAdd r (1 : Fin 3))
      rw [show Fin.natAdd r (2 : Fin 4) =
          (precedingDirectionIndex r).succAbove (Fin.natAdd r (1 : Fin 3)) by
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change r ≤ r + 1
          omega]
      exact functionExtend_succAbove_apply _ _ _
    · simp only [precedingDirectionInsertion, Fin.append_right]
      change Function.extend (precedingDirectionIndex r).succAbove x 0
        (Fin.natAdd r (3 : Fin 4)) = x (Fin.natAdd r (2 : Fin 3))
      rw [show Fin.natAdd r (3 : Fin 4) =
          (precedingDirectionIndex r).succAbove (Fin.natAdd r (2 : Fin 3)) by
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change r ≤ r + 2
          omega]
      exact functionExtend_succAbove_apply _ _ _

/-- The standard direction supported on all but the final two coordinates. -/
def standardDirectionInsertion (r : ℕ) : FABL.F₂Cube (r + 4) :=
  Fin.append (fun _ : Fin r ↦ (1 : FABL.𝔽₂)) ![1, 1, 0, 0]

private def standardDirectionLastSlice (r : ℕ) : FABL.F₂Cube (r + 3) :=
  Fin.init (standardDirectionInsertion r)

private theorem standardDirectionInsertion_eq_append_lastSlice
    (r : ℕ) :
    standardDirectionInsertion r =
      Fin.append (standardDirectionLastSlice r) (singletonF₂Cube 0) := by
  have hreconstruct :
      Fin.append (Fin.init (standardDirectionInsertion r))
          (singletonF₂Cube
            (standardDirectionInsertion r (Fin.last (r + 3)))) =
        standardDirectionInsertion r := by
    rw [Fin.append_right_eq_snoc]
    exact Fin.snoc_init_self (standardDirectionInsertion r)
  have hlast : standardDirectionInsertion r (Fin.last (r + 3)) = 0 := by
    rw [show Fin.last (r + 3) = Fin.natAdd r (3 : Fin 4) by
      apply Fin.ext
      rfl]
    simp [standardDirectionInsertion]
  rw [hlast] at hreconstruct
  exact hreconstruct.symm

private theorem standardDirectionLastSlice_ne_zero (r : ℕ) :
    standardDirectionLastSlice r ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (Fin.natAdd r (0 : Fin 3))
  change standardDirectionInsertion r
      (Fin.natAdd r (0 : Fin 3)).castSucc = 0 at hvalue
  rw [show (Fin.natAdd r (0 : Fin 3)).castSucc =
      Fin.natAdd r (0 : Fin 4) by
    apply Fin.ext
    rfl] at hvalue
  simp [standardDirectionInsertion] at hvalue

private theorem card_f₂Support_standardDirectionInsertion (r : ℕ) :
    (FABL.f₂Support (standardDirectionInsertion r)).card = r + 2 := by
  rw [standardDirectionInsertion, card_f₂Support_append]
  have hhead :
      FABL.f₂Support (fun _ : Fin r ↦ (1 : FABL.𝔽₂)) = Finset.univ := by
    ext i
    simp [FABL.mem_f₂Support]
  have htail :
      (FABL.f₂Support (![1, 1, 0, 0] : FABL.F₂Cube 4)).card = 2 := by
    decide
  rw [hhead, Finset.card_univ, Fintype.card_fin, htail]

private theorem standardDirection_lastSlice_dichotomy
    (k : ℕ) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (b : FABL.𝔽₂) :
    (∃ c : FABL.𝔽₂,
      firstBlockSlice
          (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
          (singletonF₂Cube b) = fun _ ↦ c) ∨
      IsBalanced
        (firstBlockSlice
          (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
          (singletonF₂Cube b)) := by
  let g : BooleanFunction (2 * k + 3) :=
    firstBlockSlice f (singletonF₂Cube b)
  have hg : SatisfiesPropagationCriterion (2 * k + 1) g := by
    exact satisfiesPropagationCriterion_firstBlockSlice_of_order_one
      f (2 * k + 1) (by omega) hf b
  have hderivative :
      firstBlockSlice
          (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
          (singletonF₂Cube b) =
        FABL.booleanDerivative g (standardDirectionLastSlice (2 * k)) := by
    rw [standardDirectionInsertion_eq_append_lastSlice]
    exact firstBlockSlice_booleanDerivative_append_zero
      f (standardDirectionLastSlice (2 * k)) b
  have hdichotomy :=
    isLinearStructure_or_isBalanced_of_satisfiesPropagationCriterion_pred_two_odd
      (k + 1) (by omega)
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hdichotomy
  rcases hdichotomy g hg (standardDirectionLastSlice (2 * k))
      (standardDirectionLastSlice_ne_zero (2 * k)) with
    hlinear | hbalanced
  · left
    rcases hlinear with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hderivative]
    exact funext hc
  · right
    rw [hderivative]
    exact hbalanced

private theorem exists_constant_standardDirection_lastSlice
    (k : ℕ) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (hnotBalanced :
      ¬ IsBalanced
        (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))) :
    ∃ b c : FABL.𝔽₂,
      firstBlockSlice
          (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
          (singletonF₂Cube b) = fun _ ↦ c := by
  apply exists_constant_firstBlockSlice_of_not_isBalanced
    (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
    hnotBalanced
  exact standardDirection_lastSlice_dichotomy k f hf

private theorem coordinateSwap_last_two_standardDirectionInsertion
    (r : ℕ) :
    coordinateSwapLinearEquiv
        (Fin.last (r + 2)).castSucc (Fin.last (r + 3))
        (standardDirectionInsertion r) =
      standardDirectionInsertion r := by
  funext t
  simp only [coordinateSwapLinearEquiv_apply]
  by_cases htLeft : t = (Fin.last (r + 2)).castSucc
  · subst t
    rw [Equiv.swap_apply_left]
    rw [show Fin.last (r + 3) = Fin.natAdd r (3 : Fin 4) by
      apply Fin.ext
      rfl,
      show (Fin.last (r + 2)).castSucc = Fin.natAdd r (2 : Fin 4) by
      apply Fin.ext
      rfl]
    simp [standardDirectionInsertion]
  · by_cases htRight : t = Fin.last (r + 3)
    · subst t
      rw [Equiv.swap_apply_right]
      rw [show Fin.last (r + 3) = Fin.natAdd r (3 : Fin 4) by
        apply Fin.ext
        rfl,
        show (Fin.last (r + 2)).castSucc = Fin.natAdd r (2 : Fin 4) by
        apply Fin.ext
        rfl]
      simp [standardDirectionInsertion]
    · rw [Equiv.swap_apply_of_ne_of_ne htLeft htRight]

private theorem f₂DotProduct_smul_coordinateDirection_standardDirectionInsertion
    (k : ℕ) (hk : 1 ≤ k) (c : FABL.𝔽₂) :
    FABL.f₂DotProduct
        (c • coordinateDirection (0 : Fin (2 * k + 4)))
        (standardDirectionInsertion (2 * k)) = c := by
  by_cases hc : c = 0
  · subst c
    simp [FABL.f₂DotProduct, dotProduct]
  · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
    subst c
    simp only [one_smul]
    rw [coordinateDirection, FABL.f₂DotProduct_f₂CubeOfFinset]
    simp only [FABL.coordinateSum, Finset.sum_singleton]
    let i : Fin (2 * k) := ⟨0, by omega⟩
    have hzero : (0 : Fin (2 * k + 4)) = Fin.castAdd 4 i := by
      apply Fin.ext
      rfl
    rw [hzero]
    simp [standardDirectionInsertion]

private theorem lastDirectionInsertion_shear
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) :
    lastDirectionInsertion r (directionSliceShearLinearEquiv r x) =
      precedingDirectionInsertion r x +
        x (Fin.natAdd r 0) •
          standardDirectionInsertion r := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [lastDirectionInsertion, precedingDirectionInsertion,
      directionSliceShearLinearEquiv, standardDirectionInsertion]
  · fin_cases j <;>
      simp [lastDirectionInsertion, precedingDirectionInsertion,
        directionSliceShearLinearEquiv, standardDirectionInsertion,
        CharTwo.add_self_eq_zero]

private theorem lastTwoCoordinateProduct_precedingDirectionInsertion
    (r : ℕ) (x : FABL.F₂Cube (r + 3)) :
    lastTwoCoordinateProduct (r + 2) (precedingDirectionInsertion r x) =
      x (Fin.natAdd r 1) * x (Fin.natAdd r 2) := by
  unfold lastTwoCoordinateProduct
  rw [show (Fin.last (r + 2)).castSucc = Fin.natAdd r (2 : Fin 4) by
      apply Fin.ext
      rfl,
    show Fin.last (r + 2 + 1) = Fin.natAdd r (3 : Fin 4) by
      apply Fin.ext
      rfl]
  simp [precedingDirectionInsertion]

private theorem precedingDirectionRestriction_eq_shear_add_cubic
    (r : ℕ) (f : BooleanFunction (r + 4))
    (hderivative :
      FABL.booleanDerivative f
          (standardDirectionInsertion r) =
        lastTwoCoordinateProduct (r + 2)) :
    embeddedCoordinateRestriction f (precedingDirectionEmbedding r) 0 =
      embeddedCoordinateRestriction f (lastDirectionEmbedding r) 0 ∘
          directionSliceShearLinearEquiv r +
        directionSliceCubic r := by
  funext x
  simp only [embeddedCoordinateRestriction, Function.comp_apply, Pi.add_apply]
  rw [functionExtend_precedingDirectionEmbedding_zero,
    functionExtend_lastDirectionEmbedding_zero]
  by_cases ht : x (Fin.natAdd r 0) = 0
  · have hinsertion := lastDirectionInsertion_shear r x
    rw [ht, zero_smul, add_zero] at hinsertion
    rw [hinsertion]
    simp [directionSliceCubic, ht]
  · have htOne : x (Fin.natAdd r 0) = 1 :=
      Fin.eq_one_of_ne_zero _ ht
    have hinsertion := lastDirectionInsertion_shear r x
    rw [htOne, one_smul] at hinsertion
    have hvalue := congrFun hderivative (precedingDirectionInsertion r x)
    simp only [FABL.booleanDerivative] at hvalue
    rw [← hinsertion,
      lastTwoCoordinateProduct_precedingDirectionInsertion] at hvalue
    have hvalue' := congrArg
      (fun z : FABL.𝔽₂ ↦
        z + f (lastDirectionInsertion r
          (directionSliceShearLinearEquiv r x))) hvalue
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at hvalue'
    simpa [directionSliceCubic, htOne, add_comm] using hvalue'

private def tailTriple (r : ℕ) (x : FABL.F₂Cube (r + 3)) : FABL.F₂Cube 3 :=
  fun j ↦ x (Fin.natAdd r j)

private def threeCoordinateProduct : BooleanFunction 3 :=
  fun x ↦ x 0 * x 1 * x 2

private theorem hammingWeight_tailTripleLift
    (r : ℕ) (g : BooleanFunction 3) :
    hammingWeight (fun x : FABL.F₂Cube (r + 3) ↦ g (tailTriple r x)) =
      2 ^ r * hammingWeight g := by
  classical
  change hammingNorm (fun x : FABL.F₂Cube (r + 3) ↦ g (tailTriple r x)) =
    2 ^ r * hammingNorm g
  rw [hammingNorm_eq_sum_f₂BitWeight]
  calc
    ∑ x : FABL.F₂Cube (r + 3), f₂BitWeight (g (tailTriple r x)) =
        ∑ p : FABL.F₂Cube r × FABL.F₂Cube 3,
          f₂BitWeight (g p.2) := by
      exact (Fintype.sum_equiv (Fin.appendEquiv r 3)
        (fun p : FABL.F₂Cube r × FABL.F₂Cube 3 ↦ f₂BitWeight (g p.2))
        (fun x : FABL.F₂Cube (r + 3) ↦
          f₂BitWeight (g (tailTriple r x)))
        (fun p ↦ by
          congr 2
          funext j
          simp [tailTriple])).symm
    _ = ∑ a : FABL.F₂Cube r, ∑ b : FABL.F₂Cube 3,
          f₂BitWeight (g b) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ _a : FABL.F₂Cube r, hammingNorm g := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hammingNorm_eq_sum_f₂BitWeight]
    _ = 2 ^ r * hammingNorm g := by
      simp [Finset.sum_const]

private theorem hammingWeight_booleanDerivative_threeCoordinateProduct
    (v : FABL.F₂Cube 3) (hv : v ≠ 0) :
    hammingWeight (FABL.booleanDerivative threeCoordinateProduct v) = 2 := by
  revert v
  decide

private theorem booleanDerivative_directionSliceCubic_eq_tailTripleLift
    (r : ℕ) (v : FABL.F₂Cube (r + 3)) :
    FABL.booleanDerivative (directionSliceCubic r) v =
      fun x ↦ FABL.booleanDerivative threeCoordinateProduct (tailTriple r v)
        (tailTriple r x) := by
  funext x
  rfl

private theorem hammingWeight_booleanDerivative_directionSliceCubic
    (r : ℕ) (v : FABL.F₂Cube (r + 3))
    (hv : tailTriple r v ≠ 0) :
    hammingWeight (FABL.booleanDerivative (directionSliceCubic r) v) =
      2 ^ (r + 1) := by
  rw [booleanDerivative_directionSliceCubic_eq_tailTripleLift,
    hammingWeight_tailTripleLift,
    hammingWeight_booleanDerivative_threeCoordinateProduct _ hv]
  omega

private theorem card_f₂Support_le_of_tailTriple_eq_zero
    (r : ℕ) (v : FABL.F₂Cube (r + 3)) (hv : tailTriple r v = 0) :
    (FABL.f₂Support v).card ≤ r := by
  let head : FABL.F₂Cube r := fun i ↦ v (Fin.castAdd 3 i)
  have hreconstruct : Fin.append head (tailTriple r v) = v := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [head]
    · simp [tailTriple]
  rw [← hreconstruct, hv, card_f₂Support_append]
  have hzero : FABL.f₂Support (0 : FABL.F₂Cube 3) = ∅ := by
    ext i
    simp [FABL.mem_f₂Support]
  rw [hzero, Finset.card_empty, add_zero]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq
    (Finset.card_univ.trans (Fintype.card_fin r))

private theorem hammingWeight_const_zero
    (n : ℕ) :
    hammingWeight (fun _ : FABL.F₂Cube n ↦ (0 : FABL.𝔽₂)) = 0 := by
  exact hammingNorm_zero

private theorem hammingWeight_const_one
    (n : ℕ) :
    hammingWeight (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂)) = 2 ^ n := by
  rw [hammingWeight_eq_card_support]
  have hsupport :
      support (fun _ : FABL.F₂Cube n ↦ (1 : FABL.𝔽₂)) = Finset.univ := by
    ext x
    simp [mem_support]
  rw [hsupport, Finset.card_univ, card_f₂Cube]

/-- The nonzero quadratic derivative branch is impossible at extremal
order one. -/
theorem false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_product
    (k : ℕ) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (hderivative :
      FABL.booleanDerivative f (standardDirectionInsertion (2 * k)) =
        lastTwoCoordinateProduct (2 * k + 2)) :
    False := by
  let g : BooleanFunction (2 * k + 3) :=
    embeddedCoordinateRestriction f (lastDirectionEmbedding (2 * k)) 0
  let h : BooleanFunction (2 * k + 3) :=
    embeddedCoordinateRestriction f (precedingDirectionEmbedding (2 * k)) 0
  have hg : SatisfiesPropagationCriterion (2 * k + 1) g := by
    exact satisfiesPropagationCriterion_embeddedCoordinateRestriction_of_order
      f hf (by omega) (lastDirectionEmbedding (2 * k)) 0
  have hh : SatisfiesPropagationCriterion (2 * k + 1) h := by
    exact satisfiesPropagationCriterion_embeddedCoordinateRestriction_of_order
      f hf (by omega) (precedingDirectionEmbedding (2 * k)) 0
  have hrelation :
      h = g ∘ directionSliceShearLinearEquiv (2 * k) +
        directionSliceCubic (2 * k) := by
    simpa only [g, h] using
      precedingDirectionRestriction_eq_shear_add_cubic (2 * k) f hderivative
  have hgcharacterization :=
    satisfiesPropagationCriterion_pred_two_iff_hasUniqueHighWeightLinearStructure
      (k + 1) (by omega)
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hgcharacterization
  rcases (hgcharacterization g).mp hg with
    ⟨b, hbne, hbweight, hblinear, _⟩
  let L := directionSliceShearLinearEquiv (2 * k)
  let v : FABL.F₂Cube (2 * k + 3) := L.symm b
  have hvTail : tailTriple (2 * k) v ≠ 0 := by
    have htail : tailTriple (2 * k) v = tailTriple (2 * k) b := by
      funext j
      simp [v, L, directionSliceShearLinearEquiv, tailTriple]
    rw [htail]
    intro hzero
    have hupper := card_f₂Support_le_of_tailTriple_eq_zero (2 * k) b hzero
    omega
  have hvne : v ≠ 0 := by
    intro hvzero
    apply hvTail
    rw [hvzero]
    funext j
    rfl
  rcases hblinear with ⟨ε, hε⟩
  have hLv : L v = b := by
    simp [v, L]
  have hcompDerivative :
      FABL.booleanDerivative (g ∘ L) v = fun _ ↦ ε := by
    funext x
    simp only [FABL.booleanDerivative, Function.comp_apply, map_add]
    rw [hLv]
    exact hε (L x)
  have hderivativeRelation :
      FABL.booleanDerivative h v =
        (fun _ ↦ ε) +
          FABL.booleanDerivative (directionSliceCubic (2 * k)) v := by
    rw [hrelation, booleanDerivative_add, hcompDerivative]
  have hcubicWeight :
      hammingWeight
          (FABL.booleanDerivative (directionSliceCubic (2 * k)) v) =
        2 ^ (2 * k + 1) :=
    hammingWeight_booleanDerivative_directionSliceCubic (2 * k) v hvTail
  have hderivativeWeight :
      hammingWeight (FABL.booleanDerivative h v) = 2 ^ (2 * k + 1) ∨
        hammingWeight (FABL.booleanDerivative h v) =
          2 ^ (2 * k + 3) - 2 ^ (2 * k + 1) := by
    by_cases hεzero : ε = 0
    · left
      subst ε
      rw [hderivativeRelation]
      have hzeroAdd :
          (fun _ : FABL.F₂Cube (2 * k + 3) ↦ (0 : FABL.𝔽₂)) +
              FABL.booleanDerivative (directionSliceCubic (2 * k)) v =
            FABL.booleanDerivative (directionSliceCubic (2 * k)) v := by
        funext x
        simp
      rw [hzeroAdd]
      exact hcubicWeight
    · right
      have hεone : ε = 1 := Fin.eq_one_of_ne_zero _ hεzero
      subst ε
      rw [hderivativeRelation]
      have hfunction :
          (fun _ : FABL.F₂Cube (2 * k + 3) ↦ (1 : FABL.𝔽₂)) +
              FABL.booleanDerivative (directionSliceCubic (2 * k)) v =
            FABL.booleanDerivative (directionSliceCubic (2 * k)) v +
              FABL.affineFunction 1 0 := by
        funext x
        simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct, add_comm]
      rw [hfunction, hammingWeight_add_constant_one, hcubicWeight]
  have hpositive : 0 < 2 ^ (2 * k + 1) := by positivity
  have hfull : 2 ^ (2 * k + 3) = 4 * 2 ^ (2 * k + 1) := by
    rw [show 2 * k + 3 = (2 * k + 1) + 2 by omega, pow_add]
    norm_num [mul_comm]
  have hhcharacterization :=
    isLinearStructure_or_isBalanced_of_satisfiesPropagationCriterion_pred_two_odd
      (k + 1) (by omega)
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hhcharacterization
  rcases hhcharacterization h hh v hvne with
    hlinear | hbalanced
  · rcases hlinear with ⟨δ, hδ⟩
    have hconstant :
        FABL.booleanDerivative h v = fun _ ↦ δ := funext hδ
    by_cases hδzero : δ = 0
    · subst δ
      have hweightZero :
          hammingWeight (FABL.booleanDerivative h v) = 0 := by
        rw [hconstant]
        exact hammingWeight_const_zero _
      rw [hweightZero] at hderivativeWeight
      omega
    · have hδone : δ = 1 := Fin.eq_one_of_ne_zero δ hδzero
      subst δ
      have hweightOne :
          hammingWeight (FABL.booleanDerivative h v) = 2 ^ (2 * k + 3) := by
        rw [hconstant]
        exact hammingWeight_const_one _
      rw [hweightOne, hfull] at hderivativeWeight
      omega
  · rw [IsBalanced] at hbalanced
    rw [hfull] at hbalanced
    rcases hderivativeWeight with hweight | hweight <;>
      rw [hweight] at hbalanced <;> omega

private theorem exists_extremalDerivative_normalForm
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (hnotBalanced :
      ¬ IsBalanced
        (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))) :
    ∃ g : BooleanFunction (2 * k + 4),
      SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 g ∧
        (FABL.booleanDerivative g (standardDirectionInsertion (2 * k)) = 0 ∨
          FABL.booleanDerivative g (standardDirectionInsertion (2 * k)) =
            lastTwoCoordinateProduct (2 * k + 2)) := by
  obtain ⟨bLast, cRow, hRow⟩ :=
    exists_constant_standardDirection_lastSlice k f hf hnotBalanced
  let swapped : BooleanFunction (2 * k + 4) :=
    f ∘ coordinateSwapLinearEquiv
      (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))
  have hswapped :
      SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 swapped := by
    exact
      (satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv_iff
        f (2 * k + 1) 1 (by omega)
        (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))).2 hf
  have hswappedDerivative :
      FABL.booleanDerivative swapped (standardDirectionInsertion (2 * k)) =
        FABL.booleanDerivative f (standardDirectionInsertion (2 * k)) ∘
          coordinateSwapLinearEquiv
            (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3)) := by
    dsimp only [swapped]
    rw [booleanDerivative_comp_coordinateSwapLinearEquiv,
      coordinateSwap_last_two_standardDirectionInsertion]
  have hswappedNotBalanced :
      ¬ IsBalanced
        (FABL.booleanDerivative swapped
          (standardDirectionInsertion (2 * k))) := by
    intro hbalanced
    rw [hswappedDerivative] at hbalanced
    apply hnotBalanced
    exact
      (isBalanced_comp_coordinateSwapLinearEquiv_iff
        (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))
        (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))).1 hbalanced
  obtain ⟨bPenultimate, cColumn, hColumn⟩ :=
    exists_constant_standardDirection_lastSlice
      k swapped hswapped hswappedNotBalanced
  rw [hswappedDerivative] at hColumn
  have hc : cColumn = cRow := by
    have hrowValue := congrFun hRow
      (Fin.append (m := 2 * k + 2) (n := 1)
        (0 : FABL.F₂Cube (2 * k + 2))
        (singletonF₂Cube bPenultimate))
    have hcolumnValue := congrFun hColumn
      (Fin.append (m := 2 * k + 2) (n := 1)
        (0 : FABL.F₂Cube (2 * k + 2))
        (singletonF₂Cube bLast))
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (Fin.append (m := 2 * k + 3) (n := 1)
        (Fin.append (m := 2 * k + 2) (n := 1)
          (0 : FABL.F₂Cube (2 * k + 2))
          (singletonF₂Cube bPenultimate))
        (singletonF₂Cube bLast)) = cRow at hrowValue
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (coordinateSwapLinearEquiv
        (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))
        (Fin.append (m := 2 * k + 3) (n := 1)
          (Fin.append (m := 2 * k + 2) (n := 1)
            (0 : FABL.F₂Cube (2 * k + 2))
            (singletonF₂Cube bLast))
          (singletonF₂Cube bPenultimate))) = cColumn at hcolumnValue
    rw [coordinateSwap_last_two_append_append] at hcolumnValue
    exact hcolumnValue.symm.trans hrowValue
  subst cColumn
  let z : FABL.F₂Cube (2 * k + 4) :=
    Fin.append (m := 2 * k + 3) (n := 1)
      (Fin.append (m := 2 * k + 2) (n := 1)
        (0 : FABL.F₂Cube (2 * k + 2))
        (singletonF₂Cube bPenultimate))
      (singletonF₂Cube bLast)
  let u : FABL.F₂Cube (2 * k + 4) :=
    cRow • coordinateDirection (0 : Fin (2 * k + 4))
  let g : BooleanFunction (2 * k + 4) :=
    FABL.domainTranslate f z + FABL.affineFunction 0 u
  have hg : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 g := by
    have htranslated :=
      (satisfiesPropagationCriterionOfOrder_domainTranslate_iff
        (2 * k + 1) 1 f z (by omega)).2 hf
    exact
      (satisfiesPropagationCriterionOfOrder_add_affineFunction_iff
        (2 * k + 1) 1 (FABL.domainTranslate f z) 0 u (by omega)).2
        htranslated
  have hgDerivative :
      FABL.booleanDerivative g (standardDirectionInsertion (2 * k)) =
        fun x ↦
          FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
              (x + z) + cRow := by
    change FABL.booleanDerivative
        (fun x ↦ FABL.domainTranslate f z x + FABL.affineFunction 0 u x)
        (standardDirectionInsertion (2 * k)) = _
    rw [booleanDerivative_add_affineFunction,
      f₂DotProduct_smul_coordinateDirection_standardDirectionInsertion
        k hk cRow,
      booleanDerivative_domainTranslate]
    rfl
  have hrowZero :
      firstBlockSlice (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative g (standardDirectionInsertion (2 * k)))
          (singletonF₂Cube 0) = 0 := by
    funext x
    have hvalue := congrFun hRow
      (x + Fin.append (m := 2 * k + 2) (n := 1)
        (0 : FABL.F₂Cube (2 * k + 2))
        (singletonF₂Cube bPenultimate))
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (Fin.append (m := 2 * k + 3) (n := 1)
        (x + Fin.append (m := 2 * k + 2) (n := 1)
          (0 : FABL.F₂Cube (2 * k + 2))
          (singletonF₂Cube bPenultimate))
        (singletonF₂Cube bLast)) = cRow at hvalue
    rw [hgDerivative]
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (Fin.append (m := 2 * k + 3) (n := 1)
        x (singletonF₂Cube 0) + z) + cRow = 0
    have hargument :
        Fin.append (m := 2 * k + 3) (n := 1)
            x (singletonF₂Cube 0) + z =
          Fin.append (m := 2 * k + 3) (n := 1)
            (x + Fin.append (m := 2 * k + 2) (n := 1)
              (0 : FABL.F₂Cube (2 * k + 2))
              (singletonF₂Cube bPenultimate))
            (singletonF₂Cube bLast) := by
      dsimp only [z]
      rw [← finAppend_add]
      simp
    rw [hargument, hvalue, CharTwo.add_self_eq_zero]
  have hcolumnZero :
      firstBlockSlice (n := 2 * k + 3) (m := 1)
          (FABL.booleanDerivative g (standardDirectionInsertion (2 * k)) ∘
            coordinateSwapLinearEquiv
              (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3)))
          (singletonF₂Cube 0) = 0 := by
    funext x
    have hvalue := congrFun hColumn
      (Fin.append (m := 2 * k + 2) (n := 1) (Fin.init x)
        (singletonF₂Cube
          (x (Fin.last (2 * k + 2)) + bLast)))
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (coordinateSwapLinearEquiv
        (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))
        (Fin.append (m := 2 * k + 3) (n := 1)
          (Fin.append (m := 2 * k + 2) (n := 1) (Fin.init x)
            (singletonF₂Cube
              (x (Fin.last (2 * k + 2)) + bLast)))
          (singletonF₂Cube bPenultimate))) = cRow at hvalue
    rw [coordinateSwap_last_two_append_append] at hvalue
    simp only [hgDerivative]
    change FABL.booleanDerivative f (standardDirectionInsertion (2 * k))
      (coordinateSwapLinearEquiv
          (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))
          (Fin.append (m := 2 * k + 3) (n := 1)
            x (singletonF₂Cube 0)) + z) + cRow = 0
    have hx :
        Fin.append (m := 2 * k + 2) (n := 1) (Fin.init x)
            (singletonF₂Cube (x (Fin.last (2 * k + 2)))) = x := by
      rw [Fin.append_right_eq_snoc]
      exact Fin.snoc_init_self x
    have hargument :
        coordinateSwapLinearEquiv
            (Fin.last (2 * k + 2)).castSucc (Fin.last (2 * k + 3))
            (Fin.append (m := 2 * k + 3) (n := 1)
              x (singletonF₂Cube 0)) + z =
          Fin.append (m := 2 * k + 3) (n := 1)
            (Fin.append (m := 2 * k + 2) (n := 1)
              (Fin.init x) (singletonF₂Cube bPenultimate))
            (singletonF₂Cube
              (x (Fin.last (2 * k + 2)) + bLast)) := by
      rw [← hx, coordinateSwap_last_two_append_append]
      dsimp only [z]
      rw [← finAppend_add, ← finAppend_add]
      simp only [add_zero, singletonF₂Cube_add, zero_add,
        append_singleton_last]
      congr 2
      funext i
      change Fin.init x i =
        Fin.append (Fin.init x)
          (singletonF₂Cube (x (Fin.last (2 * k + 2)))) i.castSucc
      exact (Fin.append_left (Fin.init x)
        (singletonF₂Cube (x (Fin.last (2 * k + 2)))) i).symm
    rw [hargument, hvalue, CharTwo.add_self_eq_zero]
  have hrowOne := standardDirection_lastSlice_dichotomy k g hg 1
  refine ⟨g, hg, ?_⟩
  exact eq_zero_or_eq_lastTwoCoordinateProduct
    (FABL.booleanDerivative g (standardDirectionInsertion (2 * k)))
    hrowZero hcolumnZero hrowOne

private theorem false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_zero
    (k : ℕ) (hk : 2 ≤ k) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (hderivative :
      FABL.booleanDerivative f (standardDirectionInsertion (2 * k)) = 0) :
    False := by
  let e : Fin (2 * (k + 1) + 2) ≃ Fin (2 * k + 4) := finCongr (by omega)
  let g : BooleanFunction (2 * (k + 1) + 2) :=
    f ∘ cubeReindexLinearEquiv e
  have hdirection :
      cubeReindexLinearEquiv e (standardPredThreeDirection (k + 1)) =
        standardDirectionInsertion (2 * k) := by
    funext i
    change standardPredThreeDirection (k + 1) (e.symm i) =
      standardDirectionInsertion (2 * k) i
    by_cases hi : i.val < 2 * k
    · let j : Fin (2 * k) := ⟨i, hi⟩
      let j' : Fin (2 * (k + 1)) := ⟨i, by omega⟩
      have hleft : e.symm i = Fin.castAdd 2 j' := by
        apply Fin.ext
        rfl
      have hright : i = Fin.castAdd 4 j := by
        apply Fin.ext
        rfl
      rw [hleft, hright]
      simp [standardPredThreeDirection, standardDirectionInsertion]
    · have htail : 2 * k ≤ i.val := by omega
      have hcases :
          i.val = 2 * k ∨ i.val = 2 * k + 1 ∨
            i.val = 2 * k + 2 ∨ i.val = 2 * k + 3 := by
        omega
      rcases hcases with hi0 | hi1 | hi2 | hi3
      · let q : Fin (2 * (k + 1)) := ⟨2 * k, by omega⟩
        have hleft : e.symm i = Fin.castAdd 2 q := by
          apply Fin.ext
          exact hi0
        have hright : i = Fin.natAdd (2 * k) (0 : Fin 4) := by
          apply Fin.ext
          exact hi0
        rw [hleft, hright]
        simp [standardPredThreeDirection, standardDirectionInsertion,
          fullDirection]
      · let q : Fin (2 * (k + 1)) := ⟨2 * k + 1, by omega⟩
        have hleft : e.symm i = Fin.castAdd 2 q := by
          apply Fin.ext
          exact hi1
        have hright : i = Fin.natAdd (2 * k) (1 : Fin 4) := by
          apply Fin.ext
          exact hi1
        rw [hleft, hright]
        simp [standardPredThreeDirection, standardDirectionInsertion,
          fullDirection]
      · have hleft : e.symm i =
            Fin.natAdd (2 * (k + 1)) (0 : Fin 2) := by
          apply Fin.ext
          exact hi2
        have hright : i = Fin.natAdd (2 * k) (2 : Fin 4) := by
          apply Fin.ext
          exact hi2
        rw [hleft, hright]
        simp [standardPredThreeDirection, standardDirectionInsertion]
      · have hleft : e.symm i =
            Fin.natAdd (2 * (k + 1)) (1 : Fin 2) := by
          apply Fin.ext
          exact hi3
        have hright : i = Fin.natAdd (2 * k) (3 : Fin 4) := by
          apply Fin.ext
          exact hi3
        rw [hleft, hright]
        simp [standardPredThreeDirection, standardDirectionInsertion]
  have hg :
      SatisfiesPropagationCriterionOfOrder (2 * (k + 1) - 1) 1 g := by
    apply
      (satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv_iff
        f e (by omega)).2
    simpa only [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] using hf
  have hgDerivative :
      FABL.booleanDerivative g (standardPredThreeDirection (k + 1)) = 0 := by
    dsimp only [g]
    rw [booleanDerivative_comp_cubeReindexLinearEquiv, hdirection,
      hderivative]
    funext x
    rfl
  exact
    false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_linearStructure
      (k + 1) (by omega) g hg hgDerivative

private theorem
    false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_notBalanced
    (k : ℕ) (hk : 2 ≤ k) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f)
    (hnotBalanced :
      ¬ IsBalanced
        (FABL.booleanDerivative f (standardDirectionInsertion (2 * k)))) :
    False := by
  obtain ⟨g, hg, hzero | hproduct⟩ :=
    exists_extremalDerivative_normalForm k (by omega) f hf hnotBalanced
  · exact
      false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_zero
        k hk g hg hzero
  · exact
      false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_product
        k g hg hproduct

private theorem isBent_of_satisfiesPropagationCriterionOfOrder_pred_three_two_mul_add_four
    (k : ℕ) (hk : 2 ≤ k) (f : BooleanFunction (2 * k + 4))
    (hf : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 f) :
    IsBent f := by
  classical
  by_contra hnotBent
  have hnotPC : ¬ SatisfiesPropagationCriterion (2 * k + 2) f := by
    intro hpc
    apply hnotBent
    exact isBent_of_satisfiesPropagationCriterion_pred_two_of_even
      f (by omega) ⟨k + 2, by omega⟩ (by simpa using hpc)
  simp only [SatisfiesPropagationCriterion,
    SatisfiesPropagationCriterionOn, lowWeightNonzeroDirections,
    Set.mem_setOf_eq] at hnotPC
  push Not at hnotPC
  obtain ⟨a, ⟨ha0, haweight⟩, haNotBalanced⟩ := hnotPC
  have hzero :=
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      (2 * k + 1) 1 f (by omega)).mp hf
  have hlowBalanced :
      ∀ v : FABL.F₂Cube (2 * k + 4), v ≠ 0 →
        (FABL.f₂Support v).card ≤ 2 * k + 1 →
          IsBalanced (FABL.booleanDerivative f v) := by
    intro v hv0 hvweight
    apply (isBalanced_iff_walshTransform_zero_eq_zero _).2
    have hzeroSupport :
        FABL.f₂Support (0 : FABL.F₂Cube (2 * k + 4)) = ∅ := by
      ext i
      simp [FABL.mem_f₂Support]
    apply hzero v 0 hvweight
    · rw [hzeroSupport]
      simp
    · intro hpair
      apply hv0
      simpa using congrArg Prod.fst hpair
    · rw [hzeroSupport]
      exact Finset.disjoint_empty_right _
  have hacard : (FABL.f₂Support a).card = 2 * k + 2 := by
    have hnotLow : ¬ (FABL.f₂Support a).card ≤ 2 * k + 1 := by
      intro hlow
      exact haNotBalanced (hlowBalanced a ha0 hlow)
    omega
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq
    (FABL.f₂Support (standardDirectionInsertion (2 * k)))
    (FABL.f₂Support a)
    (by rw [card_f₂Support_standardDirectionInsertion, hacard])
  have hdirection :
      cubeReindexLinearEquiv σ (standardDirectionInsertion (2 * k)) = a := by
    apply (FABL.f₂CubeEquivFinset (2 * k + 4)).injective
    rw [FABL.f₂CubeEquivFinset_apply, FABL.f₂CubeEquivFinset_apply,
      f₂Support_cubeReindexLinearEquiv]
    exact hσ
  let g : BooleanFunction (2 * k + 4) := f ∘ cubeReindexLinearEquiv σ
  have hg : SatisfiesPropagationCriterionOfOrder (2 * k + 1) 1 g := by
    exact
      (satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv_iff
        f σ (by omega)).2 hf
  have hgDerivative :
      FABL.booleanDerivative g (standardDirectionInsertion (2 * k)) =
        FABL.booleanDerivative f a ∘ cubeReindexLinearEquiv σ := by
    dsimp only [g]
    rw [booleanDerivative_comp_cubeReindexLinearEquiv, hdirection]
  have hgNotBalanced :
      ¬ IsBalanced
        (FABL.booleanDerivative g (standardDirectionInsertion (2 * k))) := by
    intro hbalanced
    rw [hgDerivative] at hbalanced
    apply haNotBalanced
    exact
      (isBalanced_comp_cubeReindexLinearEquiv_iff
        (FABL.booleanDerivative f a) σ).1 hbalanced
  exact
    false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_notBalanced
      k hk g hg hgNotBalanced

/-- Carlet Proposition 4: in even dimension at least eight, `PC(n-3)` of
order one forces bentness. -/
theorem isBent_of_satisfiesPropagationCriterionOfOrder_pred_three_of_even
    (f : BooleanFunction n) (hn : 8 ≤ n) (heven : Even n)
    (hf : SatisfiesPropagationCriterionOfOrder (n - 3) 1 f) :
    IsBent f := by
  obtain ⟨t, ht⟩ := heven
  have hnEq : n = 2 * t := by omega
  subst n
  have htLower : 4 ≤ t := by omega
  let e : Fin (2 * (t - 2) + 4) ≃ Fin (t + t) := finCongr (by omega)
  let g : BooleanFunction (2 * (t - 2) + 4) :=
    f ∘ cubeReindexLinearEquiv e
  have hg :
      SatisfiesPropagationCriterionOfOrder (2 * (t - 2) + 1) 1 g := by
    apply
      (satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv_iff
        f e (by omega)).2
    simpa only [show 2 * (t - 2) + 1 = t + t - 3 by omega] using hf
  have hgBent : IsBent g :=
    isBent_of_satisfiesPropagationCriterionOfOrder_pred_three_two_mul_add_four
      (t - 2) (by omega) g hg
  exact
    (isBent_comp_cubeReindexLinearEquiv_iff
      (by omega) f e).1 hgBent

end CryptBoolean
