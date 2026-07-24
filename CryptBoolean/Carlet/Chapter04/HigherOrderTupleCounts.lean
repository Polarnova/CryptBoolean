/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwo
public import FABL.Chapter06.F₂Polynomials.Interpolation

/-!
# Exact tuple counts for the second-order moment argument

The two-point recurrence and the instances of Carlet--Mesnager Corollary 9.2.8
needed for the consecutive seventh and eighth moments.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m l k : ℕ}

private theorem tuplePointParity_append
    (x : Fin m → FABL.F₂Cube n) (y : Fin l → FABL.F₂Cube n) :
    tuplePointParity (Fin.append x y) =
      tuplePointParity x + tuplePointParity y := by
  classical
  funext z
  simp only [tuplePointParity, Pi.add_apply]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem tuplePointParity_pair
    (a b : FABL.F₂Cube n) :
    tuplePointParity ![a, b] =
      FABL.f₂PointIndicator a + FABL.f₂PointIndicator b := by
  classical
  funext z
  simp only [tuplePointParity, Pi.add_apply, Fin.sum_univ_two]
  simp [FABL.f₂PointIndicator_eq_ite, eq_comm]

private theorem tuplePointParity_append_pair
    (x : Fin (2 * k) → FABL.F₂Cube n) (a b : FABL.F₂Cube n) :
    tuplePointParity (Fin.append x ![a, b]) =
      tuplePointParity x + FABL.f₂PointIndicator a +
        FABL.f₂PointIndicator b := by
  rw [tuplePointParity_append, tuplePointParity_pair]
  ac_rfl

private theorem tuplePointParity_append_pair_eq_iff
    (x : Fin (2 * k) → FABL.F₂Cube n) (a b : FABL.F₂Cube n)
    (h : BooleanFunction n) :
    tuplePointParity (Fin.append x ![a, b]) = h ↔
      tuplePointParity x =
        h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b := by
  rw [tuplePointParity_append_pair]
  constructor
  · intro heq
    rw [← heq]
    funext z
    simp only [Pi.add_apply]
    calc
      tuplePointParity x z = tuplePointParity x z +
          (FABL.f₂PointIndicator a z + FABL.f₂PointIndicator a z) +
          (FABL.f₂PointIndicator b z + FABL.f₂PointIndicator b z) := by
        rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero,
          add_zero]
      _ = tuplePointParity x z + FABL.f₂PointIndicator a z +
          FABL.f₂PointIndicator b z + FABL.f₂PointIndicator a z +
          FABL.f₂PointIndicator b z := by abel
  · intro heq
    rw [heq]
    funext z
    simp only [Pi.add_apply]
    calc
      h z + FABL.f₂PointIndicator a z + FABL.f₂PointIndicator b z +
          FABL.f₂PointIndicator a z + FABL.f₂PointIndicator b z =
          h z +
            (FABL.f₂PointIndicator a z + FABL.f₂PointIndicator a z) +
            (FABL.f₂PointIndicator b z + FABL.f₂PointIndicator b z) := by abel
      _ = h z := by
        rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero,
          add_zero]

private theorem tuplePointParityMultiplicity_eq_sum_indicator
    (k : ℕ) (h : BooleanFunction n) :
    tuplePointParityMultiplicity k h =
      ∑ x : Fin (2 * k) → FABL.F₂Cube n,
        if tuplePointParity x = h then 1 else 0 := by
  classical
  simp [tuplePointParityMultiplicity, tuplePointParityFiber]

/-- Appending two entries expresses a point-parity fiber as the sum of the
fibers obtained by toggling the two selected points. -/
theorem tuplePointParityMultiplicity_succ
    (k : ℕ) (h : BooleanFunction n) :
    tuplePointParityMultiplicity (k + 1) h =
      ∑ a : FABL.F₂Cube n, ∑ b : FABL.F₂Cube n,
        tuplePointParityMultiplicity k
          (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) := by
  classical
  rw [tuplePointParityMultiplicity_eq_sum_indicator]
  calc
    (∑ z : Fin (2 * k + 2) → FABL.F₂Cube n,
        if tuplePointParity z = h then 1 else 0) =
        ∑ p : (Fin (2 * k) → FABL.F₂Cube n) ×
            (Fin 2 → FABL.F₂Cube n),
          if tuplePointParity (Fin.append p.1 p.2) = h then 1 else 0 := by
      exact (Fintype.sum_equiv (Fin.appendEquiv (2 * k) 2)
        (fun p ↦ if tuplePointParity (Fin.append p.1 p.2) = h then 1 else 0)
        (fun z ↦ if tuplePointParity z = h then 1 else 0)
        (fun _ ↦ rfl)).symm
    _ = ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          ∑ y : Fin 2 → FABL.F₂Cube n,
            if tuplePointParity (Fin.append x y) = h then 1 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          ∑ a : FABL.F₂Cube n, ∑ b : FABL.F₂Cube n,
            if tuplePointParity (Fin.append x ![a, b]) = h then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      calc
        (∑ y : Fin 2 → FABL.F₂Cube n,
            if tuplePointParity (Fin.append x y) = h then 1 else 0) =
            ∑ p : FABL.F₂Cube n × FABL.F₂Cube n,
              if tuplePointParity (Fin.append x ![p.1, p.2]) = h then 1 else 0 := by
          exact Fintype.sum_equiv (finTwoArrowEquiv (FABL.F₂Cube n))
            (fun y ↦ if tuplePointParity (Fin.append x y) = h then 1 else 0)
            (fun p ↦ if tuplePointParity (Fin.append x ![p.1, p.2]) = h then 1 else 0)
            (fun y ↦ by
              have hy :
                  ![((finTwoArrowEquiv (FABL.F₂Cube n)) y).1,
                    ((finTwoArrowEquiv (FABL.F₂Cube n)) y).2] = y := by
                simpa only [finTwoArrowEquiv_symm_apply] using
                  (finTwoArrowEquiv (FABL.F₂Cube n)).symm_apply_apply y
              rw [hy])
        _ = _ := by rw [Fintype.sum_prod_type]
    _ = ∑ a : FABL.F₂Cube n, ∑ b : FABL.F₂Cube n,
          ∑ x : Fin (2 * k) → FABL.F₂Cube n,
            if tuplePointParity x =
                h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b
              then 1 else 0 := by
      simp_rw [tuplePointParity_append_pair_eq_iff]
      rw [Finset.sum_comm]
      congr 1
      funext a
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [← tuplePointParityMultiplicity_eq_sum_indicator]

private theorem support_add_pointIndicator_of_eq_zero
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 0) :
    support (h + FABL.f₂PointIndicator a) = insert a (support h) := by
  classical
  ext x
  by_cases hxa : x = a
  · subst x
    simp [mem_support, FABL.f₂PointIndicator_eq_ite, ha]
  · rw [mem_support, Pi.add_apply, FABL.f₂PointIndicator_eq_ite,
      if_neg hxa, add_zero, mem_insert]
    constructor
    · intro hx
      exact Or.inr ((mem_support h x).2 hx)
    · rintro (hxa' | hx)
      · exact (hxa hxa').elim
      · exact (mem_support h x).1 hx

private theorem support_add_pointIndicator_of_eq_one
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 1) :
    support (h + FABL.f₂PointIndicator a) = (support h).erase a := by
  classical
  ext x
  by_cases hxa : x = a
  · subst x
    simp [mem_support, FABL.f₂PointIndicator_eq_ite, ha]
  · rw [mem_support, Pi.add_apply, FABL.f₂PointIndicator_eq_ite,
      if_neg hxa, add_zero, Finset.mem_erase]
    constructor
    · intro hx
      exact ⟨hxa, (mem_support h x).2 hx⟩
    · intro hx
      exact (mem_support h x).1 hx.2

private theorem hammingWeight_add_pointIndicator_eq_add_one_of_eq_zero
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 0) :
    hammingWeight (h + FABL.f₂PointIndicator a) = hammingWeight h + 1 := by
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support,
    support_add_pointIndicator_of_eq_zero h a ha]
  rw [Finset.card_insert_of_notMem]
  intro hmem
  have hone := (mem_support h a).mp hmem
  exact zero_ne_one (ha.symm.trans hone)

private theorem hammingWeight_add_pointIndicator_add_one_of_eq_one
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 1) :
    hammingWeight (h + FABL.f₂PointIndicator a) + 1 = hammingWeight h := by
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support,
    support_add_pointIndicator_of_eq_one h a ha]
  exact Finset.card_erase_add_one ((mem_support h a).2 ha)

private theorem add_pointIndicator_apply_of_ne
    (h : BooleanFunction n) (a b : FABL.F₂Cube n) (hab : a ≠ b) :
    (h + FABL.f₂PointIndicator a) b = h b := by
  rw [Pi.add_apply, FABL.f₂PointIndicator_eq_ite,
    if_neg (Ne.symm hab), add_zero]

private theorem hammingWeight_add_two_pointIndicators_of_both_one
    (h : BooleanFunction n) (a b : FABL.F₂Cube n)
    (hab : a ≠ b) (ha : h a = 1) (hb : h b = 1) :
    hammingWeight
        (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) + 2 =
      hammingWeight h := by
  have hfirst := hammingWeight_add_pointIndicator_add_one_of_eq_one h a ha
  have hb' : (h + FABL.f₂PointIndicator a) b = 1 := by
    rw [add_pointIndicator_apply_of_ne h a b hab]
    exact hb
  have hsecond := hammingWeight_add_pointIndicator_add_one_of_eq_one
    (h + FABL.f₂PointIndicator a) b hb'
  omega

private theorem hammingWeight_add_two_pointIndicators_of_mixed
    (h : BooleanFunction n) (a b : FABL.F₂Cube n)
    (hab : a ≠ b) (ha : h a = 1) (hb : h b = 0) :
    hammingWeight
        (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) =
      hammingWeight h := by
  have hfirst := hammingWeight_add_pointIndicator_add_one_of_eq_one h a ha
  have hb' : (h + FABL.f₂PointIndicator a) b = 0 := by
    rw [add_pointIndicator_apply_of_ne h a b hab]
    exact hb
  have hsecond := hammingWeight_add_pointIndicator_eq_add_one_of_eq_zero
    (h + FABL.f₂PointIndicator a) b hb'
  omega

private theorem hammingWeight_add_two_pointIndicators_of_both_zero
    (h : BooleanFunction n) (a b : FABL.F₂Cube n)
    (hab : a ≠ b) (ha : h a = 0) (hb : h b = 0) :
    hammingWeight
        (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) =
      hammingWeight h + 2 := by
  have hfirst := hammingWeight_add_pointIndicator_eq_add_one_of_eq_zero h a ha
  have hb' : (h + FABL.f₂PointIndicator a) b = 0 := by
    rw [add_pointIndicator_apply_of_ne h a b hab]
    exact hb
  have hsecond := hammingWeight_add_pointIndicator_eq_add_one_of_eq_zero
    (h + FABL.f₂PointIndicator a) b hb'
  omega

private theorem f₂_eq_zero_of_ne_one (x : FABL.𝔽₂) (hx : x ≠ 1) :
    x = 0 := by
  by_contra hzero
  exact hx (Fin.eq_one_of_ne_zero x hzero)

private theorem add_pointIndicator_self
    (h : BooleanFunction n) (a : FABL.F₂Cube n) :
    h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator a = h := by
  funext x
  simp only [Pi.add_apply]
  calc
    h x + FABL.f₂PointIndicator a x + FABL.f₂PointIndicator a x =
        h x + (FABL.f₂PointIndicator a x + FABL.f₂PointIndicator a x) := by
      abel
    _ = h x := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem tuplePointParityMultiplicity_toggle_pair
    (k : ℕ) (h : BooleanFunction n) (a b : FABL.F₂Cube n) :
    tuplePointParityMultiplicity k
        (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) =
      if a = b then
        tuplePointParityMultiplicityByWeight k n (hammingWeight h)
      else if h a = 1 then
        if h b = 1 then
          tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2)
        else
          tuplePointParityMultiplicityByWeight k n (hammingWeight h)
      else if h b = 1 then
        tuplePointParityMultiplicityByWeight k n (hammingWeight h)
      else
        tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl, add_pointIndicator_self,
      tuplePointParityMultiplicity_eq_byWeight]
  · rw [if_neg hab]
    by_cases ha : h a = 1
    · rw [if_pos ha]
      by_cases hb : h b = 1
      · rw [if_pos hb, tuplePointParityMultiplicity_eq_byWeight]
        have hweight :
            hammingWeight
                (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b) =
              hammingWeight h - 2 := by
          have hrelation := hammingWeight_add_two_pointIndicators_of_both_one
            h a b hab ha hb
          omega
        rw [hweight]
      · have hbzero : h b = 0 := f₂_eq_zero_of_ne_one (h b) hb
        rw [if_neg hb, tuplePointParityMultiplicity_eq_byWeight,
          hammingWeight_add_two_pointIndicators_of_mixed h a b hab ha hbzero]
    · have hazero : h a = 0 := f₂_eq_zero_of_ne_one (h a) ha
      rw [if_neg ha]
      by_cases hb : h b = 1
      · rw [if_pos hb, tuplePointParityMultiplicity_eq_byWeight]
        have hweight := hammingWeight_add_two_pointIndicators_of_mixed
          h b a (Ne.symm hab) hb hazero
        rw [show h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b =
            h + FABL.f₂PointIndicator b + FABL.f₂PointIndicator a by
              ac_rfl]
        exact congrArg
          (fun w ↦ tuplePointParityMultiplicityByWeight k n w) hweight
      · have hbzero : h b = 0 := f₂_eq_zero_of_ne_one (h b) hb
        rw [if_neg hb, tuplePointParityMultiplicity_eq_byWeight,
          hammingWeight_add_two_pointIndicators_of_both_zero
            h a b hab hazero hbzero]

private theorem sum_ite_eq_filter_card_mul
    {X : Type*}
    (s : Finset X) (p : X → Prop) [DecidablePred p] (A B : ℕ) :
    (∑ x ∈ s, if p x then A else B) =
      (s.filter p).card * A + (s.filter fun x ↦ ¬p x).card * B := by
  rw [Finset.sum_ite]
  simp

private theorem card_erase_filter_one_of_eq_one
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 1) :
    (((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
        (fun b ↦ h b = 1)).card = hammingWeight h - 1 := by
  have heq :
      ((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
          (fun b ↦ h b = 1) = (support h).erase a := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      mem_support]
    tauto
  rw [heq, Finset.card_erase_of_mem ((mem_support h a).2 ha),
    ← hammingWeight_eq_card_support]

private theorem card_erase_filter_one_of_eq_zero
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 0) :
    (((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
        (fun b ↦ h b = 1)).card = hammingWeight h := by
  have heq :
      ((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
          (fun b ↦ h b = 1) = support h := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      mem_support]
    constructor
    · exact fun hb ↦ hb.2
    · intro hb
      refine ⟨⟨?_, trivial⟩, hb⟩
      rintro rfl
      exact zero_ne_one (ha.symm.trans hb)
  rw [heq, ← hammingWeight_eq_card_support]

private theorem card_erase_filter_not_one_of_eq_one
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 1) :
    (((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
        (fun b ↦ h b ≠ 1)).card = 2 ^ n - hammingWeight h := by
  have heq :
      ((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
          (fun b ↦ h b ≠ 1) =
        (Finset.univ : Finset (FABL.F₂Cube n)) \ support h := by
    ext b
    constructor
    · intro hb
      have hbparts := Finset.mem_filter.mp hb
      have hbnotone := hbparts.2
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ b, fun hbsupport ↦
          hbnotone ((mem_support h b).1 hbsupport)⟩
    · intro hb
      have hbparts := Finset.mem_sdiff.mp hb
      have hbnotone : h b ≠ 1 := fun hbOne ↦
        hbparts.2 ((mem_support h b).2 hbOne)
      have hbne : b ≠ a := by
        rintro rfl
        exact hbnotone ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hbne, Finset.mem_univ b⟩, hbnotone⟩
  rw [heq, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ (support h)),
    Finset.card_univ, card_f₂Cube, ← hammingWeight_eq_card_support]

private theorem card_erase_filter_not_one_of_eq_zero
    (h : BooleanFunction n) (a : FABL.F₂Cube n) (ha : h a = 0) :
    (((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
        (fun b ↦ h b ≠ 1)).card = 2 ^ n - hammingWeight h - 1 := by
  have heq :
      ((Finset.univ : Finset (FABL.F₂Cube n)).erase a).filter
          (fun b ↦ h b ≠ 1) =
        ((Finset.univ : Finset (FABL.F₂Cube n)) \ support h).erase a := by
    ext b
    constructor
    · intro hb
      have hbparts := Finset.mem_filter.mp hb
      have hberase := Finset.mem_erase.mp hbparts.1
      have hbnotone := hbparts.2
      exact Finset.mem_erase.mpr
        ⟨hberase.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ b, fun hbsupport ↦
            hbnotone ((mem_support h b).1 hbsupport)⟩⟩
    · intro hb
      have hbparts := Finset.mem_erase.mp hb
      have hbsdiff := Finset.mem_sdiff.mp hbparts.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hbparts.1, Finset.mem_univ b⟩,
          fun hbOne ↦ hbsdiff.2 ((mem_support h b).2 hbOne)⟩
  have haMem : a ∈
      (Finset.univ : Finset (FABL.F₂Cube n)) \ support h := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    intro haSupport
    exact zero_ne_one (ha.symm.trans ((mem_support h a).1 haSupport))
  rw [heq, Finset.card_erase_of_mem haMem,
    Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ (support h)),
    Finset.card_univ, card_f₂Cube, ← hammingWeight_eq_card_support]

private theorem sum_toggle_pair_fixed_left
    (k : ℕ) (h : BooleanFunction n) (a : FABL.F₂Cube n) :
    (∑ b : FABL.F₂Cube n,
        tuplePointParityMultiplicity k
          (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
      if h a = 1 then
        tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
          (hammingWeight h - 1) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
          (2 ^ n - hammingWeight h) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h)
      else
        tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
          hammingWeight h *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
          (2 ^ n - hammingWeight h - 1) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
  classical
  rw [← Finset.add_sum_erase (Finset.univ : Finset (FABL.F₂Cube n))
    (fun b ↦ tuplePointParityMultiplicity k
      (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b))
    (Finset.mem_univ a)]
  rw [tuplePointParityMultiplicity_toggle_pair, if_pos rfl]
  by_cases ha : h a = 1
  · rw [if_pos ha]
    have hinner :
      (∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
          tuplePointParityMultiplicity k
            (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
        (hammingWeight h - 1) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
          (2 ^ n - hammingWeight h) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h) := by
      calc
        (∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
            tuplePointParityMultiplicity k
              (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
            ∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
              if h b = 1 then
                tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2)
              else
                tuplePointParityMultiplicityByWeight k n (hammingWeight h) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hab : a ≠ b := Ne.symm (Finset.mem_erase.mp hb).1
          rw [tuplePointParityMultiplicity_toggle_pair, if_neg hab, if_pos ha]
        _ = _ := by
          rw [sum_ite_eq_filter_card_mul,
            card_erase_filter_one_of_eq_one h a ha,
            card_erase_filter_not_one_of_eq_one h a ha]
    rw [hinner]
    ac_rfl
  · have hazero : h a = 0 := f₂_eq_zero_of_ne_one (h a) ha
    rw [if_neg ha]
    have hinner :
      (∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
          tuplePointParityMultiplicity k
            (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
        hammingWeight h *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
          (2 ^ n - hammingWeight h - 1) *
            tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
      calc
        (∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
            tuplePointParityMultiplicity k
              (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
            ∑ b ∈ (Finset.univ : Finset (FABL.F₂Cube n)).erase a,
              if h b = 1 then
                tuplePointParityMultiplicityByWeight k n (hammingWeight h)
              else
                tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hab : a ≠ b := Ne.symm (Finset.mem_erase.mp hb).1
          rw [tuplePointParityMultiplicity_toggle_pair, if_neg hab, if_neg ha]
        _ = _ := by
          rw [sum_ite_eq_filter_card_mul,
            card_erase_filter_one_of_eq_zero h a hazero,
            card_erase_filter_not_one_of_eq_zero h a hazero]
    rw [hinner]
    ac_rfl

private theorem card_filter_one
    (h : BooleanFunction n) :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter
        (fun a ↦ h a = 1)).card = hammingWeight h := by
  have heq :
      (Finset.univ : Finset (FABL.F₂Cube n)).filter
          (fun a ↦ h a = 1) = support h := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_support]
  rw [heq, ← hammingWeight_eq_card_support]

private theorem card_filter_not_one
    (h : BooleanFunction n) :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter
        (fun a ↦ h a ≠ 1)).card = 2 ^ n - hammingWeight h := by
  have heq :
      (Finset.univ : Finset (FABL.F₂Cube n)).filter
          (fun a ↦ h a ≠ 1) =
        (Finset.univ : Finset (FABL.F₂Cube n)) \ support h := by
    ext a
    constructor
    · intro ha
      have hanotone := (Finset.mem_filter.mp ha).2
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ a, fun haSupport ↦
          hanotone ((mem_support h a).1 haSupport)⟩
    · intro ha
      have haparts := Finset.mem_sdiff.mp ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ a, fun haOne ↦
          haparts.2 ((mem_support h a).2 haOne)⟩
  rw [heq, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ (support h)),
    Finset.card_univ, card_f₂Cube, ← hammingWeight_eq_card_support]

private theorem tuplePointParityMultiplicityByWeight_succ_decomposed
    (k : ℕ) (h : BooleanFunction n) :
    tuplePointParityMultiplicityByWeight (k + 1) n (hammingWeight h) =
      (hammingWeight h + (2 ^ n - hammingWeight h) +
          2 * hammingWeight h * (2 ^ n - hammingWeight h)) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
        hammingWeight h * (hammingWeight h - 1) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
        (2 ^ n - hammingWeight h) * (2 ^ n - hammingWeight h - 1) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
  classical
  rw [← tuplePointParityMultiplicity_eq_byWeight (k + 1) h,
    tuplePointParityMultiplicity_succ]
  calc
    (∑ a : FABL.F₂Cube n, ∑ b : FABL.F₂Cube n,
        tuplePointParityMultiplicity k
          (h + FABL.f₂PointIndicator a + FABL.f₂PointIndicator b)) =
        ∑ a : FABL.F₂Cube n,
          if h a = 1 then
            tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
              (hammingWeight h - 1) *
                tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
              (2 ^ n - hammingWeight h) *
                tuplePointParityMultiplicityByWeight k n (hammingWeight h)
          else
            tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
              hammingWeight h *
                tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
              (2 ^ n - hammingWeight h - 1) *
                tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [sum_toggle_pair_fixed_left]
    _ = hammingWeight h *
          (tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
            (hammingWeight h - 1) *
              tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
            (2 ^ n - hammingWeight h) *
              tuplePointParityMultiplicityByWeight k n (hammingWeight h)) +
        (2 ^ n - hammingWeight h) *
          (tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
            hammingWeight h *
              tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
            (2 ^ n - hammingWeight h - 1) *
              tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2)) := by
      rw [sum_ite_eq_filter_card_mul, card_filter_one, card_filter_not_one]
    _ = _ := by ring

/-- Carlet--Mesnager's two-point recurrence for the multiplicity of a
point-parity word, expressed only through its Hamming weight. -/
theorem tuplePointParityMultiplicityByWeight_succ
    (k : ℕ) (h : BooleanFunction n) :
    tuplePointParityMultiplicityByWeight (k + 1) n (hammingWeight h) =
      (2 ^ n + 2 * hammingWeight h * (2 ^ n - hammingWeight h)) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h) +
        hammingWeight h * (hammingWeight h - 1) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h - 2) +
        (2 ^ n - hammingWeight h) * (2 ^ n - hammingWeight h - 1) *
          tuplePointParityMultiplicityByWeight k n (hammingWeight h + 2) := by
  have hweightLe : hammingWeight h ≤ 2 ^ n := by
    rw [← card_f₂Cube n]
    exact hammingNorm_le_card_fintype
  simpa only [Nat.add_sub_of_le hweightLe] using
    tuplePointParityMultiplicityByWeight_succ_decomposed k h

private theorem exists_booleanFunction_hammingWeight_eq
    {w : ℕ} (hw : w ≤ 2 ^ n) :
    ∃ h : BooleanFunction n, hammingWeight h = w := by
  classical
  have hw' : w ≤ (Finset.univ : Finset (FABL.F₂Cube n)).card := by
    simpa only [Finset.card_univ, card_f₂Cube] using hw
  obtain ⟨s, _hs, hcard⟩ := Finset.exists_subset_card_eq hw'
  let h : BooleanFunction n := fun x ↦ if x ∈ s then 1 else 0
  refine ⟨h, ?_⟩
  rw [hammingWeight_eq_card_support]
  have hsupport : support h = s := by
    ext x
    simp [h, mem_support]
  rw [hsupport, hcard]

private theorem tuplePointParityMultiplicityByWeight_succ_of_le
    (k n w : ℕ) (hw : w ≤ 2 ^ n) :
    tuplePointParityMultiplicityByWeight (k + 1) n w =
      (2 ^ n + 2 * w * (2 ^ n - w)) *
          tuplePointParityMultiplicityByWeight k n w +
        w * (w - 1) * tuplePointParityMultiplicityByWeight k n (w - 2) +
        (2 ^ n - w) * (2 ^ n - w - 1) *
          tuplePointParityMultiplicityByWeight k n (w + 2) := by
  obtain ⟨h, hweight⟩ :=
    exists_booleanFunction_hammingWeight_eq (n := n) hw
  simpa only [hweight] using tuplePointParityMultiplicityByWeight_succ k h

private theorem tuplePointParityMultiplicity_zero
    (h : BooleanFunction n) :
    tuplePointParityMultiplicity 0 h = if h = 0 then 1 else 0 := by
  classical
  have hparity : ∀ x : Fin 0 → FABL.F₂Cube n, tuplePointParity x = 0 := by
    intro x
    funext y
    simp [tuplePointParity]
  by_cases hh : h = 0
  · subst h
    rw [tuplePointParityMultiplicity, tuplePointParityFiber]
    have hfilter :
        (Finset.univ : Finset (Fin 0 → FABL.F₂Cube n)).filter
            (fun x ↦ tuplePointParity x = 0) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro x _hx
      exact hparity x
    rw [hfilter]
    simp
  · rw [tuplePointParityMultiplicity, tuplePointParityFiber]
    have hfilter :
        (Finset.univ : Finset (Fin 0 → FABL.F₂Cube n)).filter
            (fun x ↦ tuplePointParity x = h) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      intro hx
      apply hh
      rw [← hx]
      exact hparity x
    rw [hfilter, Finset.card_empty, if_neg hh]

private theorem tuplePointParityMultiplicityByWeight_zero
    (n w : ℕ) :
    tuplePointParityMultiplicityByWeight 0 n w = if w = 0 then 1 else 0 := by
  classical
  rw [tuplePointParityMultiplicityByWeight]
  by_cases hexists : ∃ h : BooleanFunction n, hammingWeight h = w
  · rw [dif_pos hexists, tuplePointParityMultiplicity_zero]
    by_cases hwzero : w = 0
    · rw [if_pos hwzero]
      have hchosen : (Classical.choose hexists : BooleanFunction n) = 0 := by
        apply hammingNorm_eq_zero.mp
        simpa only [hwzero] using Classical.choose_spec hexists
      rw [if_pos hchosen]
    · rw [if_neg hwzero, if_neg]
      intro hchosen
      have hweight := Classical.choose_spec hexists
      rw [hchosen] at hweight
      change hammingNorm (0 : BooleanFunction n) = w at hweight
      rw [hammingNorm_zero] at hweight
      exact hwzero hweight.symm
  · rw [dif_neg hexists]
    have hwzero : w ≠ 0 := by
      intro hwzero
      apply hexists
      refine ⟨0, ?_⟩
      change hammingNorm (0 : BooleanFunction n) = w
      rw [hammingNorm_zero, hwzero]
    rw [if_neg hwzero]

private def tuplePointParityCountRecurrence
    (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, j =>
      (q + 2 * (2 * j) * (q - 2 * j)) *
          tuplePointParityCountRecurrence q k j +
        (2 * j) * (2 * j - 1) *
          tuplePointParityCountRecurrence q k (j - 1) +
        (q - 2 * j) * (q - 2 * j - 1) *
          tuplePointParityCountRecurrence q k (j + 1)

private def tuplePointParityCountPolynomial
    (q : ℤ) : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, j =>
      (q + 2 * (2 * (j : ℤ)) * (q - 2 * (j : ℤ))) *
          tuplePointParityCountPolynomial q k j +
        (2 * (j : ℤ)) * (2 * (j : ℤ) - 1) *
          tuplePointParityCountPolynomial q k (j - 1) +
        (q - 2 * (j : ℤ)) * (q - 2 * (j : ℤ) - 1) *
          tuplePointParityCountPolynomial q k (j + 1)

private theorem tuplePointParityCountRecurrence_cast
    (q k j : ℕ) (hbound : 2 * (j + k) ≤ q) :
    (tuplePointParityCountRecurrence q k j : ℤ) =
      tuplePointParityCountPolynomial q k j := by
  induction k generalizing j with
  | zero =>
      cases j <;> simp [tuplePointParityCountRecurrence,
        tuplePointParityCountPolynomial]
  | succ k ih =>
      rw [tuplePointParityCountRecurrence, tuplePointParityCountPolynomial]
      have hcurrent : 2 * j ≤ q := by omega
      have hcurrentOne : 1 ≤ q - 2 * j := by omega
      have hsame : 2 * (j + k) ≤ q := by omega
      have hlower : 2 * (j - 1 + k) ≤ q := by omega
      have hupper : 2 * (j + 1 + k) ≤ q := by omega
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub hcurrentOne, Nat.cast_sub hcurrent,
        ih j hsame, ih (j - 1) hlower, ih (j + 1) hupper]
      by_cases hjzero : j = 0
      · subst j
        norm_num
      · rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
        push_cast [Nat.cast_sub hcurrent]
        ring

private theorem tuplePointParityMultiplicityByWeight_even_eq_recurrence
    (n k j : ℕ) (hj : 2 * j ≤ 2 ^ n) :
    tuplePointParityMultiplicityByWeight k n (2 * j) =
      tuplePointParityCountRecurrence (2 ^ n) k j := by
  induction k generalizing j with
  | zero =>
      rw [tuplePointParityMultiplicityByWeight_zero]
      cases j <;> rfl
  | succ k ih =>
      rw [tuplePointParityMultiplicityByWeight_succ_of_le k n (2 * j) hj,
        tuplePointParityCountRecurrence, ih j hj]
      by_cases hjzero : j = 0
      · subst j
        simp only [Nat.mul_zero, Nat.sub_zero, zero_mul, add_zero]
        by_cases hupper : 2 ≤ 2 ^ n
        · rw [ih 1 (by omega)]
        · have hqpos : 0 < 2 ^ n := pow_pos (by omega) n
          have hq : 2 ^ n = 1 := by omega
          rw [hq]
          norm_num
      · have hlower : 2 * (j - 1) ≤ 2 ^ n := by omega
        have hlowerIndex : 2 * j - 2 = 2 * (j - 1) := by omega
        rw [hlowerIndex, ih (j - 1) hlower]
        by_cases hupper : 2 * (j + 1) ≤ 2 ^ n
        · have hupperIndex : 2 * j + 2 = 2 * (j + 1) := by omega
          rw [hupperIndex, ih (j + 1) hupper]
        · have hcoefficient :
              (2 ^ n - 2 * j) * (2 ^ n - 2 * j - 1) = 0 := by
            have hdiff :
                2 ^ n - 2 * j = 0 ∨ 2 ^ n - 2 * j = 1 := by
              omega
            rcases hdiff with hdiff | hdiff
            · rw [hdiff]
            · rw [hdiff]
          rw [hcoefficient, zero_mul, zero_mul]

private theorem tuplePointParityMultiplicityByWeight_even_eq_polynomial
    (n k j : ℕ) (hbound : 2 * (j + k) ≤ 2 ^ n) :
    (tuplePointParityMultiplicityByWeight k n (2 * j) : ℤ) =
      tuplePointParityCountPolynomial ((2 ^ n : ℕ) : ℤ) k j := by
  rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence n k j (by omega),
    tuplePointParityCountRecurrence_cast (2 ^ n) k j hbound]

/-- Carlet--Mesnager Corollary 9.2.8: the exact seventh null-word
point-parity multiplicity. -/
theorem tuplePointParityMultiplicityByWeight_seven_zero
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 7 n 0 : ℤ) =
      135135 * (2 : ℤ) ^ (7 * n) -
        1891890 * (2 : ℤ) ^ (6 * n) +
        11351340 * (2 : ℤ) ^ (5 * n) -
        36636600 * (2 : ℤ) ^ (4 * n) +
        65825760 * (2 : ℤ) ^ (3 * n) -
        61152000 * (2 : ℤ) ^ (2 * n) +
        22368256 * (2 : ℤ) ^ n := by
  have hpow : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 7 0 (by omega)]
  norm_num [tuplePointParityCountPolynomial]
  ring

/-- Carlet--Mesnager Corollary 9.2.8: the exact eighth null-word
point-parity multiplicity. -/
theorem tuplePointParityMultiplicityByWeight_eight_zero
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 8 n 0 : ℤ) =
      2027025 * (2 : ℤ) ^ (8 * n) -
        37837800 * (2 : ℤ) ^ (7 * n) +
        310269960 * (2 : ℤ) ^ (6 * n) -
        1427025600 * (2 : ℤ) ^ (5 * n) +
        3918554640 * (2 : ℤ) ^ (4 * n) -
        6327135360 * (2 : ℤ) ^ (3 * n) +
        5464904448 * (2 : ℤ) ^ (2 * n) -
        1903757312 * (2 : ℤ) ^ n := by
  have hpow : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 8 0 (by omega)]
  norm_num [tuplePointParityCountPolynomial]
  ring

/-- Carlet--Mesnager Corollary 9.2.8: the exact seventh point-parity
multiplicity at weight eight. -/
theorem tuplePointParityMultiplicityByWeight_seven_eight
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 7 n 8 : ℤ) =
      1816214400 * (2 : ℤ) ^ (3 * n) -
        32691859200 * (2 : ℤ) ^ (2 * n) +
        203416012800 * (2 : ℤ) ^ n -
        435430195200 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 7 4 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
    ring
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 7 4 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact seventh point-parity
multiplicity at weight twelve. -/
theorem tuplePointParityMultiplicityByWeight_seven_twelve
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 7 n 12 : ℤ) =
      43589145600 * (2 : ℤ) ^ n - 348713164800 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 7 6 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
    ring
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 7 6 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact seventh point-parity
multiplicity at weight fourteen. -/
theorem tuplePointParityMultiplicityByWeight_seven_fourteen
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 7 n 14 : ℤ) = 87178291200 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 7 7 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 7 7 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Seven pairs cannot have point parity of weight sixteen. -/
theorem tuplePointParityMultiplicityByWeight_seven_sixteen
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMultiplicityByWeight 7 n 16 = 0 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    have hformula :=
      tuplePointParityMultiplicityByWeight_even_eq_polynomial n 7 8 (by omega)
    norm_num [tuplePointParityCountPolynomial] at hformula
    exact_mod_cast hformula
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 7 8 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact eighth point-parity
multiplicity at weight eight. -/
theorem tuplePointParityMultiplicityByWeight_eight_eight
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 8 n 8 : ℤ) =
      54486432000 * (2 : ℤ) ^ (4 * n) -
        1380322944000 * (2 : ℤ) ^ (3 * n) +
        13556224281600 * (2 : ℤ) ^ (2 * n) -
        60916868812800 * (2 : ℤ) ^ n +
        105309161717760 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 8 4 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
    ring
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 8 4 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact eighth point-parity
multiplicity at weight twelve. -/
theorem tuplePointParityMultiplicityByWeight_eight_twelve
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 8 n 12 : ℤ) =
      2615348736000 * (2 : ℤ) ^ (2 * n) -
        43589145600000 * (2 : ℤ) ^ n +
        186910256332800 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 8 6 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
    ring
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 8 6 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact eighth point-parity
multiplicity at weight fourteen. -/
theorem tuplePointParityMultiplicityByWeight_eight_fourteen
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 8 n 14 : ℤ) =
      10461394944000 * (2 : ℤ) ^ n - 97639686144000 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 8 7 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
    ring
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 8 7 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

/-- Carlet--Mesnager Corollary 9.2.8: the exact eighth point-parity
multiplicity at weight sixteen. -/
theorem tuplePointParityMultiplicityByWeight_eight_sixteen
    (n : ℕ) (hn : 4 ≤ n) :
    (tuplePointParityMultiplicityByWeight 8 n 16 : ℤ) = 20922789888000 := by
  by_cases hnfive : 5 ≤ n
  · have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnfive
    rw [tuplePointParityMultiplicityByWeight_even_eq_polynomial n 8 8 (by omega)]
    norm_num [tuplePointParityCountPolynomial]
  · have hnfour : n = 4 := by omega
    subst n
    rw [tuplePointParityMultiplicityByWeight_even_eq_recurrence 4 8 8 (by norm_num)]
    norm_num [tuplePointParityCountRecurrence]

end CryptBoolean
