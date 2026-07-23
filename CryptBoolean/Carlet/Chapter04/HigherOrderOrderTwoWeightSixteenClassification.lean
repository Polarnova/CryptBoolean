/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenTypeA
public import CryptBoolean.Carlet.Chapter04.GeneralizedLinearStructureDistance

/-!
# The weight-sixteen exceptional families

The period-space description and the six-vector count for the type-`b`
exceptional words in the Kasami--Tokura classification.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightSixteenClassificationQuotientDecidableEq
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    DecidableEq (FABL.F₂Cube n ⧸ S) :=
  Classical.decEq _

/-- The type-`b` exceptional family, characterized intrinsically by its
two-dimensional zero-derivative kernel. -/
noncomputable def orderTwoWeightSixteenTypeBWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoWeightSixteenDualWords n).filter fun h ↦
    Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 2

/-- Type-`b` words are weight-sixteen words in the dual Reed--Muller code. -/
theorem orderTwoWeightSixteenTypeBWords_subset_dualWords (n : ℕ) :
    orderTwoWeightSixteenTypeBWords n ⊆
      orderTwoWeightSixteenDualWords n := by
  intro h hh
  exact (Finset.mem_filter.mp hh).1

private theorem binaryAffineFlatIndicator_period_of_mem_direction
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) (ha : a ∈ C.direction)
    (x : FABL.F₂Cube n) :
    binaryAffineFlatIndicator C (x + a) =
      binaryAffineFlatIndicator C x := by
  classical
  have hmem : x + a ∈ C ↔ x ∈ C := by
    simpa only [vadd_eq_add, add_comm] using
      (AffineSubspace.vadd_mem_iff_mem_of_mem_direction ha (p := x))
  simp only [binaryAffineFlatIndicator]
  by_cases hx : x ∈ C
  · rw [if_pos hx, if_pos (hmem.mpr hx)]
  · rw [if_neg hx, if_neg (fun h ↦ hx (hmem.mp h))]

theorem binaryAffineFlatIndicator_zeroDerivativeKernel
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) (hC : C ≠ ⊥) :
    zeroDerivativeKernel (binaryAffineFlatIndicator C) = C.direction := by
  apply le_antisymm
  · intro a ha
    obtain ⟨x, hx⟩ := (AffineSubspace.nonempty_iff_ne_bot C).2 hC
    have hderivative := ha x
    simp only [FABL.booleanDerivative] at hderivative
    have hxOne : binaryAffineFlatIndicator C x = 1 :=
      (binaryAffineFlatIndicator_apply_eq_one_iff C x).2 hx
    have hxaOne : binaryAffineFlatIndicator C (x + a) = 1 := by
      rw [hxOne] at hderivative
      have heq := add_eq_zero_iff_eq_neg.mp hderivative
      exact (heq.trans (ZMod.neg_eq_self_mod_two
        (binaryAffineFlatIndicator C (x + a)))).symm
    have hxa : x + a ∈ C :=
      (binaryAffineFlatIndicator_apply_eq_one_iff C (x + a)).1 hxaOne
    have hvsub := AffineSubspace.vsub_mem_direction hxa hx
    have hdifference : (x + a) - x = a := by
      simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
      calc
        x + a + x = a + (x + x) := by abel
        _ = a := by rw [ZModModule.add_self, add_zero]
    rw [vsub_eq_sub, hdifference] at hvsub
    exact hvsub
  · intro a ha x
    simp only [FABL.booleanDerivative]
    rw [binaryAffineFlatIndicator_period_of_mem_direction C a ha x]
    exact ZModModule.add_self _

/-- The zero-derivative kernel of a type-`a` word has dimension four. -/
theorem finrank_zeroDerivativeKernel_of_mem_weightSixteenTypeAWords
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeAWords n) :
    Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 4 := by
  classical
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hh
  have hCdata : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  rw [binaryAffineFlatIndicator_zeroDerivativeKernel C hCdata.1,
    hCdata.2]

/-- The two exceptional weight-sixteen families are disjoint. -/
theorem disjoint_orderTwoWeightSixteenTypeAWords_typeBWords (n : ℕ) :
    Disjoint (orderTwoWeightSixteenTypeAWords n)
      (orderTwoWeightSixteenTypeBWords n) := by
  rw [Finset.disjoint_left]
  intro h hA hB
  have hfour :=
    finrank_zeroDerivativeKernel_of_mem_weightSixteenTypeAWords h hA
  have htwo : Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 2 :=
    (Finset.mem_filter.mp hB).2
  omega

/-- A Boolean function descends canonically to the quotient by its
zero-derivative kernel. -/
noncomputable def zeroDerivativeKernelQuotientFunction
    (h : BooleanFunction n) :
    (FABL.F₂Cube n ⧸ zeroDerivativeKernel h) → FABL.𝔽₂ :=
  fun q ↦ Quotient.liftOn' q h (by
    intro a b hab
    let R := zeroDerivativeKernel h
    have hquotient : R.mkQ a = R.mkQ b := Quotient.sound' hab
    have habKernel : a + b ∈ R := by
      have hdifference := (Submodule.Quotient.eq R).mp hquotient
      simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference
    have hperiod := habKernel b
    simp only [FABL.booleanDerivative] at hperiod
    have harg : b + (a + b) = a := by
      calc
        b + (a + b) = a + (b + b) := by abel
        _ = a := by rw [ZModModule.add_self, add_zero]
    rw [harg] at hperiod
    have heq : h b = -h a := add_eq_zero_iff_eq_neg.mp hperiod
    calc
      h a = -h a := (ZMod.neg_eq_self_mod_two (h a)).symm
      _ = h b := heq.symm)

@[simp] theorem zeroDerivativeKernelQuotientFunction_mkQ
    (h : BooleanFunction n) (x : FABL.F₂Cube n) :
    zeroDerivativeKernelQuotientFunction h
        ((zeroDerivativeKernel h).mkQ x) = h x := by
  rfl

private theorem card_submodule_mkQ_fiber_weightSixteen
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (q : FABL.F₂Cube n ⧸ S) :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
      S.mkQ x = q).card = Nat.card S := by
  classical
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {x : FABL.F₂Cube n // S.mkQ x = q} =
        Fintype.card S.mkQ.toAddMonoidHom.ker := by
      apply Fintype.card_congr
      exact AddMonoidHom.fiberEquivKerOfSurjective
        (f := S.mkQ.toAddMonoidHom) S.mkQ_surjective q
    _ = Nat.card S := by
      rw [← Nat.card_eq_fintype_card]
      have hker : S.mkQ.toAddMonoidHom.ker = S.toAddSubgroup := by
        rw [← LinearMap.ker_toAddSubgroup, Submodule.ker_mkQ]
      rw [hker]
      congr

private theorem card_filter_mkQ_eq_card_mul_card_filter_weightSixteen
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (P : (FABL.F₂Cube n ⧸ S) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
      P (S.mkQ x)).card =
      Nat.card S *
        ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    (t := (Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P)
    (g := S.mkQ)
  rw [Finset.sum_const_nat] at hfiber
  · calc
      ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
          P (S.mkQ x)).card =
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card *
            Nat.card S := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          hfiber.symm
      _ = Nat.card S *
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card :=
        Nat.mul_comm _ _
  · intro q hq
    exact card_submodule_mkQ_fiber_weightSixteen S q

private theorem exists_spanning_pair_of_finrank_two
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 2) :
    ∃ a b : FABL.F₂Cube n,
      H = (FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b) := by
  have hbotlt : (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) < H := by
    apply bot_lt_iff_ne_bot.mpr
    intro hHbot
    rw [hHbot, finrank_bot] at hH
    omega
  obtain ⟨a, haH, haBot⟩ := SetLike.exists_of_lt hbotlt
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    exact haBot (Submodule.zero_mem _)
  let S : Submodule FABL.𝔽₂ (FABL.F₂Cube n) := FABL.𝔽₂ ∙ a
  have hSle : S ≤ H :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 haH)
  have hSrank : Module.finrank FABL.𝔽₂ S = 1 :=
    finrank_span_singleton ha0
  have hSlt : S < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hSle (by omega)
  obtain ⟨b, hbH, hbS⟩ := SetLike.exists_of_lt hSlt
  refine ⟨a, b, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hSle
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hbH))
  · rw [Submodule.finrank_sup_span_singleton hbS, hSrank, hH]

private theorem mem_binaryAffineSubspace_iff_mkQ_eq
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a x : FABL.F₂Cube n) :
    x ∈ FABL.binaryAffineSubspace S a ↔ S.mkQ x = S.mkQ a := by
  rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
  constructor
  · intro hx
    apply (Submodule.Quotient.eq S).2
    simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hx
  · intro hx
    have hdifference := (Submodule.Quotient.eq S).1 hx
    simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference

private theorem weightSixteenClassificationDisjointPairData
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ disjointBinaryAffineThreeFlatPairs n) :
    p.1 ∈ binaryAffineFlats 3 n ∧
      p.2 ∈ binaryAffineFlats 3 n ∧ p.1 ⊓ p.2 = ⊥ := by
  have hp' : p ∈ binaryAffineThreeFlatPairs n ∧ p.1 ⊓ p.2 = ⊥ := by
    simpa only [disjointBinaryAffineThreeFlatPairs,
      Finset.mem_filter] using hp
  have hproduct : p ∈
      (binaryAffineFlats 3 n).product (binaryAffineFlats 3 n) := hp'.1
  exact ⟨(Finset.mem_product.mp hproduct).1,
    (Finset.mem_product.mp hproduct).2, hp'.2⟩

private theorem weightSixteenClassificationPairPointSetsDisjoint
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ disjointBinaryAffineThreeFlatPairs n) :
    Disjoint (binaryAffineFlatPoints p.1)
      (binaryAffineFlatPoints p.2) := by
  rw [Finset.disjoint_left]
  intro x hxFirst hxSecond
  have hxMeet : x ∈ p.1 ⊓ p.2 :=
    ⟨(mem_binaryAffineFlatPoints p.1 x).1 hxFirst,
      (mem_binaryAffineFlatPoints p.2 x).1 hxSecond⟩
  rw [(weightSixteenClassificationDisjointPairData hp).2.2] at hxMeet
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hxMeet
  exact hxMeet

private theorem firstFlatPoints_subset_support_of_mem_weightSixteenFiber
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    binaryAffineFlatPoints p.1 ⊆ support h := by
  have hpData := Finset.mem_filter.mp hp
  intro x hx
  have hxFirst : x ∈ p.1 := (mem_binaryAffineFlatPoints p.1 x).1 hx
  have hxNotSecond : x ∉ p.2 := by
    intro hxSecond
    exact (Finset.disjoint_left.mp
      (weightSixteenClassificationPairPointSetsDisjoint hpData.1)) hx
        ((mem_binaryAffineFlatPoints p.2 x).2 hxSecond)
  apply (mem_support h x).2
  rw [← hpData.2]
  simp [weightSixteenRepresentationWord, binaryAffineFlatIndicator,
    hxFirst, hxNotSecond]

private theorem parallelAffineFlatPoints_disjoint
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hdirection : A.direction = B.direction) (hne : A ≠ B) :
    Disjoint (binaryAffineFlatPoints A) (binaryAffineFlatPoints B) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  apply hne
  have hxA' : x ∈ A := (mem_binaryAffineFlatPoints A x).1 hxA
  have hxB' : x ∈ B := (mem_binaryAffineFlatPoints B x).1 hxB
  exact (AffineSubspace.eq_iff_direction_eq_of_mem hxA' hxB').2 hdirection

private theorem zeroDerivativeKernel_le_firstDirection_of_nonTypeA_fiber
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hnotA : h ∉ orderTwoWeightSixteenTypeAWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    zeroDerivativeKernel h ≤ p.1.direction := by
  intro r hr
  by_contra hrDirection
  classical
  have hpFiber := Finset.mem_filter.mp hp
  have hpData := weightSixteenClassificationDisjointPairData hpFiber.1
  have hAData : p.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.1.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpData.1
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot p.1).2 hAData.1
  let B := FABL.binaryAffineSubspace p.1.direction (a + r)
  have hBbase : a + r ∈ B := by
    change a + r ∈ FABL.binaryAffineSubspace p.1.direction (a + r)
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact p.1.direction.zero_mem
  have hBdirection : B.direction = p.1.direction := by
    exact FABL.binaryAffineSubspace_direction p.1.direction (a + r)
  have hBneBot : B ≠ ⊥ := by
    intro hbot
    have := hBbase
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at this
    exact this
  have hABne : p.1 ≠ B := by
    intro heq
    have harA : a + r ∈ p.1 := by rw [heq]; exact hBbase
    have hvsub := AffineSubspace.vsub_mem_direction harA ha
    apply hrDirection
    have hdifference : (a + r) -ᵥ a = r := by
      simp only [vsub_eq_sub, sub_eq_add_neg, ZModModule.neg_eq_self]
      calc
        a + r + a = r + (a + a) := by abel
        _ = r := by rw [ZModModule.add_self, add_zero]
    rwa [hdifference] at hvsub
  have hABdisjoint : Disjoint (binaryAffineFlatPoints p.1)
      (binaryAffineFlatPoints B) :=
    parallelAffineFlatPoints_disjoint hBdirection.symm hABne
  have hAcard : (binaryAffineFlatPoints p.1).card = 8 := by
    rw [card_binaryAffineFlatPoints p.1 hAData.1, hAData.2]
    norm_num
  have hBcard : (binaryAffineFlatPoints B).card = 8 := by
    rw [card_binaryAffineFlatPoints B hBneBot, hBdirection, hAData.2]
    norm_num
  have hfirstSubset : binaryAffineFlatPoints p.1 ⊆ support h :=
    firstFlatPoints_subset_support_of_mem_weightSixteenFiber h hp
  have hsecondSubset : binaryAffineFlatPoints B ⊆ support h := by
    intro x hx
    have hxB : x ∈ B := (mem_binaryAffineFlatPoints B x).1 hx
    have hxrA : x + r ∈ p.1 := by
      have hxDirection : x + (a + r) ∈ p.1.direction := by
        exact (FABL.mem_binaryAffineSubspace_iff_add_mem
          p.1.direction (a + r) x).1 hxB
      rw [show p.1 = FABL.binaryAffineSubspace p.1.direction a from
        (AffineSubspace.mk'_eq ha).symm]
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
      have harg : x + r + a = x + (a + r) := by abel
      rwa [harg]
    have hxrOne : h (x + r) = 1 :=
      (mem_support h (x + r)).1
        (hfirstSubset ((mem_binaryAffineFlatPoints p.1 (x + r)).2 hxrA))
    have hperiod := hr x
    simp only [FABL.booleanDerivative] at hperiod
    have hxOne : h x = 1 := by
      have heq := add_eq_zero_iff_eq_neg.mp hperiod
      rw [hxrOne] at heq
      exact heq.trans (ZMod.neg_eq_self_mod_two 1)
    exact (mem_support h x).2 hxOne
  have hsupportCard : (support h).card = 16 := by
    have hhData : h ∈ reedMuller (n - 3) n ∧ hammingWeight h = 16 := by
      simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
        Finset.mem_filter, Finset.mem_univ, true_and] using hh
    simpa only [hammingWeight_eq_card_support] using hhData.2
  have hunionCard :
      (binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints B).card = 16 := by
    rw [Finset.card_union_of_disjoint hABdisjoint, hAcard, hBcard]
  have hunionSupport :
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints B = support h := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.union_subset hfirstSubset hsecondSubset
    · rw [hsupportCard, hunionCard]
  let C := p.1 ⊔ B
  have haC : a ∈ C := (le_sup_left : p.1 ≤ p.1 ⊔ B) ha
  have hCneBot : C ≠ ⊥ := by
    intro hbot
    have := haC
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at this
    exact this
  have hdifference : (a + r) -ᵥ a ∉ p.1.direction := by
    simpa only [vsub_eq_sub, sub_eq_add_neg, ZModModule.neg_eq_self,
      show a + r + a = r by
        calc
          a + r + a = r + (a + a) := by abel
          _ = r := by rw [ZModModule.add_self, add_zero]] using hrDirection
  have hCrank : Module.finrank FABL.𝔽₂ C.direction = 4 := by
    dsimp only [C]
    rw [AffineSubspace.direction_sup ha hBbase,
      hBdirection, sup_idem,
      Submodule.finrank_sup_span_singleton hdifference, hAData.2]
  have hCcard : (binaryAffineFlatPoints C).card = 16 := by
    rw [card_binaryAffineFlatPoints C hCneBot, hCrank]
    norm_num
  have hunionC :
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints B =
        binaryAffineFlatPoints C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hxFirst | hxSecond
      · have hle : p.1 ≤ C := by
          exact le_sup_left
        exact (mem_binaryAffineFlatPoints C x).2
          (hle ((mem_binaryAffineFlatPoints p.1 x).1 hxFirst))
      · have hle : B ≤ C := by
          exact le_sup_right
        exact (mem_binaryAffineFlatPoints C x).2
          (hle ((mem_binaryAffineFlatPoints B x).1 hxSecond))
    · rw [hCcard, hunionCard]
  have hsupportC : support h = binaryAffineFlatPoints C := by
    rw [← hunionSupport, hunionC]
  have hsupportSet : (support h : Set (FABL.F₂Cube n)) = C := by
    ext x
    constructor
    · intro hx
      have hxFin : x ∈ support h := hx
      have hxPoints : x ∈ binaryAffineFlatPoints C := by
        rw [← hsupportC]
        exact hxFin
      exact (mem_binaryAffineFlatPoints C x).1 hxPoints
    · intro hx
      have hxPoints : x ∈ binaryAffineFlatPoints C :=
        (mem_binaryAffineFlatPoints C x).2 hx
      have hxFin : x ∈ support h := by
        rw [hsupportC]
        exact hxPoints
      exact hxFin
  have hCflat : C ∈ binaryAffineFlats 4 n := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using And.intro hCneBot hCrank
  have hfunction : h = binaryAffineFlatIndicator C := by
    have hflat : FABL.binaryAffineSubspace C.direction a = C :=
      AffineSubspace.mk'_eq haC
    have haffine : h = affineFlatIndicator C.direction a :=
      (eq_affineFlatIndicator_iff_support_eq h C.direction a).2 (by
        rw [hflat]
        exact hsupportSet)
    rw [binaryAffineFlatIndicator_eq_affineFlatIndicator C a haC]
    exact haffine
  have htypeA : h ∈ orderTwoWeightSixteenTypeAWords n := by
    rw [orderTwoWeightSixteenTypeAWords, Finset.mem_image]
    exact ⟨C, hCflat, hfunction.symm⟩
  exact hnotA htypeA

private theorem zeroDerivativeKernel_le_firstDirection_of_typeB_fiber
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenTypeBWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    zeroDerivativeKernel h ≤ p.1.direction := by
  apply zeroDerivativeKernel_le_firstDirection_of_nonTypeA_fiber h
    (orderTwoWeightSixteenTypeBWords_subset_dualWords n hh)
  · intro hA
    exact (Finset.disjoint_left.mp
      (disjoint_orderTwoWeightSixteenTypeAWords_typeBWords n)) hA hh
  · exact hp

/-- The quotient support of a Boolean function modulo its zero-derivative
kernel. -/
noncomputable def zeroDerivativeSupportCosets (h : BooleanFunction n) :
    Finset (FABL.F₂Cube n ⧸ zeroDerivativeKernel h) := by
  classical
  exact Finset.univ.filter fun q ↦
    zeroDerivativeKernelQuotientFunction h q = 1

/-- A type-`b` word is supported on exactly four cosets of its
two-dimensional zero-derivative kernel. -/
theorem card_zeroDerivativeSupportCosets_of_mem_typeB
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    (zeroDerivativeSupportCosets h).card = 4 := by
  classical
  let R := zeroDerivativeKernel h
  let qh := zeroDerivativeKernelQuotientFunction h
  have hhData := Finset.mem_filter.mp hh
  have hweight : hammingWeight h = 16 := by
    have hdualData : h ∈ reedMuller (n - 3) n ∧
        hammingWeight h = 16 := by
      simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
        Finset.mem_filter, Finset.mem_univ, true_and] using hhData.1
    exact hdualData.2
  have hRrank : Module.finrank FABL.𝔽₂ R = 2 := hhData.2
  have hRcard : Nat.card R = 4 := by
    rw [FABL.card_submodule_eq_two_pow_finrank, hRrank]
    norm_num
  have hfactor := card_filter_mkQ_eq_card_mul_card_filter_weightSixteen
    R (fun q ↦ qh q = 1)
  have hleft :
      ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
        qh (R.mkQ x) = 1).card = 16 := by
    simpa only [R, qh, zeroDerivativeKernelQuotientFunction_mkQ,
      support, FABL.f₂OneSupport, hammingWeight_eq_card_support] using hweight
  have heq : 16 = 4 *
      ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
        qh q = 1).card := by
    calc
      16 = ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
          qh (R.mkQ x) = 1).card := hleft.symm
      _ = Nat.card R *
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
            qh q = 1).card := hfactor
      _ = 4 *
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
            qh q = 1).card := by rw [hRcard]
  change ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
    qh q = 1).card = 4
  omega

/-- The quotient cosets met by the first flat in a weight-sixteen
representation. -/
noncomputable def weightSixteenRepresentationFirstCosets
    (h : BooleanFunction n)
    (p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (FABL.F₂Cube n ⧸ zeroDerivativeKernel h) := by
  classical
  exact (binaryAffineFlatPoints p.1).image (zeroDerivativeKernel h).mkQ

private theorem card_affineThreeFlatQuotientImage
    (h : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats 3 n)
    (hRrank : Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 2)
    (hRle : zeroDerivativeKernel h ≤ A.direction) :
    ((binaryAffineFlatPoints A).image
      (zeroDerivativeKernel h).mkQ).card = 2 := by
  classical
  let R := zeroDerivativeKernel h
  let t := (binaryAffineFlatPoints A).image R.mkQ
  have hAData : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hAcard : (binaryAffineFlatPoints A).card = 8 := by
    rw [card_binaryAffineFlatPoints A hAData.1, hAData.2]
    norm_num
  have hRcard : Nat.card R = 4 := by
    rw [FABL.card_submodule_eq_two_pow_finrank, hRrank]
    norm_num
  have hfiber : ∀ q ∈ t,
      ((binaryAffineFlatPoints A).filter fun x ↦ R.mkQ x = q).card = 4 := by
    intro q hq
    obtain ⟨x, hxA, hxq⟩ := Finset.mem_image.mp hq
    have hfiberEq :
        (binaryAffineFlatPoints A).filter (fun y ↦ R.mkQ y = q) =
          (Finset.univ : Finset (FABL.F₂Cube n)).filter
            (fun y ↦ R.mkQ y = q) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hy ↦ hy.2
      · intro hyq
        have hyxQ : R.mkQ y = R.mkQ x := hyq.trans hxq.symm
        have hyxR : y + x ∈ R := by
          have hdifference := (Submodule.Quotient.eq R).1 hyxQ
          simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference
        have hxASet : x ∈ A := (mem_binaryAffineFlatPoints A x).1 hxA
        have hyA : y ∈ A := by
          rw [show A = FABL.binaryAffineSubspace A.direction x from
            (AffineSubspace.mk'_eq hxASet).symm]
          rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
          exact hRle hyxR
        exact ⟨(mem_binaryAffineFlatPoints A y).2 hyA, hyq⟩
    rw [hfiberEq, card_submodule_mkQ_fiber_weightSixteen R q, hRcard]
  have hsum := Finset.card_eq_sum_card_image R.mkQ
    (binaryAffineFlatPoints A)
  rw [Finset.sum_const_nat hfiber, hAcard] at hsum
  change t.card = 2
  change 8 = t.card * 4 at hsum
  omega

private theorem weightSixteenRepresentationFirstCosets_mem_powersetCard
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenTypeBWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    weightSixteenRepresentationFirstCosets h p ∈
      (zeroDerivativeSupportCosets h).powersetCard 2 := by
  classical
  rw [Finset.mem_powersetCard]
  constructor
  · intro q hq
    obtain ⟨x, hxFirst, rfl⟩ := Finset.mem_image.mp hq
    have hxSupport := firstFlatPoints_subset_support_of_mem_weightSixteenFiber
      h hp hxFirst
    have hxOne : h x = 1 := (mem_support h x).1 hxSupport
    simp only [zeroDerivativeSupportCosets, Finset.mem_filter,
      Finset.mem_univ, true_and,
      zeroDerivativeKernelQuotientFunction_mkQ]
    exact hxOne
  · have hpData := weightSixteenClassificationDisjointPairData
      (Finset.mem_filter.mp hp).1
    have hRrank : Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 2 :=
      (Finset.mem_filter.mp hh).2
    exact card_affineThreeFlatQuotientImage h p.1 hpData.1 hRrank
      (zeroDerivativeKernel_le_firstDirection_of_typeB_fiber h hh hp)

private theorem firstFlat_eq_of_firstCosets_eq
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenTypeBWords n)
    {p q : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hq : q ∈ weightSixteenRepresentationFiber h)
    (hcosets : weightSixteenRepresentationFirstCosets h p =
      weightSixteenRepresentationFirstCosets h q) :
    p.1 = q.1 := by
  classical
  have hpData := weightSixteenClassificationDisjointPairData
    (Finset.mem_filter.mp hp).1
  have hqData := weightSixteenClassificationDisjointPairData
    (Finset.mem_filter.mp hq).1
  have hpRle := zeroDerivativeKernel_le_firstDirection_of_typeB_fiber
    h hh hp
  have hqRle := zeroDerivativeKernel_le_firstDirection_of_typeB_fiber
    h hh hq
  apply AffineSubspace.ext
  intro x
  constructor
  · intro hxp
    have hxCoset : (zeroDerivativeKernel h).mkQ x ∈
        weightSixteenRepresentationFirstCosets h p := by
      apply Finset.mem_image.mpr
      exact ⟨x, (mem_binaryAffineFlatPoints p.1 x).2 hxp, rfl⟩
    rw [hcosets] at hxCoset
    obtain ⟨y, hyq, hyx⟩ := Finset.mem_image.mp hxCoset
    have hyqSet : y ∈ q.1 := (mem_binaryAffineFlatPoints q.1 y).1 hyq
    have hxyKernel : x + y ∈ zeroDerivativeKernel h := by
      have hdifference := (Submodule.Quotient.eq
        (zeroDerivativeKernel h)).1 hyx.symm
      simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference
    rw [show q.1 = FABL.binaryAffineSubspace q.1.direction y from
      (AffineSubspace.mk'_eq hyqSet).symm]
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    exact hqRle hxyKernel
  · intro hxq
    have hxCoset : (zeroDerivativeKernel h).mkQ x ∈
        weightSixteenRepresentationFirstCosets h q := by
      apply Finset.mem_image.mpr
      exact ⟨x, (mem_binaryAffineFlatPoints q.1 x).2 hxq, rfl⟩
    rw [← hcosets] at hxCoset
    obtain ⟨y, hyp, hyx⟩ := Finset.mem_image.mp hxCoset
    have hypSet : y ∈ p.1 := (mem_binaryAffineFlatPoints p.1 y).1 hyp
    have hxyKernel : x + y ∈ zeroDerivativeKernel h := by
      have hdifference := (Submodule.Quotient.eq
        (zeroDerivativeKernel h)).1 hyx.symm
      simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference
    rw [show p.1 = FABL.binaryAffineSubspace p.1.direction y from
      (AffineSubspace.mk'_eq hypSet).symm]
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    exact hpRle hxyKernel

private theorem weightSixteenRepresentationFirstCosets_injective_on_typeB_fiber
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    Set.InjOn (weightSixteenRepresentationFirstCosets h)
      (weightSixteenRepresentationFiber h : Set
        (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
          AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))) := by
  intro p hp q hq hcosets
  have hpFin : p ∈ weightSixteenRepresentationFiber h := hp
  have hqFin : q ∈ weightSixteenRepresentationFiber h := hq
  have hfirst := firstFlat_eq_of_firstCosets_eq h hh hpFin hqFin hcosets
  have hpWord := (Finset.mem_filter.mp hpFin).2
  have hqWord := (Finset.mem_filter.mp hqFin).2
  have hsums : binaryAffineFlatIndicator p.1 +
      binaryAffineFlatIndicator p.2 =
        binaryAffineFlatIndicator q.1 + binaryAffineFlatIndicator q.2 := by
    exact hpWord.trans hqWord.symm
  rw [hfirst] at hsums
  have hsecondIndicator : binaryAffineFlatIndicator p.2 =
      binaryAffineFlatIndicator q.2 := add_left_cancel hsums
  have hpSecond := (weightSixteenClassificationDisjointPairData
    (Finset.mem_filter.mp hpFin).1).2.1
  have hqSecond := (weightSixteenClassificationDisjointPairData
    (Finset.mem_filter.mp hqFin).1).2.1
  have hpSecondNe : p.2 ≠ ⊥ := by
    have hpSecondData : p.2 ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ p.2.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpSecond
    exact hpSecondData.1
  have hqSecondNe : q.2 ≠ ⊥ := by
    have hqSecondData : q.2 ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ q.2.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hqSecond
    exact hqSecondData.1
  have hsecond : p.2 = q.2 :=
    binaryAffineFlatIndicator_injective_on_nonempty
      hpSecondNe hqSecondNe hsecondIndicator
  exact Prod.ext hfirst hsecond

private theorem card_weightSixteenRepresentationFiber_typeB_le_six
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    (weightSixteenRepresentationFiber h).card ≤ 6 := by
  classical
  calc
    (weightSixteenRepresentationFiber h).card ≤
        ((zeroDerivativeSupportCosets h).powersetCard 2).card := by
      apply Finset.card_le_card_of_injOn
        (weightSixteenRepresentationFirstCosets h)
      · intro p hp
        exact weightSixteenRepresentationFirstCosets_mem_powersetCard
          h hh hp
      · exact weightSixteenRepresentationFirstCosets_injective_on_typeB_fiber
          h hh
    _ = 6 := by
      rw [Finset.card_powersetCard,
        card_zeroDerivativeSupportCosets_of_mem_typeB h hh]
      norm_num [Nat.choose]

private def twoCosetAffineThreeFlat
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.binaryAffineSubspace R x ⊔ FABL.binaryAffineSubspace R y

private theorem twoCosetAffineThreeFlat_mem_flats
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 2)
    (hxy : R.mkQ x ≠ R.mkQ y) :
    twoCosetAffineThreeFlat R x y ∈ binaryAffineFlats 3 n := by
  let A := FABL.binaryAffineSubspace R x
  let B := FABL.binaryAffineSubspace R y
  have hxA : x ∈ A := by
    change x ∈ FABL.binaryAffineSubspace R x
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact R.zero_mem
  have hyB : y ∈ B := by
    change y ∈ FABL.binaryAffineSubspace R y
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact R.zero_mem
  have hdifference : y -ᵥ x ∉ R := by
    intro hyx
    apply hxy
    apply (Submodule.Quotient.eq R).2
    simpa only [vsub_eq_sub, sub_eq_add_neg, ZModModule.neg_eq_self,
      add_comm] using hyx
  have hneBot : twoCosetAffineThreeFlat R x y ≠ ⊥ := by
    intro hbot
    have hxBot : x ∈ (⊥ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
      rw [← hbot]
      exact (le_sup_left : A ≤ A ⊔ B) hxA
    rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hxBot
    exact hxBot
  have hrank : Module.finrank FABL.𝔽₂
      (twoCosetAffineThreeFlat R x y).direction = 3 := by
    rw [twoCosetAffineThreeFlat,
      AffineSubspace.direction_sup hxA hyB,
      FABL.binaryAffineSubspace_direction,
      FABL.binaryAffineSubspace_direction, sup_idem,
      Submodule.finrank_sup_span_singleton hdifference, hRrank]
  simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
    true_and] using And.intro hneBot hrank

private theorem points_twoCosetAffineThreeFlat
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 2)
    (hxy : R.mkQ x ≠ R.mkQ y) :
    binaryAffineFlatPoints (twoCosetAffineThreeFlat R x y) =
      binaryAffineFlatPoints (FABL.binaryAffineSubspace R x) ∪
        binaryAffineFlatPoints (FABL.binaryAffineSubspace R y) := by
  let A := FABL.binaryAffineSubspace R x
  let B := FABL.binaryAffineSubspace R y
  let C := twoCosetAffineThreeFlat R x y
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hx : x ∈ A := by
      change x ∈ FABL.binaryAffineSubspace R x
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
        ZModModule.add_self]
      exact R.zero_mem
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hx
    exact hx
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hy : y ∈ B := by
      change y ∈ FABL.binaryAffineSubspace R y
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
        ZModModule.add_self]
      exact R.zero_mem
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hy
    exact hy
  have hABne : A ≠ B := by
    intro heq
    apply hxy
    apply (Submodule.Quotient.eq R).2
    have hyA : y ∈ A := by
      rw [heq]
      change y ∈ FABL.binaryAffineSubspace R y
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
        ZModModule.add_self]
      exact R.zero_mem
    have hyx := (FABL.mem_binaryAffineSubspace_iff_add_mem R x y).1 hyA
    simpa only [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm] using hyx
  have hdisjoint : Disjoint (binaryAffineFlatPoints A)
      (binaryAffineFlatPoints B) :=
    parallelAffineFlatPoints_disjoint (by
      simp only [A, B, FABL.binaryAffineSubspace_direction]) hABne
  have hCflat := twoCosetAffineThreeFlat_mem_flats R x y hRrank hxy
  have hAdirection : A.direction = R := by
    exact FABL.binaryAffineSubspace_direction R x
  have hBdirection : B.direction = R := by
    exact FABL.binaryAffineSubspace_direction R y
  have hCData : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and, C] using hCflat
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rcases Finset.mem_union.mp hz with hzA | hzB
    · exact (mem_binaryAffineFlatPoints C z).2
        ((le_sup_left : A ≤ A ⊔ B)
          ((mem_binaryAffineFlatPoints A z).1 hzA))
    · exact (mem_binaryAffineFlatPoints C z).2
        ((le_sup_right : B ≤ A ⊔ B)
          ((mem_binaryAffineFlatPoints B z).1 hzB))
  · rw [card_binaryAffineFlatPoints C hCData.1, hCData.2,
      Finset.card_union_of_disjoint hdisjoint,
      card_binaryAffineFlatPoints A hAne,
      card_binaryAffineFlatPoints B hBne,
      hAdirection, hBdirection, hRrank]
    norm_num

private theorem indicator_twoCosetAffineThreeFlat
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 2)
    (hxy : R.mkQ x ≠ R.mkQ y) :
    binaryAffineFlatIndicator (twoCosetAffineThreeFlat R x y) =
      binaryAffineFlatIndicator (FABL.binaryAffineSubspace R x) +
        binaryAffineFlatIndicator (FABL.binaryAffineSubspace R y) := by
  have hpoints := points_twoCosetAffineThreeFlat R x y hRrank hxy
  have hdisjoint : Disjoint
      (binaryAffineFlatPoints (FABL.binaryAffineSubspace R x))
      (binaryAffineFlatPoints (FABL.binaryAffineSubspace R y)) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    apply hxy
    have hzx' : R.mkQ z = R.mkQ x :=
      (mem_binaryAffineSubspace_iff_mkQ_eq R x z).1
        ((mem_binaryAffineFlatPoints _ z).1 hzx)
    have hzy' : R.mkQ z = R.mkQ y :=
      (mem_binaryAffineSubspace_iff_mkQ_eq R y z).1
        ((mem_binaryAffineFlatPoints _ z).1 hzy)
    exact hzx'.symm.trans hzy'
  exact binaryAffineFlatIndicator_eq_add_of_points_eq_union
    (FABL.binaryAffineSubspace R x) (FABL.binaryAffineSubspace R y)
      (twoCosetAffineThreeFlat R x y) hpoints hdisjoint

private theorem mem_twoCosetAffineThreeFlat_iff
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y z : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 2)
    (hxy : R.mkQ x ≠ R.mkQ y) :
    z ∈ twoCosetAffineThreeFlat R x y ↔
      R.mkQ z = R.mkQ x ∨ R.mkQ z = R.mkQ y := by
  have hpoints := Finset.ext_iff.mp
    (points_twoCosetAffineThreeFlat R x y hRrank hxy) z
  simpa only [mem_binaryAffineFlatPoints, Finset.mem_union,
    mem_binaryAffineSubspace_iff_mkQ_eq] using hpoints

private theorem image_mkQ_points_twoCosetAffineThreeFlat
    (R : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 2)
    (hxy : R.mkQ x ≠ R.mkQ y) :
    (binaryAffineFlatPoints (twoCosetAffineThreeFlat R x y)).image R.mkQ =
      {R.mkQ x, R.mkQ y} := by
  ext q
  constructor
  · intro hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    have hzFlat := (mem_binaryAffineFlatPoints _ z).1 hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (mem_twoCosetAffineThreeFlat_iff R x y z hRrank hxy).1 hzFlat
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · apply Finset.mem_image.mpr
      refine ⟨x, (mem_binaryAffineFlatPoints _ x).2 ?_, rfl⟩
      exact (mem_twoCosetAffineThreeFlat_iff R x y x hRrank hxy).2
        (Or.inl rfl)
    · apply Finset.mem_image.mpr
      refine ⟨y, (mem_binaryAffineFlatPoints _ y).2 ?_, rfl⟩
      exact (mem_twoCosetAffineThreeFlat_iff R x y y hRrank hxy).2
        (Or.inr rfl)

private theorem weightSixteenRepresentationFirstCosets_surjOn_typeB_fiber
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    Set.SurjOn (weightSixteenRepresentationFirstCosets h)
      (weightSixteenRepresentationFiber h : Set
        (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
          AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)))
      ((zeroDerivativeSupportCosets h).powersetCard 2 : Set
        (Finset (FABL.F₂Cube n ⧸ zeroDerivativeKernel h))) := by
  classical
  intro t ht
  have htFin : t ∈ (zeroDerivativeSupportCosets h).powersetCard 2 := ht
  have htData := Finset.mem_powersetCard.mp htFin
  let R := zeroDerivativeKernel h
  let qs := zeroDerivativeSupportCosets h
  let u := qs \ t
  have hqscard : qs.card = 4 :=
    card_zeroDerivativeSupportCosets_of_mem_typeB h hh
  have hucard : u.card = 2 := by
    dsimp only [u]
    rw [Finset.card_sdiff_of_subset htData.1, hqscard, htData.2]
  obtain ⟨q₀, q₁, hq01, htEq⟩ := Finset.card_eq_two.mp htData.2
  obtain ⟨q₂, q₃, hq23, huEq⟩ := Finset.card_eq_two.mp hucard
  have hq0t : q₀ ∈ t := by simp [htEq]
  have hq1t : q₁ ∈ t := by simp [htEq]
  have hq2u : q₂ ∈ u := by simp [huEq]
  have hq3u : q₃ ∈ u := by simp [huEq]
  have hq2notT : q₂ ∉ t := (Finset.mem_sdiff.mp hq2u).2
  have hq3notT : q₃ ∉ t := (Finset.mem_sdiff.mp hq3u).2
  have hq02 : q₀ ≠ q₂ := by
    intro heq
    exact hq2notT (heq ▸ hq0t)
  have hq03 : q₀ ≠ q₃ := by
    intro heq
    exact hq3notT (heq ▸ hq0t)
  have hq12 : q₁ ≠ q₂ := by
    intro heq
    exact hq2notT (heq ▸ hq1t)
  have hq13 : q₁ ≠ q₃ := by
    intro heq
    exact hq3notT (heq ▸ hq1t)
  let x₀ : FABL.F₂Cube n := Quotient.out q₀
  let x₁ : FABL.F₂Cube n := Quotient.out q₁
  let x₂ : FABL.F₂Cube n := Quotient.out q₂
  let x₃ : FABL.F₂Cube n := Quotient.out q₃
  have hx₀ : R.mkQ x₀ = q₀ := Submodule.Quotient.mk_out q₀
  have hx₁ : R.mkQ x₁ = q₁ := Submodule.Quotient.mk_out q₁
  have hx₂ : R.mkQ x₂ = q₂ := Submodule.Quotient.mk_out q₂
  have hx₃ : R.mkQ x₃ = q₃ := Submodule.Quotient.mk_out q₃
  have h01 : R.mkQ x₀ ≠ R.mkQ x₁ := by
    intro heq
    exact hq01 (hx₀.symm.trans (heq.trans hx₁))
  have h23 : R.mkQ x₂ ≠ R.mkQ x₃ := by
    intro heq
    exact hq23 (hx₂.symm.trans (heq.trans hx₃))
  have h02 : R.mkQ x₀ ≠ R.mkQ x₂ := by
    intro heq
    exact hq02 (hx₀.symm.trans (heq.trans hx₂))
  have h03 : R.mkQ x₀ ≠ R.mkQ x₃ := by
    intro heq
    exact hq03 (hx₀.symm.trans (heq.trans hx₃))
  have h12 : R.mkQ x₁ ≠ R.mkQ x₂ := by
    intro heq
    exact hq12 (hx₁.symm.trans (heq.trans hx₂))
  have h13 : R.mkQ x₁ ≠ R.mkQ x₃ := by
    intro heq
    exact hq13 (hx₁.symm.trans (heq.trans hx₃))
  have hRrank : Module.finrank FABL.𝔽₂ R = 2 :=
    (Finset.mem_filter.mp hh).2
  let A := twoCosetAffineThreeFlat R x₀ x₁
  let B := twoCosetAffineThreeFlat R x₂ x₃
  have hAflat : A ∈ binaryAffineFlats 3 n :=
    twoCosetAffineThreeFlat_mem_flats R x₀ x₁ hRrank h01
  have hBflat : B ∈ binaryAffineFlats 3 n :=
    twoCosetAffineThreeFlat_mem_flats R x₂ x₃ hRrank h23
  have hpointsDisjoint : Disjoint (binaryAffineFlatPoints A)
      (binaryAffineFlatPoints B) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hzAData := (mem_twoCosetAffineThreeFlat_iff
      R x₀ x₁ z hRrank h01).1
        ((mem_binaryAffineFlatPoints A z).1 hzA)
    have hzBData := (mem_twoCosetAffineThreeFlat_iff
      R x₂ x₃ z hRrank h23).1
        ((mem_binaryAffineFlatPoints B z).1 hzB)
    rcases hzAData with hz0 | hz1 <;>
      rcases hzBData with hz2 | hz3
    · exact h02 (hz0.symm.trans hz2)
    · exact h03 (hz0.symm.trans hz3)
    · exact h12 (hz1.symm.trans hz2)
    · exact h13 (hz1.symm.trans hz3)
  have hinf : A ⊓ B = ⊥ := by
    by_contra hne
    obtain ⟨z, hz⟩ := (AffineSubspace.nonempty_iff_ne_bot (A ⊓ B)).2 hne
    exact (Finset.disjoint_left.mp hpointsDisjoint)
      ((mem_binaryAffineFlatPoints A z).2 hz.1)
      ((mem_binaryAffineFlatPoints B z).2 hz.2)
  have hpair : (A, B) ∈ disjointBinaryAffineThreeFlatPairs n := by
    simp only [disjointBinaryAffineThreeFlatPairs, Finset.mem_filter]
    constructor
    · change (A, B) ∈ (binaryAffineFlats 3 n).product
        (binaryAffineFlats 3 n)
      exact Finset.mem_product.mpr ⟨hAflat, hBflat⟩
    · exact hinf
  have hpartition : t ∪ u = qs := by
    exact Finset.union_sdiff_of_subset htData.1
  have hword : weightSixteenRepresentationWord A B = h := by
    funext z
    have hzA : z ∈ A ↔ R.mkQ z ∈ t := by
      rw [mem_twoCosetAffineThreeFlat_iff R x₀ x₁ z hRrank h01,
        htEq, hx₀, hx₁]
      simp
    have hzB : z ∈ B ↔ R.mkQ z ∈ u := by
      rw [mem_twoCosetAffineThreeFlat_iff R x₂ x₃ z hRrank h23,
        huEq, hx₂, hx₃]
      simp
    have hzSupport : h z = 1 ↔ z ∈ A ∨ z ∈ B := by
      calc
        h z = 1 ↔ R.mkQ z ∈ qs := by
          dsimp only [qs, R, zeroDerivativeSupportCosets]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            zeroDerivativeKernelQuotientFunction_mkQ]
        _ ↔ R.mkQ z ∈ t ∪ u := by rw [hpartition]
        _ ↔ R.mkQ z ∈ t ∨ R.mkQ z ∈ u := Finset.mem_union
        _ ↔ z ∈ A ∨ z ∈ B := or_congr hzA.symm hzB.symm
    have hzNotBoth : ¬(z ∈ A ∧ z ∈ B) := by
      intro hz
      exact (Finset.disjoint_left.mp hpointsDisjoint)
        ((mem_binaryAffineFlatPoints A z).2 hz.1)
        ((mem_binaryAffineFlatPoints B z).2 hz.2)
    simp only [weightSixteenRepresentationWord, Pi.add_apply,
      binaryAffineFlatIndicator]
    by_cases hza : z ∈ A <;> by_cases hzb : z ∈ B
    · exact (hzNotBoth ⟨hza, hzb⟩).elim
    · have hzOne : h z = 1 := hzSupport.2 (Or.inl hza)
      simp [hza, hzb, hzOne]
    · have hzOne : h z = 1 := hzSupport.2 (Or.inr hzb)
      simp [hza, hzb, hzOne]
    · have hzNotOne : h z ≠ 1 := by
        intro hzOne
        exact (hzSupport.1 hzOne).elim hza hzb
      have hzZero : h z = 0 := by
        by_contra hzNeZero
        exact hzNotOne (Fin.eq_one_of_ne_zero _ hzNeZero)
      simp [hza, hzb, hzZero]
  have hpFiber : (A, B) ∈ weightSixteenRepresentationFiber h := by
    simp only [weightSixteenRepresentationFiber, Finset.mem_filter]
    exact ⟨hpair, hword⟩
  refine ⟨(A, B), hpFiber, ?_⟩
  change (binaryAffineFlatPoints A).image R.mkQ = t
  dsimp only [A]
  rw [image_mkQ_points_twoCosetAffineThreeFlat
    R x₀ x₁ hRrank h01, hx₀, hx₁, htEq]

/-- A type-`b` word has exactly six ordered disjoint-three-flat
representations. -/
theorem card_weightSixteenRepresentationFiber_of_mem_typeBWords
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    (weightSixteenRepresentationFiber h).card = 6 := by
  have hlower := Finset.card_le_card_of_surjOn
    (weightSixteenRepresentationFirstCosets h)
    (weightSixteenRepresentationFirstCosets_surjOn_typeB_fiber h hh)
  have hpowerset : ((zeroDerivativeSupportCosets h).powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard,
      card_zeroDerivativeSupportCosets_of_mem_typeB h hh]
    norm_num [Nat.choose]
  rw [hpowerset] at hlower
  exact Nat.le_antisymm
    (card_weightSixteenRepresentationFiber_typeB_le_six h hh) hlower

private theorem support_weightSixteenRepresentationWord_eq_union
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ disjointBinaryAffineThreeFlatPairs n) :
    support (weightSixteenRepresentationWord p.1 p.2) =
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 := by
  classical
  have hdisjoint := weightSixteenClassificationPairPointSetsDisjoint hp
  ext x
  have hnotBoth : ¬(x ∈ p.1 ∧ x ∈ p.2) := by
    intro hboth
    exact (Finset.disjoint_left.mp hdisjoint)
      ((mem_binaryAffineFlatPoints p.1 x).2 hboth.1)
      ((mem_binaryAffineFlatPoints p.2 x).2 hboth.2)
  simp only [support, FABL.f₂OneSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, weightSixteenRepresentationWord,
    Pi.add_apply, binaryAffineFlatIndicator, Finset.mem_union,
    mem_binaryAffineFlatPoints]
  by_cases hxFirst : x ∈ p.1 <;> by_cases hxSecond : x ∈ p.2
  · exact (hnotBoth ⟨hxFirst, hxSecond⟩).elim
  · simp [hxFirst, hxSecond]
  · simp [hxFirst, hxSecond]
  · simp [hxFirst, hxSecond]

private theorem support_eq_union_of_mem_weightSixteenFiber
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    support h =
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 := by
  have hpData := Finset.mem_filter.mp hp
  rw [← hpData.2]
  exact support_weightSixteenRepresentationWord_eq_union hpData.1

private theorem swap_mem_weightSixteenRepresentationFiber
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    (p.2, p.1) ∈ weightSixteenRepresentationFiber h := by
  classical
  have hpData := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  constructor
  · have hpPair : p ∈ binaryAffineThreeFlatPairs n ∧ p.1 ⊓ p.2 = ⊥ := by
      simpa only [disjointBinaryAffineThreeFlatPairs,
        Finset.mem_filter] using hpData.1
    have hproduct := Finset.mem_product.mp hpPair.1
    rw [disjointBinaryAffineThreeFlatPairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hproduct.2, hproduct.1⟩,
      by rw [inf_comm, hpPair.2]⟩
  · simpa only [weightSixteenRepresentationWord, add_comm] using hpData.2

private theorem first_ne_second_of_mem_weightSixteenFiber
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    p.1 ≠ p.2 := by
  intro heq
  have hpData := Finset.mem_filter.mp hp
  have hmeet := (weightSixteenClassificationDisjointPairData hpData.1).2.2
  rw [heq, inf_idem] at hmeet
  have hsecondData :=
    (weightSixteenClassificationDisjointPairData hpData.1).2.1
  have hnonbot : p.2 ≠ ⊥ := by
    have hsecondData' : p.2 ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ p.2.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter,
        Finset.mem_univ, true_and] using hsecondData
    exact hsecondData'.1
  exact hnonbot hmeet

private theorem affineThreeFlat_eq_of_points_subset
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hA : A ∈ binaryAffineFlats 3 n)
    (hB : B ∈ binaryAffineFlats 3 n)
    (hsubset : binaryAffineFlatPoints A ⊆ binaryAffineFlatPoints B) :
    A = B := by
  have hAData : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hBData : B ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ B.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hB
  have hpoints : binaryAffineFlatPoints A = binaryAffineFlatPoints B := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [card_binaryAffineFlatPoints A hAData.1,
      card_binaryAffineFlatPoints B hBData.1,
      hAData.2, hBData.2]
  ext x
  have hx := Finset.ext_iff.mp hpoints x
  simpa only [mem_binaryAffineFlatPoints] using hx

private theorem weightSixteenFiber_pair_eq_of_first_eq
    (h : BooleanFunction n)
    {p q : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hq : q ∈ weightSixteenRepresentationFiber h)
    (hfirst : p.1 = q.1) :
    p = q := by
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  have hpPair := weightSixteenClassificationDisjointPairData hpData.1
  have hqPair := weightSixteenClassificationDisjointPairData hqData.1
  have hunion : binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 =
      binaryAffineFlatPoints q.1 ∪ binaryAffineFlatPoints q.2 := by
    rw [← support_eq_union_of_mem_weightSixteenFiber h hp,
      ← support_eq_union_of_mem_weightSixteenFiber h hq]
  have hsecondSubset : binaryAffineFlatPoints p.2 ⊆
      binaryAffineFlatPoints q.2 := by
    intro x hxSecond
    have hxUnion : x ∈ binaryAffineFlatPoints q.1 ∪
        binaryAffineFlatPoints q.2 := by
      rw [← hunion]
      exact Finset.mem_union_right _ hxSecond
    rcases Finset.mem_union.mp hxUnion with hxFirst | hxSecond'
    · have hxPFirst : x ∈ binaryAffineFlatPoints p.1 := by
        rw [hfirst]
        exact hxFirst
      exact (Finset.disjoint_left.mp
        (weightSixteenClassificationPairPointSetsDisjoint hpData.1))
          hxPFirst hxSecond |>.elim
    · exact hxSecond'
  apply Prod.ext hfirst
  exact affineThreeFlat_eq_of_points_subset hpPair.2.1 hqPair.2.1
    hsecondSubset

private theorem weightSixteenFiber_pair_eq_of_second_eq
    (h : BooleanFunction n)
    {p q : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hq : q ∈ weightSixteenRepresentationFiber h)
    (hsecond : p.2 = q.2) :
    p = q := by
  have hpSwap := swap_mem_weightSixteenRepresentationFiber h hp
  have hqSwap := swap_mem_weightSixteenRepresentationFiber h hq
  have hswap := weightSixteenFiber_pair_eq_of_first_eq h hpSwap hqSwap hsecond
  apply Prod.ext
  · exact congrArg Prod.snd hswap
  · exact congrArg Prod.fst hswap

private theorem binaryAffineFlatPoints_inf_eq_inter
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineFlatPoints (A ⊓ B) =
      binaryAffineFlatPoints A ∩ binaryAffineFlatPoints B := by
  ext x
  simp only [mem_binaryAffineFlatPoints, Finset.mem_inter,
    AffineSubspace.mem_inf_iff]

private theorem card_firstFlat_inter_firstFlat_eq_four_of_cross
    (h : BooleanFunction n)
    {p q : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hq : q ∈ weightSixteenRepresentationFiber h)
    (hqFirstNeSecond : q.1 ≠ p.2)
    (hqSecondNeSecond : q.2 ≠ p.2) :
    (binaryAffineFlatPoints p.1 ∩
      binaryAffineFlatPoints q.1).card = 4 := by
  classical
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  have hpPair := weightSixteenClassificationDisjointPairData hpData.1
  have hqPair := weightSixteenClassificationDisjointPairData hqData.1
  have hpFirstData : p.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.1.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpPair.1
  have hunion : binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 =
      binaryAffineFlatPoints q.1 ∪ binaryAffineFlatPoints q.2 := by
    rw [← support_eq_union_of_mem_weightSixteenFiber h hp,
      ← support_eq_union_of_mem_weightSixteenFiber h hq]
  have hfirstInterNonempty :
      (binaryAffineFlatPoints p.1 ∩
        binaryAffineFlatPoints q.1).Nonempty := by
    by_contra hnot
    have hempty : binaryAffineFlatPoints p.1 ∩
        binaryAffineFlatPoints q.1 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    have hsubset : binaryAffineFlatPoints q.1 ⊆
        binaryAffineFlatPoints p.2 := by
      intro x hxq
      have hxUnion : x ∈ binaryAffineFlatPoints p.1 ∪
          binaryAffineFlatPoints p.2 := by
        rw [hunion]
        exact Finset.mem_union_left _ hxq
      rcases Finset.mem_union.mp hxUnion with hxp | hxp
      · have hxInter : x ∈ binaryAffineFlatPoints p.1 ∩
            binaryAffineFlatPoints q.1 := Finset.mem_inter.mpr ⟨hxp, hxq⟩
        rw [hempty] at hxInter
        exact (Finset.notMem_empty x hxInter).elim
      · exact hxp
    exact hqFirstNeSecond
      (affineThreeFlat_eq_of_points_subset hqPair.1 hpPair.2.1 hsubset)
  have hsecondInterNonempty :
      (binaryAffineFlatPoints p.1 ∩
        binaryAffineFlatPoints q.2).Nonempty := by
    by_contra hnot
    have hempty : binaryAffineFlatPoints p.1 ∩
        binaryAffineFlatPoints q.2 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    have hsubset : binaryAffineFlatPoints q.2 ⊆
        binaryAffineFlatPoints p.2 := by
      intro x hxq
      have hxUnion : x ∈ binaryAffineFlatPoints p.1 ∪
          binaryAffineFlatPoints p.2 := by
        rw [hunion]
        exact Finset.mem_union_right _ hxq
      rcases Finset.mem_union.mp hxUnion with hxp | hxp
      · have hxInter : x ∈ binaryAffineFlatPoints p.1 ∩
            binaryAffineFlatPoints q.2 := Finset.mem_inter.mpr ⟨hxp, hxq⟩
        rw [hempty] at hxInter
        exact (Finset.notMem_empty x hxInter).elim
      · exact hxp
    exact hqSecondNeSecond
      (affineThreeFlat_eq_of_points_subset hqPair.2.1 hpPair.2.1 hsubset)
  have hpartition : binaryAffineFlatPoints p.1 =
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.1) ∪
        (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.2) := by
    ext x
    constructor
    · intro hxp
      have hxUnion : x ∈ binaryAffineFlatPoints q.1 ∪
          binaryAffineFlatPoints q.2 := by
        rw [← hunion]
        exact Finset.mem_union_left _ hxp
      rcases Finset.mem_union.mp hxUnion with hxq | hxq
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxp, hxq⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxp, hxq⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
  have hinterDisjoint : Disjoint
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.1)
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.2) := by
    rw [Finset.disjoint_left]
    intro x hxFirst hxSecond
    exact (Finset.disjoint_left.mp
      (weightSixteenClassificationPairPointSetsDisjoint hqData.1))
        (Finset.mem_inter.mp hxFirst).2
        (Finset.mem_inter.mp hxSecond).2
  have hsum :
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.1).card +
          (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.2).card = 8 := by
    calc
      _ = ((binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.1) ∪
          (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.2)).card :=
        (Finset.card_union_of_disjoint hinterDisjoint).symm
      _ = (binaryAffineFlatPoints p.1).card := by rw [← hpartition]
      _ = 8 := by
        rw [card_binaryAffineFlatPoints p.1 hpFirstData.1,
          hpFirstData.2]
        norm_num
  have hfirstInfNe : p.1 ⊓ q.1 ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hfirstInterNonempty
    intro hbot
    have hxInf : x ∈ p.1 ⊓ q.1 :=
      (AffineSubspace.mem_inf_iff x p.1 q.1).2
        ⟨(mem_binaryAffineFlatPoints p.1 x).1 (Finset.mem_inter.mp hx).1,
          (mem_binaryAffineFlatPoints q.1 x).1 (Finset.mem_inter.mp hx).2⟩
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hxInf
    exact hxInf
  have hsecondInfNe : p.1 ⊓ q.2 ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hsecondInterNonempty
    intro hbot
    have hxInf : x ∈ p.1 ⊓ q.2 :=
      (AffineSubspace.mem_inf_iff x p.1 q.2).2
        ⟨(mem_binaryAffineFlatPoints p.1 x).1 (Finset.mem_inter.mp hx).1,
          (mem_binaryAffineFlatPoints q.2 x).1 (Finset.mem_inter.mp hx).2⟩
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hxInf
    exact hxInf
  have hfirstCard :
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.1).card =
        2 ^ Module.finrank FABL.𝔽₂ (p.1 ⊓ q.1).direction := by
    rw [← binaryAffineFlatPoints_inf_eq_inter,
      card_binaryAffineFlatPoints (p.1 ⊓ q.1) hfirstInfNe]
  have hsecondCard :
      (binaryAffineFlatPoints p.1 ∩ binaryAffineFlatPoints q.2).card =
        2 ^ Module.finrank FABL.𝔽₂ (p.1 ⊓ q.2).direction := by
    rw [← binaryAffineFlatPoints_inf_eq_inter,
      card_binaryAffineFlatPoints (p.1 ⊓ q.2) hsecondInfNe]
  have hfirstRank : Module.finrank FABL.𝔽₂ (p.1 ⊓ q.1).direction ≤ 3 := by
    have hle := Submodule.finrank_mono
      (AffineSubspace.direction_le (inf_le_left : p.1 ⊓ q.1 ≤ p.1))
    rwa [hpFirstData.2] at hle
  have hsecondRank : Module.finrank FABL.𝔽₂ (p.1 ⊓ q.2).direction ≤ 3 := by
    have hle := Submodule.finrank_mono
      (AffineSubspace.direction_le (inf_le_left : p.1 ⊓ q.2 ≤ p.1))
    rwa [hpFirstData.2] at hle
  interval_cases hfirstRankEq :
      Module.finrank FABL.𝔽₂ (p.1 ⊓ q.1).direction <;>
    interval_cases hsecondRankEq :
      Module.finrank FABL.𝔽₂ (p.1 ⊓ q.2).direction <;>
    norm_num [hfirstRankEq, hsecondRankEq] at hfirstCard hsecondCard <;>
    omega

private theorem finrank_direction_inf_eq_two_of_card_inter_eq_four
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hA : A ∈ binaryAffineFlats 3 n)
    (hcard : (binaryAffineFlatPoints A ∩
      binaryAffineFlatPoints B).card = 4) :
    Module.finrank FABL.𝔽₂ (A ⊓ B).direction = 2 := by
  have hAData : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hnonempty :
      (binaryAffineFlatPoints A ∩ binaryAffineFlatPoints B).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hinfNe : A ⊓ B ≠ ⊥ := by
    obtain ⟨x, hx⟩ := hnonempty
    intro hbot
    have hxInf : x ∈ A ⊓ B :=
      (AffineSubspace.mem_inf_iff x A B).2
        ⟨(mem_binaryAffineFlatPoints A x).1 (Finset.mem_inter.mp hx).1,
          (mem_binaryAffineFlatPoints B x).1 (Finset.mem_inter.mp hx).2⟩
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hxInf
    exact hxInf
  have hpow : 4 = 2 ^ Module.finrank FABL.𝔽₂ (A ⊓ B).direction := by
    calc
      4 = (binaryAffineFlatPoints A ∩
          binaryAffineFlatPoints B).card := hcard.symm
      _ = (binaryAffineFlatPoints (A ⊓ B)).card := by
        rw [binaryAffineFlatPoints_inf_eq_inter]
      _ = 2 ^ Module.finrank FABL.𝔽₂ (A ⊓ B).direction :=
        card_binaryAffineFlatPoints (A ⊓ B) hinfNe
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  calc
    2 ^ Module.finrank FABL.𝔽₂ (A ⊓ B).direction = 4 := hpow.symm
    _ = 2 ^ 2 := by norm_num

private theorem direction_firstInf_eq_secondInf_of_four_four_partition
    {A C D : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hA : A ∈ binaryAffineFlats 3 n)
    (hCDdisjoint : Disjoint (binaryAffineFlatPoints C)
      (binaryAffineFlatPoints D))
    (hACcard : (binaryAffineFlatPoints A ∩
      binaryAffineFlatPoints C).card = 4)
    (hADcard : (binaryAffineFlatPoints A ∩
      binaryAffineFlatPoints D).card = 4) :
    (A ⊓ C).direction = (A ⊓ D).direction := by
  classical
  have hAData : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hACrank :=
    finrank_direction_inf_eq_two_of_card_inter_eq_four hA hACcard
  have hADrank :=
    finrank_direction_inf_eq_two_of_card_inter_eq_four hA hADcard
  by_contra hne
  have hACstrict : (A ⊓ C).direction <
      (A ⊓ C).direction ⊔ (A ⊓ D).direction := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    have hADle : (A ⊓ D).direction ≤ (A ⊓ C).direction := by
      calc
        (A ⊓ D).direction ≤
            (A ⊓ C).direction ⊔ (A ⊓ D).direction := le_sup_right
        _ = (A ⊓ C).direction := heq.symm
    have heqDirections : (A ⊓ D).direction = (A ⊓ C).direction :=
      Submodule.eq_of_le_of_finrank_eq hADle (by rw [hADrank, hACrank])
    exact hne heqDirections.symm
  have hsupLe : (A ⊓ C).direction ⊔ (A ⊓ D).direction ≤ A.direction :=
    sup_le
      (AffineSubspace.direction_le (inf_le_left : A ⊓ C ≤ A))
      (AffineSubspace.direction_le (inf_le_left : A ⊓ D ≤ A))
  have hsupRankLower : 3 ≤ Module.finrank FABL.𝔽₂
      ↥((A ⊓ C).direction ⊔ (A ⊓ D).direction) := by
    have hlt := Submodule.finrank_lt_finrank_of_lt hACstrict
    rw [hACrank] at hlt
    omega
  have hsupRankUpper : Module.finrank FABL.𝔽₂
      ↥((A ⊓ C).direction ⊔ (A ⊓ D).direction) ≤ 3 := by
    have hle := Submodule.finrank_mono hsupLe
    rwa [hAData.2] at hle
  have hsupRank : Module.finrank FABL.𝔽₂
      ↥((A ⊓ C).direction ⊔ (A ⊓ D).direction) = 3 := by omega
  have hsupEq : (A ⊓ C).direction ⊔ (A ⊓ D).direction = A.direction :=
    Submodule.eq_of_le_of_finrank_eq hsupLe (by rw [hsupRank, hAData.2])
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hACcard]; omega :
    0 < (binaryAffineFlatPoints A ∩ binaryAffineFlatPoints C).card)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hADcard]; omega :
    0 < (binaryAffineFlatPoints A ∩ binaryAffineFlatPoints D).card)
  have hxInf : x ∈ A ⊓ C :=
    (AffineSubspace.mem_inf_iff x A C).2
      ⟨(mem_binaryAffineFlatPoints A x).1 (Finset.mem_inter.mp hx).1,
        (mem_binaryAffineFlatPoints C x).1 (Finset.mem_inter.mp hx).2⟩
  have hyInf : y ∈ A ⊓ D :=
    (AffineSubspace.mem_inf_iff y A D).2
      ⟨(mem_binaryAffineFlatPoints A y).1 (Finset.mem_inter.mp hy).1,
        (mem_binaryAffineFlatPoints D y).1 (Finset.mem_inter.mp hy).2⟩
  have hyxA : y + x ∈ A.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction
      ((AffineSubspace.mem_inf_iff y A D).1 hyInf).1
      ((AffineSubspace.mem_inf_iff x A C).1 hxInf).1
    simpa only [vsub_eq_sub, sub_eq_add_neg, ZModModule.neg_eq_self] using hvsub
  have hyxSup : y + x ∈
      (A ⊓ C).direction ⊔ (A ⊓ D).direction := by
    rw [hsupEq]
    exact hyxA
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hyxSup
  let z := u + x
  have hzFirst : z ∈ A ⊓ C := by
    exact AffineSubspace.vadd_mem_of_mem_direction hu hxInf
  have hzEq : u + x = v + y := by
    calc
      u + x = u + x + (v + v) := by
        rw [ZModModule.add_self, add_zero]
      _ = (u + v) + (v + x) := by abel
      _ = (y + x) + (v + x) := by rw [huv]
      _ = y + v + (x + x) := by abel
      _ = v + y := by rw [ZModModule.add_self, add_zero, add_comm]
  have hzSecond : z ∈ A ⊓ D := by
    change u + x ∈ A ⊓ D
    rw [hzEq]
    exact AffineSubspace.vadd_mem_of_mem_direction hv hyInf
  exact (Finset.disjoint_left.mp hCDdisjoint)
    ((mem_binaryAffineFlatPoints C z).2
      ((AffineSubspace.mem_inf_iff z A C).1 hzFirst).2)
    ((mem_binaryAffineFlatPoints D z).2
      ((AffineSubspace.mem_inf_iff z A D).1 hzSecond).2)

private theorem exists_cross_weightSixteenRepresentation_of_two_lt_card
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hcard : 2 < (weightSixteenRepresentationFiber h).card) :
    ∃ q ∈ weightSixteenRepresentationFiber h,
      q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2 := by
  classical
  have hpSwap := swap_mem_weightSixteenRepresentationFiber h hp
  have hpFirstNeSecond := first_ne_second_of_mem_weightSixteenFiber h hp
  have hpNeSwap : p ≠ (p.2, p.1) := by
    intro heq
    exact hpFirstNeSecond (congrArg Prod.fst heq)
  have hpairCard : ({p, (p.2, p.1)} : Finset
      (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))).card = 2 := by
    rw [Finset.card_pair hpNeSwap]
  have hpairLt : ({p, (p.2, p.1)} : Finset
      (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))).card <
        (weightSixteenRepresentationFiber h).card := by
    rwa [hpairCard]
  obtain ⟨q, hq, hqNotPair⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hpairLt
  have hqNeP : q ≠ p := by
    intro heq
    apply hqNotPair
    simp [heq]
  have hqNeSwap : q ≠ (p.2, p.1) := by
    intro heq
    apply hqNotPair
    simp [heq]
  have hqFirstNePFirst : q.1 ≠ p.1 := by
    intro heq
    apply hqNeP
    exact (weightSixteenFiber_pair_eq_of_first_eq h hp hq heq.symm).symm
  have hqFirstNePSecond : q.1 ≠ p.2 := by
    intro heq
    apply hqNeSwap
    exact weightSixteenFiber_pair_eq_of_first_eq h hpSwap hq heq.symm |>.symm
  have hqSecondNePFirst : q.2 ≠ p.1 := by
    intro heq
    apply hqNeSwap
    exact weightSixteenFiber_pair_eq_of_second_eq h hq hpSwap heq
  have hqSecondNePSecond : q.2 ≠ p.2 := by
    intro heq
    apply hqNeP
    exact weightSixteenFiber_pair_eq_of_second_eq h hq hp heq
  exact ⟨q, hq, hqFirstNePFirst, hqFirstNePSecond,
    hqSecondNePFirst, hqSecondNePSecond⟩

private theorem two_le_finrank_zeroDerivativeKernel_of_two_lt_fiber_card
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hcard : 2 < (weightSixteenRepresentationFiber h).card) :
    2 ≤ Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) := by
  classical
  obtain ⟨q, hq, hqFirstNePFirst, hqFirstNePSecond,
      hqSecondNePFirst, hqSecondNePSecond⟩ :=
    exists_cross_weightSixteenRepresentation_of_two_lt_card h hp hcard
  have hpData := Finset.mem_filter.mp hp
  have hqData := Finset.mem_filter.mp hq
  have hpPair := weightSixteenClassificationDisjointPairData hpData.1
  have hqPair := weightSixteenClassificationDisjointPairData hqData.1
  have hpSwap := swap_mem_weightSixteenRepresentationFiber h hp
  have hACcard := card_firstFlat_inter_firstFlat_eq_four_of_cross
    h hp hq hqFirstNePSecond hqSecondNePSecond
  have hBCcard := card_firstFlat_inter_firstFlat_eq_four_of_cross
    h hpSwap hq hqFirstNePFirst hqSecondNePFirst
  have hCcolumn := direction_firstInf_eq_secondInf_of_four_four_partition
    hqPair.1
    (weightSixteenClassificationPairPointSetsDisjoint hpData.1)
    (by simpa only [Finset.inter_comm] using hACcard)
    (by simpa only [Finset.inter_comm] using hBCcard)
  let R := (p.1 ⊓ q.1).direction
  have hRrank : Module.finrank FABL.𝔽₂ R = 2 := by
    exact finrank_direction_inf_eq_two_of_card_inter_eq_four hpPair.1 hACcard
  have hRBC : R = (p.2 ⊓ q.1).direction := by
    calc
      R = (q.1 ⊓ p.1).direction := by
        simp only [R, inf_comm]
      _ = (q.1 ⊓ p.2).direction := hCcolumn
      _ = (p.2 ⊓ q.1).direction := by rw [inf_comm]
  have hRleFirst : R ≤ p.1.direction := by
    exact AffineSubspace.direction_le (inf_le_left : p.1 ⊓ q.1 ≤ p.1)
  have hRleSecond : R ≤ p.2.direction := by
    rw [hRBC]
    exact AffineSubspace.direction_le (inf_le_left : p.2 ⊓ q.1 ≤ p.2)
  have hRleKernel : R ≤ zeroDerivativeKernel h := by
    intro r hr
    apply (mem_zeroDerivativeKernel h r).2
    intro x
    have hpWord := (Finset.mem_filter.mp hp).2
    rw [← hpWord]
    simp only [FABL.booleanDerivative, weightSixteenRepresentationWord,
      Pi.add_apply]
    rw [binaryAffineFlatIndicator_period_of_mem_direction
        p.1 r (hRleFirst hr) x,
      binaryAffineFlatIndicator_period_of_mem_direction
        p.2 r (hRleSecond hr) x]
    exact ZModModule.add_self _
  have hle := Submodule.finrank_mono hRleKernel
  rwa [hRrank] at hle

private theorem mem_typeA_of_parallel_weightSixteenRepresentation
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h)
    (hdirection : p.1.direction = p.2.direction) :
    h ∈ orderTwoWeightSixteenTypeAWords n := by
  classical
  have hpData := Finset.mem_filter.mp hp
  have hpPair := weightSixteenClassificationDisjointPairData hpData.1
  have hAData : p.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.1.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpPair.1
  have hBData : p.2 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.2.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpPair.2.1
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot p.1).2 hAData.1
  obtain ⟨b, hb⟩ := (AffineSubspace.nonempty_iff_ne_bot p.2).2 hBData.1
  have hbNotA : b ∉ p.1 := by
    intro hbA
    have hbMeet : b ∈ p.1 ⊓ p.2 :=
      (AffineSubspace.mem_inf_iff b p.1 p.2).2 ⟨hbA, hb⟩
    rw [hpPair.2.2, ← SetLike.mem_coe, AffineSubspace.bot_coe] at hbMeet
    exact hbMeet
  have hdifference : b -ᵥ a ∉ p.1.direction := by
    intro hdifference
    apply hbNotA
    simpa only [vsub_vadd] using
      AffineSubspace.vadd_mem_of_mem_direction hdifference ha
  let C := p.1 ⊔ p.2
  have haC : a ∈ C := (le_sup_left : p.1 ≤ p.1 ⊔ p.2) ha
  have hCneBot : C ≠ ⊥ := by
    intro hbot
    have := haC
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at this
    exact this
  have hCrank : Module.finrank FABL.𝔽₂ C.direction = 4 := by
    dsimp only [C]
    rw [AffineSubspace.direction_sup ha hb, ← hdirection, sup_idem,
      Submodule.finrank_sup_span_singleton hdifference, hAData.2]
  have hCcard : (binaryAffineFlatPoints C).card = 16 := by
    rw [card_binaryAffineFlatPoints C hCneBot, hCrank]
    norm_num
  have hdisjoint :=
    weightSixteenClassificationPairPointSetsDisjoint hpData.1
  have hunionCard :
      (binaryAffineFlatPoints p.1 ∪
        binaryAffineFlatPoints p.2).card = 16 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      card_binaryAffineFlatPoints p.1 hAData.1,
      card_binaryAffineFlatPoints p.2 hBData.1,
      hAData.2, hBData.2]
    norm_num
  have hpoints : binaryAffineFlatPoints C =
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with hxFirst | hxSecond
      · exact (mem_binaryAffineFlatPoints C x).2
          ((le_sup_left : p.1 ≤ p.1 ⊔ p.2)
            ((mem_binaryAffineFlatPoints p.1 x).1 hxFirst))
      · exact (mem_binaryAffineFlatPoints C x).2
          ((le_sup_right : p.2 ≤ p.1 ⊔ p.2)
            ((mem_binaryAffineFlatPoints p.2 x).1 hxSecond))
    · rw [hCcard, hunionCard]
  have hCflat : C ∈ binaryAffineFlats 4 n := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using And.intro hCneBot hCrank
  have hindicator := binaryAffineFlatIndicator_eq_add_of_points_eq_union
    p.1 p.2 C hpoints hdisjoint
  have hfunction : h = binaryAffineFlatIndicator C := by
    calc
      h = weightSixteenRepresentationWord p.1 p.2 := hpData.2.symm
      _ = binaryAffineFlatIndicator p.1 +
          binaryAffineFlatIndicator p.2 := rfl
      _ = binaryAffineFlatIndicator C := hindicator.symm
  rw [orderTwoWeightSixteenTypeAWords, Finset.mem_image]
  exact ⟨C, hCflat, hfunction.symm⟩

private theorem finrank_zeroDerivativeKernel_le_two_of_nonTypeA_fiber
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hnotA : h ∉ orderTwoWeightSixteenTypeAWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) ≤ 2 := by
  have hpData := Finset.mem_filter.mp hp
  have hpPair := weightSixteenClassificationDisjointPairData hpData.1
  have hfirstRank : Module.finrank FABL.𝔽₂ p.1.direction = 3 := by
    exact (by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpPair.1 :
          p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 3).2
  have hsecondRank : Module.finrank FABL.𝔽₂ p.2.direction = 3 := by
    exact (by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpPair.2.1 :
          p.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.direction = 3).2
  have hleFirst := zeroDerivativeKernel_le_firstDirection_of_nonTypeA_fiber
    h hh hnotA hp
  have hpSwap := swap_mem_weightSixteenRepresentationFiber h hp
  have hleSecond : zeroDerivativeKernel h ≤ p.2.direction := by
    simpa only using
      zeroDerivativeKernel_le_firstDirection_of_nonTypeA_fiber
        h hh hnotA hpSwap
  have hkernelRankLeThree := Submodule.finrank_mono hleFirst
  rw [hfirstRank] at hkernelRankLeThree
  by_contra hnotLe
  have hkernelRank :
      Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 3 := by
    omega
  have hkernelFirst : zeroDerivativeKernel h = p.1.direction :=
    Submodule.eq_of_le_of_finrank_eq hleFirst (by
      rw [hkernelRank, hfirstRank])
  have hkernelSecond : zeroDerivativeKernel h = p.2.direction :=
    Submodule.eq_of_le_of_finrank_eq hleSecond (by
      rw [hkernelRank, hsecondRank])
  apply hnotA
  exact mem_typeA_of_parallel_weightSixteenRepresentation h hp
    (hkernelFirst.symm.trans hkernelSecond)

private theorem two_le_card_weightSixteenRepresentationFiber_of_mem
    (h : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    2 ≤ (weightSixteenRepresentationFiber h).card := by
  classical
  let q := (p.2, p.1)
  have hq : q ∈ weightSixteenRepresentationFiber h := by
    exact swap_mem_weightSixteenRepresentationFiber h hp
  have hpq : p ≠ q := by
    intro heq
    apply first_ne_second_of_mem_weightSixteenFiber h hp
    simpa only [q] using congrArg Prod.fst heq
  have hsubset : ({p, q} : Finset
      (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))) ⊆
      weightSixteenRepresentationFiber h := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  calc
    2 = ({p, q} : Finset
        (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
          AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))).card := by
      simp [hpq]
    _ ≤ (weightSixteenRepresentationFiber h).card :=
      Finset.card_le_card hsubset

private theorem card_weightSixteenRepresentationFiber_le_two_of_not_typeA_typeB
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hnotA : h ∉ orderTwoWeightSixteenTypeAWords n)
    (hnotB : h ∉ orderTwoWeightSixteenTypeBWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    (weightSixteenRepresentationFiber h).card ≤ 2 := by
  classical
  by_contra hnotLe
  have hcard : 2 < (weightSixteenRepresentationFiber h).card := by
    omega
  have hkernelLower :=
    two_le_finrank_zeroDerivativeKernel_of_two_lt_fiber_card h hp hcard
  have hkernelUpper :=
    finrank_zeroDerivativeKernel_le_two_of_nonTypeA_fiber h hh hnotA hp
  have hkernelRank :
      Module.finrank FABL.𝔽₂ (zeroDerivativeKernel h) = 2 := by
    omega
  apply hnotB
  rw [orderTwoWeightSixteenTypeBWords, Finset.mem_filter]
  exact ⟨hh, hkernelRank⟩

/-- A represented weight-sixteen dual word outside the two multiple-
representation families has only the two ordered representations obtained by
swapping its affine three-flats. -/
theorem card_weightSixteenRepresentationFiber_of_not_mem_typeA_typeB
    (h : BooleanFunction n)
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hnotA : h ∉ orderTwoWeightSixteenTypeAWords n)
    (hnotB : h ∉ orderTwoWeightSixteenTypeBWords n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ weightSixteenRepresentationFiber h) :
    (weightSixteenRepresentationFiber h).card = 2 :=
  Nat.le_antisymm
    (card_weightSixteenRepresentationFiber_le_two_of_not_typeA_typeB
      h hh hnotA hnotB hp)
    (two_le_card_weightSixteenRepresentationFiber_of_mem h hp)

private structure WeightSixteenTypeBWordWitness
    (h : BooleanFunction n) where
  a : FABL.F₂Cube n
  b : FABL.F₂Cube n
  x₀ : FABL.F₂Cube n
  x₁ : FABL.F₂Cube n
  x₂ : FABL.F₂Cube n
  x₃ : FABL.F₂Cube n
  word_eq : h =
    binaryAffineFlatIndicator
        (FABL.binaryAffineSubspace
          ((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) x₀) +
      binaryAffineFlatIndicator
        (FABL.binaryAffineSubspace
          ((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) x₁) +
      binaryAffineFlatIndicator
        (FABL.binaryAffineSubspace
          ((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) x₂) +
      binaryAffineFlatIndicator
        (FABL.binaryAffineSubspace
          ((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) x₃)

private noncomputable def weightSixteenTypeBWordWitness
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeBWords n) :
    WeightSixteenTypeBWordWitness h := by
  classical
  let R := zeroDerivativeKernel h
  let qh := zeroDerivativeKernelQuotientFunction h
  have hhData := Finset.mem_filter.mp hh
  have hweight : hammingWeight h = 16 := by
    have hdualData : h ∈ reedMuller (n - 3) n ∧
        hammingWeight h = 16 := by
      simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
        Finset.mem_filter, Finset.mem_univ, true_and] using hhData.1
    exact hdualData.2
  have hRrank : Module.finrank FABL.𝔽₂ R = 2 := hhData.2
  have hRcard : Nat.card R = 4 := by
    rw [FABL.card_submodule_eq_two_pow_finrank, hRrank]
    norm_num
  let qs : Finset (FABL.F₂Cube n ⧸ R) :=
    Finset.univ.filter fun q ↦ qh q = 1
  have hfactor := card_filter_mkQ_eq_card_mul_card_filter_weightSixteen
    R (fun q ↦ qh q = 1)
  have hleft :
      ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
        qh (R.mkQ x) = 1).card = 16 := by
    simpa only [R, qh, zeroDerivativeKernelQuotientFunction_mkQ,
      support, FABL.f₂OneSupport, hammingWeight_eq_card_support] using hweight
  have hqscard : qs.card = 4 := by
    have heq : 16 = 4 *
        ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
          qh q = 1).card := by
      calc
        16 = ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
            qh (R.mkQ x) = 1).card := hleft.symm
        _ = Nat.card R *
            ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
              qh q = 1).card := hfactor
        _ = 4 *
            ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
              qh q = 1).card := by rw [hRcard]
    change ((Finset.univ : Finset (FABL.F₂Cube n ⧸ R)).filter fun q ↦
      qh q = 1).card = 4
    omega
  let e : Fin 4 ≃ {q // q ∈ qs} := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, hqscard])
  let q₀ : FABL.F₂Cube n ⧸ R := (e 0).1
  let q₁ : FABL.F₂Cube n ⧸ R := (e 1).1
  let q₂ : FABL.F₂Cube n ⧸ R := (e 2).1
  let q₃ : FABL.F₂Cube n ⧸ R := (e 3).1
  have h01 : q₀ ≠ q₁ := by
    intro heq
    have : (0 : Fin 4) = 1 := e.injective (Subtype.ext heq)
    norm_num at this
  have h02 : q₀ ≠ q₂ := by
    intro heq
    have : (0 : Fin 4) = 2 := e.injective (Subtype.ext heq)
    exact (by decide : (0 : Fin 4) ≠ 2) this
  have h03 : q₀ ≠ q₃ := by
    intro heq
    have : (0 : Fin 4) = 3 := e.injective (Subtype.ext heq)
    exact (by decide : (0 : Fin 4) ≠ 3) this
  have h12 : q₁ ≠ q₂ := by
    intro heq
    have : (1 : Fin 4) = 2 := e.injective (Subtype.ext heq)
    exact (by decide : (1 : Fin 4) ≠ 2) this
  have h13 : q₁ ≠ q₃ := by
    intro heq
    have : (1 : Fin 4) = 3 := e.injective (Subtype.ext heq)
    exact (by decide : (1 : Fin 4) ≠ 3) this
  have h23 : q₂ ≠ q₃ := by
    intro heq
    have : (2 : Fin 4) = 3 := e.injective (Subtype.ext heq)
    exact (by decide : (2 : Fin 4) ≠ 3) this
  have hqs : qs = {q₀, q₁, q₂, q₃} := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
      fin_cases i
      all_goals
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have hvalue := congrArg Subtype.val hi
      · exact Or.inl hvalue.symm
      · exact Or.inr (Or.inl hvalue.symm)
      · exact Or.inr (Or.inr (Or.inl hvalue.symm))
      · exact Or.inr (Or.inr (Or.inr hvalue.symm))
    · intro hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact (e 0).2
      · exact (e 1).2
      · exact (e 2).2
      · exact (e 3).2
  let x₀ : FABL.F₂Cube n := Quotient.out q₀
  let x₁ : FABL.F₂Cube n := Quotient.out q₁
  let x₂ : FABL.F₂Cube n := Quotient.out q₂
  let x₃ : FABL.F₂Cube n := Quotient.out q₃
  have hx₀ : R.mkQ x₀ = q₀ := Submodule.Quotient.mk_out q₀
  have hx₁ : R.mkQ x₁ = q₁ := Submodule.Quotient.mk_out q₁
  have hx₂ : R.mkQ x₂ = q₂ := Submodule.Quotient.mk_out q₂
  have hx₃ : R.mkQ x₃ = q₃ := Submodule.Quotient.mk_out q₃
  let a := Classical.choose
    (exists_spanning_pair_of_finrank_two R hRrank)
  let b := Classical.choose (Classical.choose_spec
    (exists_spanning_pair_of_finrank_two R hRrank))
  have hRspan := Classical.choose_spec (Classical.choose_spec
    (exists_spanning_pair_of_finrank_two R hRrank))
  refine ⟨a, b, x₀, x₁, x₂, x₃, ?_⟩
  change R = (FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b) at hRspan
  rw [← hRspan]
  funext x
  have hquotientValue : qh (R.mkQ x) = h x := by
    rfl
  have hsupport : qh (R.mkQ x) = 1 ↔
      R.mkQ x = R.mkQ x₀ ∨ R.mkQ x = R.mkQ x₁ ∨
        R.mkQ x = R.mkQ x₂ ∨ R.mkQ x = R.mkQ x₃ := by
    have hmem : R.mkQ x ∈ qs ↔ qh (R.mkQ x) = 1 := by
      simp only [qs, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hmem, hqs, hx₀, hx₁, hx₂, hx₃]
    simp
  simp only [Pi.add_apply, binaryAffineFlatIndicator,
    mem_binaryAffineSubspace_iff_mkQ_eq]
  by_cases h0 : R.mkQ x = R.mkQ x₀
  · have h1 : R.mkQ x ≠ R.mkQ x₁ := fun hx ↦
      h01 (hx₀.symm.trans ((h0.symm.trans hx).trans hx₁))
    have h2 : R.mkQ x ≠ R.mkQ x₂ := fun hx ↦
      h02 (hx₀.symm.trans ((h0.symm.trans hx).trans hx₂))
    have h3 : R.mkQ x ≠ R.mkQ x₃ := fun hx ↦
      h03 (hx₀.symm.trans ((h0.symm.trans hx).trans hx₃))
    have hxOne : h x = 1 := by
      rw [← hquotientValue]
      exact hsupport.mpr (Or.inl h0)
    rw [hxOne, if_pos h0, if_neg h1, if_neg h2, if_neg h3]
    norm_num
  · by_cases h1 : R.mkQ x = R.mkQ x₁
    · have h2 : R.mkQ x ≠ R.mkQ x₂ := fun hx ↦
        h12 (hx₁.symm.trans ((h1.symm.trans hx).trans hx₂))
      have h3 : R.mkQ x ≠ R.mkQ x₃ := fun hx ↦
        h13 (hx₁.symm.trans ((h1.symm.trans hx).trans hx₃))
      have hxOne : h x = 1 := by
        rw [← hquotientValue]
        exact hsupport.mpr (Or.inr (Or.inl h1))
      rw [hxOne, if_neg h0, if_pos h1, if_neg h2, if_neg h3]
      norm_num
    · by_cases h2 : R.mkQ x = R.mkQ x₂
      · have h3 : R.mkQ x ≠ R.mkQ x₃ := fun hx ↦
          h23 (hx₂.symm.trans ((h2.symm.trans hx).trans hx₃))
        have hxOne : h x = 1 := by
          rw [← hquotientValue]
          exact hsupport.mpr (Or.inr (Or.inr (Or.inl h2)))
        rw [hxOne, if_neg h0, if_neg h1, if_pos h2, if_neg h3]
        norm_num
      · by_cases h3 : R.mkQ x = R.mkQ x₃
        · have hxOne : h x = 1 := by
            rw [← hquotientValue]
            exact hsupport.mpr (Or.inr (Or.inr (Or.inr h3)))
          rw [hxOne, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
          norm_num
        · have hxNotOne : h x ≠ 1 := by
            intro hxOne
            have hqOne : qh (R.mkQ x) = 1 := by
              exact hquotientValue.trans hxOne
            exact hsupport.mp hqOne |>.elim h0 fun hrest ↦
              hrest.elim h1 fun hrest' ↦ hrest'.elim h2 h3
          have hxZero : h x = 0 := by
            by_contra hxNeZero
            exact hxNotOne (Fin.eq_one_of_ne_zero _ hxNeZero)
          rw [hxZero, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
          norm_num

private def weightSixteenTypeBWordWitnessCode
    {h : BooleanFunction n} (w : WeightSixteenTypeBWordWitness h) :
    Fin 6 → FABL.F₂Cube n :=
  ![w.a, w.b, w.x₀, w.x₁, w.x₂, w.x₃]

private noncomputable def weightSixteenTypeBWordCode
    (h : BooleanFunction n) : Fin 6 → FABL.F₂Cube n := by
  classical
  exact if hh : h ∈ orderTwoWeightSixteenTypeBWords n then
    weightSixteenTypeBWordWitnessCode
      (weightSixteenTypeBWordWitness h hh)
  else 0

private theorem weightSixteenTypeBWordCode_injective_on :
    Set.InjOn (weightSixteenTypeBWordCode (n := n))
      (orderTwoWeightSixteenTypeBWords n : Set (BooleanFunction n)) := by
  intro f hf g hg hcode
  have hfFin : f ∈ orderTwoWeightSixteenTypeBWords n := hf
  have hgFin : g ∈ orderTwoWeightSixteenTypeBWords n := hg
  let wf := weightSixteenTypeBWordWitness f hfFin
  let wg := weightSixteenTypeBWordWitness g hgFin
  have hcode' : weightSixteenTypeBWordWitnessCode wf =
      weightSixteenTypeBWordWitnessCode wg := by
    unfold weightSixteenTypeBWordCode at hcode
    rw [dif_pos hfFin, dif_pos hgFin] at hcode
    simpa only [wf, wg] using hcode
  have h0 : wf.a = wg.a := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (0 : Fin 6)
  have h1 : wf.b = wg.b := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (1 : Fin 6)
  have h2 : wf.x₀ = wg.x₀ := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (2 : Fin 6)
  have h3 : wf.x₁ = wg.x₁ := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (3 : Fin 6)
  have h4 : wf.x₂ = wg.x₂ := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (4 : Fin 6)
  have h5 : wf.x₃ = wg.x₃ := by
    simpa [weightSixteenTypeBWordWitnessCode] using
      congrFun hcode' (5 : Fin 6)
  rw [wf.word_eq, wg.word_eq, h0, h1, h2, h3, h4, h5]

/-- Type-`b` exceptional words inject into six ambient vectors. -/
theorem card_orderTwoWeightSixteenTypeBWords_le (n : ℕ) :
    (orderTwoWeightSixteenTypeBWords n).card ≤ (2 ^ n) ^ 6 := by
  classical
  calc
    (orderTwoWeightSixteenTypeBWords n).card ≤
        (Finset.univ : Finset (Fin 6 → FABL.F₂Cube n)).card := by
      apply Finset.card_le_card_of_injOn
        (weightSixteenTypeBWordCode (n := n))
      · intro h _hh
        exact Finset.mem_univ _
      · exact weightSixteenTypeBWordCode_injective_on
    _ = (2 ^ n) ^ 6 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_f₂Cube]

/-- The canonical exceptional families satisfy the count interface used by
the weight-sixteen character-sum estimate. -/
theorem hasWeightSixteenExceptionalCountBounds_typeA_typeB (n : ℕ) :
    HasWeightSixteenExceptionalCountBounds
      (orderTwoWeightSixteenTypeAWords n)
      (orderTwoWeightSixteenTypeBWords n) := by
  exact ⟨card_orderTwoWeightSixteenTypeAWords_le n,
    card_orderTwoWeightSixteenTypeBWords_le n⟩

end CryptBoolean
