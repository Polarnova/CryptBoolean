/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.ExtremalPropagation

import Mathlib.Data.Fin.Tuple.Embedding
import CryptBoolean.Carlet.Chapter08.OrderCharacterization

/-!
# Embedded coordinate restrictions

Coordinate restrictions with arbitrary enumerations of their free variables,
together with propagation-order transport under restriction.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Reindex a binary cube along an equivalence of its coordinate types. -/
def cubeReindexLinearEquiv {r s : ℕ} (e : Fin r ≃ Fin s) :
    FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Reindexing the coordinates of a Boolean function preserves its Hamming
weight. -/
theorem hammingWeight_comp_cubeReindexLinearEquiv
    {r s : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s) :
    hammingWeight (f ∘ cubeReindexLinearEquiv e) = hammingWeight f := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  simp only [support, FABL.f₂OneSupport, Function.comp_apply]
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp (cubeReindexLinearEquiv e).toEquiv
    (fun x ↦ if f x = 1 then (1 : ℕ) else 0)

/-- Reindexing the coordinates of a Boolean function preserves balancedness. -/
theorem isBalanced_comp_cubeReindexLinearEquiv_iff
    {r s : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s) :
    IsBalanced (f ∘ cubeReindexLinearEquiv e) ↔ IsBalanced f := by
  have hrs : r = s := by
    have hcard := Fintype.card_congr e
    simpa using hcard
  unfold IsBalanced
  rw [hammingWeight_comp_cubeReindexLinearEquiv, hrs]

/-- Coordinate reindexing preserves the support cardinality of a direction. -/
theorem card_f₂Support_cubeReindexLinearEquiv
    {r s : ℕ} (e : Fin r ≃ Fin s) (a : FABL.F₂Cube r) :
    (FABL.f₂Support (cubeReindexLinearEquiv e a)).card =
      (FABL.f₂Support a).card := by
  classical
  rw [FABL.f₂Support, FABL.f₂Support,
    Finset.card_filter, Finset.card_filter]
  apply Fintype.sum_equiv e.symm
  intro i
  simp [cubeReindexLinearEquiv]

/-- Coordinate reindexing maps the support of a direction by the same
coordinate equivalence. -/
theorem f₂Support_cubeReindexLinearEquiv
    {r s : ℕ} (e : Fin r ≃ Fin s) (a : FABL.F₂Cube r) :
    FABL.f₂Support (cubeReindexLinearEquiv e a) =
      (FABL.f₂Support a).map e.toEmbedding := by
  ext j
  simp [FABL.mem_f₂Support, cubeReindexLinearEquiv]

/-- Binary differentiation commutes with coordinate reindexing. -/
theorem booleanDerivative_comp_cubeReindexLinearEquiv
    {r s : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s)
    (a : FABL.F₂Cube r) :
    FABL.booleanDerivative (f ∘ cubeReindexLinearEquiv e) a =
      FABL.booleanDerivative f (cubeReindexLinearEquiv e a) ∘
        cubeReindexLinearEquiv e := by
  funext x
  simp only [FABL.booleanDerivative, Function.comp_apply, map_add]

/-- Coordinate reindexing preserves every propagation criterion. -/
theorem satisfiesPropagationCriterion_comp_cubeReindexLinearEquiv_iff
    {r s l : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s) :
    SatisfiesPropagationCriterion l (f ∘ cubeReindexLinearEquiv e) ↔
      SatisfiesPropagationCriterion l f := by
  constructor
  · intro hf a ha
    let b := (cubeReindexLinearEquiv e).symm a
    have hb0 : b ≠ 0 := by
      intro hb
      apply ha.1
      calc
        a = cubeReindexLinearEquiv e b :=
          ((cubeReindexLinearEquiv e).apply_symm_apply a).symm
        _ = cubeReindexLinearEquiv e 0 := by rw [hb]
        _ = 0 := map_zero (cubeReindexLinearEquiv e)
    have hbweight : (FABL.f₂Support b).card ≤ l := by
      rw [show b = cubeReindexLinearEquiv e.symm a by rfl,
        card_f₂Support_cubeReindexLinearEquiv]
      exact ha.2
    have hbalanced := hf b ⟨hb0, hbweight⟩
    rw [booleanDerivative_comp_cubeReindexLinearEquiv] at hbalanced
    rw [(cubeReindexLinearEquiv e).apply_symm_apply] at hbalanced
    exact (isBalanced_comp_cubeReindexLinearEquiv_iff _ e).1 hbalanced
  · intro hf a ha
    rw [booleanDerivative_comp_cubeReindexLinearEquiv]
    apply (isBalanced_comp_cubeReindexLinearEquiv_iff _ e).2
    apply hf (cubeReindexLinearEquiv e a)
    constructor
    · intro hzero
      apply ha.1
      exact (cubeReindexLinearEquiv e).injective (by simpa using hzero)
    · rw [card_f₂Support_cubeReindexLinearEquiv]
      exact ha.2

private theorem f₂DotProduct_cubeReindexLinearEquiv
    {r s : ℕ} (e : Fin r ≃ Fin s) (a x : FABL.F₂Cube r) :
    FABL.f₂DotProduct (cubeReindexLinearEquiv e a)
        (cubeReindexLinearEquiv e x) =
      FABL.f₂DotProduct a x := by
  simp only [FABL.f₂DotProduct, dotProduct, cubeReindexLinearEquiv]
  exact Equiv.sum_comp e.symm (fun i ↦ a i * x i)

private theorem walshTransform_comp_cubeReindexLinearEquiv
    {r s : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s)
    (b : FABL.F₂Cube r) :
    walshTransform (f ∘ cubeReindexLinearEquiv e) b =
      walshTransform f (cubeReindexLinearEquiv e b) := by
  classical
  rw [walshTransform, walshTransform]
  apply Fintype.sum_equiv (cubeReindexLinearEquiv e).toEquiv
  intro x
  simp only [walshTerm, Function.comp_apply]
  apply congrArg bitSignInt
  congr 1
  exact (f₂DotProduct_cubeReindexLinearEquiv e b x).symm

private theorem disjoint_f₂Support_cubeReindexLinearEquiv
    {r s : ℕ} (e : Fin r ≃ Fin s) (a b : FABL.F₂Cube r)
    (hab : Disjoint (FABL.f₂Support a) (FABL.f₂Support b)) :
    Disjoint
      (FABL.f₂Support (cubeReindexLinearEquiv e a))
      (FABL.f₂Support (cubeReindexLinearEquiv e b)) := by
  rw [Finset.disjoint_left] at hab ⊢
  intro t hta htb
  apply hab (a := e.symm t)
  · rw [FABL.mem_f₂Support] at hta ⊢
    simpa [cubeReindexLinearEquiv] using hta
  · rw [FABL.mem_f₂Support] at htb ⊢
    simpa [cubeReindexLinearEquiv] using htb

private theorem satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv
    {r s l k : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s)
    (hparameters : l + k ≤ r)
    (hf : SatisfiesPropagationCriterionOfOrder l k f) :
    SatisfiesPropagationCriterionOfOrder l k
      (f ∘ cubeReindexLinearEquiv e) := by
  have hrs : r = s := by
    simpa using Fintype.card_congr e
  subst s
  apply
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k (f ∘ cubeReindexLinearEquiv e) hparameters).mpr
  have hzero :=
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k f hparameters).mp hf
  intro a b haweight hbweight hab hdisjoint
  rw [booleanDerivative_comp_cubeReindexLinearEquiv,
    walshTransform_comp_cubeReindexLinearEquiv]
  apply hzero
  · simpa [card_f₂Support_cubeReindexLinearEquiv] using haweight
  · simpa [card_f₂Support_cubeReindexLinearEquiv] using hbweight
  · intro hpair
    apply hab
    apply Prod.ext
    · apply (cubeReindexLinearEquiv e).injective
      simpa using congrArg Prod.fst hpair
    · apply (cubeReindexLinearEquiv e).injective
      simpa using congrArg Prod.snd hpair
  · exact disjoint_f₂Support_cubeReindexLinearEquiv e a b hdisjoint

/-- Reindexing the input coordinates preserves every propagation criterion
at every fixed-coordinate order. -/
theorem satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv_iff
    {r s l k : ℕ} (f : BooleanFunction s) (e : Fin r ≃ Fin s)
    (hparameters : l + k ≤ r) :
    SatisfiesPropagationCriterionOfOrder l k
        (f ∘ cubeReindexLinearEquiv e) ↔
      SatisfiesPropagationCriterionOfOrder l k f := by
  have hrs : r = s := by
    simpa using Fintype.card_congr e
  subst s
  constructor
  · intro hf
    have htwice :=
      satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv
        (f ∘ cubeReindexLinearEquiv e) e.symm hparameters hf
    have hfunction :
        (f ∘ cubeReindexLinearEquiv e) ∘
            cubeReindexLinearEquiv e.symm = f := by
      funext x
      simp [cubeReindexLinearEquiv]
    simpa only [hfunction] using htwice
  · exact satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv
      f e hparameters

/-- The coordinate image of an embedding, indexed by its original finite
domain. -/
noncomputable def embeddingFinsetEquiv {r : ℕ}
    (e : Fin r ↪ Fin n) : Fin r ≃ ↥(Finset.univ.map e) where
  toFun i := ⟨e i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  invFun j := Classical.choose (Finset.mem_map.mp j.property)
  left_inv i := by
    apply e.injective
    exact (Classical.choose_spec
      (Finset.mem_map.mp
        (show e i ∈ Finset.univ.map e by simp))).2
  right_inv j := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_map.mp j.property)).2

/-- The change from an arbitrary enumeration of free coordinates to FABL's
canonical increasing enumeration of the same finite set. -/
noncomputable def canonicalEmbeddingReindexEquiv {r : ℕ}
    (e : Fin r ↪ Fin n) :
    Fin r ≃ Fin (Finset.univ.map e).card :=
  (embeddingFinsetEquiv e).trans (Finset.univ.map e).equivFin

@[simp] theorem freeCoordinateEmbedding_canonicalEmbeddingReindexEquiv
    {r : ℕ} (e : Fin r ↪ Fin n) (i : Fin r) :
    FABL.freeCoordinateEmbedding (Finset.univ.map e)
        (canonicalEmbeddingReindexEquiv e i) = e i := by
  exact FABL.freeCoordinateEmbedding_equivFin
    (Finset.univ.map e) (embeddingFinsetEquiv e i)

/-- Restrict a Boolean function along an arbitrary injective enumeration of
free coordinates, taking every other value from an ambient point. -/
noncomputable def embeddedCoordinateRestriction {r : ℕ}
    (f : BooleanFunction n) (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    BooleanFunction r :=
  fun x ↦ f (Function.extend e x x₀)

private theorem embeddedCoordinateRestriction_embeddedCoordinateRestriction
    {r s : ℕ} (f : BooleanFunction n) (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) (e' : Fin s ↪ Fin r)
    (x₁ : FABL.F₂Cube r) :
    embeddedCoordinateRestriction
        (embeddedCoordinateRestriction f e x₀) e' x₁ =
      embeddedCoordinateRestriction f (e'.trans e)
        (Function.extend e x₁ x₀) := by
  funext x
  change f (Function.extend e (Function.extend e' x x₁) x₀) =
    f (Function.extend (e'.trans e) x (Function.extend e x₁ x₀))
  congr 1
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [e.injective.extend_apply]
    by_cases hq : ∃ p, e' p = q
    · obtain ⟨p, rfl⟩ := hq
      rw [e'.injective.extend_apply,
        ← show (e'.trans e) p = e (e' p) by rfl,
        (e'.trans e).injective.extend_apply]
    · rw [Function.extend_apply' _ _ q hq]
      have hnot : ¬ ∃ p, (e'.trans e) p = e q := by
        rintro ⟨p, hp⟩
        exact hq ⟨p, e.injective hp⟩
      rw [Function.extend_apply' _ _ _ hnot,
        e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ i hi]
    have hnot : ¬ ∃ p, (e'.trans e) p = i := by
      rintro ⟨p, hp⟩
      exact hi ⟨e' p, hp⟩
    rw [Function.extend_apply' _ _ i hnot,
      Function.extend_apply' _ _ i hi]

private theorem embeddedCoordinateRestriction_eq_coordinateRestriction_comp
    {r : ℕ} (f : BooleanFunction n) (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) :
    embeddedCoordinateRestriction f e x₀ =
      coordinateRestriction f (Finset.univ.map e)
          (coordinateFixedSignAssignment (Finset.univ.map e) x₀) ∘
        cubeReindexLinearEquiv (canonicalEmbeddingReindexEquiv e) := by
  funext x
  change f (Function.extend e x x₀) =
    coordinateRestriction f (Finset.univ.map e)
      (coordinateFixedSignAssignment (Finset.univ.map e) x₀)
      (cubeReindexLinearEquiv (canonicalEmbeddingReindexEquiv e) x)
  rw [coordinateRestriction_fixedAssignment_apply]
  congr 1
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [e.injective.extend_apply,
      ← freeCoordinateEmbedding_canonicalEmbeddingReindexEquiv e q,
      (FABL.freeCoordinateEmbedding (Finset.univ.map e)).injective.extend_apply]
    simp [cubeReindexLinearEquiv]
  · rw [Function.extend_apply' x x₀ i hi]
    have hcanonical :
        ¬ ∃ q,
          FABL.freeCoordinateEmbedding (Finset.univ.map e) q = i := by
      rintro ⟨q, hq⟩
      let p := (canonicalEmbeddingReindexEquiv e).symm q
      apply hi
      refine ⟨p, ?_⟩
      rw [← freeCoordinateEmbedding_canonicalEmbeddingReindexEquiv e p]
      simpa [p] using hq
    rw [Function.extend_apply' _ x₀ i hcanonical]

/-- An arbitrary free-coordinate enumeration realizes the propagation
criterion supplied by the complementary ambient coordinate order. -/
theorem satisfiesPropagationCriterion_embeddedCoordinateRestriction_of_order
    {r k l : ℕ} (f : BooleanFunction n)
    (hf : SatisfiesPropagationCriterionOfOrder l k f)
    (hrk : r + k = n) (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    SatisfiesPropagationCriterion l
      (embeddedCoordinateRestriction f e x₀) := by
  rw [embeddedCoordinateRestriction_eq_coordinateRestriction_comp]
  apply
    (satisfiesPropagationCriterion_comp_cubeReindexLinearEquiv_iff _ _).2
  apply hf (Finset.univ.map e)
    (coordinateFixedSignAssignment (Finset.univ.map e) x₀)
  change Fintype.card
    {i : Fin n // ¬i ∈ Finset.univ.map e} = k
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_map,
    Finset.card_univ]
  omega

/-- Restricting an order propagation criterion to an embedded coordinate
subcube subtracts the coordinates already fixed outside that subcube. -/
theorem satisfiesPropagationCriterionOfOrder_embeddedCoordinateRestriction
    {r l k k' : ℕ} (f : BooleanFunction n)
    (hf : SatisfiesPropagationCriterionOfOrder l k f)
    (horders : r + k = n + k') (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) :
    SatisfiesPropagationCriterionOfOrder l k'
      (embeddedCoordinateRestriction f e x₀) := by
  intro J z hfixed
  have hJle : J.card ≤ r := by
    simpa using Finset.card_le_univ J
  have hcomplement : r - J.card = k' := by
    simpa [FABL.FixedIndex] using hfixed
  have hJparameters : J.card + k = n := by omega
  let x₁ : FABL.F₂Cube r := fun i ↦
    if hi : i ∈ J then 0 else FABL.binarySignEquiv.symm (z ⟨i, hi⟩)
  have hz : coordinateFixedSignAssignment J x₁ = z := by
    funext i
    simp [coordinateFixedSignAssignment, x₁, i.property]
  let e' := FABL.freeCoordinateEmbedding J
  have hambient :
      SatisfiesPropagationCriterion l
        (embeddedCoordinateRestriction f (e'.trans e)
          (Function.extend e x₁ x₀)) :=
    satisfiesPropagationCriterion_embeddedCoordinateRestriction_of_order
      f hf hJparameters (e'.trans e) (Function.extend e x₁ x₀)
  have hnested :
      SatisfiesPropagationCriterion l
        (embeddedCoordinateRestriction
          (embeddedCoordinateRestriction f e x₀) e' x₁) := by
    rw [embeddedCoordinateRestriction_embeddedCoordinateRestriction]
    exact hambient
  have hrestriction :
      embeddedCoordinateRestriction
          (embeddedCoordinateRestriction f e x₀) e' x₁ =
        coordinateRestriction (embeddedCoordinateRestriction f e x₀) J z := by
    funext x
    rw [← hz]
    exact (coordinateRestriction_fixedAssignment_apply
      (embeddedCoordinateRestriction f e x₀) J x₁ x).symm
  rw [hrestriction] at hnested
  exact hnested

/-- Reindexing equivalent coordinate types preserves bentness. -/
theorem isBent_comp_cubeReindexLinearEquiv_iff
    {r s : ℕ} (hrs : r = s) (f : BooleanFunction s) (e : Fin r ≃ Fin s) :
    IsBent (f ∘ cubeReindexLinearEquiv e) ↔ IsBent f := by
  subst s
  exact isBent_comp_affineEquiv_iff f
    (cubeReindexLinearEquiv e).toAffineEquiv

/-- Bentness of an arbitrarily enumerated coordinate restriction agrees with
bentness of the canonical restriction on the same free-coordinate set. -/
theorem isBent_embeddedCoordinateRestriction_iff {r : ℕ}
    (f : BooleanFunction n) (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    IsBent (embeddedCoordinateRestriction f e x₀) ↔
      IsBent (coordinateRestriction f (Finset.univ.map e)
        (coordinateFixedSignAssignment (Finset.univ.map e) x₀)) := by
  rw [embeddedCoordinateRestriction_eq_coordinateRestriction_comp]
  have hr : (Finset.univ.map e).card = r := by simp
  exact isBent_comp_cubeReindexLinearEquiv_iff hr.symm _
    (canonicalEmbeddingReindexEquiv e)

/-- Full-level propagation at the complementary coordinate order makes every
arbitrarily enumerated restriction bent. -/
theorem isBent_embeddedCoordinateRestriction_of_order_dimension {r k : ℕ}
    (f : BooleanFunction n) (hf : SatisfiesPropagationCriterionOfOrder r k f)
    (hrk : r + k = n) (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    IsBent (embeddedCoordinateRestriction f e x₀) := by
  apply (isBent_embeddedCoordinateRestriction_iff f e x₀).2
  apply (isBent_iff_satisfiesPropagationCriterion_dimension _).2
  have hfixed :
      Fintype.card (FABL.FixedIndex (Finset.univ.map e)) = k := by
    change Fintype.card
      {i : Fin n // ¬i ∈ Finset.univ.map e} = k
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_map,
      Finset.card_univ]
    omega
  simpa using hf (Finset.univ.map e)
    (coordinateFixedSignAssignment (Finset.univ.map e) x₀) hfixed

/-- For an even restriction dimension at least four, `PC(r-2)` at the
complementary coordinate order makes every arbitrarily enumerated restriction
bent. -/
theorem isBent_embeddedCoordinateRestriction_of_order_pred_two
    {r k : ℕ} (f : BooleanFunction n)
    (hf : SatisfiesPropagationCriterionOfOrder (r - 2) k f)
    (hrk : r + k = n) (hr : 4 ≤ r) (heven : Even r)
    (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    IsBent (embeddedCoordinateRestriction f e x₀) := by
  apply (isBent_embeddedCoordinateRestriction_iff f e x₀).2
  apply (satisfiesPropagationCriterion_pred_two_iff_isBent_of_even
    (coordinateRestriction f (Finset.univ.map e)
      (coordinateFixedSignAssignment (Finset.univ.map e) x₀))
    (by simpa using hr) (by simpa using heven)).1
  have hfixed :
      Fintype.card (FABL.FixedIndex (Finset.univ.map e)) = k := by
    change Fintype.card
      {i : Fin n // ¬i ∈ Finset.univ.map e} = k
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_map,
      Finset.card_univ]
    omega
  simpa using hf (Finset.univ.map e)
    (coordinateFixedSignAssignment (Finset.univ.map e) x₀) hfixed

end CryptBoolean
