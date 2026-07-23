/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderLowWeightFlats
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The weight-sixteen dual character sum

The disjoint-three-flat square-sum argument behind Carlet--Mesnager
Proposition 9.2.10(4).
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightSixteenFintypeAffineSubspace : Fintype
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance weightSixteenDecidableEqAffineSubspace : DecidableEq
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

noncomputable local instance weightSixteenFintypeDual
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fintype (Module.Dual FABL.𝔽₂ H) :=
  Module.fintypeOfFintype (Module.finBasis FABL.𝔽₂ H).dualBasis

/-- Ordered pairs of binary affine three-flats. -/
noncomputable def binaryAffineThreeFlatPairs (n : ℕ) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  (binaryAffineFlats 3 n).product (binaryAffineFlats 3 n)

/-- Ordered pairs of disjoint binary affine three-flats. -/
noncomputable def disjointBinaryAffineThreeFlatPairs (n : ℕ) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineThreeFlatPairs n).filter fun p ↦ p.1 ⊓ p.2 = ⊥

/-- Ordered pairs of intersecting binary affine three-flats. -/
noncomputable def intersectingBinaryAffineThreeFlatPairs (n : ℕ) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineThreeFlatPairs n).filter fun p ↦ p.1 ⊓ p.2 ≠ ⊥

/-- The Boolean word represented by two affine three-flats. -/
noncomputable def weightSixteenRepresentationWord
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    BooleanFunction n :=
  binaryAffineFlatIndicator A + binaryAffineFlatIndicator B

/-- The weight-sixteen words in the dual Reed--Muller code. -/
noncomputable def orderTwoWeightSixteenDualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoDualWords n).filter fun h ↦ hammingWeight h = 16

/-- The canonical character sum over weight-sixteen dual words. -/
noncomputable def orderTwoWeightSixteenCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightSixteenDualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

/-- The normalized character sum over ordered disjoint-flat
representations. -/
noncomputable def weightSixteenRepresentationCharacterSum
    (f : BooleanFunction n) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2

private theorem affineThreeFlatPairData
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : (A, B) ∈ binaryAffineThreeFlatPairs n) :
    A ∈ binaryAffineFlats 3 n ∧ B ∈ binaryAffineFlats 3 n := by
  change (A, B) ∈ (binaryAffineFlats 3 n).product
    (binaryAffineFlats 3 n) at hp
  exact Finset.mem_product.mp hp

private theorem affineThreeFlatData
    {A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hA : A ∈ binaryAffineFlats 3 n) :
    A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
  simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
    true_and] using hA

private theorem disjointAffineThreeFlatPairData
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : (A, B) ∈ disjointBinaryAffineThreeFlatPairs n) :
    A ∈ binaryAffineFlats 3 n ∧ B ∈ binaryAffineFlats 3 n ∧
      A ⊓ B = ⊥ := by
  have hp' : (A, B) ∈ binaryAffineThreeFlatPairs n ∧ A ⊓ B = ⊥ := by
    simpa only [disjointBinaryAffineThreeFlatPairs,
      Finset.mem_filter] using hp
  exact ⟨(affineThreeFlatPairData hp'.1).1,
    (affineThreeFlatPairData hp'.1).2, hp'.2⟩

private theorem binaryAffineFlatPoints_inter_eq_empty
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hdisjoint : A ⊓ B = ⊥) :
    binaryAffineFlatPoints A ∩ binaryAffineFlatPoints B = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    have hx' := Finset.mem_inter.mp hx
    have hxMeet : x ∈ A ⊓ B := by
      exact ⟨(mem_binaryAffineFlatPoints A x).mp hx'.1,
        (mem_binaryAffineFlatPoints B x).mp hx'.2⟩
    rw [hdisjoint] at hxMeet
    rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hxMeet
    simp at hxMeet
  · intro hx
    simp at hx

/-- A disjoint pair of affine three-flats represents a word of Hamming
weight sixteen. -/
theorem hammingWeight_weightSixteenRepresentationWord
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (A, B) ∈ disjointBinaryAffineThreeFlatPairs n) :
    hammingWeight (weightSixteenRepresentationWord A B) = 16 := by
  have hpdata := disjointAffineThreeFlatPairData hp
  have hAdata := affineThreeFlatData hpdata.1
  have hBdata := affineThreeFlatData hpdata.2.1
  have hintersection := binaryAffineFlatPoints_inter_eq_empty
    A B hpdata.2.2
  have hidentity := hammingWeight_add_add_two_mul_card_support_inter
    (binaryAffineFlatIndicator A) (binaryAffineFlatIndicator B)
  rw [support_binaryAffineFlatIndicator,
    support_binaryAffineFlatIndicator, hintersection,
    hammingWeight_binaryAffineFlatIndicator A hAdata.1,
    hammingWeight_binaryAffineFlatIndicator B hBdata.1,
    hAdata.2, hBdata.2] at hidentity
  change hammingWeight
    (binaryAffineFlatIndicator A + binaryAffineFlatIndicator B) = 16
  norm_num at hidentity
  omega

/-- Every disjoint-three-flat representation produces a weight-sixteen
dual Reed--Muller word. -/
theorem weightSixteenRepresentationWord_mem_dualWords
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (A, B) ∈ disjointBinaryAffineThreeFlatPairs n) :
    weightSixteenRepresentationWord A B ∈
      orderTwoWeightSixteenDualWords n := by
  have hpdata := disjointAffineThreeFlatPairData hp
  have hA := binaryAffineFlatIndicator_mem_reedMuller A hpdata.1
  have hB := binaryAffineFlatIndicator_mem_reedMuller B hpdata.2.1
  simp only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(reedMuller (n - 3) n).add_mem hA hB,
    hammingWeight_weightSixteenRepresentationWord A B hp⟩

/-- The character of a represented word is the product of its two
affine-flat characters. -/
theorem weightSixteenRepresentationWord_character
    (f : BooleanFunction n)
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    FABL.binarySign (booleanFunctionPairing n f
      (weightSixteenRepresentationWord A B)) =
      binaryAffineFlatCharacter f A * binaryAffineFlatCharacter f B := by
  rw [weightSixteenRepresentationWord, map_add, AddChar.map_add_eq_mul]
  rfl

/-- The type-`a` exceptional words: indicators of affine four-flats. -/
noncomputable def orderTwoWeightSixteenTypeAWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (binaryAffineFlats 4 n).image binaryAffineFlatIndicator

/-- Every affine-four-flat indicator is a weight-sixteen word in the dual
Reed--Muller code. -/
theorem orderTwoWeightSixteenTypeAWords_subset_dualWords (n : ℕ) :
    orderTwoWeightSixteenTypeAWords n ⊆ orderTwoWeightSixteenDualWords n := by
  classical
  intro h hh
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hh
  have hAdata : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 4 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hmemComplementary := binaryAffineFlatIndicator_mem_reedMuller A hA
  have hmem : binaryAffineFlatIndicator A ∈ reedMuller (n - 3) n :=
    reedMuller_mono (by omega : n - 4 ≤ n - 3) hmemComplementary
  have hweight : hammingWeight (binaryAffineFlatIndicator A) = 16 := by
    rw [hammingWeight_binaryAffineFlatIndicator A hAdata.1, hAdata.2]
    norm_num
  simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
    Finset.mem_filter, Finset.mem_univ, true_and] using ⟨hmem, hweight⟩

private theorem exists_spanning_quadruple_of_finrank_four
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 4) :
    ∃ a b c d : FABL.F₂Cube n,
      H = (((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) ⊔
        (FABL.𝔽₂ ∙ c)) ⊔ (FABL.𝔽₂ ∙ d) := by
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
  let S₁ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) := FABL.𝔽₂ ∙ a
  have hS₁le : S₁ ≤ H :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 haH)
  have hS₁rank : Module.finrank FABL.𝔽₂ S₁ = 1 :=
    finrank_span_singleton ha0
  have hS₁lt : S₁ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₁le (by omega)
  obtain ⟨b, hbH, hbS₁⟩ := SetLike.exists_of_lt hS₁lt
  let S₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    S₁ ⊔ (FABL.𝔽₂ ∙ b)
  have hS₂le : S₂ ≤ H := by
    exact sup_le hS₁le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hbH))
  have hS₂rank : Module.finrank FABL.𝔽₂ S₂ = 2 := by
    dsimp only [S₂]
    rw [Submodule.finrank_sup_span_singleton hbS₁, hS₁rank]
  have hS₂lt : S₂ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₂le (by omega)
  obtain ⟨c, hcH, hcS₂⟩ := SetLike.exists_of_lt hS₂lt
  let S₃ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    S₂ ⊔ (FABL.𝔽₂ ∙ c)
  have hS₃le : S₃ ≤ H := by
    exact sup_le hS₂le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hcH))
  have hS₃rank : Module.finrank FABL.𝔽₂ S₃ = 3 := by
    dsimp only [S₃]
    rw [Submodule.finrank_sup_span_singleton hcS₂, hS₂rank]
  have hS₃lt : S₃ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₃le (by omega)
  obtain ⟨d, hdH, hdS₃⟩ := SetLike.exists_of_lt hS₃lt
  refine ⟨a, b, c, d, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hS₃le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hdH))
  · rw [Submodule.finrank_sup_span_singleton hdS₃, hS₃rank, hH]

private structure AffineFourFlatWitness
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) where
  u : FABL.F₂Cube n
  a : FABL.F₂Cube n
  b : FABL.F₂Cube n
  c : FABL.F₂Cube n
  d : FABL.F₂Cube n
  flat_eq : A = FABL.binaryAffineSubspace
    ((((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) ⊔
      (FABL.𝔽₂ ∙ c)) ⊔ (FABL.𝔽₂ ∙ d)) u

private noncomputable def affineFourFlatWitness
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats 4 n) : AffineFourFlatWitness A := by
  classical
  have hAdata : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 4 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  let u := Classical.choose
    ((AffineSubspace.nonempty_iff_ne_bot A).2 hAdata.1)
  have hu := Classical.choose_spec
    ((AffineSubspace.nonempty_iff_ne_bot A).2 hAdata.1)
  let hspanExists :=
    exists_spanning_quadruple_of_finrank_four A.direction hAdata.2
  let a := Classical.choose hspanExists
  let b := Classical.choose (Classical.choose_spec hspanExists)
  let c := Classical.choose
    (Classical.choose_spec (Classical.choose_spec hspanExists))
  let d := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec hspanExists)))
  have hspan := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec hspanExists)))
  refine ⟨u, a, b, c, d, ?_⟩
  calc
    A = FABL.binaryAffineSubspace A.direction u :=
      (AffineSubspace.mk'_eq hu).symm
    _ = FABL.binaryAffineSubspace
        ((((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) ⊔
          (FABL.𝔽₂ ∙ c)) ⊔ (FABL.𝔽₂ ∙ d)) u := by rw [hspan]

private def affineFourFlatWitnessCode
    {A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (w : AffineFourFlatWitness A) : Fin 5 → FABL.F₂Cube n :=
  ![w.u, w.a, w.b, w.c, w.d]

private noncomputable def affineFourFlatCode
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fin 5 → FABL.F₂Cube n := by
  classical
  exact if hA : A ∈ binaryAffineFlats 4 n then
    affineFourFlatWitnessCode (affineFourFlatWitness A hA)
  else 0

private theorem affineFourFlatCode_injective_on :
    Set.InjOn (affineFourFlatCode (n := n))
      (binaryAffineFlats 4 n :
        Set (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))) := by
  intro A hA B hB hcode
  have hA' : A ∈ binaryAffineFlats 4 n := hA
  have hB' : B ∈ binaryAffineFlats 4 n := hB
  let wA := affineFourFlatWitness A hA
  let wB := affineFourFlatWitness B hB
  have hcode' : affineFourFlatWitnessCode wA =
      affineFourFlatWitnessCode wB := by
    unfold affineFourFlatCode at hcode
    rw [dif_pos hA', dif_pos hB'] at hcode
    simpa only [wA, wB] using hcode
  have h0 : wA.u = wB.u := by
    simpa [affineFourFlatWitnessCode] using congrFun hcode' (0 : Fin 5)
  have h1 : wA.a = wB.a := by
    simpa [affineFourFlatWitnessCode] using congrFun hcode' (1 : Fin 5)
  have h2 : wA.b = wB.b := by
    simpa [affineFourFlatWitnessCode] using congrFun hcode' (2 : Fin 5)
  have h3 : wA.c = wB.c := by
    simpa [affineFourFlatWitnessCode] using congrFun hcode' (3 : Fin 5)
  have h4 : wA.d = wB.d := by
    simpa [affineFourFlatWitnessCode] using congrFun hcode' (4 : Fin 5)
  rw [wA.flat_eq, wB.flat_eq, h0, h1, h2, h3, h4]

/-- The type-`a` exceptional family has at most `(2^n)^5` words. -/
theorem card_orderTwoWeightSixteenTypeAWords_le (n : ℕ) :
    (orderTwoWeightSixteenTypeAWords n).card ≤ (2 ^ n) ^ 5 := by
  classical
  calc
    (orderTwoWeightSixteenTypeAWords n).card ≤
        (binaryAffineFlats 4 n).card := by
      exact Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin 5 → FABL.F₂Cube n)).card := by
      apply Finset.card_le_card_of_injOn (affineFourFlatCode (n := n))
      · intro A _hA
        exact Finset.mem_univ _
      · exact affineFourFlatCode_injective_on
    _ = (2 ^ n) ^ 5 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_f₂Cube]

private noncomputable def nonzeroBinaryDuals
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (Module.Dual FABL.𝔽₂ H) := by
  classical
  exact Finset.univ.filter fun ℓ ↦ ℓ ≠ 0

private theorem card_nonzeroBinaryDuals_of_finrank_four
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 4) :
    (nonzeroBinaryDuals H).card = 15 := by
  classical
  let B : Module.Basis (Fin (Module.finrank FABL.𝔽₂ H)) FABL.𝔽₂ H :=
    Module.finBasis FABL.𝔽₂ H
  have hcardDual : Fintype.card (Module.Dual FABL.𝔽₂ H) = 16 := by
    calc
      Fintype.card (Module.Dual FABL.𝔽₂ H) =
          Fintype.card (Fin (Module.finrank FABL.𝔽₂ H) → FABL.𝔽₂) :=
        Fintype.card_congr B.dualBasis.equivFun.toEquiv
      _ = 16 := by
        rw [Fintype.card_fun, Fintype.card_fin, hH]
        norm_num
  have hfilter : nonzeroBinaryDuals H =
      (Finset.univ : Finset (Module.Dual FABL.𝔽₂ H)).erase 0 := by
    ext ℓ
    simp [nonzeroBinaryDuals]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, hcardDual]

private theorem exists_spanning_triple_of_finrank_three
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 3) :
    ∃ a b c : FABL.F₂Cube n,
      H = ((FABL.𝔽₂ ∙ a) ⊔ (FABL.𝔽₂ ∙ b)) ⊔
        (FABL.𝔽₂ ∙ c) := by
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
  let S₁ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) := FABL.𝔽₂ ∙ a
  have hS₁le : S₁ ≤ H :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 haH)
  have hS₁rank : Module.finrank FABL.𝔽₂ S₁ = 1 :=
    finrank_span_singleton ha0
  have hS₁lt : S₁ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₁le (by omega)
  obtain ⟨b, hbH, hbS₁⟩ := SetLike.exists_of_lt hS₁lt
  let S₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    S₁ ⊔ (FABL.𝔽₂ ∙ b)
  have hS₂le : S₂ ≤ H := by
    exact sup_le hS₁le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hbH))
  have hS₂rank : Module.finrank FABL.𝔽₂ S₂ = 2 := by
    dsimp only [S₂]
    rw [Submodule.finrank_sup_span_singleton hbS₁, hS₁rank]
  have hS₂lt : S₂ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₂le (by omega)
  obtain ⟨c, hcH, hcS₂⟩ := SetLike.exists_of_lt hS₂lt
  refine ⟨a, b, c, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hS₂le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hcH))
  · rw [Submodule.finrank_sup_span_singleton hcS₂, hS₂rank, hH]

private structure IntersectingAffineThreeFlatPairWitness
    (p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) where
  u : FABL.F₂Cube n
  a₁ : FABL.F₂Cube n
  b₁ : FABL.F₂Cube n
  c₁ : FABL.F₂Cube n
  a₂ : FABL.F₂Cube n
  b₂ : FABL.F₂Cube n
  c₂ : FABL.F₂Cube n
  first_eq : p.1 = FABL.binaryAffineSubspace
    (((FABL.𝔽₂ ∙ a₁) ⊔ (FABL.𝔽₂ ∙ b₁)) ⊔
      (FABL.𝔽₂ ∙ c₁)) u
  second_eq : p.2 = FABL.binaryAffineSubspace
    (((FABL.𝔽₂ ∙ a₂) ⊔ (FABL.𝔽₂ ∙ b₂)) ⊔
      (FABL.𝔽₂ ∙ c₂)) u

private noncomputable def intersectingAffineThreeFlatPairWitness
    (p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : p ∈ intersectingBinaryAffineThreeFlatPairs n) :
    IntersectingAffineThreeFlatPairWitness p := by
  classical
  have hp' : p ∈ binaryAffineThreeFlatPairs n ∧ p.1 ⊓ p.2 ≠ ⊥ := by
    simpa only [intersectingBinaryAffineThreeFlatPairs,
      Finset.mem_filter] using hp
  have hpdata := affineThreeFlatPairData hp'.1
  have hfirstData := affineThreeFlatData hpdata.1
  have hsecondData := affineThreeFlatData hpdata.2
  let u := Classical.choose
    ((AffineSubspace.nonempty_iff_ne_bot (p.1 ⊓ p.2)).2 hp'.2)
  have hu := Classical.choose_spec
    ((AffineSubspace.nonempty_iff_ne_bot (p.1 ⊓ p.2)).2 hp'.2)
  let a₁ := Classical.choose
    (exists_spanning_triple_of_finrank_three p.1.direction hfirstData.2)
  let b₁ := Classical.choose (Classical.choose_spec
    (exists_spanning_triple_of_finrank_three p.1.direction hfirstData.2))
  let c₁ := Classical.choose (Classical.choose_spec (Classical.choose_spec
    (exists_spanning_triple_of_finrank_three p.1.direction hfirstData.2)))
  have hfirstSpan := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (exists_spanning_triple_of_finrank_three p.1.direction hfirstData.2)))
  let a₂ := Classical.choose
    (exists_spanning_triple_of_finrank_three p.2.direction hsecondData.2)
  let b₂ := Classical.choose (Classical.choose_spec
    (exists_spanning_triple_of_finrank_three p.2.direction hsecondData.2))
  let c₂ := Classical.choose (Classical.choose_spec (Classical.choose_spec
    (exists_spanning_triple_of_finrank_three p.2.direction hsecondData.2)))
  have hsecondSpan := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      (exists_spanning_triple_of_finrank_three p.2.direction hsecondData.2)))
  refine ⟨u, a₁, b₁, c₁, a₂, b₂, c₂, ?_, ?_⟩
  · calc
      p.1 = FABL.binaryAffineSubspace p.1.direction u :=
        (AffineSubspace.mk'_eq hu.1).symm
      _ = FABL.binaryAffineSubspace
          (((FABL.𝔽₂ ∙ a₁) ⊔ (FABL.𝔽₂ ∙ b₁)) ⊔
            (FABL.𝔽₂ ∙ c₁)) u := by rw [hfirstSpan]
  · calc
      p.2 = FABL.binaryAffineSubspace p.2.direction u :=
        (AffineSubspace.mk'_eq hu.2).symm
      _ = FABL.binaryAffineSubspace
          (((FABL.𝔽₂ ∙ a₂) ⊔ (FABL.𝔽₂ ∙ b₂)) ⊔
            (FABL.𝔽₂ ∙ c₂)) u := by rw [hsecondSpan]

private def intersectingAffineThreeFlatPairWitnessCode
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (w : IntersectingAffineThreeFlatPairWitness p) :
    Fin 7 → FABL.F₂Cube n :=
  ![w.u, w.a₁, w.b₁, w.c₁, w.a₂, w.b₂, w.c₂]

private noncomputable def intersectingAffineThreeFlatPairCode
    (p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fin 7 → FABL.F₂Cube n := by
  classical
  exact if hp : p ∈ intersectingBinaryAffineThreeFlatPairs n then
    intersectingAffineThreeFlatPairWitnessCode
      (intersectingAffineThreeFlatPairWitness p hp)
  else 0

private theorem intersectingAffineThreeFlatPairCode_injective_on :
    Set.InjOn (intersectingAffineThreeFlatPairCode (n := n))
      (intersectingBinaryAffineThreeFlatPairs n :
        Set (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
          AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))) := by
  intro p hp q hq hcode
  have hpFin : p ∈ intersectingBinaryAffineThreeFlatPairs n := hp
  have hqFin : q ∈ intersectingBinaryAffineThreeFlatPairs n := hq
  let wp := intersectingAffineThreeFlatPairWitness p hp
  let wq := intersectingAffineThreeFlatPairWitness q hq
  have hcode' : intersectingAffineThreeFlatPairWitnessCode wp =
      intersectingAffineThreeFlatPairWitnessCode wq := by
    unfold intersectingAffineThreeFlatPairCode at hcode
    rw [dif_pos hpFin, dif_pos hqFin] at hcode
    simpa only [wp, wq] using hcode
  have h0 : wp.u = wq.u := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (0 : Fin 7)
  have h1 : wp.a₁ = wq.a₁ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (1 : Fin 7)
  have h2 : wp.b₁ = wq.b₁ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (2 : Fin 7)
  have h3 : wp.c₁ = wq.c₁ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (3 : Fin 7)
  have h4 : wp.a₂ = wq.a₂ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (4 : Fin 7)
  have h5 : wp.b₂ = wq.b₂ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (5 : Fin 7)
  have h6 : wp.c₂ = wq.c₂ := by
    simpa [intersectingAffineThreeFlatPairWitnessCode] using
      congrFun hcode' (6 : Fin 7)
  apply Prod.ext
  · rw [wp.first_eq, wq.first_eq, h0, h1, h2, h3]
  · rw [wp.second_eq, wq.second_eq, h0, h4, h5, h6]

/-- Intersecting ordered pairs of affine three-flats inject into seven
ambient vectors. -/
theorem card_intersectingBinaryAffineThreeFlatPairs_le (n : ℕ) :
    (intersectingBinaryAffineThreeFlatPairs n).card ≤ (2 ^ n) ^ 7 := by
  classical
  calc
    (intersectingBinaryAffineThreeFlatPairs n).card ≤
        (Finset.univ : Finset (Fin 7 → FABL.F₂Cube n)).card := by
      apply Finset.card_le_card_of_injOn
        (intersectingAffineThreeFlatPairCode (n := n))
      · intro p _hp
        exact Finset.mem_univ _
      · exact intersectingAffineThreeFlatPairCode_injective_on
    _ = (2 ^ n) ^ 7 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_f₂Cube]

private theorem allAffineThreeFlatPairCharacterSum_eq_sq
    (f : BooleanFunction n) :
    (∑ p ∈ binaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2) =
      (binaryAffineFlatCharacterSum 3 f) ^ 2 := by
  classical
  rw [binaryAffineThreeFlatPairs, binaryAffineFlatCharacterSum]
  calc
    (∑ p ∈ (binaryAffineFlats 3 n).product (binaryAffineFlats 3 n),
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) =
        ∑ A ∈ binaryAffineFlats 3 n,
          ∑ B ∈ binaryAffineFlats 3 n,
            binaryAffineFlatCharacter f A *
              binaryAffineFlatCharacter f B := by
      exact Finset.sum_product _ _ _
    _ = (∑ A ∈ binaryAffineFlats 3 n,
        binaryAffineFlatCharacter f A) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, mul_comm]

private theorem affineThreeFlatPairCharacterSum_split
    (f : BooleanFunction n) :
    (∑ p ∈ binaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2) =
      (∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) +
      ∑ p ∈ intersectingBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (binaryAffineThreeFlatPairs n) (fun p ↦ p.1 ⊓ p.2 = ⊥)
    (fun p ↦ binaryAffineFlatCharacter f p.1 *
      binaryAffineFlatCharacter f p.2)
  change
    (∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) +
      (∑ p ∈ intersectingBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) =
      ∑ p ∈ binaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2 at hsplit
  exact hsplit.symm

private theorem binaryAffineFlatCharacter_mul_le_one
    (f : BooleanFunction n)
    (A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineFlatCharacter f A * binaryAffineFlatCharacter f B ≤ 1 := by
  rcases binaryAffineFlatCharacter_eq_one_or_neg_one f A with hA | hA <;>
    rcases binaryAffineFlatCharacter_eq_one_or_neg_one f B with hB | hB <;>
    simp only [hA, hB] <;> norm_num

private theorem intersectingAffineThreeFlatPairCharacterSum_le_card
    (f : BooleanFunction n) :
    (∑ p ∈ intersectingBinaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2) ≤
      ((intersectingBinaryAffineThreeFlatPairs n).card : ℝ) := by
  calc
    (∑ p ∈ intersectingBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) ≤
        ∑ _p ∈ intersectingBinaryAffineThreeFlatPairs n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact binaryAffineFlatCharacter_mul_le_one f p.1 p.2
    _ = ((intersectingBinaryAffineThreeFlatPairs n).card : ℝ) := by simp

private theorem disjointAffineThreeFlatPairCharacterSum_ge_neg_card
    (f : BooleanFunction n) :
    (∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2) ≥
      -((intersectingBinaryAffineThreeFlatPairs n).card : ℝ) := by
  have hall : 0 ≤ ∑ p ∈ binaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2 := by
    rw [allAffineThreeFlatPairCharacterSum_eq_sq]
    positivity
  rw [affineThreeFlatPairCharacterSum_split] at hall
  have hintersecting :=
    intersectingAffineThreeFlatPairCharacterSum_le_card f
  linarith

/-- The disjoint-three-flat representation sum has the `O((2^n)^7)`
lower bound required by the seventh/eighth moment argument. -/
theorem weightSixteenRepresentationCharacterSum_ge
    (f : BooleanFunction n) :
    weightSixteenRepresentationCharacterSum f ≥
      -((2 ^ n : ℝ) ^ 7) / 2 := by
  have hsum := disjointAffineThreeFlatPairCharacterSum_ge_neg_card f
  have hcardNat := card_intersectingBinaryAffineThreeFlatPairs_le n
  have hcardReal :
      ((intersectingBinaryAffineThreeFlatPairs n).card : ℝ) ≤
        (((2 ^ n) ^ 7 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcardReal
  calc
    weightSixteenRepresentationCharacterSum f =
        (1 / 2 : ℝ) *
          ∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
            binaryAffineFlatCharacter f p.1 *
              binaryAffineFlatCharacter f p.2 := rfl
    _ ≥ (1 / 2 : ℝ) *
        -((intersectingBinaryAffineThreeFlatPairs n).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≥ -((2 ^ n : ℝ) ^ 7) / 2 := by
      nlinarith

/-- The ordered disjoint-flat representations of a Boolean word. -/
noncomputable def weightSixteenRepresentationFiber
    (h : BooleanFunction n) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  (disjointBinaryAffineThreeFlatPairs n).filter fun p ↦
    weightSixteenRepresentationWord p.1 p.2 = h

/-- The exact Kasami--Tokura exceptional-multiplicity interface.  Type `a`
words have thirty ordered representations, type `b` words have six, and
all remaining weight-sixteen words have two.  The zero fibers outside the
dual code also encode the existence classification. -/
def HasWeightSixteenExceptionalMultiplicity
    (typeA typeB : Finset (BooleanFunction n)) : Prop :=
  typeA ⊆ orderTwoWeightSixteenDualWords n ∧
    typeB ⊆ orderTwoWeightSixteenDualWords n ∧
    Disjoint typeA typeB ∧
    ∀ h : BooleanFunction n,
      (weightSixteenRepresentationFiber h).card =
        if h ∈ orderTwoWeightSixteenDualWords n then
          if h ∈ typeA then 30 else if h ∈ typeB then 6 else 2
        else 0

/-- The coarse consequences of the exact exceptional-word counts: type
`a` contributes `O((2^n)^5)` words and type `b` contributes
`O((2^n)^6)`. -/
def HasWeightSixteenExceptionalCountBounds
    (typeA typeB : Finset (BooleanFunction n)) : Prop :=
  typeA.card ≤ (2 ^ n) ^ 5 ∧ typeB.card ≤ (2 ^ n) ^ 6

private theorem sum_ite_mem_subset
    {s t : Finset (BooleanFunction n)}
    (hst : s ⊆ t) (g : BooleanFunction n → ℝ) :
    (∑ h ∈ t, if h ∈ s then g h else 0) = ∑ h ∈ s, g h := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext h
  simp only [Finset.mem_filter]
  constructor
  · exact fun hh ↦ hh.2
  · exact fun hh ↦ ⟨hst hh, hh⟩

private theorem binarySign_le_one (b : FABL.𝔽₂) :
    FABL.binarySign b ≤ 1 := by
  by_cases hb : b = 0
  · rw [hb]
    norm_num
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
    rw [hbOne, FABL.binarySign_one]
    norm_num

private theorem booleanWordCharacterSum_le_card
    (f : BooleanFunction n) (s : Finset (BooleanFunction n)) :
    (∑ h ∈ s, FABL.binarySign (booleanFunctionPairing n f h)) ≤
      (s.card : ℝ) := by
  calc
    (∑ h ∈ s, FABL.binarySign (booleanFunctionPairing n f h)) ≤
        ∑ _h ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h _hh
      exact binarySign_le_one (booleanFunctionPairing n f h)
    _ = (s.card : ℝ) := by simp

private theorem sum_disjointWeightSixteenRepresentations_eq
    (f : BooleanFunction n)
    (typeA typeB : Finset (BooleanFunction n))
    (hmultiplicity : HasWeightSixteenExceptionalMultiplicity typeA typeB) :
    (∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
      binaryAffineFlatCharacter f p.1 *
        binaryAffineFlatCharacter f p.2) =
      2 * orderTwoWeightSixteenCharacterSum f +
        28 * ∑ h ∈ typeA,
          FABL.binarySign (booleanFunctionPairing n f h) +
        4 * ∑ h ∈ typeB,
          FABL.binarySign (booleanFunctionPairing n f h) := by
  classical
  have htypeA := hmultiplicity.1
  have htypeB := hmultiplicity.2.1
  have hdisjoint := hmultiplicity.2.2.1
  have htypeASum := sum_ite_mem_subset htypeA
    (fun h ↦ 28 * FABL.binarySign (booleanFunctionPairing n f h))
  have htypeBSum := sum_ite_mem_subset htypeB
    (fun h ↦ 4 * FABL.binarySign (booleanFunctionPairing n f h))
  calc
    (∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
        binaryAffineFlatCharacter f p.1 *
          binaryAffineFlatCharacter f p.2) =
        ∑ p ∈ disjointBinaryAffineThreeFlatPairs n,
          FABL.binarySign (booleanFunctionPairing n f
            (weightSixteenRepresentationWord p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [weightSixteenRepresentationWord_character]
    _ = ∑ h ∈ orderTwoWeightSixteenDualWords n,
        ∑ p ∈ weightSixteenRepresentationFiber h,
          FABL.binarySign (booleanFunctionPairing n f
            (weightSixteenRepresentationWord p.1 p.2)) := by
      symm
      unfold weightSixteenRepresentationFiber
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      exact weightSixteenRepresentationWord_mem_dualWords p.1 p.2 hp
    _ = ∑ h ∈ orderTwoWeightSixteenDualWords n,
        ((weightSixteenRepresentationFiber h).card : ℝ) *
          FABL.binarySign (booleanFunctionPairing n f h) := by
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        (∑ p ∈ weightSixteenRepresentationFiber h,
            FABL.binarySign (booleanFunctionPairing n f
              (weightSixteenRepresentationWord p.1 p.2))) =
            ∑ _p ∈ weightSixteenRepresentationFiber h,
              FABL.binarySign (booleanFunctionPairing n f h) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = ((weightSixteenRepresentationFiber h).card : ℝ) *
            FABL.binarySign (booleanFunctionPairing n f h) := by simp
    _ = ∑ h ∈ orderTwoWeightSixteenDualWords n,
        (2 * FABL.binarySign (booleanFunctionPairing n f h) +
          (if h ∈ typeA then
            28 * FABL.binarySign (booleanFunctionPairing n f h) else 0) +
          if h ∈ typeB then
            4 * FABL.binarySign (booleanFunctionPairing n f h) else 0) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [hmultiplicity.2.2.2 h, if_pos hh]
      by_cases hA : h ∈ typeA
      · have hB : h ∉ typeB := by
          intro hB
          exact (Finset.disjoint_left.mp hdisjoint) hA hB
        simp [hA, hB]
        ring
      · by_cases hB : h ∈ typeB
        · simp [hA, hB]
          ring
        · simp [hA, hB]
    _ = 2 * orderTwoWeightSixteenCharacterSum f +
        28 * ∑ h ∈ typeA,
          FABL.binarySign (booleanFunctionPairing n f h) +
        4 * ∑ h ∈ typeB,
          FABL.binarySign (booleanFunctionPairing n f h) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        htypeASum, htypeBSum]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

/-- Conditional on the cited exceptional-multiplicity classification, the
canonical weight-sixteen sum is the representation sum with the two
exceptional overcount corrections. -/
theorem orderTwoWeightSixteenCharacterSum_eq_representation_sub_exceptions
    (f : BooleanFunction n)
    (typeA typeB : Finset (BooleanFunction n))
    (hmultiplicity : HasWeightSixteenExceptionalMultiplicity typeA typeB) :
    orderTwoWeightSixteenCharacterSum f =
      weightSixteenRepresentationCharacterSum f -
        14 * ∑ h ∈ typeA,
          FABL.binarySign (booleanFunctionPairing n f h) -
        2 * ∑ h ∈ typeB,
          FABL.binarySign (booleanFunctionPairing n f h) := by
  rw [weightSixteenRepresentationCharacterSum,
    sum_disjointWeightSixteenRepresentations_eq
      f typeA typeB hmultiplicity]
  ring

/-- A conditional canonical lower bound retaining the sharper orders of
the two exceptional families. -/
theorem orderTwoWeightSixteenCharacterSum_ge
    (f : BooleanFunction n)
    (typeA typeB : Finset (BooleanFunction n))
    (hmultiplicity : HasWeightSixteenExceptionalMultiplicity typeA typeB)
    (hcounts : HasWeightSixteenExceptionalCountBounds typeA typeB) :
    orderTwoWeightSixteenCharacterSum f ≥
      -((2 ^ n : ℝ) ^ 7) / 2 - 14 * (2 ^ n : ℝ) ^ 5 -
        2 * (2 ^ n : ℝ) ^ 6 := by
  have hrepresentation := weightSixteenRepresentationCharacterSum_ge f
  have htypeASum := booleanWordCharacterSum_le_card f typeA
  have htypeBSum := booleanWordCharacterSum_le_card f typeB
  have htypeACard : (typeA.card : ℝ) ≤ (2 ^ n : ℝ) ^ 5 := by
    exact_mod_cast hcounts.1
  have htypeBCard : (typeB.card : ℝ) ≤ (2 ^ n : ℝ) ^ 6 := by
    exact_mod_cast hcounts.2
  rw [orderTwoWeightSixteenCharacterSum_eq_representation_sub_exceptions
    f typeA typeB hmultiplicity]
  linarith

end CryptBoolean
