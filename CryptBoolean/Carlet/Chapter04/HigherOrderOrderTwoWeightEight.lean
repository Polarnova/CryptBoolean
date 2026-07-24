/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderLowWeightFlats
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The weight-eight dual character sum

Carlet--Mesnager Proposition 9.2.10 for the minimum-weight words of
`RM(n - 3, n)`.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightEightAffineSubspaceFintype : Fintype
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance weightEightAffineSubspaceDecidableEq : DecidableEq
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

noncomputable local instance weightEightAffineSubspacePointFintype
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype A :=
  Fintype.ofFinite A

/-- The weight-eight words in the dual Reed--Muller code `RM(n - 3,n)`. -/
noncomputable def orderTwoWeightEightDualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoDualWords n).filter fun h ↦ hammingWeight h = 8

/-- Carlet--Mesnager's `M_f^(8)`, as a canonical dual-code character sum. -/
noncomputable def orderTwoWeightEightCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightEightDualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

private theorem mem_orderTwoWeightEightDualWords_iff_exists_flat
    (h : BooleanFunction n) (hn : 3 ≤ n) :
    h ∈ orderTwoWeightEightDualWords n ↔
      ∃ A ∈ binaryAffineFlats 3 n, h = binaryAffineFlatIndicator A := by
  classical
  constructor
  · intro hh
    have hh' :
        h ∈ reedMuller (n - 3) n ∧ hammingWeight h = 8 := by
      simpa only [orderTwoWeightEightDualWords, orderTwoDualWords,
        Finset.mem_filter, Finset.mem_univ, true_and] using hh
    have hdual : h ∈ reedMuller (n - 3) n := by
      exact hh'.1
    have hweight : hammingWeight h = 8 := hh'.2
    have hnonzero : h ≠ 0 := by
      intro hzero
      subst h
      simp at hweight
    have hdegreeLe : FABL.functionAlgebraicDegree h ≤ n - 3 := by
      simpa only [mem_reedMuller_iff] using hdual
    have hdegree : FABL.functionAlgebraicDegree h = n - 3 := by
      apply Nat.le_antisymm hdegreeLe
      by_contra hnot
      have hn4 : 4 ≤ n := by omega
      have hdegreeFour : FABL.functionAlgebraicDegree h ≤ n - 4 := by
        omega
      have hlower := two_pow_sub_le_hammingWeight_of_degree_le
        (r := n - 4) h hdegreeFour hnonzero
      have hexponent : n - (n - 4) = 4 := by omega
      rw [hexponent, hweight] at hlower
      norm_num at hlower
    have hweightPow : hammingWeight h = 2 ^ (n - (n - 3)) := by
      rw [hweight]
      have hexponent : n - (n - 3) = 3 := by omega
      rw [hexponent]
      norm_num
    obtain ⟨H, a, hHrank, hhIndicator⟩ :=
      (degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator
        h (r := n - 3) (by omega)).1 ⟨hdegree, hweightPow⟩
    let A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
      FABL.binaryAffineSubspace H a
    have hAmem : A ∈ binaryAffineFlats 3 n := by
      have hAne : A ≠ ⊥ := by
        intro hbot
        have haBot : a ∈ (⊥ :
            AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
          rw [← hbot]
          exact AffineSubspace.self_mem_mk' a H
        rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at haBot
        exact haBot
      have hArank : Module.finrank FABL.𝔽₂ A.direction = 3 := by
        change Module.finrank FABL.𝔽₂
          (FABL.binaryAffineSubspace H a).direction = 3
        rw [FABL.binaryAffineSubspace_direction]
        simpa only [show n - (n - 3) = 3 by omega] using hHrank
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using And.intro hAne hArank
    refine ⟨A, hAmem, ?_⟩
    rw [hhIndicator]
    have hdirection : A.direction = H := by
      exact FABL.binaryAffineSubspace_direction H a
    rw [← hdirection]
    exact (binaryAffineFlatIndicator_eq_affineFlatIndicator A a
      (AffineSubspace.self_mem_mk' a H)).symm
  · rintro ⟨A, hAmem, rfl⟩
    have hAdata : A ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ A.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAmem
    have hA : A ≠ ⊥ := by
      exact hAdata.1
    have hArank : Module.finrank FABL.𝔽₂ A.direction = 3 := by
      exact hAdata.2
    obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hA
    have hdegree :
        FABL.functionAlgebraicDegree (binaryAffineFlatIndicator A) = n - 3 := by
      rw [binaryAffineFlatIndicator_eq_affineFlatIndicator A a ha,
        functionAlgebraicDegree_affineFlatIndicator, FABL.f₂Codimension,
        FABL.finrank_perpendicularSubspace, hArank]
    have hdual : binaryAffineFlatIndicator A ∈ reedMuller (n - 3) n := by
      simpa only [mem_reedMuller_iff] using hdegree.le
    have hweight : hammingWeight (binaryAffineFlatIndicator A) = 8 := by
      rw [hammingWeight_binaryAffineFlatIndicator A hA, hArank]
      norm_num
    simp only [orderTwoWeightEightDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hdual, hweight⟩

/-- Minimum-weight classification identifies the weight-eight dual words
with the indicators of the canonical three-dimensional affine flats. -/
theorem orderTwoWeightEightDualWords_eq_affineFlatIndicators
    (hn : 3 ≤ n) :
    orderTwoWeightEightDualWords n =
      (binaryAffineFlats 3 n).image binaryAffineFlatIndicator := by
  classical
  ext h
  rw [Finset.mem_image]
  exact (mem_orderTwoWeightEightDualWords_iff_exists_flat h hn).trans
    (exists_congr fun A ↦ and_congr_right fun _ ↦ eq_comm)

/-- The dual-code definition of `M_f^(8)` is the affine-three-flat
character sum used in Proposition 9.2.10. -/
theorem orderTwoWeightEightCharacterSum_eq_affineFlatCharacterSum
    (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoWeightEightCharacterSum f =
      binaryAffineFlatCharacterSum 3 f := by
  classical
  rw [orderTwoWeightEightCharacterSum,
    orderTwoWeightEightDualWords_eq_affineFlatIndicators hn,
    binaryAffineFlatCharacterSum]
  rw [Finset.sum_image]
  · rfl
  · intro A hA B hB hAB
    have hAdata : A ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ A.direction = 3 := by
      have hA' : A ∈ binaryAffineFlats 3 n := hA
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hA'
    have hBdata : B ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ B.direction = 3 := by
      have hB' : B ∈ binaryAffineFlats 3 n := hB
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hB'
    exact binaryAffineFlatIndicator_injective_on_nonempty
      hAdata.1 hBdata.1
      hAB

private abbrev AffinePlaneEmbedding (n : ℕ) :=
  Fin 3 ↪ FABL.F₂Cube n

private def affinePlaneFirstDirection
    (e : AffinePlaneEmbedding n) : FABL.F₂Cube n :=
  e 1 + e 0

private def affinePlaneSecondDirection
    (e : AffinePlaneEmbedding n) : FABL.F₂Cube n :=
  e 2 + e 0

private theorem affinePlaneFirstDirection_ne_zero
    (e : AffinePlaneEmbedding n) :
    affinePlaneFirstDirection e ≠ 0 := by
  intro hzero
  have heq : e 1 + e 0 = e 0 + e 0 :=
    hzero.trans (ZModModule.add_self (e 0)).symm
  have hindices : (1 : Fin 3) = 0 :=
    e.injective (add_right_cancel heq)
  norm_num at hindices

private theorem affinePlaneSecondDirection_ne_zero
    (e : AffinePlaneEmbedding n) :
    affinePlaneSecondDirection e ≠ 0 := by
  intro hzero
  have heq : e 2 + e 0 = e 0 + e 0 :=
    hzero.trans (ZModModule.add_self (e 0)).symm
  have hindices : (2 : Fin 3) = 0 :=
    e.injective (add_right_cancel heq)
  omega

private theorem affinePlaneDirections_ne
    (e : AffinePlaneEmbedding n) :
    affinePlaneFirstDirection e ≠ affinePlaneSecondDirection e := by
  intro heq
  have hpoints : e 1 = e 2 := add_right_cancel heq
  have hindices : (1 : Fin 3) = 2 := e.injective hpoints
  omega

private theorem affinePlaneSecondDirection_not_mem_firstSpan
    (e : AffinePlaneEmbedding n) :
    affinePlaneSecondDirection e ∉
      FABL.𝔽₂ ∙ affinePlaneFirstDirection e := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨c, hc⟩
  by_cases hczero : c = 0
  · subst c
    simp only [zero_smul] at hc
    exact affinePlaneSecondDirection_ne_zero e hc.symm
  · have hcone : c = 1 := Fin.eq_one_of_ne_zero c hczero
    subst c
    simp only [one_smul] at hc
    exact affinePlaneDirections_ne e hc

private noncomputable def affinePlaneThroughEmbedding
    (e : AffinePlaneEmbedding n) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.binaryAffineSubspace
    ((FABL.𝔽₂ ∙ affinePlaneFirstDirection e) ⊔
      (FABL.𝔽₂ ∙ affinePlaneSecondDirection e))
    (e 0)

private theorem affinePlaneThroughEmbedding_direction_finrank
    (e : AffinePlaneEmbedding n) :
    Module.finrank FABL.𝔽₂ (affinePlaneThroughEmbedding e).direction = 2 := by
  rw [affinePlaneThroughEmbedding, FABL.binaryAffineSubspace_direction,
    Submodule.finrank_sup_span_singleton
      (affinePlaneSecondDirection_not_mem_firstSpan e),
    finrank_span_singleton (affinePlaneFirstDirection_ne_zero e)]

private theorem affinePlaneThroughEmbedding_ne_bot
    (e : AffinePlaneEmbedding n) :
    affinePlaneThroughEmbedding e ≠ ⊥ := by
  intro hbot
  have hmem : e 0 ∈ (⊥ :
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
    rw [← hbot]
    exact AffineSubspace.self_mem_mk' _ _
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hmem
  exact hmem

private theorem affinePlaneThroughEmbedding_mem_flats
    (e : AffinePlaneEmbedding n) :
    affinePlaneThroughEmbedding e ∈ binaryAffineFlats 2 n := by
  simp only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨affinePlaneThroughEmbedding_ne_bot e,
    affinePlaneThroughEmbedding_direction_finrank e⟩

private theorem neg_f₂Cube (x : FABL.F₂Cube n) : -x = x := by
  funext i
  exact ZMod.neg_eq_self_mod_two (x i)

private theorem affinePlaneEmbedding_mem
    (e : AffinePlaneEmbedding n) (i : Fin 3) :
    e i ∈ affinePlaneThroughEmbedding e := by
  fin_cases i
  · exact AffineSubspace.self_mem_mk' _ _
  · rw [affinePlaneThroughEmbedding,
      FABL.mem_binaryAffineSubspace_iff_add_mem]
    exact (le_sup_left :
      FABL.𝔽₂ ∙ affinePlaneFirstDirection e ≤
        (FABL.𝔽₂ ∙ affinePlaneFirstDirection e) ⊔
          (FABL.𝔽₂ ∙ affinePlaneSecondDirection e))
      (Submodule.mem_span_singleton_self (affinePlaneFirstDirection e))
  · rw [affinePlaneThroughEmbedding,
      FABL.mem_binaryAffineSubspace_iff_add_mem]
    exact (le_sup_right :
      FABL.𝔽₂ ∙ affinePlaneSecondDirection e ≤
        (FABL.𝔽₂ ∙ affinePlaneFirstDirection e) ⊔
          (FABL.𝔽₂ ∙ affinePlaneSecondDirection e))
      (Submodule.mem_span_singleton_self (affinePlaneSecondDirection e))

private def affinePlaneEmbeddingOfSubtype
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (e : Fin 3 ↪ A) : AffinePlaneEmbedding n :=
  e.trans (Function.Embedding.subtype _)

private theorem affinePlaneThroughEmbeddingOfSubtype_eq
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats 2 n) (e : Fin 3 ↪ A) :
    affinePlaneThroughEmbedding (affinePlaneEmbeddingOfSubtype A e) = A := by
  have hAdata : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  let e' := affinePlaneEmbeddingOfSubtype A e
  have hfirst : affinePlaneFirstDirection e' ∈ A.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction (e 1).2 (e 0).2
    change (e 1 : FABL.F₂Cube n) - (e 0 : FABL.F₂Cube n) ∈ A.direction at hvsub
    rw [sub_eq_add_neg, neg_f₂Cube] at hvsub
    simpa only [affinePlaneFirstDirection, e', affinePlaneEmbeddingOfSubtype,
      Function.Embedding.trans_apply, Function.Embedding.subtype_apply] using hvsub
  have hsecond : affinePlaneSecondDirection e' ∈ A.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction (e 2).2 (e 0).2
    change (e 2 : FABL.F₂Cube n) - (e 0 : FABL.F₂Cube n) ∈ A.direction at hvsub
    rw [sub_eq_add_neg, neg_f₂Cube] at hvsub
    simpa only [affinePlaneSecondDirection, e', affinePlaneEmbeddingOfSubtype,
      Function.Embedding.trans_apply, Function.Embedding.subtype_apply] using hvsub
  have hdirectionLe : (affinePlaneThroughEmbedding e').direction ≤ A.direction := by
    rw [affinePlaneThroughEmbedding, FABL.binaryAffineSubspace_direction]
    exact sup_le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hfirst))
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hsecond))
  have hdirection : (affinePlaneThroughEmbedding e').direction = A.direction := by
    apply Submodule.eq_of_le_of_finrank_eq hdirectionLe
    rw [affinePlaneThroughEmbedding_direction_finrank, hAdata.2]
  apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (affinePlaneEmbedding_mem e' 0) (e 0).2).2
  exact hdirection

private noncomputable def affinePlaneFiberEquiv
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats 2 n) :
    {e : AffinePlaneEmbedding n // affinePlaneThroughEmbedding e = A} ≃
      (Fin 3 ↪ A) where
  toFun e :=
    { toFun := fun i ↦ ⟨e.1 i, by
        have hi := affinePlaneEmbedding_mem e.1 i
        simpa only [e.2] using hi⟩
      inj' := fun _ _ hij ↦ e.1.injective (congrArg Subtype.val hij) }
  invFun e :=
    ⟨affinePlaneEmbeddingOfSubtype A e,
      affinePlaneThroughEmbeddingOfSubtype_eq A hA e⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    rfl

private theorem affinePlaneFiber_card
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats 2 n) :
    ((Finset.univ : Finset (AffinePlaneEmbedding n)).filter fun e ↦
      affinePlaneThroughEmbedding e = A).card = 24 := by
  classical
  have hAdata : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (affinePlaneFiberEquiv A hA),
    Fintype.card_embedding_eq]
  have hcardA : Fintype.card A = 4 := by
    rw [Fintype.card_subtype]
    change (binaryAffineFlatPoints A).card = 4
    rw [card_binaryAffineFlatPoints A hAdata.1, hAdata.2]
    norm_num
  rw [hcardA]
  decide

/-- The number of affine two-flats is
`2^n (2^n - 1) (2^n - 2) / 24`, in division-free form. -/
theorem card_binaryAffineFlats_two (n : ℕ) :
    (binaryAffineFlats 2 n).card * 24 =
      2 ^ n * (2 ^ n - 1) * (2 ^ n - 2) := by
  classical
  have hmaps :
      ((Finset.univ : Finset (AffinePlaneEmbedding n)) :
          Set (AffinePlaneEmbedding n)).MapsTo
        affinePlaneThroughEmbedding (binaryAffineFlats 2 n) := by
    intro e _he
    exact affinePlaneThroughEmbedding_mem_flats e
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (binaryAffineFlats 2 n).card * 24 =
        ∑ A ∈ binaryAffineFlats 2 n,
          (((Finset.univ : Finset (AffinePlaneEmbedding n)).filter fun e ↦
            affinePlaneThroughEmbedding e = A).card) := by
      symm
      exact Finset.sum_const_nat fun A hA ↦ affinePlaneFiber_card A hA
    _ = (Finset.univ : Finset (AffinePlaneEmbedding n)).card := hfiber.symm
    _ = (2 ^ n).descFactorial 3 := by
      rw [Finset.card_univ, Fintype.card_embedding_eq,
        Fintype.card_fin, card_f₂Cube]
    _ = 2 ^ n * (2 ^ n - 1) * (2 ^ n - 2) := by
      simp [Nat.descFactorial_succ]
      ring

private noncomputable def parallelAffinePlanePairs (n : ℕ) :
    Finset
      (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact ((binaryAffineFlats 2 n).product (binaryAffineFlats 2 n)).filter
    fun p ↦ p.1.direction = p.2.direction

private noncomputable def distinctParallelAffinePlanePairs (n : ℕ) :
    Finset
      (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (parallelAffinePlanePairs n).filter fun p ↦ p.1 ≠ p.2

private def affineThreeFlatOfParallelPair
    (p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  p.1 ⊔ p.2

private theorem affinePlaneData_of_mem_parallelPairs
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ parallelAffinePlanePairs n) :
    p.1 ∈ binaryAffineFlats 2 n ∧
      p.2 ∈ binaryAffineFlats 2 n ∧
      p.1.direction = p.2.direction := by
  have hp' :
      p ∈ (binaryAffineFlats 2 n).product (binaryAffineFlats 2 n) ∧
        p.1.direction = p.2.direction := by
    simpa only [parallelAffinePlanePairs, Finset.mem_filter] using hp
  have hproduct := Finset.mem_product.mp hp'.1
  exact ⟨hproduct.1, hproduct.2, hp'.2⟩

private theorem affinePlaneData_of_mem_distinctParallelPairs
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n) :
    p.1 ∈ binaryAffineFlats 2 n ∧
      p.2 ∈ binaryAffineFlats 2 n ∧
      p.1.direction = p.2.direction ∧ p.1 ≠ p.2 := by
  have hp' : p ∈ parallelAffinePlanePairs n ∧ p.1 ≠ p.2 := by
    simpa only [distinctParallelAffinePlanePairs, Finset.mem_filter] using hp
  obtain ⟨hfirst, hsecond, hdirection⟩ :=
    affinePlaneData_of_mem_parallelPairs hp'.1
  exact ⟨hfirst, hsecond, hdirection, hp'.2⟩

private theorem parallelAffinePlanes_disjoint
    {A B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hdirection : A.direction = B.direction) (hne : A ≠ B) :
    Disjoint (binaryAffineFlatPoints A) (binaryAffineFlatPoints B) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  apply hne
  have hxA' : x ∈ A := by
    simpa only [binaryAffineFlatPoints, Finset.mem_filter,
      Finset.mem_univ, true_and] using hxA
  have hxB' : x ∈ B := by
    simpa only [binaryAffineFlatPoints, Finset.mem_filter,
      Finset.mem_univ, true_and] using hxB
  exact (AffineSubspace.eq_iff_direction_eq_of_mem hxA' hxB').2 hdirection

private theorem affineThreeFlatOfParallelPair_mem_flats
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n) :
    affineThreeFlatOfParallelPair p ∈ binaryAffineFlats 3 n := by
  obtain ⟨hA, hB, hdirection, hne⟩ :=
    affinePlaneData_of_mem_distinctParallelPairs hp
  have hAdata : p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hBdata : p.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hB
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot p.1).2 hAdata.1
  obtain ⟨b, hb⟩ := (AffineSubspace.nonempty_iff_ne_bot p.2).2 hBdata.1
  have hdifference : b -ᵥ a ∉ p.1.direction := by
    intro hdifference
    have hbA : b ∈ p.1 := by
      simpa only [vsub_vadd] using
        (AffineSubspace.vadd_mem_of_mem_direction hdifference ha)
    exact hne (AffineSubspace.ext_of_direction_eq hdirection ⟨b, hbA, hb⟩)
  have hnebot : affineThreeFlatOfParallelPair p ≠ ⊥ := by
    intro hbot
    have haBot : a ∈ (⊥ :
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
      rw [← hbot]
      exact (le_sup_left : p.1 ≤ p.1 ⊔ p.2) ha
    rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at haBot
    exact haBot
  have hrank : Module.finrank FABL.𝔽₂
      (affineThreeFlatOfParallelPair p).direction = 3 := by
    rw [affineThreeFlatOfParallelPair,
      AffineSubspace.direction_sup ha hb, ← hdirection, sup_idem,
      Submodule.finrank_sup_span_singleton hdifference, hAdata.2]
  simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
    true_and] using And.intro hnebot hrank

private theorem points_affineThreeFlatOfParallelPair
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n) :
    binaryAffineFlatPoints (affineThreeFlatOfParallelPair p) =
      binaryAffineFlatPoints p.1 ∪ binaryAffineFlatPoints p.2 := by
  obtain ⟨hA, hB, hdirection, hne⟩ :=
    affinePlaneData_of_mem_distinctParallelPairs hp
  have hAdata : p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  have hBdata : p.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hB
  have hC := affineThreeFlatOfParallelPair_mem_flats hp
  have hCdata : affineThreeFlatOfParallelPair p ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂
        (affineThreeFlatOfParallelPair p).direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_union] at hx
    simp only [binaryAffineFlatPoints, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    exact hx.elim (fun hxA ↦ (le_sup_left : p.1 ≤ p.1 ⊔ p.2) hxA)
      (fun hxB ↦ (le_sup_right : p.2 ≤ p.1 ⊔ p.2) hxB)
  · rw [card_binaryAffineFlatPoints _ hCdata.1, hCdata.2,
      Finset.card_union_of_disjoint
        (parallelAffinePlanes_disjoint hdirection hne),
      card_binaryAffineFlatPoints _ hAdata.1, hAdata.2,
      card_binaryAffineFlatPoints _ hBdata.1, hBdata.2]
    norm_num

private theorem indicator_affineThreeFlatOfParallelPair
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n) :
    binaryAffineFlatIndicator (affineThreeFlatOfParallelPair p) =
      binaryAffineFlatIndicator p.1 + binaryAffineFlatIndicator p.2 := by
  have hpoints := points_affineThreeFlatOfParallelPair hp
  have hdisjoint := parallelAffinePlanes_disjoint
    (affinePlaneData_of_mem_distinctParallelPairs hp).2.2.1
    (affinePlaneData_of_mem_distinctParallelPairs hp).2.2.2
  exact binaryAffineFlatIndicator_eq_add_of_points_eq_union
    p.1 p.2 (affineThreeFlatOfParallelPair p) hpoints hdisjoint

private theorem character_affineThreeFlatOfParallelPair
    (f : BooleanFunction n)
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n) :
    binaryAffineFlatCharacter f (affineThreeFlatOfParallelPair p) =
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2 := by
  exact binaryAffineFlatCharacter_eq_mul_of_indicator_eq_add
    f p.1 p.2 (affineThreeFlatOfParallelPair p)
      (indicator_affineThreeFlatOfParallelPair hp)

private noncomputable def affinePlanesIn
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineFlats 2 n).filter fun A ↦ A ≤ C

private theorem affinePlaneThroughEmbeddingOfSubtype_le
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (e : Fin 3 ↪ C) :
    affinePlaneThroughEmbedding (affinePlaneEmbeddingOfSubtype C e) ≤ C := by
  let e' := affinePlaneEmbeddingOfSubtype C e
  have hfirst : affinePlaneFirstDirection e' ∈ C.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction (e 1).2 (e 0).2
    change (e 1 : FABL.F₂Cube n) - (e 0 : FABL.F₂Cube n) ∈ C.direction at hvsub
    rw [sub_eq_add_neg, neg_f₂Cube] at hvsub
    simpa only [affinePlaneFirstDirection, e', affinePlaneEmbeddingOfSubtype,
      Function.Embedding.trans_apply, Function.Embedding.subtype_apply] using hvsub
  have hsecond : affinePlaneSecondDirection e' ∈ C.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction (e 2).2 (e 0).2
    change (e 2 : FABL.F₂Cube n) - (e 0 : FABL.F₂Cube n) ∈ C.direction at hvsub
    rw [sub_eq_add_neg, neg_f₂Cube] at hvsub
    simpa only [affinePlaneSecondDirection, e', affinePlaneEmbeddingOfSubtype,
      Function.Embedding.trans_apply, Function.Embedding.subtype_apply] using hvsub
  have hdirectionLe : (affinePlaneThroughEmbedding e').direction ≤ C.direction := by
    rw [affinePlaneThroughEmbedding, FABL.binaryAffineSubspace_direction]
    exact sup_le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hfirst))
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hsecond))
  intro x hx
  have hbase : (e' 0) ∈ C := (e 0).2
  have hdiffPlane : x -ᵥ e' 0 ∈ (affinePlaneThroughEmbedding e').direction :=
    AffineSubspace.vsub_mem_direction hx (affinePlaneEmbedding_mem e' 0)
  have hdiffC : x -ᵥ e' 0 ∈ C.direction := hdirectionLe hdiffPlane
  simpa only [vsub_vadd] using
    (AffineSubspace.vadd_mem_of_mem_direction hdiffC hbase)

private theorem affinePlaneThroughSubtype_mem_affinePlanesIn
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (e : Fin 3 ↪ C) :
    affinePlaneThroughEmbedding (affinePlaneEmbeddingOfSubtype C e) ∈
      affinePlanesIn C := by
  simp only [affinePlanesIn, Finset.mem_filter]
  exact ⟨affinePlaneThroughEmbedding_mem_flats _,
    affinePlaneThroughEmbeddingOfSubtype_le C e⟩

private noncomputable def affinePlaneInFiberEquiv
    (C A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ affinePlanesIn C) :
    {e : Fin 3 ↪ C //
      affinePlaneThroughEmbedding (affinePlaneEmbeddingOfSubtype C e) = A} ≃
      (Fin 3 ↪ A) where
  toFun e :=
    { toFun := fun i ↦ ⟨e.1 i, by
        have hi := affinePlaneEmbedding_mem
          (affinePlaneEmbeddingOfSubtype C e.1) i
        have hset :
            (affinePlaneThroughEmbedding
                (affinePlaneEmbeddingOfSubtype C e.1) : Set (FABL.F₂Cube n)) =
              (A : Set (FABL.F₂Cube n)) := congrArg SetLike.coe e.2
        have hiA :
            affinePlaneEmbeddingOfSubtype C e.1 i ∈ (A : Set (FABL.F₂Cube n)) :=
          (Set.ext_iff.mp hset _).mp hi
        change (e.1 i : FABL.F₂Cube n) ∈ (A : Set (FABL.F₂Cube n)) at hiA
        change (e.1 i : FABL.F₂Cube n) ∈ (A : Set (FABL.F₂Cube n))
        exact hiA⟩
      inj' := by
        intro i j hij
        have hval : (e.1 i : FABL.F₂Cube n) =
            (e.1 j : FABL.F₂Cube n) :=
          congrArg (fun z : A ↦ (z : FABL.F₂Cube n)) hij
        apply e.1.injective
        apply Subtype.ext
        exact hval }
  invFun e := by
    have hAdata : A ∈ binaryAffineFlats 2 n ∧ A ≤ C := by
      simpa only [affinePlanesIn, Finset.mem_filter] using hA
    let eC : Fin 3 ↪ C :=
      { toFun := fun i ↦ ⟨e i, hAdata.2 (e i).2⟩
        inj' := by
          intro i j hij
          have hval : (e i : FABL.F₂Cube n) =
              (e j : FABL.F₂Cube n) :=
            congrArg (fun z : C ↦ (z : FABL.F₂Cube n)) hij
          apply e.injective
          apply Subtype.ext
          exact hval }
    refine ⟨eC, ?_⟩
    have hembedding : affinePlaneEmbeddingOfSubtype C eC =
        affinePlaneEmbeddingOfSubtype A e := by
      apply Function.Embedding.ext
      intro i
      rfl
    rw [hembedding]
    exact affinePlaneThroughEmbeddingOfSubtype_eq A hAdata.1 e
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    rfl

private theorem affinePlaneInFiber_card
    (C A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ affinePlanesIn C) :
    ((Finset.univ : Finset (Fin 3 ↪ C)).filter fun e ↦
      affinePlaneThroughEmbedding (affinePlaneEmbeddingOfSubtype C e) = A).card = 24 := by
  classical
  have hAdata : A ∈ binaryAffineFlats 2 n ∧ A ≤ C := by
    simpa only [affinePlanesIn, Finset.mem_filter] using hA
  have hAflat : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hAdata.1
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (affinePlaneInFiberEquiv C A hA),
    Fintype.card_embedding_eq]
  have hcardA : Fintype.card A = 4 := by
    rw [Fintype.card_subtype]
    change (binaryAffineFlatPoints A).card = 4
    rw [card_binaryAffineFlatPoints A hAflat.1, hAflat.2]
    norm_num
  rw [hcardA]
  decide

private theorem card_affinePlanesIn
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 3 n) :
    (affinePlanesIn C).card = 14 := by
  classical
  have hCdata : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  have hmaps :
      ((Finset.univ : Finset (Fin 3 ↪ C)) : Set (Fin 3 ↪ C)).MapsTo
        (fun e ↦ affinePlaneThroughEmbedding
          (affinePlaneEmbeddingOfSubtype C e)) (affinePlanesIn C) := by
    intro e _he
    exact affinePlaneThroughSubtype_mem_affinePlanesIn C e
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  have hcardC : Fintype.card C = 8 := by
    rw [Fintype.card_subtype]
    change (binaryAffineFlatPoints C).card = 8
    rw [card_binaryAffineFlatPoints C hCdata.1, hCdata.2]
    norm_num
  have hcount : (affinePlanesIn C).card * 24 = 336 := by
    calc
      (affinePlanesIn C).card * 24 =
          ∑ A ∈ affinePlanesIn C,
            (((Finset.univ : Finset (Fin 3 ↪ C)).filter fun e ↦
              affinePlaneThroughEmbedding
                (affinePlaneEmbeddingOfSubtype C e) = A).card) := by
        symm
        exact Finset.sum_const_nat fun A hA ↦ affinePlaneInFiber_card C A hA
      _ = (Finset.univ : Finset (Fin 3 ↪ C)).card := hfiber.symm
      _ = 336 := by
        rw [Finset.card_univ, Fintype.card_embedding_eq,
          Fintype.card_fin, hcardC]
        decide
  omega

private theorem mem_affineThreeFlatOfParallelPair_iff
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n)
    (x : FABL.F₂Cube n) :
    x ∈ affineThreeFlatOfParallelPair p ↔ x ∈ p.1 ∨ x ∈ p.2 := by
  have hpoints := points_affineThreeFlatOfParallelPair hp
  have hx := Finset.ext_iff.mp hpoints x
  simpa only [binaryAffineFlatPoints, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union] using hx

private theorem exists_parallelAffinePlaneComplement
    (C A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 3 n)
    (hA : A ∈ affinePlanesIn C) :
    ∃ B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n),
      (A, B) ∈ distinctParallelAffinePlanePairs n ∧ A ⊔ B = C := by
  have hCdata : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  have hAdata : A ∈ binaryAffineFlats 2 n ∧ A ≤ C := by
    simpa only [affinePlanesIn, Finset.mem_filter] using hA
  have hAflat : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 2 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hAdata.1
  have hdirectionLe : A.direction ≤ C.direction :=
    AffineSubspace.direction_le hAdata.2
  have hdirectionLt : A.direction < C.direction :=
    Submodule.lt_of_le_of_finrank_lt_finrank hdirectionLe (by
      rw [hAflat.2, hCdata.2]
      omega)
  obtain ⟨d, hdC, hdA⟩ := SetLike.exists_of_lt hdirectionLt
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hAflat.1
  let b : FABL.F₂Cube n := d +ᵥ a
  have haC : a ∈ C := hAdata.2 ha
  have hbC : b ∈ C := by
    exact AffineSubspace.vadd_mem_of_mem_direction hdC haC
  have hbA : b ∉ A := by
    intro hbA
    have hdirection := AffineSubspace.vsub_mem_direction hbA ha
    have hdb : b -ᵥ a = d := by simp [b]
    exact hdA (hdb ▸ hdirection)
  let B : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.binaryAffineSubspace A.direction b
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hbBot : b ∈ (⊥ :
        AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
      rw [← hbot]
      exact AffineSubspace.self_mem_mk' _ _
    rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hbBot
    exact hbBot
  have hBflat : B ∈ binaryAffineFlats 2 n := by
    have hBrank : Module.finrank FABL.𝔽₂ B.direction = 2 := by
      change Module.finrank FABL.𝔽₂
        (FABL.binaryAffineSubspace A.direction b).direction = 2
      rw [FABL.binaryAffineSubspace_direction, hAflat.2]
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using And.intro hBne hBrank
  have hBdirection : B.direction = A.direction := by
    exact FABL.binaryAffineSubspace_direction A.direction b
  have hABne : A ≠ B := by
    intro hAB
    apply hbA
    rw [hAB]
    exact AffineSubspace.self_mem_mk' _ _
  have hpair : (A, B) ∈ distinctParallelAffinePlanePairs n := by
    have hparallel : (A, B) ∈ parallelAffinePlanePairs n := by
      simp only [parallelAffinePlanePairs, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hAdata.1, hBflat⟩,
        hBdirection.symm⟩
    simpa only [distinctParallelAffinePlanePairs, Finset.mem_filter] using
      And.intro hparallel hABne
  have hBle : B ≤ C := by
    intro x hx
    have hdiffB : x -ᵥ b ∈ B.direction :=
      AffineSubspace.vsub_mem_direction hx (AffineSubspace.self_mem_mk' _ _)
    have hdiffC : x -ᵥ b ∈ C.direction := by
      rw [hBdirection] at hdiffB
      exact hdirectionLe hdiffB
    simpa only [vsub_vadd] using
      (AffineSubspace.vadd_mem_of_mem_direction hdiffC hbC)
  have hhullLe : A ⊔ B ≤ C := sup_le hAdata.2 hBle
  have hhullFlat := affineThreeFlatOfParallelPair_mem_flats hpair
  have hhullData : A ⊔ B ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ (A ⊔ B).direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and, affineThreeFlatOfParallelPair] using hhullFlat
  have hdirectionHull : (A ⊔ B).direction = C.direction := by
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hhullLe)
    rw [hhullData.2, hCdata.2]
  have hhull : A ⊔ B = C :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirectionHull
      ⟨a, (le_sup_left : A ≤ A ⊔ B) ha⟩ hhullLe
  exact ⟨B, hpair, hhull⟩

private theorem distinctParallelPair_eq_of_first_eq_of_hull_eq
    {p q : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ distinctParallelAffinePlanePairs n)
    (hq : q ∈ distinctParallelAffinePlanePairs n)
    (hfirst : p.1 = q.1)
    (hhull : affineThreeFlatOfParallelPair p =
      affineThreeFlatOfParallelPair q) :
    p = q := by
  apply Prod.ext
  · exact hfirst
  · obtain ⟨hpA, hpB, hpdir, hpne⟩ :=
      affinePlaneData_of_mem_distinctParallelPairs hp
    obtain ⟨hqA, hqB, hqdir, hqne⟩ :=
      affinePlaneData_of_mem_distinctParallelPairs hq
    have hpBdata : p.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.direction = 2 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hpB
    obtain ⟨b, hb⟩ := (AffineSubspace.nonempty_iff_ne_bot p.2).2 hpBdata.1
    have hbNotFirst : b ∉ p.1 := by
      intro hbFirst
      exact hpne (AffineSubspace.ext_of_direction_eq hpdir ⟨b, hbFirst, hb⟩)
    have hbNotQfirst : b ∉ q.1 := by
      rw [← hfirst]
      exact hbNotFirst
    have hbHullQ : b ∈ affineThreeFlatOfParallelPair q := by
      rw [← hhull]
      exact (le_sup_right : p.2 ≤ p.1 ⊔ p.2) hb
    have hbQ : b ∈ q.2 :=
      ((mem_affineThreeFlatOfParallelPair_iff hq b).1 hbHullQ).resolve_left hbNotQfirst
    have hdirection : p.2.direction = q.2.direction :=
      hpdir.symm.trans ((congrArg AffineSubspace.direction hfirst).trans hqdir)
    exact AffineSubspace.ext_of_direction_eq hdirection ⟨b, hb, hbQ⟩

private theorem parallelPairFiber_card
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 3 n) :
    ((distinctParallelAffinePlanePairs n).filter fun p ↦
      affineThreeFlatOfParallelPair p = C).card = 14 := by
  classical
  rw [← card_affinePlanesIn C hC]
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' : p ∈ distinctParallelAffinePlanePairs n ∧
        affineThreeFlatOfParallelPair p = C := by
      simpa only [Finset.mem_filter] using hp
    simp only [affinePlanesIn, Finset.mem_filter]
    exact ⟨(affinePlaneData_of_mem_distinctParallelPairs hp'.1).1,
      (le_sup_left : p.1 ≤ affineThreeFlatOfParallelPair p).trans_eq hp'.2⟩
  · intro p hp q hq hfirst
    have hp' : p ∈ distinctParallelAffinePlanePairs n ∧
        affineThreeFlatOfParallelPair p = C := by
      simpa only [Finset.mem_filter] using hp
    have hq' : q ∈ distinctParallelAffinePlanePairs n ∧
        affineThreeFlatOfParallelPair q = C := by
      simpa only [Finset.mem_filter] using hq
    exact distinctParallelPair_eq_of_first_eq_of_hull_eq
      hp'.1 hq'.1 hfirst (hp'.2.trans hq'.2.symm)
  · intro A hA
    obtain ⟨B, hpair, hhull⟩ :=
      exists_parallelAffinePlaneComplement C A hC hA
    refine ⟨(A, B), ?_, rfl⟩
    simpa only [Finset.mem_filter, affineThreeFlatOfParallelPair] using
      And.intro hpair hhull

private theorem distinctParallelPairCharacterSum_eq_fourteen_mul
    (f : BooleanFunction n) :
    (∑ p ∈ distinctParallelAffinePlanePairs n,
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
      14 * binaryAffineFlatCharacterSum 3 f := by
  classical
  calc
    (∑ p ∈ distinctParallelAffinePlanePairs n,
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
        ∑ C ∈ binaryAffineFlats 3 n,
          ∑ p ∈ (distinctParallelAffinePlanePairs n).filter fun p ↦
              affineThreeFlatOfParallelPair p = C,
            binaryAffineFlatCharacter f p.1 *
              binaryAffineFlatCharacter f p.2 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      exact affineThreeFlatOfParallelPair_mem_flats hp
    _ = ∑ C ∈ binaryAffineFlats 3 n,
          14 * binaryAffineFlatCharacter f C := by
      apply Finset.sum_congr rfl
      intro C hC
      calc
        (∑ p ∈ (distinctParallelAffinePlanePairs n).filter fun p ↦
              affineThreeFlatOfParallelPair p = C,
            binaryAffineFlatCharacter f p.1 *
              binaryAffineFlatCharacter f p.2) =
            ∑ p ∈ (distinctParallelAffinePlanePairs n).filter fun p ↦
                affineThreeFlatOfParallelPair p = C,
              binaryAffineFlatCharacter f C := by
          apply Finset.sum_congr rfl
          intro p hp
          have hp' : p ∈ distinctParallelAffinePlanePairs n ∧
              affineThreeFlatOfParallelPair p = C := by
            simpa only [Finset.mem_filter] using hp
          rw [← hp'.2, character_affineThreeFlatOfParallelPair f hp'.1]
        _ = 14 * binaryAffineFlatCharacter f C := by
          rw [Finset.sum_const, nsmul_eq_mul,
            parallelPairFiber_card C hC]
          norm_num
    _ = 14 * binaryAffineFlatCharacterSum 3 f := by
      rw [binaryAffineFlatCharacterSum]
      simp only [Finset.mul_sum]

private noncomputable def affinePlaneDirections (n : ℕ) :
    Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineFlats 2 n).image AffineSubspace.direction

private noncomputable def affinePlanesWithDirection
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineFlats 2 n).filter fun A ↦ A.direction = H

private theorem parallelPairFiber_eq_product
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    (parallelAffinePlanePairs n).filter (fun p ↦ p.1.direction = H) =
      (affinePlanesWithDirection H).product
        (affinePlanesWithDirection H) := by
  classical
  ext p
  constructor
  · intro hp
    have hpOuter := Finset.mem_filter.mp hp
    have hpParallel := Finset.mem_filter.mp hpOuter.1
    have hpProduct := Finset.mem_product.mp hpParallel.1
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨hpProduct.1, hpOuter.2⟩,
      Finset.mem_filter.mpr
        ⟨hpProduct.2, hpParallel.2.symm.trans hpOuter.2⟩⟩
  · intro hp
    have hpProduct := Finset.mem_product.mp hp
    have hpFirst := Finset.mem_filter.mp hpProduct.1
    have hpSecond := Finset.mem_filter.mp hpProduct.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ?_, hpFirst.2⟩
    exact ⟨Finset.mem_product.mpr ⟨hpFirst.1, hpSecond.1⟩,
      hpFirst.2.trans hpSecond.2.symm⟩

private theorem parallelPairCharacterSum_eq_directionSquares
    (f : BooleanFunction n) :
    (∑ p ∈ parallelAffinePlanePairs n,
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
      ∑ H ∈ affinePlaneDirections n,
        (∑ A ∈ affinePlanesWithDirection H,
          binaryAffineFlatCharacter f A) ^ 2 := by
  classical
  calc
    (∑ p ∈ parallelAffinePlanePairs n,
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
        ∑ H ∈ affinePlaneDirections n,
          ∑ p ∈ (parallelAffinePlanePairs n).filter fun p ↦
              p.1.direction = H,
            binaryAffineFlatCharacter f p.1 *
              binaryAffineFlatCharacter f p.2 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      have hpdata := affinePlaneData_of_mem_parallelPairs hp
      simp only [affinePlaneDirections, Finset.mem_image]
      exact ⟨p.1, hpdata.1, rfl⟩
    _ = ∑ H ∈ affinePlaneDirections n,
        (∑ A ∈ affinePlanesWithDirection H,
          binaryAffineFlatCharacter f A) ^ 2 := by
      apply Finset.sum_congr rfl
      intro H _hH
      rw [parallelPairFiber_eq_product]
      calc
        (∑ p ∈ (affinePlanesWithDirection H).product
              (affinePlanesWithDirection H),
            binaryAffineFlatCharacter f p.1 *
              binaryAffineFlatCharacter f p.2) =
            ∑ A ∈ affinePlanesWithDirection H,
              ∑ B ∈ affinePlanesWithDirection H,
                binaryAffineFlatCharacter f A *
                  binaryAffineFlatCharacter f B := by
          exact Finset.sum_product _ _ _
        _ = (∑ A ∈ affinePlanesWithDirection H,
            binaryAffineFlatCharacter f A) ^ 2 := by
          simp only [pow_two, Finset.mul_sum, mul_comm]

private theorem parallelPairCharacterSum_nonneg
    (f : BooleanFunction n) :
    0 ≤ ∑ p ∈ parallelAffinePlanePairs n,
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2 := by
  rw [parallelPairCharacterSum_eq_directionSquares]
  positivity

private theorem diagonalParallelAffinePlanePairs_eq_image :
    (parallelAffinePlanePairs n).filter (fun p ↦ ¬ p.1 ≠ p.2) =
      (binaryAffineFlats 2 n).image fun A ↦ (A, A) := by
  classical
  ext p
  constructor
  · intro hp
    have hp' : p ∈ parallelAffinePlanePairs n ∧ p.1 = p.2 := by
      simpa only [Finset.mem_filter, not_ne_iff] using hp
    have hpdata := affinePlaneData_of_mem_parallelPairs hp'.1
    apply Finset.mem_image.mpr
    refine ⟨p.1, hpdata.1, ?_⟩
    exact Prod.ext rfl hp'.2
  · intro hp
    obtain ⟨A, hA, hp⟩ := Finset.mem_image.mp hp
    subst p
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simp⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hA, hA⟩, rfl⟩

private theorem diagonalParallelPairCharacterSum_eq_card
    (f : BooleanFunction n) :
    (∑ p ∈ (parallelAffinePlanePairs n).filter (fun p ↦ ¬ p.1 ≠ p.2),
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
      ((binaryAffineFlats 2 n).card : ℝ) := by
  classical
  rw [diagonalParallelAffinePlanePairs_eq_image]
  rw [Finset.sum_image]
  · calc
      (∑ A ∈ binaryAffineFlats 2 n,
          binaryAffineFlatCharacter f A * binaryAffineFlatCharacter f A) =
          ∑ _A ∈ binaryAffineFlats 2 n, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro A _hA
        rw [← pow_two, sq_binaryAffineFlatCharacter]
      _ = ((binaryAffineFlats 2 n).card : ℝ) := by simp
  · intro A _hA B _hB hpair
    exact congrArg Prod.fst hpair

private theorem parallelPairCharacterSum_eq_distinct_add_card
    (f : BooleanFunction n) :
    (∑ p ∈ parallelAffinePlanePairs n,
      binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
      (∑ p ∈ distinctParallelAffinePlanePairs n,
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) +
        ((binaryAffineFlats 2 n).card : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (parallelAffinePlanePairs n) (fun p ↦ p.1 ≠ p.2)
    (fun p ↦ binaryAffineFlatCharacter f p.1 *
      binaryAffineFlatCharacter f p.2)
  change
    (∑ p ∈ distinctParallelAffinePlanePairs n,
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) +
      (∑ p ∈ (parallelAffinePlanePairs n).filter (fun p ↦ ¬ p.1 ≠ p.2),
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2) =
      ∑ p ∈ parallelAffinePlanePairs n,
        binaryAffineFlatCharacter f p.1 * binaryAffineFlatCharacter f p.2 at hsplit
  rw [diagonalParallelPairCharacterSum_eq_card f] at hsplit
  exact hsplit.symm

/-- The three-flat character sum is bounded below by minus one fourteenth
of the number of affine two-flats. -/
theorem binaryAffineFlatCharacterSum_three_ge_neg_card
    (f : BooleanFunction n) :
    binaryAffineFlatCharacterSum 3 f ≥
      -((binaryAffineFlats 2 n).card : ℝ) / 14 := by
  have hnonneg := parallelPairCharacterSum_nonneg f
  rw [parallelPairCharacterSum_eq_distinct_add_card,
    distinctParallelPairCharacterSum_eq_fourteen_mul] at hnonneg
  linarith

/-- Carlet--Mesnager Proposition 9.2.10(1), in its affine-flat form:
`M_f^(8) ≥ -2^n(2^n-1)(2^n-2)/336`. -/
theorem binaryAffineFlatCharacterSum_three_ge
    (f : BooleanFunction n) (hn : 3 ≤ n) :
    binaryAffineFlatCharacterSum 3 f ≥
      -((2 ^ n : ℝ) * ((2 ^ n : ℝ) - 1) *
        ((2 ^ n : ℝ) - 2)) / 336 := by
  have hqTwo : 2 ≤ 2 ^ n := by
    have hpow : 2 ^ 3 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by omega) hn
    norm_num at hpow ⊢
    omega
  have hqOne : 1 ≤ 2 ^ n := by omega
  have hcount := congrArg (fun m : ℕ ↦ (m : ℝ))
    (card_binaryAffineFlats_two n)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcount
  rw [Nat.cast_sub hqOne, Nat.cast_sub hqTwo] at hcount
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcount
  have hlower := binaryAffineFlatCharacterSum_three_ge_neg_card f
  nlinarith

/-- Carlet--Mesnager Proposition 9.2.10(1) for the canonical weight-eight
dual-code character sum. -/
theorem orderTwoWeightEightCharacterSum_ge
    (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoWeightEightCharacterSum f ≥
      -((2 ^ n : ℝ) * ((2 ^ n : ℝ) - 1) *
        ((2 ^ n : ℝ) - 2)) / 336 := by
  rw [orderTwoWeightEightCharacterSum_eq_affineFlatCharacterSum f hn]
  exact binaryAffineFlatCharacterSum_three_ge f hn

end CryptBoolean
