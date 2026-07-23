/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderLowWeightFlats
public import CryptBoolean.Carlet.Chapter02.Subspaces
public import FABL.Chapter06.F₂Polynomials.Encoding
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The weight-fourteen dual character sum

The square-sum argument behind Carlet--Mesnager Proposition 9.2.10(3).
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightFourteenFintypeSubmodule : Fintype
    (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance weightFourteenDecidableEqSubmodule : DecidableEq
    (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

noncomputable local instance weightFourteenDecidablePredSubmoduleMembership
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    DecidablePred (fun x ↦ x ∈ H) :=
  Classical.decPred _

/-- Ordered pairs of three-dimensional binary linear subspaces. -/
noncomputable def binaryThreeSubspacePairs (n : ℕ) :
    Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :=
  (binaryLinearSubspaces 3 n).product (binaryLinearSubspaces 3 n)

/-- Ordered pairs of three-spaces with trivial intersection. -/
noncomputable def transverseBinaryThreeSubspacePairs (n : ℕ) :
    Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryThreeSubspacePairs n).filter fun p ↦ p.1 ⊓ p.2 = ⊥

/-- Ordered pairs of three-spaces with nontrivial intersection. -/
noncomputable def nontransverseBinaryThreeSubspacePairs (n : ℕ) :
    Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryThreeSubspacePairs n).filter fun p ↦ p.1 ⊓ p.2 ≠ ⊥

/-- A basepoint together with an ordered pair of transverse three-space
directions. -/
abbrev WeightFourteenRepresentation (n : ℕ) :=
  FABL.F₂Cube n ×
    (Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n))

/-- The finite family of ordered singleton-intersection representations. -/
noncomputable def weightFourteenRepresentations (n : ℕ) :
    Finset (WeightFourteenRepresentation n) :=
  Finset.univ.product (transverseBinaryThreeSubspacePairs n)

@[simp] theorem mem_weightFourteenRepresentations
    (p : WeightFourteenRepresentation n) :
    p ∈ weightFourteenRepresentations n ↔
      p.2 ∈ transverseBinaryThreeSubspacePairs n := by
  classical
  simp [weightFourteenRepresentations]

/-- The normalized character sum over ordered singleton-intersection
representations by two affine three-flats. -/
noncomputable def weightFourteenRepresentationCharacterSum
    (f : BooleanFunction n) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ u : FABL.F₂Cube n,
      ∑ p ∈ transverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2

/-- The Boolean word represented by two affine three-flats through `u`. -/
noncomputable def weightFourteenRepresentationWord
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : BooleanFunction n :=
  binaryAffineFlatIndicator (FABL.binaryAffineSubspace H u) +
    binaryAffineFlatIndicator (FABL.binaryAffineSubspace K u)

/-- The weight-fourteen words in the dual Reed--Muller code. -/
noncomputable def orderTwoWeightFourteenDualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoDualWords n).filter fun h ↦ hammingWeight h = 14

/-- The canonical character sum over weight-fourteen words in the dual
Reed--Muller code. -/
noncomputable def orderTwoWeightFourteenCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightFourteenDualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

private theorem binaryAffineCosetPoints_inter_eq_singleton
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (htransverse : H ⊓ K = ⊥) :
    binaryAffineFlatPoints (FABL.binaryAffineSubspace H u) ∩
      binaryAffineFlatPoints (FABL.binaryAffineSubspace K u) = {u} := by
  classical
  ext x
  simp only [Finset.mem_inter, mem_binaryAffineFlatPoints,
    FABL.mem_binaryAffineSubspace_iff_add_mem, Finset.mem_singleton]
  constructor
  · rintro ⟨hxH, hxK⟩
    have hxMeet : x + u ∈ H ⊓ K := ⟨hxH, hxK⟩
    rw [htransverse] at hxMeet
    have hxzero : x + u = 0 := by simpa using hxMeet
    exact (add_eq_zero_iff_eq_neg.mp hxzero).trans (by
      funext i
      exact ZMod.neg_eq_self_mod_two (u i))
  · intro hxu
    subst x
    have hzero : u + u = 0 := ZModModule.add_self u
    rw [hzero]
    exact ⟨H.zero_mem, K.zero_mem⟩

private theorem transversePairData
    {H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n) :
    H ∈ binaryLinearSubspaces 3 n ∧
      K ∈ binaryLinearSubspaces 3 n ∧ H ⊓ K = ⊥ := by
  have hp' : (H, K) ∈ binaryThreeSubspacePairs n ∧ H ⊓ K = ⊥ := by
    simpa only [transverseBinaryThreeSubspacePairs,
      Finset.mem_filter] using hp
  have hpPair := hp'.1
  change (H, K) ∈ (binaryLinearSubspaces 3 n).product
    (binaryLinearSubspaces 3 n) at hpPair
  exact ⟨(Finset.mem_product.mp hpPair).1,
    (Finset.mem_product.mp hpPair).2, hp'.2⟩

@[simp] theorem swap_mem_transverseBinaryThreeSubspacePairs
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    (K, H) ∈ transverseBinaryThreeSubspacePairs n ↔
      (H, K) ∈ transverseBinaryThreeSubspacePairs n := by
  constructor
  · intro hKH
    have hdata := transversePairData hKH
    simp only [transverseBinaryThreeSubspacePairs, Finset.mem_filter]
    constructor
    · change (H, K) ∈ (binaryLinearSubspaces 3 n).product
        (binaryLinearSubspaces 3 n)
      exact Finset.mem_product.mpr ⟨hdata.2.1, hdata.1⟩
    · simpa only [inf_comm] using hdata.2.2
  · intro hHK
    have hdata := transversePairData hHK
    simp only [transverseBinaryThreeSubspacePairs, Finset.mem_filter]
    constructor
    · change (K, H) ∈ (binaryLinearSubspaces 3 n).product
        (binaryLinearSubspaces 3 n)
      exact Finset.mem_product.mpr ⟨hdata.2.1, hdata.1⟩
    · simpa only [inf_comm] using hdata.2.2

private theorem transversePair_ne
    {H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n) :
    H ≠ K := by
  have hpdata := transversePairData hp
  have hHrank : Module.finrank FABL.𝔽₂ H = 3 :=
    (mem_binaryLinearSubspaces H).mp hpdata.1
  intro hHK
  have hHbot : H = ⊥ := by
    simpa only [hHK, inf_idem] using hpdata.2.2
  rw [hHbot] at hHrank
  simp at hHrank

private theorem binaryAffineSubspace_ne_bot
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (u : FABL.F₂Cube n) :
    FABL.binaryAffineSubspace H u ≠ ⊥ := by
  intro hbot
  have hu : u ∈ (⊥ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
    rw [← hbot]
    exact AffineSubspace.self_mem_mk' _ _
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hu
  exact hu

/-- A transverse pair of affine three-flats through one point represents a
word of Hamming weight fourteen. -/
theorem hammingWeight_weightFourteenRepresentationWord
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n) :
    hammingWeight (weightFourteenRepresentationWord u H K) = 14 := by
  have hpdata := transversePairData hp
  have hfirstRank : Module.finrank FABL.𝔽₂ H = 3 :=
    (mem_binaryLinearSubspaces H).mp hpdata.1
  have hsecondRank : Module.finrank FABL.𝔽₂ K = 3 :=
    (mem_binaryLinearSubspaces K).mp hpdata.2.1
  have hintersection := binaryAffineCosetPoints_inter_eq_singleton
    u H K hpdata.2.2
  have hidentity := hammingWeight_add_add_two_mul_card_support_inter
    (binaryAffineFlatIndicator (FABL.binaryAffineSubspace H u))
    (binaryAffineFlatIndicator (FABL.binaryAffineSubspace K u))
  rw [support_binaryAffineFlatIndicator,
    support_binaryAffineFlatIndicator, hintersection,
    hammingWeight_binaryAffineFlatIndicator _
      (binaryAffineSubspace_ne_bot H u),
    hammingWeight_binaryAffineFlatIndicator _
      (binaryAffineSubspace_ne_bot K u),
    FABL.binaryAffineSubspace_direction,
    FABL.binaryAffineSubspace_direction,
    hfirstRank, hsecondRank] at hidentity
  have hweight : hammingWeight
      (binaryAffineFlatIndicator (FABL.binaryAffineSubspace H u) +
        binaryAffineFlatIndicator (FABL.binaryAffineSubspace K u)) = 14 := by
    norm_num at hidentity
    omega
  simpa only [weightFourteenRepresentationWord] using hweight

/-- Every transverse singleton-intersection representation produces a
weight-fourteen dual Reed--Muller word. -/
theorem weightFourteenRepresentationWord_mem_dualWords
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n) :
    weightFourteenRepresentationWord u H K ∈
      orderTwoWeightFourteenDualWords n := by
  have hpdata := transversePairData hp
  have hfirst := binaryAffineFlatIndicator_mem_reedMuller
    (FABL.binaryAffineSubspace H u)
    (binaryAffineSubspace_mem_binaryAffineFlats H u hpdata.1)
  have hsecond := binaryAffineFlatIndicator_mem_reedMuller
    (FABL.binaryAffineSubspace K u)
    (binaryAffineSubspace_mem_binaryAffineFlats K u hpdata.2.1)
  simp only [orderTwoWeightFourteenDualWords, orderTwoDualWords,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(reedMuller (n - 3) n).add_mem hfirst hsecond,
    hammingWeight_weightFourteenRepresentationWord u H K hp⟩

/-- The character of a represented weight-fourteen word is the product of
the two affine-flat characters. -/
theorem weightFourteenRepresentationWord_character
    (f : BooleanFunction n) (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    FABL.binarySign (booleanFunctionPairing n f
      (weightFourteenRepresentationWord u H K)) =
      binaryAffineCosetCharacter f u H *
        binaryAffineCosetCharacter f u K := by
  rw [weightFourteenRepresentationWord, map_add, AddChar.map_add_eq_mul]
  rfl

private theorem mem_binaryAffineSubspace_bot_iff
    (u x : FABL.F₂Cube n) :
    x ∈ FABL.binaryAffineSubspace
      (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u ↔ x = u := by
  rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
  constructor
  · intro hx
    have hzero : x + u = 0 := by simpa using hx
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans (by
      funext i
      exact ZMod.neg_eq_self_mod_two (u i))
  · rintro rfl
    simpa only [ZModModule.add_self] using
      (Submodule.zero_mem (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)))

private theorem booleanRealEmbedding_weightFourteenRepresentationWord
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (htransverse : H ⊓ K = ⊥) :
    FABL.booleanRealEmbedding (weightFourteenRepresentationWord u H K) =
      fun x ↦
        FABL.setIndicator (FABL.binaryAffineSubspace H u :
            Set (FABL.F₂Cube n)) x +
          FABL.setIndicator (FABL.binaryAffineSubspace K u :
            Set (FABL.F₂Cube n)) x -
          2 * FABL.setIndicator
            (FABL.binaryAffineSubspace
              (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u :
                Set (FABL.F₂Cube n)) x := by
  funext x
  have hintersection : x ∈ FABL.binaryAffineSubspace H u ∧
      x ∈ FABL.binaryAffineSubspace K u ↔ x = u := by
    constructor
    · intro hx
      have hxMeet : x + u ∈ H ⊓ K := by
        exact ⟨(FABL.mem_binaryAffineSubspace_iff_add_mem H u x).mp hx.1,
          (FABL.mem_binaryAffineSubspace_iff_add_mem K u x).mp hx.2⟩
      rw [htransverse] at hxMeet
      have hzero : x + u = 0 := by simpa using hxMeet
      exact (add_eq_zero_iff_eq_neg.mp hzero).trans (by
        funext i
        exact ZMod.neg_eq_self_mod_two (u i))
    · rintro rfl
      constructor <;> rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
        ZModModule.add_self] <;> exact Submodule.zero_mem _
  by_cases hxH : x ∈ FABL.binaryAffineSubspace H u <;>
    by_cases hxK : x ∈ FABL.binaryAffineSubspace K u
  · have hxu : x = u := hintersection.mp ⟨hxH, hxK⟩
    have hxBot : x ∈ FABL.binaryAffineSubspace
        (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u :=
      (mem_binaryAffineSubspace_bot_iff u x).mpr hxu
    simp [FABL.booleanRealEmbedding, weightFourteenRepresentationWord,
      binaryAffineFlatIndicator, FABL.setIndicator, hxH, hxK, hxBot]
    norm_num
  · have hxBot : x ∉ FABL.binaryAffineSubspace
        (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u := by
      intro hxBot
      have hxu := (mem_binaryAffineSubspace_bot_iff u x).mp hxBot
      exact hxK (hintersection.mpr hxu).2
    simp [FABL.booleanRealEmbedding, weightFourteenRepresentationWord,
      binaryAffineFlatIndicator, FABL.setIndicator, hxH, hxK, hxBot]
  · have hxBot : x ∉ FABL.binaryAffineSubspace
        (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u := by
      intro hxBot
      have hxu := (mem_binaryAffineSubspace_bot_iff u x).mp hxBot
      exact hxH (hintersection.mpr hxu).1
    simp [FABL.booleanRealEmbedding, weightFourteenRepresentationWord,
      binaryAffineFlatIndicator, FABL.setIndicator, hxH, hxK, hxBot]
  · have hxBot : x ∉ FABL.binaryAffineSubspace
        (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u := by
      intro hxBot
      have hxu := (mem_binaryAffineSubspace_bot_iff u x).mp hxBot
      exact hxH (hintersection.mpr hxu).1
    simp [FABL.booleanRealEmbedding, weightFourteenRepresentationWord,
      binaryAffineFlatIndicator, FABL.setIndicator, hxH, hxK, hxBot]

private theorem rawFourierTransform_setIndicator_binaryAffineSubspace
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (u a : FABL.F₂Cube n) :
    rawFourierTransform
        (FABL.setIndicator (FABL.binaryAffineSubspace H u :
          Set (FABL.F₂Cube n))) a =
      FABL.vectorWalshCharacter a u *
        if a ∈ FABL.perpendicularSubspace H then (Nat.card H : ℝ) else 0 := by
  classical
  by_cases ha : a ∈ FABL.perpendicularSubspace H
  · rw [if_pos ha, rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem H u a ha]
    calc
      (2 ^ n : ℝ) *
          (FABL.vectorWalshCharacter a u * FABL.inversePerpendicularCard H) =
          FABL.vectorWalshCharacter a u *
            ((2 ^ n : ℝ) * FABL.inversePerpendicularCard H) := by ring
      _ = FABL.vectorWalshCharacter a u * (Nat.card H : ℝ) := by
        rw [two_pow_mul_inversePerpendicularCard_eq_card]
  · rw [if_neg ha, rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem
        H u a ha, mul_zero, mul_zero]

private noncomputable def weightFourteenRawCoefficient
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : ℝ := by
  classical
  exact (if a ∈ FABL.perpendicularSubspace H then 8 else 0) +
    (if a ∈ FABL.perpendicularSubspace K then 8 else 0) - 2

private theorem rawFourierTransform_weightFourteenRepresentationWord
    (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 3)
    (hK : Module.finrank FABL.𝔽₂ K = 3)
    (htransverse : H ⊓ K = ⊥)
    (a : FABL.F₂Cube n) :
    rawFourierTransform
        (FABL.booleanRealEmbedding
          (weightFourteenRepresentationWord u H K)) a =
      FABL.vectorWalshCharacter a u *
        weightFourteenRawCoefficient H K a := by
  classical
  have hreal := booleanRealEmbedding_weightFourteenRepresentationWord
    u H K htransverse
  calc
    rawFourierTransform
        (FABL.booleanRealEmbedding
          (weightFourteenRepresentationWord u H K)) a =
        rawFourierTransform
            (FABL.setIndicator (FABL.binaryAffineSubspace H u :
              Set (FABL.F₂Cube n))) a +
          rawFourierTransform
            (FABL.setIndicator (FABL.binaryAffineSubspace K u :
              Set (FABL.F₂Cube n))) a -
          2 * rawFourierTransform
            (FABL.setIndicator
              (FABL.binaryAffineSubspace
                (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) u :
                  Set (FABL.F₂Cube n))) a := by
      rw [hreal]
      simp only [rawFourierTransform]
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = FABL.vectorWalshCharacter a u *
        weightFourteenRawCoefficient H K a := by
      have haBot : a ∈ FABL.perpendicularSubspace
          (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
        rw [FABL.mem_perpendicularSubspace_iff]
        intro x hx
        have hxzero : x = 0 := by simpa using hx
        subst x
        simp [FABL.f₂DotProduct]
      have hcardBot : Nat.card
          (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) = 1 := by
        rw [FABL.card_submodule_eq_two_pow_finrank, finrank_bot]
        norm_num
      rw [rawFourierTransform_setIndicator_binaryAffineSubspace,
        rawFourierTransform_setIndicator_binaryAffineSubspace,
        rawFourierTransform_setIndicator_binaryAffineSubspace]
      rw [FABL.card_submodule_eq_two_pow_finrank,
        FABL.card_submodule_eq_two_pow_finrank, hH, hK]
      rw [hcardBot, if_pos haBot]
      norm_num only [Nat.cast_one]
      unfold weightFourteenRawCoefficient
      ring

private theorem weightFourteenRawCoefficient_cases
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    weightFourteenRawCoefficient H K a = -2 ∨
      weightFourteenRawCoefficient H K a = 6 ∨
      weightFourteenRawCoefficient H K a = 14 := by
  classical
  unfold weightFourteenRawCoefficient
  by_cases haH : a ∈ FABL.perpendicularSubspace H <;>
    by_cases haK : a ∈ FABL.perpendicularSubspace K <;>
    simp [haH, haK] <;> norm_num

private theorem weightFourteenRawCoefficient_ne_zero
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    weightFourteenRawCoefficient H K a ≠ 0 := by
  rcases weightFourteenRawCoefficient_cases H K a with h | h | h <;>
    rw [h] <;> norm_num

private theorem weightFourteenRawCoefficient_eq_of_sq_eq_sq
    (H K L M : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (hsq : weightFourteenRawCoefficient H K a ^ 2 =
      weightFourteenRawCoefficient L M a ^ 2) :
    weightFourteenRawCoefficient H K a =
      weightFourteenRawCoefficient L M a := by
  rcases weightFourteenRawCoefficient_cases H K a with hHK | hHK | hHK <;>
    rcases weightFourteenRawCoefficient_cases L M a with hLM | hLM | hLM <;>
    nlinarith [hsq]

private theorem vectorWalshCharacter_sq
    (a u : FABL.F₂Cube n) :
    FABL.vectorWalshCharacter a u ^ 2 = 1 := by
  rcases FABL.vectorWalshCharacter_eq_neg_one_or_one a u with h | h <;>
    rw [h] <;> norm_num

private theorem weightFourteenRepresentationWord_apply_eq_one_iff_of_ne_zero
    (u y : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (htransverse : H ⊓ K = ⊥) (hy : y ≠ 0) :
    weightFourteenRepresentationWord u H K (y + u) = 1 ↔
      y ∈ H ∨ y ∈ K := by
  have hnotBoth : ¬ (y ∈ H ∧ y ∈ K) := by
    intro hboth
    have hyMeet : y ∈ H ⊓ K := hboth
    rw [htransverse] at hyMeet
    exact hy (by simpa using hyMeet)
  simp only [weightFourteenRepresentationWord,
    binaryAffineFlatIndicator, Pi.add_apply,
    FABL.mem_binaryAffineSubspace_iff_add_mem]
  have hyu : y + u + u = y := by
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [hyu]
  by_cases hyH : y ∈ H <;> by_cases hyK : y ∈ K
  · exact (hnotBoth ⟨hyH, hyK⟩).elim
  · simp [hyH, hyK]
  · simp [hyH, hyK]
  · simp [hyH, hyK]

/-- Once the singleton intersection point is fixed, the two three-space
directions representing a weight-fourteen word are unique up to swapping. -/
theorem weightFourteenRepresentationWord_eq_same_basepoint_iff
    (u : FABL.F₂Cube n)
    (H K L M : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n)
    (hq : (L, M) ∈ transverseBinaryThreeSubspacePairs n) :
    weightFourteenRepresentationWord u H K =
        weightFourteenRepresentationWord u L M ↔
      (H = L ∧ K = M) ∨ (H = M ∧ K = L) := by
  constructor
  · intro hword
    have hpdata := transversePairData hp
    have hqdata := transversePairData hq
    have hHrank : Module.finrank FABL.𝔽₂ H = 3 :=
      (mem_binaryLinearSubspaces H).mp hpdata.1
    have hKrank : Module.finrank FABL.𝔽₂ K = 3 :=
      (mem_binaryLinearSubspaces K).mp hpdata.2.1
    have hLrank : Module.finrank FABL.𝔽₂ L = 3 :=
      (mem_binaryLinearSubspaces L).mp hqdata.1
    have hMrank : Module.finrank FABL.𝔽₂ M = 3 :=
      (mem_binaryLinearSubspaces M).mp hqdata.2.1
    have hHKne : H ≠ K := transversePair_ne hp
    have hunion : ∀ y, y ∈ H ∨ y ∈ K ↔ y ∈ L ∨ y ∈ M := by
      intro y
      by_cases hy : y = 0
      · subst y
        simp
      · rw [← weightFourteenRepresentationWord_apply_eq_one_iff_of_ne_zero
          u y H K hpdata.2.2 hy,
          ← weightFourteenRepresentationWord_apply_eq_one_iff_of_ne_zero
            u y L M hqdata.2.2 hy,
          hword]
    exact unordered_submodule_pair_eq_of_union_eq H K L M
      (hHrank.trans hLrank.symm) (hHrank.trans hMrank.symm)
      (hKrank.trans hLrank.symm) (hKrank.trans hMrank.symm)
      hHKne hunion
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp only [weightFourteenRepresentationWord, add_comm]

private theorem weightFourteenRepresentationWord_basepoint_eq
    (u v : FABL.F₂Cube n)
    (H K L M : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n)
    (hq : (L, M) ∈ transverseBinaryThreeSubspacePairs n)
    (hword : weightFourteenRepresentationWord u H K =
      weightFourteenRepresentationWord v L M) :
    u = v := by
  have hpdata := transversePairData hp
  have hqdata := transversePairData hq
  have hHrank : Module.finrank FABL.𝔽₂ H = 3 :=
    (mem_binaryLinearSubspaces H).mp hpdata.1
  have hKrank : Module.finrank FABL.𝔽₂ K = 3 :=
    (mem_binaryLinearSubspaces K).mp hpdata.2.1
  have hLrank : Module.finrank FABL.𝔽₂ L = 3 :=
    (mem_binaryLinearSubspaces L).mp hqdata.1
  have hMrank : Module.finrank FABL.𝔽₂ M = 3 :=
    (mem_binaryLinearSubspaces M).mp hqdata.2.1
  apply FABL.vectorWalshCharacter_injective
  ext a
  have hraw :
      FABL.vectorWalshCharacter a u *
          weightFourteenRawCoefficient H K a =
        FABL.vectorWalshCharacter a v *
          weightFourteenRawCoefficient L M a := by
    have htransform := congrArg
      (fun g : BooleanFunction n ↦
        rawFourierTransform (FABL.booleanRealEmbedding g) a) hword
    rw [rawFourierTransform_weightFourteenRepresentationWord
        u H K hHrank hKrank hpdata.2.2 a,
      rawFourierTransform_weightFourteenRepresentationWord
        v L M hLrank hMrank hqdata.2.2 a] at htransform
    exact htransform
  have hsq : weightFourteenRawCoefficient H K a ^ 2 =
      weightFourteenRawCoefficient L M a ^ 2 := by
    calc
      weightFourteenRawCoefficient H K a ^ 2 =
          FABL.vectorWalshCharacter a u ^ 2 *
            weightFourteenRawCoefficient H K a ^ 2 := by
        rw [vectorWalshCharacter_sq, one_mul]
      _ = (FABL.vectorWalshCharacter a u *
          weightFourteenRawCoefficient H K a) ^ 2 := by ring
      _ = (FABL.vectorWalshCharacter a v *
          weightFourteenRawCoefficient L M a) ^ 2 :=
        congrArg (fun x : ℝ ↦ x ^ 2) hraw
      _ = FABL.vectorWalshCharacter a v ^ 2 *
          weightFourteenRawCoefficient L M a ^ 2 := by ring
      _ = weightFourteenRawCoefficient L M a ^ 2 := by
        rw [vectorWalshCharacter_sq, one_mul]
  have hcoefficient :=
    weightFourteenRawCoefficient_eq_of_sq_eq_sq H K L M a hsq
  have hphase : FABL.vectorWalshCharacter a u =
      FABL.vectorWalshCharacter a v := by
    apply mul_right_cancel₀ (weightFourteenRawCoefficient_ne_zero H K a)
    calc
      FABL.vectorWalshCharacter a u *
          weightFourteenRawCoefficient H K a =
          FABL.vectorWalshCharacter a v *
            weightFourteenRawCoefficient L M a := hraw
      _ = FABL.vectorWalshCharacter a v *
          weightFourteenRawCoefficient H K a := by rw [hcoefficient]
  calc
    FABL.vectorWalshCharacter u a =
        FABL.vectorWalshCharacter a u := by
      rw [FABL.vectorWalshCharacter_apply,
        FABL.vectorWalshCharacter_apply]
      exact congrArg FABL.binarySign (dotProduct_comm u a)
    _ = FABL.vectorWalshCharacter a v := hphase
    _ = FABL.vectorWalshCharacter v a := by
      rw [FABL.vectorWalshCharacter_apply,
        FABL.vectorWalshCharacter_apply]
      exact congrArg FABL.binarySign (dotProduct_comm a v)

/-- A singleton-intersection representation of a weight-fourteen word is
unique up to exchanging its two affine three-flats. -/
theorem weightFourteenRepresentationWord_eq_iff
    (u v : FABL.F₂Cube n)
    (H K L M : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : (H, K) ∈ transverseBinaryThreeSubspacePairs n)
    (hq : (L, M) ∈ transverseBinaryThreeSubspacePairs n) :
    weightFourteenRepresentationWord u H K =
        weightFourteenRepresentationWord v L M ↔
      u = v ∧ ((H = L ∧ K = M) ∨ (H = M ∧ K = L)) := by
  constructor
  · intro hword
    have huv := weightFourteenRepresentationWord_basepoint_eq
      u v H K L M hp hq hword
    subst v
    exact ⟨rfl,
      (weightFourteenRepresentationWord_eq_same_basepoint_iff
        u H K L M hp hq).mp hword⟩
  · rintro ⟨rfl, hpairs⟩
    exact (weightFourteenRepresentationWord_eq_same_basepoint_iff
      u H K L M hp hq).mpr hpairs

/-- The remaining Kasami--Tokura input: every weight-fourteen word of the
dual code has a singleton-intersection representation by two affine
three-flats.  Uniqueness is proved above and is not part of this interface. -/
def HasWeightFourteenFlatPairClassification (n : ℕ) : Prop :=
  ∀ h ∈ orderTwoWeightFourteenDualWords n,
    ∃ u : FABL.F₂Cube n,
      ∃ H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
        (H, K) ∈ transverseBinaryThreeSubspacePairs n ∧
          weightFourteenRepresentationWord u H K = h

/-- Assuming only existence from the Kasami--Tokura classification, every
weight-fourteen word has exactly the two ordered representations obtained
by exchanging its affine three-flats. -/
theorem card_weightFourteenRepresentationWord_fiber
    (hclassification : HasWeightFourteenFlatPairClassification n)
    (h : BooleanFunction n) :
    ((weightFourteenRepresentations n).filter fun p ↦
      weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h).card =
        if h ∈ orderTwoWeightFourteenDualWords n then 2 else 0 := by
  classical
  by_cases hh : h ∈ orderTwoWeightFourteenDualWords n
  · rw [if_pos hh]
    obtain ⟨u, H, K, hp, hword⟩ := hclassification h hh
    have hfiber :
        (weightFourteenRepresentations n).filter (fun p ↦
          weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h) =
          {(u, (H, K)), (u, (K, H))} := by
      ext p
      rcases p with ⟨v, L, M⟩
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hrepresentation, hrepresentationWord⟩
        have hq : (L, M) ∈ transverseBinaryThreeSubspacePairs n :=
          (mem_weightFourteenRepresentations (v, (L, M))).mp
            hrepresentation
        have heq := (weightFourteenRepresentationWord_eq_iff
          v u L M H K hq hp).mp
            (hrepresentationWord.trans hword.symm)
        rcases heq with ⟨hu, (⟨hLH, hMK⟩ | ⟨hLK, hMH⟩)⟩
        · left
          subst v
          subst L
          subst M
          rfl
        · right
          subst v
          subst L
          subst M
          rfl
      · rintro (hfirst | hsecond)
        · cases hfirst
          exact ⟨(mem_weightFourteenRepresentations (u, (H, K))).mpr hp,
            hword⟩
        · cases hsecond
          exact ⟨(mem_weightFourteenRepresentations (u, (K, H))).mpr
              ((swap_mem_transverseBinaryThreeSubspacePairs H K).mpr hp),
            by simpa only [weightFourteenRepresentationWord, add_comm]
              using hword⟩
    have hdistinct : (u, (H, K)) ≠ (u, (K, H)) := by
      intro heq
      apply transversePair_ne hp
      simpa using congrArg
        (fun p : WeightFourteenRepresentation n ↦ p.2.1) heq
    rw [hfiber]
    simp [hdistinct]
  · rw [if_neg hh]
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hrepresentation, hrepresentationWord⟩
      exfalso
      apply hh
      rw [← hrepresentationWord]
      exact weightFourteenRepresentationWord_mem_dualWords
        p.1 p.2.1 p.2.2
        ((mem_weightFourteenRepresentations p).mp hrepresentation)
    · intro hpempty
      simp at hpempty

private theorem exists_spanning_pair_of_mem_threeSubspace
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hH : Module.finrank FABL.𝔽₂ H = 3)
    (v : FABL.F₂Cube n) (hvH : v ∈ H) (hv0 : v ≠ 0) :
    ∃ a b : FABL.F₂Cube n,
      H = ((FABL.𝔽₂ ∙ v) ⊔ (FABL.𝔽₂ ∙ a)) ⊔
        (FABL.𝔽₂ ∙ b) := by
  let S₁ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) := FABL.𝔽₂ ∙ v
  have hS₁le : S₁ ≤ H := by
    exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hvH)
  have hS₁rank : Module.finrank FABL.𝔽₂ S₁ = 1 := by
    exact finrank_span_singleton hv0
  have hS₁lt : S₁ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₁le (by omega)
  obtain ⟨a, haH, haS₁⟩ := SetLike.exists_of_lt hS₁lt
  let S₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    S₁ ⊔ (FABL.𝔽₂ ∙ a)
  have hS₂le : S₂ ≤ H := by
    exact sup_le hS₁le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 haH))
  have hS₂rank : Module.finrank FABL.𝔽₂ S₂ = 2 := by
    dsimp only [S₂]
    rw [Submodule.finrank_sup_span_singleton haS₁, hS₁rank]
  have hS₂lt : S₂ < H :=
    Submodule.lt_of_le_of_finrank_lt_finrank hS₂le (by omega)
  obtain ⟨b, hbH, hbS₂⟩ := SetLike.exists_of_lt hS₂lt
  refine ⟨a, b, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hS₂le
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 hbH))
  · rw [Submodule.finrank_sup_span_singleton hbS₂, hS₂rank, hH]

private theorem exists_common_nonzero_of_nontransverse
    {H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (hHK : H ⊓ K ≠ ⊥) :
    ∃ v : FABL.F₂Cube n, v ≠ 0 ∧ v ∈ H ∧ v ∈ K := by
  obtain ⟨v, hv⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr hHK)
  refine ⟨v, ?_, v.2.1, v.2.2⟩
  intro hv0
  apply hv
  apply Subtype.ext
  exact hv0

private structure NontransversePairWitness
    (p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)) where
  v : FABL.F₂Cube n
  a₁ : FABL.F₂Cube n
  b₁ : FABL.F₂Cube n
  a₂ : FABL.F₂Cube n
  b₂ : FABL.F₂Cube n
  first_span : p.1 =
    ((FABL.𝔽₂ ∙ v) ⊔ (FABL.𝔽₂ ∙ a₁)) ⊔ (FABL.𝔽₂ ∙ b₁)
  second_span : p.2 =
    ((FABL.𝔽₂ ∙ v) ⊔ (FABL.𝔽₂ ∙ a₂)) ⊔ (FABL.𝔽₂ ∙ b₂)

private noncomputable def nontransversePairWitness
    (p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : p ∈ nontransverseBinaryThreeSubspacePairs n) :
    NontransversePairWitness p := by
  classical
  have hp' : p ∈ binaryThreeSubspacePairs n ∧ p.1 ⊓ p.2 ≠ ⊥ := by
    simpa only [nontransverseBinaryThreeSubspacePairs,
      Finset.mem_filter] using hp
  have hpProduct : p.1 ∈ binaryLinearSubspaces 3 n ∧
      p.2 ∈ binaryLinearSubspaces 3 n := by
    have hpPair := hp'.1
    change p ∈ (binaryLinearSubspaces 3 n).product
      (binaryLinearSubspaces 3 n) at hpPair
    exact Finset.mem_product.mp hpPair
  have hfirstRank : Module.finrank FABL.𝔽₂ p.1 = 3 :=
    (mem_binaryLinearSubspaces p.1).mp hpProduct.1
  have hsecondRank : Module.finrank FABL.𝔽₂ p.2 = 3 :=
    (mem_binaryLinearSubspaces p.2).mp hpProduct.2
  let v := Classical.choose (exists_common_nonzero_of_nontransverse hp'.2)
  have hv := Classical.choose_spec
    (exists_common_nonzero_of_nontransverse hp'.2)
  let a₁ := Classical.choose
    (exists_spanning_pair_of_mem_threeSubspace p.1 hfirstRank v hv.2.1 hv.1)
  let b₁ := Classical.choose (Classical.choose_spec
    (exists_spanning_pair_of_mem_threeSubspace p.1 hfirstRank v hv.2.1 hv.1))
  have hfirst := Classical.choose_spec (Classical.choose_spec
    (exists_spanning_pair_of_mem_threeSubspace p.1 hfirstRank v hv.2.1 hv.1))
  let a₂ := Classical.choose
    (exists_spanning_pair_of_mem_threeSubspace p.2 hsecondRank v hv.2.2 hv.1)
  let b₂ := Classical.choose (Classical.choose_spec
    (exists_spanning_pair_of_mem_threeSubspace p.2 hsecondRank v hv.2.2 hv.1))
  have hsecond := Classical.choose_spec (Classical.choose_spec
    (exists_spanning_pair_of_mem_threeSubspace p.2 hsecondRank v hv.2.2 hv.1))
  exact ⟨v, a₁, b₁, a₂, b₂, hfirst, hsecond⟩

private noncomputable def chosenNontransversePairWitness
    (p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hp : p ∈ nontransverseBinaryThreeSubspacePairs n) :
    NontransversePairWitness p :=
  nontransversePairWitness p hp

private def nontransversePairWitnessCode
    {p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (w : NontransversePairWitness p) : Fin 5 → FABL.F₂Cube n :=
  ![w.v, w.a₁, w.b₁, w.a₂, w.b₂]

private noncomputable def nontransversePairCode
    (p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
      Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fin 5 → FABL.F₂Cube n := by
  classical
  exact if hp : p ∈ nontransverseBinaryThreeSubspacePairs n then
    nontransversePairWitnessCode (chosenNontransversePairWitness p hp)
  else 0

private theorem nontransversePairCode_injective_on :
    Set.InjOn (nontransversePairCode (n := n))
      (nontransverseBinaryThreeSubspacePairs n :
        Set (Submodule FABL.𝔽₂ (FABL.F₂Cube n) ×
          Submodule FABL.𝔽₂ (FABL.F₂Cube n))) := by
  intro p hp q hq hcode
  have hpFin : p ∈ nontransverseBinaryThreeSubspacePairs n := hp
  have hqFin : q ∈ nontransverseBinaryThreeSubspacePairs n := hq
  have hcode' :
      nontransversePairWitnessCode
          (chosenNontransversePairWitness p hp) =
        nontransversePairWitnessCode
          (chosenNontransversePairWitness q hq) := by
    unfold nontransversePairCode at hcode
    rw [dif_pos hpFin, dif_pos hqFin] at hcode
    simpa only using hcode
  have h0 : (chosenNontransversePairWitness p hp).v =
      (chosenNontransversePairWitness q hq).v := by
    simpa [nontransversePairWitnessCode] using congrFun hcode' (0 : Fin 5)
  have h1 : (chosenNontransversePairWitness p hp).a₁ =
      (chosenNontransversePairWitness q hq).a₁ := by
    simpa [nontransversePairWitnessCode] using congrFun hcode' (1 : Fin 5)
  have h2 : (chosenNontransversePairWitness p hp).b₁ =
      (chosenNontransversePairWitness q hq).b₁ := by
    simpa [nontransversePairWitnessCode] using congrFun hcode' (2 : Fin 5)
  have h3 : (chosenNontransversePairWitness p hp).a₂ =
      (chosenNontransversePairWitness q hq).a₂ := by
    simpa [nontransversePairWitnessCode] using congrFun hcode' (3 : Fin 5)
  have h4 : (chosenNontransversePairWitness p hp).b₂ =
      (chosenNontransversePairWitness q hq).b₂ := by
    simpa [nontransversePairWitnessCode] using congrFun hcode' (4 : Fin 5)
  apply Prod.ext
  · rw [(chosenNontransversePairWitness p hp).first_span,
      (chosenNontransversePairWitness q hq).first_span,
      h0, h1, h2]
  · rw [(chosenNontransversePairWitness p hp).second_span,
      (chosenNontransversePairWitness q hq).second_span,
      h0, h3, h4]

/-- Nontransverse ordered pairs of binary three-spaces inject
into five ambient vectors. -/
theorem card_nontransverseBinaryThreeSubspacePairs_le (n : ℕ) :
    (nontransverseBinaryThreeSubspacePairs n).card ≤ (2 ^ n) ^ 5 := by
  classical
  calc
    (nontransverseBinaryThreeSubspacePairs n).card ≤
        (Finset.univ : Finset (Fin 5 → FABL.F₂Cube n)).card := by
      apply Finset.card_le_card_of_injOn (nontransversePairCode (n := n))
      · intro p _hp
        exact Finset.mem_univ _
      · exact nontransversePairCode_injective_on
    _ = (2 ^ n) ^ 5 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_f₂Cube]

private theorem allThreeSubspacePairCharacterSum_eq_sq
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (∑ p ∈ binaryThreeSubspacePairs n,
      binaryAffineCosetCharacter f u p.1 *
        binaryAffineCosetCharacter f u p.2) =
      (∑ H ∈ binaryLinearSubspaces 3 n,
        binaryAffineCosetCharacter f u H) ^ 2 := by
  classical
  rw [binaryThreeSubspacePairs]
  calc
    (∑ p ∈ (binaryLinearSubspaces 3 n).product
          (binaryLinearSubspaces 3 n),
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2) =
        ∑ H ∈ binaryLinearSubspaces 3 n,
          ∑ K ∈ binaryLinearSubspaces 3 n,
            binaryAffineCosetCharacter f u H *
              binaryAffineCosetCharacter f u K := by
      exact Finset.sum_product _ _ _
    _ = (∑ H ∈ binaryLinearSubspaces 3 n,
        binaryAffineCosetCharacter f u H) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, mul_comm]

private theorem threeSubspacePairCharacterSum_split
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (∑ p ∈ binaryThreeSubspacePairs n,
      binaryAffineCosetCharacter f u p.1 *
        binaryAffineCosetCharacter f u p.2) =
      (∑ p ∈ transverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2) +
      ∑ p ∈ nontransverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (binaryThreeSubspacePairs n) (fun p ↦ p.1 ⊓ p.2 = ⊥)
    (fun p ↦ binaryAffineCosetCharacter f u p.1 *
      binaryAffineCosetCharacter f u p.2)
  change
    (∑ p ∈ transverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2) +
      (∑ p ∈ nontransverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2) =
      ∑ p ∈ binaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2 at hsplit
  exact hsplit.symm

private theorem nontransverseThreeSubspacePairCharacterSum_le_card
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (∑ p ∈ nontransverseBinaryThreeSubspacePairs n,
      binaryAffineCosetCharacter f u p.1 *
        binaryAffineCosetCharacter f u p.2) ≤
      ((nontransverseBinaryThreeSubspacePairs n).card : ℝ) := by
  calc
    (∑ p ∈ nontransverseBinaryThreeSubspacePairs n,
        binaryAffineCosetCharacter f u p.1 *
          binaryAffineCosetCharacter f u p.2) ≤
        ∑ _p ∈ nontransverseBinaryThreeSubspacePairs n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact binaryAffineCosetCharacter_mul_le_one f u p.1 p.2
    _ = ((nontransverseBinaryThreeSubspacePairs n).card : ℝ) := by simp

private theorem transverseThreeSubspacePairCharacterSum_ge_neg_card
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (∑ p ∈ transverseBinaryThreeSubspacePairs n,
      binaryAffineCosetCharacter f u p.1 *
        binaryAffineCosetCharacter f u p.2) ≥
      -((nontransverseBinaryThreeSubspacePairs n).card : ℝ) := by
  have hall : 0 ≤ ∑ p ∈ binaryThreeSubspacePairs n,
      binaryAffineCosetCharacter f u p.1 *
        binaryAffineCosetCharacter f u p.2 := by
    rw [allThreeSubspacePairCharacterSum_eq_sq]
    positivity
  rw [threeSubspacePairCharacterSum_split] at hall
  have hexcluded := nontransverseThreeSubspacePairCharacterSum_le_card f u
  linarith

/-- A dimension-free coarse form of the weight-fourteen square-sum bound.
It has the `O(2^(6n))` order needed by the moment argument. -/
theorem weightFourteenRepresentationCharacterSum_ge
    (f : BooleanFunction n) :
    weightFourteenRepresentationCharacterSum f ≥
      -((2 ^ n : ℝ) ^ 6) / 2 := by
  classical
  have hsum :
      ∑ _u : FABL.F₂Cube n,
          -((nontransverseBinaryThreeSubspacePairs n).card : ℝ) ≤
        ∑ u : FABL.F₂Cube n,
          ∑ p ∈ transverseBinaryThreeSubspacePairs n,
            binaryAffineCosetCharacter f u p.1 *
              binaryAffineCosetCharacter f u p.2 := by
    apply Finset.sum_le_sum
    intro u _hu
    exact transverseThreeSubspacePairCharacterSum_ge_neg_card f u
  have hcardNat := card_nontransverseBinaryThreeSubspacePairs_le n
  have hcardReal :
      ((nontransverseBinaryThreeSubspacePairs n).card : ℝ) ≤
        (((2 ^ n) ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcardReal
  have hqnonneg : 0 ≤ (2 ^ n : ℝ) := by positivity
  have hproduct := mul_le_mul_of_nonneg_left hcardReal hqnonneg
  calc
    weightFourteenRepresentationCharacterSum f =
        (1 / 2 : ℝ) *
          ∑ u : FABL.F₂Cube n,
            ∑ p ∈ transverseBinaryThreeSubspacePairs n,
              binaryAffineCosetCharacter f u p.1 *
                binaryAffineCosetCharacter f u p.2 := rfl
    _ ≥ (1 / 2 : ℝ) *
        ∑ _u : FABL.F₂Cube n,
          -((nontransverseBinaryThreeSubspacePairs n).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = -((2 ^ n : ℝ) *
          (nontransverseBinaryThreeSubspacePairs n).card) / 2 := by
      rw [Finset.sum_const, Finset.card_univ, card_f₂Cube]
      norm_num
      ring
    _ ≥ -((2 ^ n : ℝ) ^ 6) / 2 := by
      nlinarith

private theorem sum_weightFourteenRepresentations_eq_two_mul
    (f : BooleanFunction n)
    (hclassification : HasWeightFourteenFlatPairClassification n) :
    (∑ p ∈ weightFourteenRepresentations n,
      binaryAffineCosetCharacter f p.1 p.2.1 *
        binaryAffineCosetCharacter f p.1 p.2.2) =
      2 * orderTwoWeightFourteenCharacterSum f := by
  classical
  calc
    (∑ p ∈ weightFourteenRepresentations n,
        binaryAffineCosetCharacter f p.1 p.2.1 *
          binaryAffineCosetCharacter f p.1 p.2.2) =
        ∑ p ∈ weightFourteenRepresentations n,
          FABL.binarySign (booleanFunctionPairing n f
            (weightFourteenRepresentationWord p.1 p.2.1 p.2.2)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [weightFourteenRepresentationWord_character]
    _ = ∑ h ∈ orderTwoWeightFourteenDualWords n,
        ∑ p ∈ (weightFourteenRepresentations n).filter
            (fun p ↦
              weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h),
          FABL.binarySign (booleanFunctionPairing n f
            (weightFourteenRepresentationWord p.1 p.2.1 p.2.2)) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      exact weightFourteenRepresentationWord_mem_dualWords
        p.1 p.2.1 p.2.2
        ((mem_weightFourteenRepresentations p).mp hp)
    _ = ∑ h ∈ orderTwoWeightFourteenDualWords n,
        2 * FABL.binarySign (booleanFunctionPairing n f h) := by
      apply Finset.sum_congr rfl
      intro h hh
      calc
        (∑ p ∈ (weightFourteenRepresentations n).filter
            (fun p ↦
              weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h),
            FABL.binarySign (booleanFunctionPairing n f
              (weightFourteenRepresentationWord p.1 p.2.1 p.2.2))) =
            ∑ _p ∈ (weightFourteenRepresentations n).filter
                (fun p ↦
                  weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h),
              FABL.binarySign (booleanFunctionPairing n f h) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = (((weightFourteenRepresentations n).filter fun p ↦
              weightFourteenRepresentationWord p.1 p.2.1 p.2.2 = h).card : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h) := by simp
        _ = 2 * FABL.binarySign (booleanFunctionPairing n f h) := by
          rw [card_weightFourteenRepresentationWord_fiber
            hclassification h, if_pos hh]
          norm_num
    _ = 2 * orderTwoWeightFourteenCharacterSum f := by
      rw [orderTwoWeightFourteenCharacterSum, Finset.mul_sum]

/-- Under the Kasami--Tokura existence classification, the canonical
weight-fourteen character sum is exactly the normalized representation
sum. -/
theorem orderTwoWeightFourteenCharacterSum_eq_representation
    (f : BooleanFunction n)
    (hclassification : HasWeightFourteenFlatPairClassification n) :
    orderTwoWeightFourteenCharacterSum f =
      weightFourteenRepresentationCharacterSum f := by
  have hsum := sum_weightFourteenRepresentations_eq_two_mul
    f hclassification
  have hproduct :
      (∑ p ∈ weightFourteenRepresentations n,
        binaryAffineCosetCharacter f p.1 p.2.1 *
          binaryAffineCosetCharacter f p.1 p.2.2) =
        ∑ u : FABL.F₂Cube n,
          ∑ p ∈ transverseBinaryThreeSubspacePairs n,
            binaryAffineCosetCharacter f u p.1 *
              binaryAffineCosetCharacter f u p.2 := by
    rw [weightFourteenRepresentations]
    exact Finset.sum_product _ _ _
  rw [weightFourteenRepresentationCharacterSum]
  calc
    orderTwoWeightFourteenCharacterSum f =
        (1 / 2 : ℝ) *
          (2 * orderTwoWeightFourteenCharacterSum f) := by ring
    _ = (1 / 2 : ℝ) *
        ∑ p ∈ weightFourteenRepresentations n,
          binaryAffineCosetCharacter f p.1 p.2.1 *
            binaryAffineCosetCharacter f p.1 p.2.2 := by rw [hsum]
    _ = (1 / 2 : ℝ) *
        ∑ u : FABL.F₂Cube n,
          ∑ p ∈ transverseBinaryThreeSubspacePairs n,
            binaryAffineCosetCharacter f u p.1 *
              binaryAffineCosetCharacter f u p.2 := by rw [hproduct]

/-- A reusable `O((2^n)^6)` lower bound for the canonical weight-fourteen
contribution, conditional only on the cited Kasami--Tokura existence
classification. -/
theorem orderTwoWeightFourteenCharacterSum_ge
    (f : BooleanFunction n)
    (hclassification : HasWeightFourteenFlatPairClassification n) :
    orderTwoWeightFourteenCharacterSum f ≥ -((2 ^ n : ℝ) ^ 6) / 2 := by
  rw [orderTwoWeightFourteenCharacterSum_eq_representation
    f hclassification]
  exact weightFourteenRepresentationCharacterSum_ge f

end CryptBoolean
