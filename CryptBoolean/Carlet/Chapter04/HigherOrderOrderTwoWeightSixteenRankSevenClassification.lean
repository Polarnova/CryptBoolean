/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenCandidateSoundnessCertificates
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenCharacterBound
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenSupportNormalization
public import CryptBoolean.Carlet.Chapter04.HigherOrderSharpAsymptotics

/-!
# Rank-seven classification of weight-sixteen dual words
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Composition of seven-variable affine-map data. -/
def sevenVariableAffineMapDataComp
    (outer : SevenVariableAffineMapData n)
    (inner : SevenVariableAffineMapData 7) :
    SevenVariableAffineMapData n :=
  (sevenVariableAffinePoint outer inner.1,
    fun i ↦ (sevenVariableAffineMap outer).linear (inner.2 i))

/-- Evaluation of composed affine-map data is functional composition. -/
theorem sevenVariableAffinePoint_comp
    (outer : SevenVariableAffineMapData n)
    (inner : SevenVariableAffineMapData 7)
    (x : FABL.F₂Cube 7) :
    sevenVariableAffinePoint (sevenVariableAffineMapDataComp outer inner) x =
      sevenVariableAffinePoint outer (sevenVariableAffinePoint inner x) := by
  change
    (outer.1 + (sevenVariableAffineMap outer).linear inner.1) +
        ∑ i, x i • (sevenVariableAffineMap outer).linear (inner.2 i) =
      outer.1 + (sevenVariableAffineMap outer).linear
        (inner.1 + ∑ i, x i • inner.2 i)
  rw [map_add, map_sum]
  simp_rw [map_smul]
  abel

/-- Composition preserves independent directions when both affine maps have
independent linear parts. -/
theorem linearIndependent_sevenVariableAffineMapDataComp
    (outer : SevenVariableAffineMapData n)
    (inner : SevenVariableAffineMapData 7)
    (houter : LinearIndependent FABL.𝔽₂ outer.2)
    (hinner : LinearIndependent FABL.𝔽₂ inner.2) :
    LinearIndependent FABL.𝔽₂
      (sevenVariableAffineMapDataComp outer inner).2 := by
  have hpoint : Function.Injective (sevenVariableAffinePoint outer) :=
    (sevenVariableAffinePoint_injective_iff outer).2 houter
  have hlinear : Function.Injective (sevenVariableAffineMap outer).linear := by
    intro x y hxy
    apply hpoint
    change outer.1 + (sevenVariableAffineMap outer).linear x =
      outer.1 + (sevenVariableAffineMap outer).linear y
    rw [hxy]
  have hmapped := hinner.map' (sevenVariableAffineMap outer).linear
    (LinearMap.ker_eq_bot.mpr hlinear)
  change LinearIndependent FABL.𝔽₂
    (fun i ↦ (sevenVariableAffineMap outer).linear (inner.2 i)) at hmapped
  change LinearIndependent FABL.𝔽₂
    (fun i ↦ (sevenVariableAffineMap outer).linear (inner.2 i))
  exact hmapped

/-- Canonical pattern images commute with affine-data composition. -/
theorem rankSevenWeightSixteenPatternImage_comp
    (c : RankSevenWeightSixteenPatternClass)
    (outer : SevenVariableAffineMapData n)
    (inner : SevenVariableAffineMapData 7) :
    rankSevenWeightSixteenPatternImage c
        (sevenVariableAffineMapDataComp outer inner) =
      (rankSevenWeightSixteenPatternImage c inner).image
        (sevenVariableAffinePoint outer) := by
  unfold rankSevenWeightSixteenPatternImage
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _hx
  exact sevenVariableAffinePoint_comp outer inner x

private theorem booleanFunction_eq_of_support_eq
    {f g : BooleanFunction n}
    (hfg : support f = support g) :
    f = g := by
  funext x
  have hx : x ∈ support f ↔ x ∈ support g := by rw [hfg]
  have hxOne : f x = 1 ↔ g x = 1 := by
    simpa only [mem_support] using hx
  by_cases hfx : f x = 0
  · have hgx : g x = 0 := by
      by_contra hgx
      have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      have hfxOne : f x = 1 := hxOne.mpr hgxOne
      exact zero_ne_one (hfx.symm.trans hfxOne)
    rw [hfx, hgx]
  · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    have hgxOne : g x = 1 := hxOne.mp hfxOne
    rw [hfxOne, hgxOne]

/-- Compact soundness of every generated normalized candidate yields
nonempty canonical-pattern certificate data for each rank-seven dual word. -/
theorem nonempty_rankSevenWeightSixteenPatternCertificate_of_mem_of_compactSoundness
    (hn : 3 ≤ n)
    (hcandidate : HasNormalizedWeightSixteenCompactCandidateSoundness)
    {h : BooleanFunction n}
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hrank : HasSupportAffineSpanRankSeven h) :
    Nonempty (RankSevenWeightSixteenPatternCertificate h) := by
  have hhData : h ∈ reedMuller (n - 3) n ∧ hammingWeight h = 16 := by
    simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hdual : h ∈ reedMullerDual 2 n := by
    rw [reedMullerDual_eq (r := 2) (n := n) (by omega)]
    simpa only [show n - 2 - 1 = n - 3 by omega] using hhData.1
  obtain ⟨p, hp, hspan⟩ := hrank
  obtain ⟨outer, code, _horigin, houter, hconstraints, hsupport⟩ :=
    exists_systematicWeightSixteenNormalization
      h p hp hdual hhData.2 hspan
  obtain ⟨candidate, hcode, hcompact⟩ := hcandidate hconstraints
  have hpoint : Function.Injective (sevenVariableAffinePoint outer) :=
    (sevenVariableAffinePoint_injective_iff outer).2 houter
  have hsupportCard : (support h).card = 16 := by
    simpa only [hammingWeight_eq_card_support] using hhData.2
  have hsystematicCard :
      (systematicWeightSixteenSupportOfCode
        candidate.systematicCode).card = 16 := by
    calc
      (systematicWeightSixteenSupportOfCode
          candidate.systematicCode).card =
          (systematicWeightSixteenSupportOfCode code).card := by rw [hcode]
      _ = (support h).card := by
        rw [← hsupport, Finset.card_image_of_injective _ hpoint]
      _ = 16 := hsupportCard
  have hsound : candidate.IsSound := hcompact.isSound hsystematicCard
  let inner := normalizedCandidateAffineMapData candidate
  have hfixed : systematicWeightSixteenFixedPoints ⊆
      rankSevenWeightSixteenPatternImage candidate.patternClass inner := by
    rw [hsound, systematicWeightSixteenSupportOfCode]
    exact Finset.subset_union_left
  have hinner : LinearIndependent FABL.𝔽₂ inner.2 :=
    linearIndependent_of_systematicFixedPoints_subset_patternImage
      candidate.patternClass inner hfixed
  let composed := sevenVariableAffineMapDataComp outer inner
  have hcomposed : LinearIndependent FABL.𝔽₂ composed.2 := by
    exact linearIndependent_sevenVariableAffineMapDataComp
      outer inner houter hinner
  have hpatternSupport :
      rankSevenWeightSixteenPatternImage candidate.patternClass composed =
        support h := by
    calc
      rankSevenWeightSixteenPatternImage candidate.patternClass composed =
          (rankSevenWeightSixteenPatternImage candidate.patternClass inner).image
            (sevenVariableAffinePoint outer) :=
        rankSevenWeightSixteenPatternImage_comp
          candidate.patternClass outer inner
      _ = (systematicWeightSixteenSupportOfCode
          candidate.systematicCode).image
            (sevenVariableAffinePoint outer) := by rw [hsound]
      _ = (systematicWeightSixteenSupportOfCode code).image
            (sevenVariableAffinePoint outer) := by rw [hcode]
      _ = support h := hsupport
  refine
    ⟨RankSevenWeightSixteenPatternCertificate.mk
      candidate.patternClass composed hcomposed ?_⟩
  apply booleanFunction_eq_of_support_eq
  rw [support_rankSevenWeightSixteenPatternWord, hpatternSupport]

/-- Compact soundness of every generated normalized candidate selects a
canonical-pattern certificate for each rank-seven dual word. -/
noncomputable def rankSevenWeightSixteenPatternCertificate_of_mem_of_compactSoundness
    (hn : 3 ≤ n)
    (hcandidate : HasNormalizedWeightSixteenCompactCandidateSoundness)
    {h : BooleanFunction n}
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hrank : HasSupportAffineSpanRankSeven h) :
    RankSevenWeightSixteenPatternCertificate h :=
  Classical.choice
    (nonempty_rankSevenWeightSixteenPatternCertificate_of_mem_of_compactSoundness
      hn hcandidate hh hrank)

/-- Every rank-seven weight-sixteen dual word has a selected canonical-pattern
certificate. -/
noncomputable def rankSevenWeightSixteenPatternCertificate
    (hn : 3 ≤ n)
    {h : BooleanFunction n}
    (hh : h ∈ orderTwoWeightSixteenDualWords n)
    (hrank : HasSupportAffineSpanRankSeven h) :
    RankSevenWeightSixteenPatternCertificate h :=
  rankSevenWeightSixteenPatternCertificate_of_mem_of_compactSoundness
    hn normalizedWeightSixteenCompactCandidateSoundness hh hrank

/-- The rank-seven weight-sixteen dual words are exactly the disjoint union of
the three canonical affine-pattern orbits. -/
theorem hasRankSevenWeightSixteenOrbitClassification
    (n : ℕ) (hn : 3 ≤ n) :
    HasRankSevenWeightSixteenOrbitClassification n :=
  hasRankSevenWeightSixteenOrbitClassification_of_certificate
    (fun _h hh hrank ↦
      rankSevenWeightSixteenPatternCertificate hn hh hrank)

/-- The compact candidate-soundness interface closes the full
weight-sixteen character lower bound. -/
theorem orderTwoWeightSixteenCharacterSum_ge_of_compactCandidateSoundness
    (f : BooleanFunction n)
    (hn : 3 ≤ n)
    (hcandidate : HasNormalizedWeightSixteenCompactCandidateSoundness) :
    orderTwoWeightSixteenCharacterSum f ≥
      -((3 * 127 + 127 * 2 ^ 128) * (2 ^ n : ℝ) ^ 7) :=
  orderTwoWeightSixteenCharacterSum_ge_of_certificate f hn
    (fun _h hh hrank ↦
      rankSevenWeightSixteenPatternCertificate_of_mem_of_compactSoundness
        hn hcandidate hh hrank)

/-- The complete weight-sixteen dual character sum has a uniform seventh-power
lower bound. -/
theorem orderTwoWeightSixteenCharacterSum_ge_rankSevenClassification
    (f : BooleanFunction n)
    (hn : 3 ≤ n) :
    orderTwoWeightSixteenCharacterSum f ≥
      -((3 * 127 + 127 * 2 ^ 128) * (2 ^ n : ℝ) ^ 7) :=
  orderTwoWeightSixteenCharacterSum_ge_of_compactCandidateSoundness
    f hn normalizedWeightSixteenCompactCandidateSoundness

/-- Compact soundness of the generated normalized candidates closes the sharp
fixed-order higher-order nonlinearity upper bound. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_of_compactCandidateSoundness
    (hcandidate : HasNormalizedWeightSixteenCompactCandidateSoundness)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          ((Real.sqrt 15 / 2) *
              (1 + Real.sqrt 2) ^ (r - 2)) *
            (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) :=
  exists_maximumHigherOrderNonlinearity_cast_le_of_weightSixteenCharacterSum
    (fun {n} f hn ↦ by
      simpa only [orderTwoWeightSixteenCharacterLoss, neg_mul] using
        orderTwoWeightSixteenCharacterSum_ge_of_compactCandidateSoundness
          f (by omega) hcandidate)
    r hr

/-- Carlet--Mesnager's sharp fixed-order upper bound for higher-order
nonlinearity. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_sharp
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          ((Real.sqrt 15 / 2) *
              (1 + Real.sqrt 2) ^ (r - 2)) *
            (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) :=
  exists_maximumHigherOrderNonlinearity_cast_le_of_compactCandidateSoundness
    normalizedWeightSixteenCompactCandidateSoundness r hr

end CryptBoolean
