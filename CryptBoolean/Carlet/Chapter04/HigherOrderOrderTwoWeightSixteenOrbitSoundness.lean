/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenRankSevenPatterns
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen
public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds

/-!
# Soundness of the rank-seven weight-sixteen pattern orbits

The canonical seven-variable pattern indicators belong to `RM(4,7)`.
Orthogonality with affine pullbacks of ambient quadratic functions then shows
that every injective affine pattern image belongs to the ambient
codimension-three Reed--Muller code.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

set_option maxRecDepth 100000 in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 3000000 in
/-- Each canonical rank-seven pattern indicator has algebraic degree at most
four. -/
theorem rankSevenWeightSixteenPatternIndicator_mem_reedMuller_four
    (c : RankSevenWeightSixteenPatternClass) :
    rankSevenWeightSixteenPatternIndicator c ∈ reedMuller 4 7 := by
  cases c <;> rw [mem_reedMuller_iff] <;> decide

/-- The affine map encoded by a translation and seven ambient directions. -/
def sevenVariableAffineMap (d : SevenVariableAffineMapData n) :
    FABL.F₂Cube 7 →ᵃ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun := sevenVariableAffinePoint d
  linear := Fintype.linearCombination FABL.𝔽₂ d.2
  map_vadd' x v := by
    change d.1 + ∑ i, (v i + x i) • d.2 i =
      (∑ i, v i • d.2 i) + (d.1 + ∑ i, x i • d.2 i)
    simp only [add_smul, Finset.sum_add_distrib]
    abel

@[simp] theorem sevenVariableAffineMap_apply
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 7) :
    sevenVariableAffineMap d x = sevenVariableAffinePoint d x :=
  rfl

private theorem booleanFunctionPairing_patternWord_eq_patternIndicator
    (q : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    booleanFunctionPairing n q (rankSevenWeightSixteenPatternWord c d) =
      booleanFunctionPairing 7 (q ∘ sevenVariableAffineMap d)
        (rankSevenWeightSixteenPatternIndicator c) := by
  classical
  have hinjective : Function.Injective (sevenVariableAffinePoint d) :=
    (sevenVariableAffinePoint_injective_iff d).2 hd
  simp only [booleanFunctionPairing_apply,
    rankSevenWeightSixteenPatternWord,
    rankSevenWeightSixteenPatternIndicator, Function.comp_apply,
    sevenVariableAffineMap_apply]
  simp only [mul_ite, mul_one, mul_zero]
  change Finset.sum Finset.univ (fun x ↦
      if x ∈ rankSevenWeightSixteenPatternImage c d then q x else 0) =
    Finset.sum Finset.univ (fun x ↦
      if x ∈ rankSevenWeightSixteenPattern c then
        q (sevenVariableAffinePoint d x) else 0)
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.univ_inter]
  unfold rankSevenWeightSixteenPatternImage
  rw [Finset.sum_image hinjective.injOn]

/-- Every injective affine image of a canonical rank-seven pattern is a
weight-sixteen word in the ambient dual Reed--Muller code. -/
theorem rankSevenWeightSixteenPatternWord_mem_orderTwoWeightSixteenDualWords
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    rankSevenWeightSixteenPatternWord c d ∈
      orderTwoWeightSixteenDualWords n := by
  have hn : 7 ≤ n := by
    have hfinrank := hd.fintype_card_le_finrank
    rw [Module.finrank_pi FABL.𝔽₂] at hfinrank
    simpa only [Fintype.card_fin] using hfinrank
  have hdual : rankSevenWeightSixteenPatternWord c d ∈
      reedMullerDual 2 n := by
    rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    have hqDegree : FABL.functionAlgebraicDegree q ≤ 2 := by
      simpa only [mem_reedMuller_iff] using hq
    have hpullbackDegree : FABL.functionAlgebraicDegree
        (q ∘ sevenVariableAffineMap d) ≤ 2 :=
      (functionAlgebraicDegree_comp_affineMap_le_general q
        (sevenVariableAffineMap d)).trans hqDegree
    have hpullback : q ∘ sevenVariableAffineMap d ∈ reedMuller 2 7 := by
      simpa only [mem_reedMuller_iff] using hpullbackDegree
    have hindicatorDual : rankSevenWeightSixteenPatternIndicator c ∈
        reedMullerDual 2 7 := by
      rw [reedMullerDual_eq (r := 2) (n := 7) (by omega)]
      simpa only using
        rankSevenWeightSixteenPatternIndicator_mem_reedMuller_four c
    rw [booleanFunctionPairing_patternWord_eq_patternIndicator q c d hd]
    exact hindicatorDual (q ∘ sevenVariableAffineMap d) hpullback
  have hmem : rankSevenWeightSixteenPatternWord c d ∈
      reedMuller (n - 3) n := by
    rw [reedMullerDual_eq (r := 2) (n := n) (by omega)] at hdual
    simpa only [show n - 2 - 1 = n - 3 by omega] using hdual
  simp only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hmem,
    hammingWeight_rankSevenWeightSixteenPatternWord_of_independent c d hd⟩

/-- The support-affine-span rank of an injective canonical pattern image is
exactly seven. -/
theorem finrank_supportDifferenceSpan_rankSevenWeightSixteenPatternWord
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    Module.finrank FABL.𝔽₂
      (supportDifferenceSpan (rankSevenWeightSixteenPatternWord c d) d.1) = 7 := by
  classical
  let L : FABL.F₂Cube 7 →ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
    (sevenVariableAffineMap d).linear
  let b : Fin 7 → FABL.F₂Cube 7 :=
    rankSevenWeightSixteenPatternAffineBasis c
  let w : Fin 7 → FABL.F₂Cube n := fun i ↦ L (b i)
  have hpointInjective : Function.Injective (sevenVariableAffinePoint d) :=
    (sevenVariableAffinePoint_injective_iff d).2 hd
  have hLInjective : Function.Injective L := by
    intro x y hxy
    apply hpointInjective
    change d.1 + L x = d.1 + L y
    rw [hxy]
  have hbIndependent : LinearIndependent FABL.𝔽₂ b := by
    exact linearIndependent_rankSevenWeightSixteenPatternAffineBasis c
  have hwIndependent : LinearIndependent FABL.𝔽₂ w := by
    exact hbIndependent.map' L (LinearMap.ker_eq_bot.mpr hLInjective)
  have hp : d.1 ∈ support (rankSevenWeightSixteenPatternWord c d) := by
    rw [support_rankSevenWeightSixteenPatternWord]
    unfold rankSevenWeightSixteenPatternImage
    exact Finset.mem_image.2 ⟨0, zero_mem_rankSevenWeightSixteenPattern c, by
      simp [sevenVariableAffinePoint]⟩
  have hwMem (i : Fin 7) :
      w i ∈ supportDifferenceSpan
        (rankSevenWeightSixteenPatternWord c d) d.1 := by
    rw [supportDifferenceSpan_eq_span_supportDifferences]
    apply Submodule.subset_span
    refine ⟨sevenVariableAffinePoint d (b i), ?_, ?_⟩
    · apply Finset.mem_erase.2
      constructor
      · intro hpoint
        have hzero : b i = 0 := by
          apply hpointInjective
          simpa [sevenVariableAffinePoint] using hpoint
        exact (hbIndependent.ne_zero i) hzero
      · rw [support_rankSevenWeightSixteenPatternWord]
        unfold rankSevenWeightSixteenPatternImage
        exact Finset.mem_image.2
          ⟨b i, rankSevenWeightSixteenPatternAffineBasis_mem c i, rfl⟩
    · change L (b i) = sevenVariableAffinePoint d (b i) + d.1
      change L (b i) = (d.1 + L (b i)) + d.1
      calc
        L (b i) = (d.1 + d.1) + L (b i) := by
          rw [ZModModule.add_self, zero_add]
        _ = (d.1 + L (b i)) + d.1 := by abel
  let ws : Fin 7 →
      supportDifferenceSpan (rankSevenWeightSixteenPatternWord c d) d.1 :=
    fun i ↦ ⟨w i, hwMem i⟩
  have hwsIndependent : LinearIndependent FABL.𝔽₂ ws := by
    apply LinearIndependent.of_comp
      (supportDifferenceSpan
        (rankSevenWeightSixteenPatternWord c d) d.1).subtype
    change LinearIndependent FABL.𝔽₂ w
    exact hwIndependent
  have hlower : 7 ≤ Module.finrank FABL.𝔽₂
      (supportDifferenceSpan
        (rankSevenWeightSixteenPatternWord c d) d.1) := by
    simpa only [Fintype.card_fin] using hwsIndependent.fintype_card_le_finrank
  have hn : 7 ≤ n := by
    have hfinrank := hd.fintype_card_le_finrank
    rw [Module.finrank_pi FABL.𝔽₂] at hfinrank
    simpa only [Fintype.card_fin] using hfinrank
  have hdual :=
    rankSevenWeightSixteenPatternWord_mem_orderTwoWeightSixteenDualWords c d hd
  have hdualData : rankSevenWeightSixteenPatternWord c d ∈
        reedMuller (n - 3) n ∧
      hammingWeight (rankSevenWeightSixteenPatternWord c d) = 16 := by
    simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hdual
  have hupper := finrank_supportDifferenceSpan_le_seven_of_weight_sixteen
    (rankSevenWeightSixteenPatternWord c d) d.1 hp (by omega)
      hdualData.1 hdualData.2
  omega

end CryptBoolean
