/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.PartialBentDual
public import FABL.Chapter06.F₂Polynomials.ExtremalBounds

/-!
# Counterexamples for printed partial-bent assertions

Finite two-variable counterexamples to the algebraic-degree and disjoint-support
sum assertions printed on Carlet p. 105 under the exact punctured two-level definition.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The indicator of the singleton binary point `![1, 0]`. -/
def partialBentDegreeCounterexample : BooleanFunction 2 :=
  fun x ↦ if x = ![1, 0] then 1 else 0

/-- The indicator of the two points whose second coordinate is one. -/
def partialBentSumCounterexampleCompanion : BooleanFunction 2 :=
  fun x ↦ x 1

private theorem partialBentIntegerFourier_partialBentDegreeCounterexample
    (u : FABL.F₂Cube 2) :
    partialBentIntegerFourier partialBentDegreeCounterexample u =
      if u = 0 then 1 else if u 0 = 0 then 1 else -1 := by
  decide +revert

private theorem partialBentIntegerFourier_partialBentSumCounterexampleCompanion
    (u : FABL.F₂Cube 2) :
    partialBentIntegerFourier partialBentSumCounterexampleCompanion u =
      if u = 0 then 2 else if u = ![0, 1] then -2 else 0 := by
  decide +revert

private theorem partialBentIntegerFourier_add_partialBentCounterexamples
    (u : FABL.F₂Cube 2) :
    partialBentIntegerFourier
        (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion) u =
      if u = 0 then 3 else -1 := by
  decide +revert

private theorem rawFourierTransform_partialBentDegreeCounterexample
    (u : FABL.F₂Cube 2) :
    rawFourierTransform
        (FABL.booleanRealEmbedding partialBentDegreeCounterexample) u =
      if u = 0 then 1 else if u 0 = 0 then 1 else -1 := by
  rw [← partialBentIntegerFourier_cast,
    partialBentIntegerFourier_partialBentDegreeCounterexample]
  split <;> norm_num

private theorem rawFourierTransform_partialBentSumCounterexampleCompanion
    (u : FABL.F₂Cube 2) :
    rawFourierTransform
        (FABL.booleanRealEmbedding partialBentSumCounterexampleCompanion) u =
      if u = 0 then 2 else if u = ![0, 1] then -2 else 0 := by
  rw [← partialBentIntegerFourier_cast,
    partialBentIntegerFourier_partialBentSumCounterexampleCompanion]
  split <;> norm_num

private theorem rawFourierTransform_add_partialBentCounterexamples
    (u : FABL.F₂Cube 2) :
    rawFourierTransform
        (FABL.booleanRealEmbedding
          (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion)) u =
      if u = 0 then 3 else -1 := by
  rw [← partialBentIntegerFourier_cast,
    partialBentIntegerFourier_add_partialBentCounterexamples]
  split <;> norm_num

private theorem hasPartialBentFourierLevels_partialBentDegreeCounterexample :
    HasPartialBentFourierLevels partialBentDegreeCounterexample (-1) := by
  rw [HasPartialBentFourierLevels]
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    change rawFourierTransform
      (FABL.booleanRealEmbedding partialBentDegreeCounterexample) u.1 ∈ _
    rw [rawFourierTransform_partialBentDegreeCounterexample, if_neg u.2]
    split <;> norm_num
  · intro hz
    norm_num at hz
    rcases hz with rfl | rfl
    · have hpoint : ![1, 0] ≠ (0 : FABL.F₂Cube 2) := by decide
      refine ⟨⟨![1, 0], hpoint⟩, ?_⟩
      change rawFourierTransform
        (FABL.booleanRealEmbedding partialBentDegreeCounterexample) ![1, 0] = -1
      rw [rawFourierTransform_partialBentDegreeCounterexample]
      norm_num
    · have hpoint : ![0, 1] ≠ (0 : FABL.F₂Cube 2) := by decide
      refine ⟨⟨![0, 1], hpoint⟩, ?_⟩
      change rawFourierTransform
        (FABL.booleanRealEmbedding partialBentDegreeCounterexample) ![0, 1] = 1
      rw [rawFourierTransform_partialBentDegreeCounterexample]
      norm_num

private theorem hasPartialBentFourierLevels_partialBentSumCounterexampleCompanion :
    HasPartialBentFourierLevels partialBentSumCounterexampleCompanion (-2) := by
  rw [HasPartialBentFourierLevels]
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    change rawFourierTransform
      (FABL.booleanRealEmbedding partialBentSumCounterexampleCompanion) u.1 ∈ _
    rw [rawFourierTransform_partialBentSumCounterexampleCompanion, if_neg u.2]
    split <;> norm_num
  · intro hz
    norm_num at hz
    rcases hz with rfl | rfl
    · have hpoint : ![0, 1] ≠ (0 : FABL.F₂Cube 2) := by decide
      refine ⟨⟨![0, 1], hpoint⟩, ?_⟩
      change rawFourierTransform
        (FABL.booleanRealEmbedding partialBentSumCounterexampleCompanion) ![0, 1] = -2
      rw [rawFourierTransform_partialBentSumCounterexampleCompanion]
      norm_num
    · have hpoint : ![1, 0] ≠ (0 : FABL.F₂Cube 2) := by decide
      refine ⟨⟨![1, 0], hpoint⟩, ?_⟩
      change rawFourierTransform
        (FABL.booleanRealEmbedding partialBentSumCounterexampleCompanion) ![1, 0] = 0
      rw [rawFourierTransform_partialBentSumCounterexampleCompanion]
      norm_num

private theorem isPartialBent_partialBentDegreeCounterexample :
    IsPartialBent partialBentDegreeCounterexample :=
  ⟨by norm_num, -1, hasPartialBentFourierLevels_partialBentDegreeCounterexample⟩

private theorem isPartialBent_partialBentSumCounterexampleCompanion :
    IsPartialBent partialBentSumCounterexampleCompanion :=
  ⟨by norm_num, -2, hasPartialBentFourierLevels_partialBentSumCounterexampleCompanion⟩

private theorem functionAlgebraicDegree_partialBentDegreeCounterexample :
    FABL.functionAlgebraicDegree partialBentDegreeCounterexample = 2 := by
  apply (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
    partialBentDegreeCounterexample (by norm_num)).2
  decide

/-- The exact punctured two-level definition permits algebraic degree
strictly greater than half the dimension. -/
theorem partialBentDegreeCounterexample_refutes_bound :
    IsPartialBent partialBentDegreeCounterexample ∧
      FABL.functionAlgebraicDegree partialBentDegreeCounterexample = 2 ∧
      2 / 2 < FABL.functionAlgebraicDegree partialBentDegreeCounterexample := by
  refine ⟨isPartialBent_partialBentDegreeCounterexample,
    functionAlgebraicDegree_partialBentDegreeCounterexample, ?_⟩
  rw [functionAlgebraicDegree_partialBentDegreeCounterexample]
  norm_num

private theorem partialBentDegreeCounterexample_has_first_type :
    partialBentIntegerFourier partialBentDegreeCounterexample 0 -
        bitValueInt (partialBentDegreeCounterexample 0) =
      -((-1 : ℤ) - bitValueInt (partialBentDegreeCounterexample 0)) *
        ((2 : ℤ) ^ (2 / 2) - 1) := by
  decide

private theorem partialBentSumCounterexampleCompanion_has_first_type :
    partialBentIntegerFourier partialBentSumCounterexampleCompanion 0 -
        bitValueInt (partialBentSumCounterexampleCompanion 0) =
      -((-2 : ℤ) - bitValueInt (partialBentSumCounterexampleCompanion 0)) *
        ((2 : ℤ) ^ (2 / 2) - 1) := by
  decide

private theorem partialBentCounterexamples_support_inter_subset_zero :
    support partialBentDegreeCounterexample ∩ support partialBentSumCounterexampleCompanion ⊆
      ({0} : Finset (FABL.F₂Cube 2)) := by
  decide

private theorem not_isPartialBent_add_partialBentCounterexamples :
    ¬ IsPartialBent
      (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion) := by
  rintro ⟨_even, level, hlevels⟩
  rw [HasPartialBentFourierLevels] at hlevels
  have hlevelRange : (level : ℝ) ∈
      Set.range (fun u : {u : FABL.F₂Cube 2 // u ≠ 0} ↦
        rawFourierTransform
          (FABL.booleanRealEmbedding
            (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion)) u.1) := by
    rw [hlevels]
    simp
  obtain ⟨u, hu⟩ := hlevelRange
  change rawFourierTransform
    (FABL.booleanRealEmbedding
      (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion)) u.1 =
        (level : ℝ) at hu
  rw [rawFourierTransform_add_partialBentCounterexamples, if_neg u.2] at hu
  have hupperRange : (level : ℝ) + (2 : ℝ) ^ (2 / 2) ∈
      Set.range (fun u : {u : FABL.F₂Cube 2 // u ≠ 0} ↦
        rawFourierTransform
          (FABL.booleanRealEmbedding
            (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion)) u.1) := by
    rw [hlevels]
    simp
  obtain ⟨v, hv⟩ := hupperRange
  change rawFourierTransform
    (FABL.booleanRealEmbedding
      (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion)) v.1 =
        (level : ℝ) + (2 : ℝ) ^ (2 / 2) at hv
  rw [rawFourierTransform_add_partialBentCounterexamples, if_neg v.2] at hv
  norm_num at hv
  linarith

/-- Two partial bent functions of the corrected first Fourier type can
have disjoint supports while their sum fails to be partial bent. -/
theorem partialBentCounterexamples_refute_disjoint_support_sum :
    HasPartialBentFourierLevels partialBentDegreeCounterexample (-1) ∧
      HasPartialBentFourierLevels partialBentSumCounterexampleCompanion (-2) ∧
      IsPartialBent partialBentDegreeCounterexample ∧
      IsPartialBent partialBentSumCounterexampleCompanion ∧
      (partialBentIntegerFourier partialBentDegreeCounterexample 0 -
          bitValueInt (partialBentDegreeCounterexample 0) =
        -((-1 : ℤ) - bitValueInt (partialBentDegreeCounterexample 0)) *
          ((2 : ℤ) ^ (2 / 2) - 1)) ∧
      (partialBentIntegerFourier partialBentSumCounterexampleCompanion 0 -
          bitValueInt (partialBentSumCounterexampleCompanion 0) =
        -((-2 : ℤ) - bitValueInt (partialBentSumCounterexampleCompanion 0)) *
          ((2 : ℤ) ^ (2 / 2) - 1)) ∧
      support partialBentDegreeCounterexample ∩ support partialBentSumCounterexampleCompanion ⊆
        ({0} : Finset (FABL.F₂Cube 2)) ∧
      ¬ IsPartialBent
        (partialBentDegreeCounterexample + partialBentSumCounterexampleCompanion) := by
  exact ⟨hasPartialBentFourierLevels_partialBentDegreeCounterexample,
    hasPartialBentFourierLevels_partialBentSumCounterexampleCompanion,
    isPartialBent_partialBentDegreeCounterexample,
    isPartialBent_partialBentSumCounterexampleCompanion,
    partialBentDegreeCounterexample_has_first_type,
    partialBentSumCounterexampleCompanion_has_first_type,
    partialBentCounterexamples_support_inter_subset_zero,
    not_isPartialBent_add_partialBentCounterexamples⟩

end CryptBoolean
