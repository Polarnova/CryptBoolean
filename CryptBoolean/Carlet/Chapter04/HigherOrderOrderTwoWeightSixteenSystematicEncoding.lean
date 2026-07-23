/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenNormalizedClassification
public import Mathlib.Data.Finset.Sort

/-!
# Systematic encoding of normalized rank-seven supports

A normalized support contains zero and the seven coordinate points.  After
the constant row is replaced by its sum with the seven coordinate rows, these
eight points give the identity columns.  Every remaining point is encoded by
an odd eight-bit column, and the seven coordinate bits recover the point.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The systematic eight-bit column attached to a seven-variable point. -/
def systematicWeightSixteenPointColumn
    (x : FABL.F₂Cube 7) : BitVec 8 :=
  BitVec.ofFnLE fun i ↦
    Fin.cases
      (decide ((1 + ∑ j : Fin 7, x j) = (1 : FABL.𝔽₂)))
      (fun j ↦ decide (x j = 1)) i

/-- Recover a seven-variable point from the coordinate bits of a systematic
column. -/
def systematicWeightSixteenColumnPoint
    (column : BitVec 8) : FABL.F₂Cube 7 :=
  fun j ↦ if column.getLsb j.succ then 1 else 0

@[simp] theorem systematicWeightSixteenColumnPoint_pointColumn
    (x : FABL.F₂Cube 7) :
    systematicWeightSixteenColumnPoint
        (systematicWeightSixteenPointColumn x) = x := by
  funext j
  simp only [systematicWeightSixteenColumnPoint,
    systematicWeightSixteenPointColumn, BitVec.getLsb_ofFnLE]
  by_cases hx : x j = 1
  · simp [hx]
  · have hxzero : x j = 0 := by
      by_contra hzero
      exact hx (Fin.eq_one_of_ne_zero (x j) hzero)
    simp [hxzero]

/-- Distinct normalized points have distinct systematic columns. -/
theorem systematicWeightSixteenPointColumn_injective :
    Function.Injective systematicWeightSixteenPointColumn := by
  intro x y hxy
  rw [← systematicWeightSixteenColumnPoint_pointColumn x,
    ← systematicWeightSixteenColumnPoint_pointColumn y, hxy]

/-- The normalized affine-basis points already represented by the identity
columns. -/
def systematicWeightSixteenFixedPoints : Finset (FABL.F₂Cube 7) :=
  {0} ∪ Finset.univ.image fun i : Fin 7 ↦
    Pi.single i (1 : FABL.𝔽₂)

@[simp] theorem card_systematicWeightSixteenFixedPoints :
    systematicWeightSixteenFixedPoints.card = 8 := by
  classical
  rw [systematicWeightSixteenFixedPoints,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_singleton,
      Finset.card_image_of_injective Finset.univ
        (Pi.linearIndependent_single_one (Fin 7) FABL.𝔽₂).injective]
    simp
  · rw [Finset.disjoint_left]
    intro x hxZero hxImage
    simp only [Finset.mem_singleton] at hxZero
    subst x
    obtain ⟨i, _hi, hzero⟩ := Finset.mem_image.mp hxImage
    have hi := congrFun hzero i
    simp at hi

/-- Reconstruct the full normalized support from its eight packed nonidentity
systematic columns. -/
def systematicWeightSixteenSupportOfCode
    (code : BitVec 64) : Finset (FABL.F₂Cube 7) :=
  systematicWeightSixteenFixedPoints ∪
    Finset.univ.image fun i : Fin 8 ↦
      systematicWeightSixteenColumnPoint
        (systematicWeightSixteenColumn code i)

end CryptBoolean
