/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerWeightSixteenSelfDual
public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.SystematicEncoding

/-!
# Normalize full-span weight-sixteen supports

A basis of seven actual support differences identifies a full-span
weight-sixteen support with a normalized subset of the seven-variable cube.
The eight points outside the affine basis give a sorted systematic code whose
columns are orthonormal.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The inverse-image support under seven-variable affine-map data. -/
noncomputable def normalizedRankSevenSupport
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n) :
    Finset (FABL.F₂Cube 7) :=
  Finset.univ.filter fun x ↦ sevenVariableAffinePoint d x ∈ support h

@[simp] theorem mem_normalizedRankSevenSupport
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (x : FABL.F₂Cube 7) :
    x ∈ normalizedRankSevenSupport h d ↔
      sevenVariableAffinePoint d x ∈ support h := by
  simp [normalizedRankSevenSupport]

/-- If the seven directions span the support-difference space, the normalized
support maps exactly onto the original support. -/
theorem image_normalizedRankSevenSupport_eq_support
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1) :
    (normalizedRankSevenSupport h d).image
        (sevenVariableAffinePoint d) = support h := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_normalizedRankSevenSupport h d x).mp hx
  · intro hy
    have hySpan : y + d.1 ∈ supportDifferenceSpan h d.1 := by
      have hyAffine :=
        support_subset_binaryAffineSubspace_supportDifferenceSpan h d.1 hy
      change y ∈ FABL.binaryAffineSubspace
        (supportDifferenceSpan h d.1) d.1 at hyAffine
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hyAffine
      exact hyAffine
    rw [← hspan, ← Fintype.range_linearCombination] at hySpan
    obtain ⟨x, hx⟩ := hySpan
    have hpoint : sevenVariableAffinePoint d x = y := by
      rw [sevenVariableAffinePoint,
        ← Fintype.linearCombination_apply, hx]
      calc
        d.1 + (y + d.1) = y + (d.1 + d.1) := by abel
        _ = y := by rw [ZModModule.add_self, add_zero]
    exact Finset.mem_image.mpr ⟨x,
      (mem_normalizedRankSevenSupport h d x).mpr (hpoint ▸ hy), hpoint⟩

/-- Pack eight little-endian eight-bit columns into one 64-bit word. -/
def packSystematicWeightSixteenColumns
    (columns : Fin 8 → BitVec 8) : BitVec 64 :=
  columns 7 ++ (columns 6 ++ (columns 5 ++ (columns 4 ++
    (columns 3 ++ (columns 2 ++ (columns 1 ++ columns 0))))))

@[simp] theorem systematicWeightSixteenColumn_pack
    (columns : Fin 8 → BitVec 8) (i : Fin 8) :
    systematicWeightSixteenColumn
        (packSystematicWeightSixteenColumns columns) i = columns i := by
  fin_cases i <;>
    simp only [systematicWeightSixteenColumn,
      packSystematicWeightSixteenColumns]
  all_goals
    repeat' (rw [BitVec.extractLsb'_append_eq_ite] <;> norm_num)
  all_goals simp

/-- Every point column has odd Hamming weight. -/
theorem systematicWeightSixteenPointColumn_odd
    (x : FABL.F₂Cube 7) :
    (systematicWeightSixteenPointColumn x).cpop.getLsbD 0 = true := by
  revert x
  set_option maxRecDepth 100000 in decide

/-- A point column is nonunit exactly away from the normalized affine basis. -/
theorem systematicWeightSixteenPointColumn_nonunit_iff
    (x : FABL.F₂Cube 7) :
    ((systematicWeightSixteenPointColumn x) &&&
        (systematicWeightSixteenPointColumn x - 1) != 0) =
      decide (x ∉ systematicWeightSixteenFixedPoints) := by
  revert x
  set_option maxRecDepth 100000 in decide

/-- Interpret one Boolean bit as a binary-field element. -/
def boolF₂ (b : Bool) : FABL.𝔽₂ :=
  if b then 1 else 0

/-- Deciding whether a binary-field element is one recovers that element. -/
@[simp] theorem boolF₂_decide_eq_one (a : FABL.𝔽₂) :
    boolF₂ (decide (a = 1)) = a := by
  by_cases ha : a = 0
  · simp [ha, boolF₂]
  · have haOne : a = 1 := Fin.eq_one_of_ne_zero a ha
    simp [haOne, boolF₂]

/-- Deciding whether a binary-field element is zero gives its complement. -/
@[simp] theorem boolF₂_decide_eq_zero (a : FABL.𝔽₂) :
    boolF₂ (decide (a = 0)) = 1 + a := by
  by_cases ha : a = 0
  · simp [ha, boolF₂]
  · have haOne : a = 1 := Fin.eq_one_of_ne_zero a ha
    simp [haOne, boolF₂]

/-- Interpret an eight-bit word as a binary vector. -/
def bitVecEightF₂ (x : BitVec 8) : FABL.F₂Cube 8 :=
  fun i ↦ boolF₂ (x.getLsbD i)

@[simp] theorem boolF₂_and (a b : Bool) :
    boolF₂ (a && b) = boolF₂ a * boolF₂ b := by
  cases a <;> cases b <;> rfl

@[simp] theorem boolF₂_xor (a b : Bool) :
    boolF₂ (Bool.xor a b) = boolF₂ a + boolF₂ b := by
  cases a <;> cases b <;> decide

/-- The explicit parity of the eight coordinatewise conjunctions. -/
def bitVecEightAndParity (x y : BitVec 8) : Bool :=
  Bool.xor (x.getLsbD 0 && y.getLsbD 0)
    (Bool.xor (x.getLsbD 1 && y.getLsbD 1)
      (Bool.xor (x.getLsbD 2 && y.getLsbD 2)
        (Bool.xor (x.getLsbD 3 && y.getLsbD 3)
          (Bool.xor (x.getLsbD 4 && y.getLsbD 4)
            (Bool.xor (x.getLsbD 5 && y.getLsbD 5)
              (Bool.xor (x.getLsbD 6 && y.getLsbD 6)
                (x.getLsbD 7 && y.getLsbD 7)))))))

theorem bitVecEight_cpop_and_lsb_zero
    (x y : BitVec 8) :
    (x &&& y).cpop.getLsbD 0 = bitVecEightAndParity x y := by
  unfold bitVecEightAndParity
  bv_decide

theorem bitVecEight_cpop_and_odd_iff_dotProduct_one
    (x y : BitVec 8) :
    (x &&& y).cpop.getLsbD 0 = true ↔
      FABL.f₂DotProduct (bitVecEightF₂ x) (bitVecEightF₂ y) = 1 := by
  rw [bitVecEight_cpop_and_lsb_zero]
  have hdot :
      FABL.f₂DotProduct (bitVecEightF₂ x) (bitVecEightF₂ y) =
        boolF₂ (bitVecEightAndParity x y) := by
    unfold FABL.f₂DotProduct dotProduct bitVecEightF₂
      bitVecEightAndParity
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [boolF₂_xor, boolF₂_and]
    norm_num
  rw [hdot]
  unfold boolF₂
  cases bitVecEightAndParity x y <;> simp

theorem bitVecEight_cpop_and_even_iff_dotProduct_zero
    (x y : BitVec 8) :
    (x &&& y).cpop.getLsbD 0 = false ↔
      FABL.f₂DotProduct (bitVecEightF₂ x) (bitVecEightF₂ y) = 0 := by
  constructor
  · intro heven
    by_contra hdot
    have hdotOne :
        FABL.f₂DotProduct (bitVecEightF₂ x) (bitVecEightF₂ y) = 1 :=
      Fin.eq_one_of_ne_zero _ hdot
    have hodd :=
      (bitVecEight_cpop_and_odd_iff_dotProduct_one x y).mpr hdotOne
    rw [heven] at hodd
    exact Bool.false_ne_true hodd
  · intro hdot
    by_contra heven
    have hodd : (x &&& y).cpop.getLsbD 0 = true :=
      Bool.eq_true_of_not_eq_false heven
    have hdotOne :=
      (bitVecEight_cpop_and_odd_iff_dotProduct_one x y).mp hodd
    rw [hdot] at hdotOne
    exact zero_ne_one hdotOne

theorem areSystematicWeightSixteenColumnsOrthogonal_iff
    (x y : BitVec 8) :
    areSystematicWeightSixteenColumnsOrthogonal x y = true ↔
      FABL.f₂DotProduct (bitVecEightF₂ x) (bitVecEightF₂ y) = 0 := by
  rw [← bitVecEight_cpop_and_even_iff_dotProduct_zero]
  simp [areSystematicWeightSixteenColumnsOrthogonal]

/-- The normalized support has the original weight when the affine map is
injective and spans all support differences. -/
theorem card_normalizedRankSevenSupport
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1) :
    (normalizedRankSevenSupport h d).card = hammingWeight h := by
  have himage := image_normalizedRankSevenSupport_eq_support h d hspan
  have hinjective : Function.Injective (sevenVariableAffinePoint d) :=
    (sevenVariableAffinePoint_injective_iff d).2 hd
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ hinjective,
    ← hammingWeight_eq_card_support] at hcard
  exact hcard

/-- Actual support-difference basis vectors put zero and the seven coordinate
points into the normalized support. -/
theorem systematicWeightSixteenFixedPoints_subset_normalizedRankSevenSupport
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (v : Fin 7 → FABL.F₂Cube n) (hp : p ∈ support h)
    (hv : ∀ i, v i ∈ supportDifferences h p) :
    systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h (p, v) := by
  intro x hx
  simp only [systematicWeightSixteenFixedPoints, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain rfl | ⟨i, rfl⟩ := hx
  · simpa [sevenVariableAffinePoint] using hp
  · obtain ⟨y, hy, hvEq⟩ := hv i
    have hySupport : y ∈ support h := (Finset.mem_erase.mp hy).2
    rw [mem_normalizedRankSevenSupport]
    have hpoint :
        sevenVariableAffinePoint (p, v) (Pi.single i (1 : FABL.𝔽₂)) = y := by
      change p + Fintype.linearCombination FABL.𝔽₂ v
        (Pi.single i (1 : FABL.𝔽₂)) = y
      rw [Fintype.linearCombination_apply_single, one_smul]
      rw [hvEq]
      calc
        p + (y + p) = y + (p + p) := by abel
        _ = y := by rw [ZModModule.add_self, add_zero]
    simpa only [hpoint] using hySupport

/-- A linear left inverse of the seven selected support directions, translated
to an affine projection sending the selected basepoint to zero. -/
noncomputable def rankSevenAffineProjection
    (d : SevenVariableAffineMapData n) :
    FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube 7 where
  toFun y := (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse (y + d.1)
  linear := (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse
  map_vadd' y v := by
    change (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse
        (v + y + d.1) =
      (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse v +
        (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse (y + d.1)
    rw [show v + y + d.1 = v + (y + d.1) by abel, map_add]

/-- The affine projection is a left inverse to the selected affine embedding. -/
theorem rankSevenAffineProjection_sevenVariableAffinePoint
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (x : FABL.F₂Cube 7) :
    rankSevenAffineProjection d (sevenVariableAffinePoint d x) = x := by
  have hinjective : Function.Injective
      (Fintype.linearCombination FABL.𝔽₂ d.2) := by
    intro a b hab
    have haffine : sevenVariableAffinePoint d a =
        sevenVariableAffinePoint d b := by
      change d.1 + Fintype.linearCombination FABL.𝔽₂ d.2 a =
        d.1 + Fintype.linearCombination FABL.𝔽₂ d.2 b
      rw [hab]
    exact (sevenVariableAffinePoint_injective_iff d).2 hd haffine
  have hker : LinearMap.ker (Fintype.linearCombination FABL.𝔽₂ d.2) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjective
  change (Fintype.linearCombination FABL.𝔽₂ d.2).leftInverse
      (d.1 + Fintype.linearCombination FABL.𝔽₂ d.2 x + d.1) = x
  rw [show d.1 + Fintype.linearCombination FABL.𝔽₂ d.2 x + d.1 =
    Fintype.linearCombination FABL.𝔽₂ d.2 x by
      calc
        d.1 + Fintype.linearCombination FABL.𝔽₂ d.2 x + d.1 =
            Fintype.linearCombination FABL.𝔽₂ d.2 x + (d.1 + d.1) := by
          abel
        _ = Fintype.linearCombination FABL.𝔽₂ d.2 x := by
          rw [ZModModule.add_self, add_zero]]
  exact LinearMap.leftInverse_apply_of_inj hker x

/-- The `i`th binary row of the transformed affine-evaluation matrix. -/
def systematicWeightSixteenPointCoordinate
    (i : Fin 8) : BooleanFunction 7 :=
  fun x ↦ bitVecEightF₂ (systematicWeightSixteenPointColumn x) i

@[simp] theorem systematicWeightSixteenPointCoordinate_zero
    (x : FABL.F₂Cube 7) :
    systematicWeightSixteenPointCoordinate 0 x =
      1 + ∑ j : Fin 7, x j := by
  simp [systematicWeightSixteenPointCoordinate, bitVecEightF₂,
    systematicWeightSixteenPointColumn]

@[simp] theorem systematicWeightSixteenPointCoordinate_succ
    (j : Fin 7) (x : FABL.F₂Cube 7) :
    systematicWeightSixteenPointCoordinate j.succ x = x j := by
  have hj : (j : ℕ) + 1 < 8 := by omega
  simp [systematicWeightSixteenPointCoordinate, bitVecEightF₂,
    systematicWeightSixteenPointColumn, hj]

/-- Every transformed systematic row is affine. -/
theorem systematicWeightSixteenPointCoordinate_mem_reedMuller_one
    (i : Fin 8) :
    systematicWeightSixteenPointCoordinate i ∈ reedMuller 1 7 := by
  classical
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hcoordinate :
        systematicWeightSixteenPointCoordinate (0 : Fin 8) =
          FABL.affineFunction 1
            (fun _ : Fin 7 ↦ (1 : FABL.𝔽₂)) := by
      funext x
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
    rw [hcoordinate]
    exact affineFunction_mem_reedMuller_one _ _
  · have hcoordinate :
        systematicWeightSixteenPointCoordinate j.succ =
          FABL.affineFunction 0
            (Pi.single j (1 : FABL.𝔽₂)) := by
      funext x
      simp [FABL.affineFunction, FABL.f₂DotProduct]
    rw [hcoordinate]
    exact affineFunction_mem_reedMuller_one _ _

private theorem booleanFunctionPairing_eq_sum_support_right
    (f h : BooleanFunction n) :
    booleanFunctionPairing n f h = ∑ x ∈ support h, f x := by
  rw [booleanFunctionPairing_apply]
  rw [support, FABL.f₂OneSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hhx : h x = 0
  · simp [hhx]
  · have hhxOne : h x = 1 := Fin.eq_one_of_ne_zero _ hhx
    simp [hhxOne]

/-- Orthogonality to ambient quadratics makes every pair of transformed
systematic rows orthogonal on the full normalized support. -/
theorem normalizedRankSevenSupport_pointCoordinate_gram_zero
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hdual : h ∈ reedMullerDual 2 n)
    (i j : Fin 8) :
    (∑ x ∈ normalizedRankSevenSupport h d,
      systematicWeightSixteenPointCoordinate i x *
        systematicWeightSixteenPointCoordinate j x) = 0 := by
  let projection := rankSevenAffineProjection d
  let left : BooleanFunction n :=
    systematicWeightSixteenPointCoordinate i ∘ projection
  let right : BooleanFunction n :=
    systematicWeightSixteenPointCoordinate j ∘ projection
  have hleftDegree : FABL.functionAlgebraicDegree left ≤ 1 := by
    exact (functionAlgebraicDegree_comp_affineMap_le_general
      (systematicWeightSixteenPointCoordinate i) projection).trans
        (systematicWeightSixteenPointCoordinate_mem_reedMuller_one i)
  have hrightDegree : FABL.functionAlgebraicDegree right ≤ 1 := by
    exact (functionAlgebraicDegree_comp_affineMap_le_general
      (systematicWeightSixteenPointCoordinate j) projection).trans
        (systematicWeightSixteenPointCoordinate_mem_reedMuller_one j)
  have hproduct : left * right ∈ reedMuller 2 n := by
    rw [mem_reedMuller_iff]
    exact (FABL.functionAlgebraicDegree_mul_le_add left right).trans
      (by omega)
  have hpair : booleanFunctionPairing n (left * right) h = 0 := by
    exact hdual (left * right) hproduct
  rw [booleanFunctionPairing_eq_sum_support_right] at hpair
  have himage := image_normalizedRankSevenSupport_eq_support h d hspan
  rw [← himage, Finset.sum_image
    ((sevenVariableAffinePoint_injective_iff d).2 hd).injOn] at hpair
  simpa only [Pi.mul_apply, Function.comp_apply, left, right, projection,
    rankSevenAffineProjection_sevenVariableAffinePoint d hd] using hpair

/-- The eight normalized points outside the affine basis. -/
noncomputable def normalizedRankSevenRemainder
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n) :
    Finset (FABL.F₂Cube 7) :=
  normalizedRankSevenSupport h d \ systematicWeightSixteenFixedPoints

/-- Their corresponding systematic columns. -/
noncomputable def normalizedRankSevenRemainingColumns
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n) :
    Finset (BitVec 8) :=
  (normalizedRankSevenRemainder h d).image
    systematicWeightSixteenPointColumn

private def normalizedRankSevenFixedPointFamily
    (i : Fin 8) : FABL.F₂Cube 7 :=
  Fin.cases 0 (fun j ↦ Pi.single j (1 : FABL.𝔽₂)) i

private theorem image_normalizedRankSevenFixedPointFamily :
    (Finset.univ : Finset (Fin 8)).image
        normalizedRankSevenFixedPointFamily =
      systematicWeightSixteenFixedPoints := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [normalizedRankSevenFixedPointFamily,
        systematicWeightSixteenFixedPoints]
    · simp [normalizedRankSevenFixedPointFamily,
        systematicWeightSixteenFixedPoints]
  · intro hx
    simp only [systematicWeightSixteenFixedPoints, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    obtain rfl | ⟨j, rfl⟩ := hx
    · exact Finset.mem_image.mpr ⟨0, by simp,
        by simp [normalizedRankSevenFixedPointFamily]⟩
    · exact Finset.mem_image.mpr ⟨j.succ, by simp,
        by simp [normalizedRankSevenFixedPointFamily]⟩

@[simp] private theorem
    systematicWeightSixteenPointCoordinate_fixedPointFamily
    (i k : Fin 8) :
    systematicWeightSixteenPointCoordinate i
        (normalizedRankSevenFixedPointFamily k) =
      if i = k then 1 else 0 := by
  classical
  have hsumSingle (j : Fin 7) :
      (∑ k : Fin 7, (Pi.single j (1 : FABL.𝔽₂)) k) = 1 := by
    rw [Fintype.sum_eq_single j]
    · simp
    · intro k hkj
      exact Pi.single_eq_of_ne hkj _
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp [normalizedRankSevenFixedPointFamily]
    · have hne : (0 : Fin 8) ≠ k.succ :=
        Ne.symm (Fin.succ_ne_zero k)
      simp [normalizedRankSevenFixedPointFamily, hsumSingle, hne]
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp [normalizedRankSevenFixedPointFamily]
    · by_cases hjk : j = k
      · subst k
        simp [normalizedRankSevenFixedPointFamily]
      · rw [systematicWeightSixteenPointCoordinate_succ]
        simp [normalizedRankSevenFixedPointFamily, hjk]

private theorem normalizedRankSevenFixedPointFamily_injective :
    Function.Injective normalizedRankSevenFixedPointFamily := by
  intro i k hik
  by_contra hne
  have heval := congrArg
    (systematicWeightSixteenPointCoordinate i) hik
  simp [hne] at heval

/-- The fixed normalized affine-basis columns contribute the identity Gram
matrix. -/
theorem systematicWeightSixteenFixedPoints_gram
    (i j : Fin 8) :
    (∑ x ∈ systematicWeightSixteenFixedPoints,
      systematicWeightSixteenPointCoordinate i x *
        systematicWeightSixteenPointCoordinate j x) =
      (1 : Matrix (Fin 8) (Fin 8) FABL.𝔽₂) i j := by
  classical
  rw [← image_normalizedRankSevenFixedPointFamily,
    Finset.sum_image normalizedRankSevenFixedPointFamily_injective.injOn]
  simp only [systematicWeightSixteenPointCoordinate_fixedPointFamily]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply, eq_comm]
  · intro k _hk hki
    simp [Ne.symm hki]
  · simp

/-- The remainder contains exactly eight points. -/
theorem card_normalizedRankSevenRemainder
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    (normalizedRankSevenRemainder h d).card = 8 := by
  rw [normalizedRankSevenRemainder,
    Finset.card_sdiff_of_subset hfixed,
    card_normalizedRankSevenSupport h d hd hspan, hweight,
    card_systematicWeightSixteenFixedPoints]

/-- The remainder columns are distinct and hence also number eight. -/
theorem card_normalizedRankSevenRemainingColumns
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    (normalizedRankSevenRemainingColumns h d).card = 8 := by
  rw [normalizedRankSevenRemainingColumns,
    Finset.card_image_of_injective _
      systematicWeightSixteenPointColumn_injective,
    card_normalizedRankSevenRemainder h d hd hspan hweight hfixed]

local instance bitVecEightLinearOrder : LinearOrder (BitVec 8) :=
  LinearOrder.lift' BitVec.toNat
    (fun _ _ h ↦ BitVec.eq_of_toNat_eq h)

/-- The canonical increasing enumeration of the eight remaining columns. -/
noncomputable def normalizedRankSevenRemainingColumnOrderEmbedding
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    Fin 8 ↪o BitVec 8 :=
  (normalizedRankSevenRemainingColumns h d).orderEmbOfFin
    (card_normalizedRankSevenRemainingColumns
      h d hd hspan hweight hfixed)

/-- The canonical remaining-column enumeration is injective. -/
theorem normalizedRankSevenRemainingColumnOrderEmbedding_injective
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    Function.Injective
      (normalizedRankSevenRemainingColumnOrderEmbedding
        h d hd hspan hweight hfixed) :=
  (normalizedRankSevenRemainingColumnOrderEmbedding
    h d hd hspan hweight hfixed).injective

/-- The canonical remaining-column enumeration is strictly increasing. -/
theorem normalizedRankSevenRemainingColumnOrderEmbedding_strictMono
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    StrictMono (normalizedRankSevenRemainingColumnOrderEmbedding
      h d hd hspan hweight hfixed) :=
  (normalizedRankSevenRemainingColumnOrderEmbedding
    h d hd hspan hweight hfixed).strictMono

/-- The canonical enumeration has exactly the remaining columns as its image. -/
theorem image_normalizedRankSevenRemainingColumnOrderEmbedding_univ
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    (Finset.univ : Finset (Fin 8)).image
        (normalizedRankSevenRemainingColumnOrderEmbedding
          h d hd hspan hweight hfixed) =
      normalizedRankSevenRemainingColumns h d := by
  apply Finset.eq_of_subset_of_card_le
  · intro column hcolumn
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hcolumn
    unfold normalizedRankSevenRemainingColumnOrderEmbedding
    exact Finset.orderEmbOfFin_mem
      (normalizedRankSevenRemainingColumns h d)
      (card_normalizedRankSevenRemainingColumns
        h d hd hspan hweight hfixed) i
  · rw [card_normalizedRankSevenRemainingColumns
      h d hd hspan hweight hfixed,
      Finset.card_image_of_injective _
        (normalizedRankSevenRemainingColumnOrderEmbedding_injective
          h d hd hspan hweight hfixed)]
    simp

/-- Every canonically enumerated column belongs to the remaining-column set. -/
theorem normalizedRankSevenRemainingColumnOrderEmbedding_mem
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d)
    (i : Fin 8) :
    normalizedRankSevenRemainingColumnOrderEmbedding
        h d hd hspan hweight hfixed i ∈
      normalizedRankSevenRemainingColumns h d := by
  rw [← image_normalizedRankSevenRemainingColumnOrderEmbedding_univ
    h d hd hspan hweight hfixed]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- The packed constraints follow from nonunit columns, sorted order, and
pairwise orthogonality. -/
theorem systematicWeightSixteenConstraints_pack_of
    (columns : Fin 8 → BitVec 8)
    (hnonunit : ∀ i,
      isSystematicWeightSixteenNonunitOddColumn (columns i) = true)
    (hstrict : StrictMono columns)
    (horthogonal : ∀ i j, i ≠ j →
      areSystematicWeightSixteenColumnsOrthogonal
        (columns i) (columns j) = true) :
    SystematicWeightSixteenConstraints
        (packSystematicWeightSixteenColumns columns) = true := by
  have hcolumn0 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 0 = columns 0 := by
    simpa using systematicWeightSixteenColumn_pack columns (0 : Fin 8)
  have hcolumn1 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 1 = columns 1 := by
    simpa using systematicWeightSixteenColumn_pack columns (1 : Fin 8)
  have hcolumn2 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 2 = columns 2 := by
    simpa using systematicWeightSixteenColumn_pack columns (2 : Fin 8)
  have hcolumn3 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 3 = columns 3 := by
    simpa using systematicWeightSixteenColumn_pack columns (3 : Fin 8)
  have hcolumn4 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 4 = columns 4 := by
    simpa using systematicWeightSixteenColumn_pack columns (4 : Fin 8)
  have hcolumn5 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 5 = columns 5 := by
    simpa using systematicWeightSixteenColumn_pack columns (5 : Fin 8)
  have hcolumn6 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 6 = columns 6 := by
    simpa using systematicWeightSixteenColumn_pack columns (6 : Fin 8)
  have hcolumn7 : systematicWeightSixteenColumn
      (packSystematicWeightSixteenColumns columns) 7 = columns 7 := by
    simpa using systematicWeightSixteenColumn_pack columns (7 : Fin 8)
  unfold SystematicWeightSixteenConstraints
  simp only [hcolumn0, hcolumn1, hcolumn2, hcolumn3, hcolumn4, hcolumn5,
    hcolumn6, hcolumn7]
  simp only [hnonunit]
  simp only [BitVec.ult_eq_decide_lt]
  simp only [hstrict (by decide : (0 : Fin 8) < 1),
    hstrict (by decide : (1 : Fin 8) < 2),
    hstrict (by decide : (2 : Fin 8) < 3),
    hstrict (by decide : (3 : Fin 8) < 4),
    hstrict (by decide : (4 : Fin 8) < 5),
    hstrict (by decide : (5 : Fin 8) < 6),
    hstrict (by decide : (6 : Fin 8) < 7)]
  simp only [
    horthogonal 0 1 (by decide), horthogonal 0 2 (by decide),
    horthogonal 0 3 (by decide), horthogonal 0 4 (by decide),
    horthogonal 0 5 (by decide), horthogonal 0 6 (by decide),
    horthogonal 0 7 (by decide), horthogonal 1 2 (by decide),
    horthogonal 1 3 (by decide), horthogonal 1 4 (by decide),
    horthogonal 1 5 (by decide), horthogonal 1 6 (by decide),
    horthogonal 1 7 (by decide), horthogonal 2 3 (by decide),
    horthogonal 2 4 (by decide), horthogonal 2 5 (by decide),
    horthogonal 2 6 (by decide), horthogonal 2 7 (by decide),
    horthogonal 3 4 (by decide), horthogonal 3 5 (by decide),
    horthogonal 3 6 (by decide), horthogonal 3 7 (by decide),
    horthogonal 4 5 (by decide), horthogonal 4 6 (by decide),
    horthogonal 4 7 (by decide), horthogonal 5 6 (by decide),
    horthogonal 5 7 (by decide), horthogonal 6 7 (by decide)]
  rfl

/-- Removing the fixed identity columns from the full zero Gram leaves the
identity Gram on the eight remaining points. -/
theorem normalizedRankSevenRemainder_pointCoordinate_gram_one
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hdual : h ∈ reedMullerDual 2 n)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d)
    (i j : Fin 8) :
    (∑ x ∈ normalizedRankSevenRemainder h d,
      systematicWeightSixteenPointCoordinate i x *
        systematicWeightSixteenPointCoordinate j x) =
      (1 : Matrix (Fin 8) (Fin 8) FABL.𝔽₂) i j := by
  have hfull := normalizedRankSevenSupport_pointCoordinate_gram_zero
    h d hd hspan hdual i j
  rw [← Finset.union_sdiff_of_subset hfixed] at hfull
  rw [Finset.sum_union Finset.disjoint_sdiff] at hfull
  rw [systematicWeightSixteenFixedPoints_gram] at hfull
  change (∑ x ∈ normalizedRankSevenSupport h d \
    systematicWeightSixteenFixedPoints,
      systematicWeightSixteenPointCoordinate i x *
        systematicWeightSixteenPointCoordinate j x) =
    (1 : Matrix (Fin 8) (Fin 8) FABL.𝔽₂) i j
  exact (ZMod.neg_eq_self_mod_two _).symm.trans
    (add_eq_zero_iff_eq_neg.mp hfull).symm

/-- The binary matrix whose columns are the given eight-bit words. -/
def systematicWeightSixteenColumnMatrix
    (columns : Fin 8 → BitVec 8) :
    Matrix (Fin 8) (Fin 8) FABL.𝔽₂ :=
  fun i k ↦ bitVecEightF₂ (columns k) i

/-- Enumerating the remaining point columns transports their identity row
Gram to the corresponding square binary matrix. -/
theorem normalizedRankSevenColumnEnumeration_rowGram
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (columns : Fin 8 → BitVec 8)
    (hinjective : Function.Injective columns)
    (henumerates : (Finset.univ : Finset (Fin 8)).image columns =
      normalizedRankSevenRemainingColumns h d)
    (hgram : ∀ i j : Fin 8,
      (∑ x ∈ normalizedRankSevenRemainder h d,
        systematicWeightSixteenPointCoordinate i x *
          systematicWeightSixteenPointCoordinate j x) =
        (1 : Matrix (Fin 8) (Fin 8) FABL.𝔽₂) i j) :
    systematicWeightSixteenColumnMatrix columns *
        Matrix.transpose (systematicWeightSixteenColumnMatrix columns) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    systematicWeightSixteenColumnMatrix]
  calc
    (∑ k : Fin 8,
        bitVecEightF₂ (columns k) i * bitVecEightF₂ (columns k) j) =
        Finset.sum (normalizedRankSevenRemainingColumns h d) (fun c ↦
          bitVecEightF₂ c i * bitVecEightF₂ c j) := by
      rw [← henumerates, Finset.sum_image hinjective.injOn]
    _ = Finset.sum (normalizedRankSevenRemainder h d) (fun x ↦
        systematicWeightSixteenPointCoordinate i x *
          systematicWeightSixteenPointCoordinate j x) := by
      rw [normalizedRankSevenRemainingColumns,
        Finset.sum_image
          systematicWeightSixteenPointColumn_injective.injOn]
      rfl
    _ = (1 : Matrix (Fin 8) (Fin 8) FABL.𝔽₂) i j := hgram i j

/-- A square binary matrix with identity row Gram also has identity column
Gram, so distinct enumerated columns have zero binary dot product. -/
theorem normalizedRankSevenColumnEnumeration_dotProduct_zero
    (columns : Fin 8 → BitVec 8)
    (hrow : systematicWeightSixteenColumnMatrix columns *
        Matrix.transpose (systematicWeightSixteenColumnMatrix columns) = 1)
    (i j : Fin 8) (hij : i ≠ j) :
    FABL.f₂DotProduct (bitVecEightF₂ (columns i))
      (bitVecEightF₂ (columns j)) = 0 := by
  have hcolumn := mul_eq_one_symm hrow
  have hijEntry := congrFun (congrFun hcolumn i) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply,
    systematicWeightSixteenColumnMatrix, FABL.f₂DotProduct, dotProduct,
    Matrix.one_apply, hij,
    ↓reduceIte] using hijEntry

/-- Every column arising from a remaining normalized point is odd and avoids
the eight identity columns. -/
theorem normalizedRankSevenRemainingColumn_nonunitOdd
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (column : BitVec 8)
    (hcolumn : column ∈ normalizedRankSevenRemainingColumns h d) :
    isSystematicWeightSixteenNonunitOddColumn column = true := by
  rw [normalizedRankSevenRemainingColumns] at hcolumn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hcolumn
  have hxNotFixed : x ∉ systematicWeightSixteenFixedPoints :=
    (Finset.mem_sdiff.mp hx).2
  unfold isSystematicWeightSixteenNonunitOddColumn
  rw [systematicWeightSixteenPointColumn_odd,
    systematicWeightSixteenPointColumn_nonunit_iff]
  simp [hxNotFixed]

/-- Decoding any injective enumeration of all remaining columns recovers the
remaining normalized point set. -/
theorem normalizedRankSevenColumnEnumeration_decode
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (columns : Fin 8 → BitVec 8)
    (henumerates : (Finset.univ : Finset (Fin 8)).image columns =
      normalizedRankSevenRemainingColumns h d) :
    (Finset.univ : Finset (Fin 8)).image (fun i ↦
        systematicWeightSixteenColumnPoint (columns i)) =
      normalizedRankSevenRemainder h d := by
  calc
    (Finset.univ : Finset (Fin 8)).image (fun i ↦
        systematicWeightSixteenColumnPoint (columns i)) =
        ((Finset.univ : Finset (Fin 8)).image columns).image
          systematicWeightSixteenColumnPoint := by
      rw [Finset.image_image]
      rfl
    _ = (normalizedRankSevenRemainingColumns h d).image
        systematicWeightSixteenColumnPoint := by rw [henumerates]
    _ = normalizedRankSevenRemainder h d := by
      rw [normalizedRankSevenRemainingColumns]
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
        simpa using hy
      · intro hx
        exact Finset.mem_image.mpr ⟨systematicWeightSixteenPointColumn x,
          Finset.mem_image.mpr ⟨x, hx, rfl⟩,
          systematicWeightSixteenColumnPoint_pointColumn x⟩

/-- A normalized full-span support produces a sorted systematic code with the
same reconstructed support. -/
theorem exists_systematicWeightSixteenCode_of_normalizedRankSevenSupport
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (hspan : Submodule.span FABL.𝔽₂ (Set.range d.2) =
      supportDifferenceSpan h d.1)
    (hdual : h ∈ reedMullerDual 2 n)
    (hweight : hammingWeight h = 16)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d) :
    ∃ code : BitVec 64,
      SystematicWeightSixteenConstraints code = true ∧
        systematicWeightSixteenSupportOfCode code =
          normalizedRankSevenSupport h d := by
  classical
  let columns : Fin 8 → BitVec 8 :=
    normalizedRankSevenRemainingColumnOrderEmbedding
      h d hd hspan hweight hfixed
  let code := packSystematicWeightSixteenColumns columns
  have henumerates : (Finset.univ : Finset (Fin 8)).image columns =
      normalizedRankSevenRemainingColumns h d := by
    simpa only [columns] using
      (image_normalizedRankSevenRemainingColumnOrderEmbedding_univ
        h d hd hspan hweight hfixed)
  have hinjective : Function.Injective columns := by
    simpa only [columns] using
      (normalizedRankSevenRemainingColumnOrderEmbedding_injective
        h d hd hspan hweight hfixed)
  have hremainderGram (i j : Fin 8) :=
    normalizedRankSevenRemainder_pointCoordinate_gram_one
      h d hd hspan hdual hfixed i j
  have hrow : systematicWeightSixteenColumnMatrix columns *
      Matrix.transpose (systematicWeightSixteenColumnMatrix columns) = 1 :=
    normalizedRankSevenColumnEnumeration_rowGram h d columns
      hinjective henumerates hremainderGram
  have hdot (i j : Fin 8) (hij : i ≠ j) :
      FABL.f₂DotProduct (bitVecEightF₂ (columns i))
        (bitVecEightF₂ (columns j)) = 0 := by
    exact normalizedRankSevenColumnEnumeration_dotProduct_zero
      columns hrow i j hij
  have hnonunit (i : Fin 8) :
      isSystematicWeightSixteenNonunitOddColumn (columns i) = true := by
    apply normalizedRankSevenRemainingColumn_nonunitOdd h d
    simpa only [columns] using
      (normalizedRankSevenRemainingColumnOrderEmbedding_mem
        h d hd hspan hweight hfixed i)
  have hstrict : StrictMono columns := by
    simpa only [columns] using
      (normalizedRankSevenRemainingColumnOrderEmbedding_strictMono
        h d hd hspan hweight hfixed)
  have horthogonal (i j : Fin 8) (hij : i ≠ j) :
      areSystematicWeightSixteenColumnsOrthogonal
        (columns i) (columns j) = true :=
    (areSystematicWeightSixteenColumnsOrthogonal_iff _ _).mpr
      (hdot i j hij)
  have hconstraints : SystematicWeightSixteenConstraints code = true :=
    systematicWeightSixteenConstraints_pack_of
      columns hnonunit hstrict horthogonal
  have hdecoded :
      (Finset.univ : Finset (Fin 8)).image (fun i ↦
          systematicWeightSixteenColumnPoint (columns i)) =
        normalizedRankSevenRemainder h d :=
    normalizedRankSevenColumnEnumeration_decode h d columns henumerates
  refine ⟨code, hconstraints, ?_⟩
  rw [systematicWeightSixteenSupportOfCode]
  simp only [code, systematicWeightSixteenColumn_pack]
  rw [hdecoded]
  exact Finset.union_sdiff_of_subset hfixed

/-- Every rank-seven weight-sixteen dual word has a systematic normalization
whose decoded support maps exactly onto the original word. -/
theorem exists_systematicWeightSixteenNormalization
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n)
    (hweight : hammingWeight h = 16)
    (hspan : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) = 7) :
    ∃ (d : SevenVariableAffineMapData n) (code : BitVec 64),
      d.1 = p ∧
        LinearIndependent FABL.𝔽₂ d.2 ∧
        SystematicWeightSixteenConstraints code = true ∧
        (systematicWeightSixteenSupportOfCode code).image
          (sevenVariableAffinePoint d) = support h := by
  obtain ⟨v, hv, hvSpan, hvIndependent⟩ :=
    exists_supportDifferenceBasis_of_finrank_eq h p hspan
  let d : SevenVariableAffineMapData n := (p, v)
  have hfixed : systematicWeightSixteenFixedPoints ⊆
      normalizedRankSevenSupport h d := by
    exact systematicWeightSixteenFixedPoints_subset_normalizedRankSevenSupport
      h p v hp hv
  obtain ⟨code, hconstraints, hsupport⟩ :=
    exists_systematicWeightSixteenCode_of_normalizedRankSevenSupport
      h d hvIndependent hvSpan hdual hweight hfixed
  refine ⟨d, code, rfl, hvIndependent, hconstraints, ?_⟩
  rw [hsupport]
  exact image_normalizedRankSevenSupport_eq_support h d hvSpan

end CryptBoolean
