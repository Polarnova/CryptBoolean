/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree
public import CryptBoolean.Carlet.Chapter07.IndirectSumDegree
public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarland
public import FABL.Chapter06.F₂Polynomials.Examples
public import FABL.Chapter06.FoolingF₂Polynomials.DirectionalDerivatives

/-!
# Algebraic degree of general Maiorana--McFarland functions

Carlet Chapter 7: the exact top-degree criterion for the general
Maiorana--McFarland construction and the two cases in which its guaranteed
resiliency order attains Siegenthaler's degree bound.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- The `i`th Boolean coordinate function of a binary vector-valued map. -/
def maioranaMcFarlandCoordinate
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (i : Fin r) :
    BooleanFunction s :=
  fun y ↦ φ y i

/-- The algebraic degree of a binary vector-valued map is the largest degree
of one of its coordinate functions. -/
noncomputable def maioranaMcFarlandMapAlgebraicDegree
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) : ℕ :=
  (Finset.univ : Finset (Fin r)).sup fun i ↦
    FABL.functionAlgebraicDegree (maioranaMcFarlandCoordinate φ i)

/-- Every coordinate degree is bounded by the degree of the vector-valued
map. -/
theorem functionAlgebraicDegree_maioranaMcFarlandCoordinate_le
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (i : Fin r) :
    FABL.functionAlgebraicDegree (maioranaMcFarlandCoordinate φ i) ≤
      maioranaMcFarlandMapAlgebraicDegree φ := by
  exact Finset.le_sup (f := fun j : Fin r ↦
    FABL.functionAlgebraicDegree (maioranaMcFarlandCoordinate φ j))
    (Finset.mem_univ i)

/-- The degree of a vector-valued map is bounded by the dimension of its
domain. -/
theorem maioranaMcFarlandMapAlgebraicDegree_le_dimension
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) :
    maioranaMcFarlandMapAlgebraicDegree φ ≤ s := by
  apply Finset.sup_le
  intro i _hi
  exact FABL.functionAlgebraicDegree_le_dimension
    (maioranaMcFarlandCoordinate φ i)

/-- In a nonempty codomain, a vector-valued map has full degree exactly when
one coordinate function has full degree. -/
theorem maioranaMcFarlandMapAlgebraicDegree_eq_dimension_iff
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (hr : 0 < r) :
    maioranaMcFarlandMapAlgebraicDegree φ = s ↔
      ∃ i : Fin r,
        FABL.functionAlgebraicDegree
          (maioranaMcFarlandCoordinate φ i) = s := by
  constructor
  · intro hdegree
    have hnonempty : (Finset.univ : Finset (Fin r)).Nonempty := by
      exact ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    obtain ⟨i, _hi, hsup⟩ := Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin r)) hnonempty
      (fun j ↦ FABL.functionAlgebraicDegree
        (maioranaMcFarlandCoordinate φ j))
    refine ⟨i, ?_⟩
    rw [← hsup]
    exact hdegree
  · rintro ⟨i, hi⟩
    apply Nat.le_antisymm
    · exact maioranaMcFarlandMapAlgebraicDegree_le_dimension φ
    · calc
        s = FABL.functionAlgebraicDegree
            (maioranaMcFarlandCoordinate φ i) := hi.symm
        _ ≤ maioranaMcFarlandMapAlgebraicDegree φ :=
          functionAlgebraicDegree_maioranaMcFarlandCoordinate_le φ i

private def maioranaMcFarlandLeftCoordinate (i : Fin r) :
    BooleanFunction r :=
  fun x ↦ x i

private theorem functionAlgebraicDegree_maioranaMcFarlandLeftCoordinate
    (i : Fin r) :
    FABL.functionAlgebraicDegree
      (maioranaMcFarlandLeftCoordinate i) = 1 := by
  have hfunction :
      maioranaMcFarlandLeftCoordinate i = FABL.anfMonomial {i} := by
    funext x
    simp [maioranaMcFarlandLeftCoordinate, FABL.anfMonomial]
  rw [hfunction, FABL.functionAlgebraicDegree_anfMonomial]
  simp

private theorem maioranaMcFarlandLeftCoordinate_ne_zero (i : Fin r) :
    maioranaMcFarlandLeftCoordinate i ≠ 0 := by
  intro hzero
  have hdegree := functionAlgebraicDegree_maioranaMcFarlandLeftCoordinate i
  rw [hzero, FABL.functionAlgebraicDegree_zero] at hdegree
  omega

private theorem booleanMaioranaMcFarlandGeneral_eq_sum_blockProducts
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    booleanMaioranaMcFarlandGeneral φ g =
      (∑ i : Fin r,
        booleanBlockProduct
          (maioranaMcFarlandLeftCoordinate i)
          (maioranaMcFarlandCoordinate φ i)) +
        booleanDirectSum (0 : BooleanFunction r) g := by
  funext z
  let blocks := (Fin.appendEquiv r s).symm z
  have hz : Fin.append blocks.1 blocks.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz, booleanMaioranaMcFarlandGeneral_append]
  simp only [Fintype.sum_apply, booleanBlockProduct_append,
    Pi.add_apply]
  simp [maioranaMcFarlandLeftCoordinate, maioranaMcFarlandCoordinate,
    booleanDirectSum, FABL.f₂DotProduct, dotProduct]

private theorem functionAlgebraicDegree_blockProduct_leftCoordinate_le
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (i : Fin r) :
    FABL.functionAlgebraicDegree
        (booleanBlockProduct
          (maioranaMcFarlandLeftCoordinate i)
          (maioranaMcFarlandCoordinate φ i)) ≤
      1 + FABL.functionAlgebraicDegree
        (maioranaMcFarlandCoordinate φ i) := by
  by_cases hcoordinate : maioranaMcFarlandCoordinate φ i = 0
  · have hproduct :
        booleanBlockProduct
          (maioranaMcFarlandLeftCoordinate i)
          (maioranaMcFarlandCoordinate φ i) = 0 := by
      funext z
      simp [booleanBlockProduct, hcoordinate]
    rw [hproduct, FABL.functionAlgebraicDegree_zero]
    omega
  · rw [functionAlgebraicDegree_booleanBlockProduct _ _
      (maioranaMcFarlandLeftCoordinate_ne_zero i) hcoordinate,
      functionAlgebraicDegree_maioranaMcFarlandLeftCoordinate]

private theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le_of_coordinate_le
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (d : ℕ)
    (hcoordinates : ∀ i : Fin r,
      FABL.functionAlgebraicDegree
        (maioranaMcFarlandCoordinate φ i) ≤ d)
    (hg : FABL.functionAlgebraicDegree g ≤ d + 1) :
    FABL.functionAlgebraicDegree
      (booleanMaioranaMcFarlandGeneral φ g) ≤ d + 1 := by
  rw [booleanMaioranaMcFarlandGeneral_eq_sum_blockProducts]
  apply (FABL.functionAlgebraicDegree_add_le_max _ _).trans
  apply max_le
  · apply FABL.functionAlgebraicDegree_finset_sum_le
    intro i _hi
    exact (functionAlgebraicDegree_blockProduct_leftCoordinate_le φ i).trans
      (by
        simpa [Nat.add_comm] using
          Nat.add_le_add_left (hcoordinates i) 1)
  · rw [functionAlgebraicDegree_booleanDirectSum]
    simpa using hg

/-- The general Maiorana--McFarland function on `r+s` variables has
algebraic degree at most `s+1`. -/
theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    FABL.functionAlgebraicDegree
      (booleanMaioranaMcFarlandGeneral φ g) ≤ s + 1 := by
  apply functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le_of_coordinate_le
  · intro i
    exact FABL.functionAlgebraicDegree_le_dimension
      (maioranaMcFarlandCoordinate φ i)
  · exact (FABL.functionAlgebraicDegree_le_dimension g).trans (by omega)

private theorem booleanDerivative_booleanMaioranaMcFarlandGeneral_leftUnit
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (i : Fin r) :
    FABL.booleanDerivative (booleanMaioranaMcFarlandGeneral φ g)
        (Fin.append (Pi.single i 1) 0) =
      booleanDirectSum (0 : BooleanFunction r)
        (maioranaMcFarlandCoordinate φ i) := by
  funext z
  let blocks := (Fin.appendEquiv r s).symm z
  have hz : Fin.append blocks.1 blocks.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz]
  have hadd :
      Fin.append blocks.1 blocks.2 + Fin.append (Pi.single i 1) 0 =
        Fin.append (blocks.1 + Pi.single i 1) blocks.2 := by
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simp
    · simp
  rw [FABL.booleanDerivative, hadd,
    booleanMaioranaMcFarlandGeneral_append,
    booleanMaioranaMcFarlandGeneral_append]
  rw [show booleanDirectSum (0 : BooleanFunction r)
      (maioranaMcFarlandCoordinate φ i)
      (Fin.append blocks.1 blocks.2) =
        maioranaMcFarlandCoordinate φ i blocks.2 by
      simp [booleanDirectSum]]
  simp only [FABL.f₂DotProduct]
  rw [add_dotProduct, single_dotProduct]
  simp only [one_mul, maioranaMcFarlandCoordinate]
  change blocks.1 ⬝ᵥ φ blocks.2 + g blocks.2 +
      (blocks.1 ⬝ᵥ φ blocks.2 + φ blocks.2 i + g blocks.2) =
    φ blocks.2 i
  calc
    blocks.1 ⬝ᵥ φ blocks.2 + g blocks.2 +
          (blocks.1 ⬝ᵥ φ blocks.2 + φ blocks.2 i + g blocks.2) =
        (blocks.1 ⬝ᵥ φ blocks.2 + blocks.1 ⬝ᵥ φ blocks.2) +
          (g blocks.2 + g blocks.2) + φ blocks.2 i := by
      abel
    _ = φ blocks.2 i := by
      rw [ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]

private theorem coordinate_degree_succ_le_maioranaMcFarland_degree
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (i : Fin r)
    (hpositive : 0 < FABL.functionAlgebraicDegree
      (maioranaMcFarlandCoordinate φ i)) :
    FABL.functionAlgebraicDegree
          (maioranaMcFarlandCoordinate φ i) + 1 ≤
      FABL.functionAlgebraicDegree
        (booleanMaioranaMcFarlandGeneral φ g) := by
  have hderivative := FABL.functionAlgebraicDegree_booleanDerivative_le
    (booleanMaioranaMcFarlandGeneral φ g)
    (Fin.append (Pi.single i 1) 0)
  rw [booleanDerivative_booleanMaioranaMcFarlandGeneral_leftUnit,
    functionAlgebraicDegree_booleanDirectSum] at hderivative
  have hcoordinate :
      FABL.functionAlgebraicDegree
          (maioranaMcFarlandCoordinate φ i) ≤
        FABL.functionAlgebraicDegree
            (booleanMaioranaMcFarlandGeneral φ g) - 1 := by
    simpa using hderivative
  omega

/-- The degree upper bound is sharp exactly when one coordinate function of
`φ` has full degree `s`. -/
theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hs : 0 < s) :
    FABL.functionAlgebraicDegree
        (booleanMaioranaMcFarlandGeneral φ g) = s + 1 ↔
      ∃ i : Fin r,
        FABL.functionAlgebraicDegree
          (maioranaMcFarlandCoordinate φ i) = s := by
  constructor
  · intro hdegree
    by_contra hcoordinate
    push Not at hcoordinate
    have hle :
        FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) ≤ s := by
      have hbound :=
        functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le_of_coordinate_le
        φ g (s - 1)
        (fun i ↦ by
          have hdimension := FABL.functionAlgebraicDegree_le_dimension
            (maioranaMcFarlandCoordinate φ i)
          have hne := hcoordinate i
          omega)
        (by
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt hs))] using
            FABL.functionAlgebraicDegree_le_dimension g)
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hs))] using hbound
    omega
  · rintro ⟨i, hi⟩
    apply Nat.le_antisymm
    · exact functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le φ g
    · calc
        s + 1 = FABL.functionAlgebraicDegree
              (maioranaMcFarlandCoordinate φ i) + 1 := by rw [hi]
        _ ≤ FABL.functionAlgebraicDegree
            (booleanMaioranaMcFarlandGeneral φ g) :=
          coordinate_degree_succ_le_maioranaMcFarland_degree φ g i
            (by rw [hi]; exact hs)

/-- The degree upper bound is sharp exactly when the vector-valued map has
full algebraic degree. -/
theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff_mapDegree
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s) :
    FABL.functionAlgebraicDegree
        (booleanMaioranaMcFarlandGeneral φ g) = s + 1 ↔
      maioranaMcFarlandMapAlgebraicDegree φ = s := by
  rw [functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff
      φ g hs,
    maioranaMcFarlandMapAlgebraicDegree_eq_dimension_iff φ hr]

private theorem f₂Cube_eq_one_of_support_card_gt_natPred
    (a : FABL.F₂Cube r) (hr : 0 < r)
    (hweight : r - 1 < (FABL.f₂Support a).card) :
    a = 1 := by
  have hcardLe : (FABL.f₂Support a).card ≤ r := by
    calc
      (FABL.f₂Support a).card ≤
          (Finset.univ : Finset (Fin r)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = r := by simp
  have hcard : (FABL.f₂Support a).card = r := by omega
  have hsupport : FABL.f₂Support a = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  funext i
  have hi : i ∈ FABL.f₂Support a := by simp [hsupport]
  exact Fin.eq_one_of_ne_zero (a i) ((FABL.mem_f₂Support a i).mp hi)

theorem map_eq_one_of_weight_gt_natPred
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (hr : 0 < r)
    (hweight : ∀ y, r - 1 < (FABL.f₂Support (φ y)).card) :
    φ = fun _ ↦ 1 := by
  funext y
  exact f₂Cube_eq_one_of_support_card_gt_natPred (φ y) hr (hweight y)

theorem booleanMaioranaMcFarlandGeneral_constant_one_eq_directSum
    (g : BooleanFunction s) :
    booleanMaioranaMcFarlandGeneral
        (fun _ : FABL.F₂Cube s ↦ (1 : FABL.F₂Cube r)) g =
      booleanDirectSum
        (FABL.coordinateSum (Finset.univ : Finset (Fin r))) g := by
  funext z
  let blocks := (Fin.appendEquiv r s).symm z
  have hz : Fin.append blocks.1 blocks.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz, booleanMaioranaMcFarlandGeneral_append]
  rw [show booleanDirectSum
      (FABL.coordinateSum (Finset.univ : Finset (Fin r))) g
      (Fin.append blocks.1 blocks.2) =
        FABL.coordinateSum Finset.univ blocks.1 + g blocks.2 by
      simp [booleanDirectSum]]
  congr 1
  simp [FABL.f₂DotProduct, dotProduct, FABL.coordinateSum]

/-- For the constant all-one frequency map, the construction is the direct
sum of full parity and `g`, hence has degree `max 1 (deg g)`. -/
theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_constant_one
    (g : BooleanFunction s) (hr : 0 < r) :
    FABL.functionAlgebraicDegree
        (booleanMaioranaMcFarlandGeneral
          (fun _ : FABL.F₂Cube s ↦ (1 : FABL.F₂Cube r)) g) =
      max 1 (FABL.functionAlgebraicDegree g) := by
  rw [booleanMaioranaMcFarlandGeneral_constant_one_eq_directSum,
    functionAlgebraicDegree_booleanDirectSum,
    FABL.functionAlgebraicDegree_coordinateSum_univ hr]

/-- If every image value has weight greater than `k`, sharpness of the
`s+1` degree bound forces `k ≤ r-2`. -/
theorem le_r_sub_two_of_weight_gt_of_maioranaMcFarland_degree_eq
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hdegree : FABL.functionAlgebraicDegree
      (booleanMaioranaMcFarlandGeneral φ g) = s + 1) :
    k ≤ r - 2 := by
  have hk : k < r := by
    exact (hweight 0).trans_le (by
      calc
        (FABL.f₂Support (φ 0)).card ≤
            (Finset.univ : Finset (Fin r)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = r := by simp)
  by_contra hnot
  have hkEq : k = r - 1 := by omega
  have hmap : φ = fun _ ↦ 1 := by
    apply map_eq_one_of_weight_gt_natPred φ hr
    intro y
    simpa [← hkEq] using hweight y
  rw [hmap,
    functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_constant_one
      g hr] at hdegree
  have hg := FABL.functionAlgebraicDegree_le_dimension g
  omega

private theorem max_one_degree_eq_dimension_iff
    (g : BooleanFunction s) (hs : 0 < s) :
    max 1 (FABL.functionAlgebraicDegree g) = s ↔
      s = 1 ∨ FABL.functionAlgebraicDegree g = s := by
  have hg := FABL.functionAlgebraicDegree_le_dimension g
  omega

/-- For the construction's weight-guaranteed resiliency order `k`, equality
in Siegenthaler's degree bound occurs exactly in Carlet's two branches. The
constant-map branch includes the corrected unary endpoint, where the full
parity term already has degree one for every `g`. -/
theorem functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_siegenthalerBound_iff
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card) :
    FABL.functionAlgebraicDegree
        (booleanMaioranaMcFarlandGeneral φ g) = r + s - k - 1 ↔
      (k = r - 2 ∧
        maioranaMcFarlandMapAlgebraicDegree φ = s ∧
        s = r + s - k - 2) ∨
      (k = r - 1 ∧ φ = (fun _ ↦ 1) ∧
        (s = 1 ∨ FABL.functionAlgebraicDegree g = s) ∧
        s = r + s - k - 1) := by
  have hk : k < r := by
    exact (hweight 0).trans_le (by
      calc
        (FABL.f₂Support (φ 0)).card ≤
            (Finset.univ : Finset (Fin r)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = r := by simp)
  constructor
  · intro hdegree
    by_cases hkLow : k + 1 < r
    · have hupper :=
        functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le φ g
      rw [hdegree] at hupper
      have hkEq : k = r - 2 := by omega
      left
      refine ⟨hkEq, ?_, ?_⟩
      · rw [← functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff_mapDegree
          φ g hr hs]
        omega
      · omega
    · have hkEq : k = r - 1 := by omega
      have hmap : φ = fun _ ↦ 1 := by
        apply map_eq_one_of_weight_gt_natPred φ hr
        intro y
        simpa [← hkEq] using hweight y
      right
      refine ⟨hkEq, hmap, ?_, ?_⟩
      · rw [hmap,
          functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_constant_one
            g hr] at hdegree
        apply (max_one_degree_eq_dimension_iff g hs).mp
        omega
      · omega
  · rintro (hfirst | hsecond)
    · rcases hfirst with ⟨hkEq, hmapDegree, hsBound⟩
      have hsharp : FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) = s + 1 :=
        (functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff_mapDegree
          φ g hr hs).mpr hmapDegree
      omega
    · rcases hsecond with ⟨hkEq, hmap, hdegreeG, hsBound⟩
      rw [hmap,
        functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_constant_one
          g hr]
      have hmax := (max_one_degree_eq_dimension_iff g hs).mpr hdegreeG
      omega

/-- Under the weight hypothesis, the same classification describes when the
resulting `k`-resilient function reaches Siegenthaler's degree bound. -/
theorem isResilient_and_functionAlgebraicDegree_eq_siegenthalerBound_iff
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card) :
    IsResilient k (booleanMaioranaMcFarlandGeneral φ g) ∧
        FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) = r + s - k - 1 ↔
      (k = r - 2 ∧
        maioranaMcFarlandMapAlgebraicDegree φ = s ∧
        s = r + s - k - 2) ∨
      (k = r - 1 ∧ φ = (fun _ ↦ 1) ∧
        (s = 1 ∨ FABL.functionAlgebraicDegree g = s) ∧
        s = r + s - k - 1) := by
  rw [and_iff_right
    (isResilient_booleanMaioranaMcFarlandGeneral k φ g hweight)]
  exact
    functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_siegenthalerBound_iff
      k φ g hr hs hweight

end CryptBoolean
