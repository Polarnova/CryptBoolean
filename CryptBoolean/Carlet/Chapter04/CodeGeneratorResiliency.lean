/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Resiliency
public import FABL.Chapter06.Constructions.KWiseIndependence
public import Mathlib.LinearAlgebra.Matrix.Rank

import FABL.Chapter06.Pseudorandomness.FourierFourthMoment

/-!
# Carlet Chapter 4 code-generator construction

The generator matrix is kept in Carlet's row orientation: its row space is the
binary linear code, while multiplication by the matrix sends an input row
vector through the displayed transpose.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

@[expose] public section

namespace CryptBoolean

variable {n k d : ℕ}

/-- The codeword obtained from the coefficient row vector `u` and the
generator matrix `G`. -/
def binaryGeneratorCodeword
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂)
    (u : FABL.F₂Cube k) : FABL.F₂Cube n :=
  u ᵥ* G

/-- A binary `[n,k,d]` generator matrix: its rows are independent and
the least weight of a nonzero generated codeword is exactly `d`. -/
def IsBinaryCodeGenerator
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ) : Prop :=
  LinearIndependent FABL.𝔽₂ G.row ∧
    (∀ u : FABL.F₂Cube k, u ≠ 0 →
      d ≤ (FABL.f₂Support (binaryGeneratorCodeword G u)).card) ∧
    ∃ u : FABL.F₂Cube k, u ≠ 0 ∧
      (FABL.f₂Support (binaryGeneratorCodeword G u)).card = d

/-- Carlet's function `f(x)=g(xGᵀ)`, using Mathlib's column action for
the displayed multiplication by `Gᵀ`. -/
def binaryGeneratorPullback
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂)
    (g : BooleanFunction k) : BooleanFunction n :=
  fun x ↦ g (G *ᵥ x)

private theorem mulVecLin_surjective_of_rows_linearIndependent
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂)
    (hrows : LinearIndependent FABL.𝔽₂ G.row) :
    Function.Surjective G.mulVecLin := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change G.rank = Module.finrank FABL.𝔽₂ (FABL.F₂Cube k)
  rw [hrows.rank_matrix, Module.finrank_fintype_fun_eq_card]

private theorem mean_comp_surjective_linearMap
    (L : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube k)
    (hL : Function.Surjective L) (q : FABL.F₂Cube k → ℝ) :
    FABL.mean (fun x ↦ q (L x)) = FABL.mean q := by
  letI : Fintype (LinearMap.ker L) := Fintype.ofFinite _
  obtain ⟨R, hR⟩ := L.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hR_apply (y : FABL.F₂Cube k) : L (R y) = y := by
    have h := LinearMap.congr_fun hR y
    simpa using h
  let e : (FABL.F₂Cube k × LinearMap.ker L) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n :=
    { toFun := fun p ↦ R p.1 + p.2.1
      invFun := fun x ↦
        (L x, ⟨x - R (L x), by
          rw [LinearMap.mem_ker]
          simp [hR_apply]⟩)
      left_inv := by
        intro p
        apply Prod.ext
        · simp [hR_apply]
        · apply Subtype.ext
          simp [hR_apply]
      right_inv := by
        intro x
        simp
      map_add' := by
        intro p q
        simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c p
        simp [smul_add] }
  have he (p : FABL.F₂Cube k × LinearMap.ker L) :
      L (e p) = p.1 := by
    simp [e, hR_apply]
  calc
    FABL.mean (fun x ↦ q (L x)) =
        FABL.mean (fun p : FABL.F₂Cube k × LinearMap.ker L ↦
          q (L (e p))) := by
      symm
      apply Finset.expect_equiv e.toEquiv
      · simp
      · simp
    _ = FABL.mean (fun p : FABL.F₂Cube k × LinearMap.ker L ↦ q p.1) := by
      apply Finset.expect_congr rfl
      intro p _
      rw [he]
    _ = FABL.mean q := by
      change
        Finset.expect Finset.univ
            (fun p : FABL.F₂Cube k × LinearMap.ker L ↦ q p.1) =
          Finset.expect Finset.univ q
      rw [show
          (Finset.univ : Finset (FABL.F₂Cube k × LinearMap.ker L)) =
            (Finset.univ : Finset (FABL.F₂Cube k)) ×ˢ
              (Finset.univ : Finset (LinearMap.ker L)) by ext; simp,
        Finset.expect_product]
      simp

/-- Pulling a balanced Boolean function back through a full-row-rank binary
generator matrix preserves balancedness. -/
theorem isBalanced_binaryGeneratorPullback
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂)
    (g : BooleanFunction k)
    (hrows : LinearIndependent FABL.𝔽₂ G.row)
    (hg : IsBalanced g) :
    IsBalanced (binaryGeneratorPullback G g) := by
  have hsurjective : Function.Surjective G.mulVecLin :=
    mulVecLin_surjective_of_rows_linearIndependent G hrows
  have hmean :
      FABL.mean (realSignView (binaryGeneratorPullback G g)) =
        FABL.mean (realSignView g) := by
    change FABL.mean (fun x ↦ realSignView g (G *ᵥ x)) =
      FABL.mean (realSignView g)
    simpa [Matrix.mulVecLin_apply] using
      mean_comp_surjective_linearMap G.mulVecLin hsurjective
        (realSignView g)
  have hgmean : FABL.mean (realSignView g) = 0 := by
    rw [← FABL.vectorFourierCoeff_zero_eq_mean]
    exact walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero g 0 |>.mp
      (isBalanced_iff_walshTransform_zero_eq_zero g |>.mp hg)
  apply isBalanced_iff_walshTransform_zero_eq_zero _ |>.mpr
  apply walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero _ 0 |>.mpr
  rw [FABL.vectorFourierCoeff_zero_eq_mean]
  exact hmean.trans hgmean

private theorem codeDistance_pos
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ)
    (hG : IsBinaryCodeGenerator G d) :
    0 < d := by
  obtain ⟨u, hu, hweight⟩ := hG.2.2
  have hinjective : Function.Injective G.vecMul :=
    Matrix.vecMul_injective_iff.mpr hG.1
  have hcodeword : binaryGeneratorCodeword G u ≠ 0 := by
    intro hzero
    apply hu
    apply hinjective
    simpa [binaryGeneratorCodeword] using hzero
  have hsupport :
      (FABL.f₂Support (binaryGeneratorCodeword G u)).Nonempty :=
    (FABL.f₂Support_nonempty_iff _).mpr hcodeword
  rw [← hweight]
  exact Finset.card_pos.mpr hsupport

private theorem codeDistance_le_length
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ)
    (hG : IsBinaryCodeGenerator G d) :
    d ≤ n := by
  obtain ⟨u, _hu, hweight⟩ := hG.2.2
  rw [← hweight]
  calc
    (FABL.f₂Support (binaryGeneratorCodeword G u)).card ≤
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

private theorem ker_mulVecLin_eq_perpendicular_rowSpan
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) :
    LinearMap.ker G.mulVecLin =
      FABL.perpendicularSubspace (FABL.matrixRowSpan G) := by
  ext u
  simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using
    (FABL.mem_perpendicular_matrixRowSpan_iff_mulVec_eq_zero G u).symm

private theorem lowWeight_ne_perpendicular_ker
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ)
    (hG : IsBinaryCodeGenerator G d)
    (u : FABL.F₂Cube n) (hu : u ≠ 0)
    (hweight : (FABL.f₂Support u).card ≤ d - 1) :
    u ∉ FABL.perpendicularSubspace (LinearMap.ker G.mulVecLin) := by
  intro huperp
  have hurow : u ∈ FABL.matrixRowSpan G := by
    rw [ker_mulVecLin_eq_perpendicular_rowSpan,
      FABL.perpendicularSubspace_perpendicularSubspace] at huperp
    exact huperp
  rcases hurow with ⟨a, ha⟩
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hu
    simpa [hzero] using ha.symm
  have hminimum := hG.2.1 a ha_ne
  change binaryGeneratorCodeword G a = u at ha
  rw [ha] at hminimum
  have hd : 0 < d := codeDistance_pos G d hG
  omega

private theorem lowWeight_vectorFourierCoeff_eq_zero
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ)
    (hG : IsBinaryCodeGenerator G d)
    (g : BooleanFunction k) (u : FABL.F₂Cube n)
    (hu : u ≠ 0)
    (hweight : (FABL.f₂Support u).card ≤ d - 1) :
    FABL.vectorFourierCoeff
        (realSignView (binaryGeneratorPullback G g)) u = 0 := by
  have hnotperp :=
    lowWeight_ne_perpendicular_ker G d hG u hu hweight
  have hnotall :
      ¬ ∀ v : FABL.F₂Cube n, v ∈ LinearMap.ker G.mulVecLin →
        FABL.f₂DotProduct u v = 0 := by
    intro h
    exact hnotperp
      ((FABL.mem_perpendicularSubspace_iff
        (LinearMap.ker G.mulVecLin) u).mpr h)
  push Not at hnotall
  obtain ⟨v, hvker, hvdot⟩ := hnotall
  have hmul : G *ᵥ v = 0 := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvker
  have hinvariant :
      (fun x ↦ realSignView (binaryGeneratorPullback G g) (x + v)) =
        realSignView (binaryGeneratorPullback G g) := by
    funext x
    have hinput : G *ᵥ (x + v) = G *ᵥ x := by
      rw [Matrix.mulVec_add, hmul, add_zero]
    change
      FABL.signValue (FABL.signEncode (g (G *ᵥ (x + v)))) =
        FABL.signValue (FABL.signEncode (g (G *ᵥ x)))
    rw [hinput]
  have hdot_one : FABL.f₂DotProduct u v = 1 :=
    Fin.eq_one_of_ne_zero _ hvdot
  have hcharacter : FABL.vectorWalshCharacter u v = -1 := by
    rw [FABL.vectorWalshCharacter_apply, hdot_one]
    exact FABL.binarySign_one
  have htranslation :=
    FABL.vectorFourierCoeff_translate_add
      (realSignView (binaryGeneratorPullback G g)) v u
  rw [hinvariant, hcharacter] at htranslation
  linarith

/-- Carlet's code-generator construction: if `G` generates a binary
`[n,k,d]` linear code and `g` is balanced, then
`x ↦ g(xGᵀ)` is `(d-1)`-resilient. -/
theorem binaryGeneratorPullback_isResilient
    (G : Matrix (Fin k) (Fin n) FABL.𝔽₂) (d : ℕ)
    (hG : IsBinaryCodeGenerator G d)
    (g : BooleanFunction k) (hg : IsBalanced g) :
    IsResilient (d - 1) (binaryGeneratorPullback G g) := by
  have hd : 0 < d := codeDistance_pos G d hG
  have hdn : d ≤ n := codeDistance_le_length G d hG
  have hn : 0 < n := hd.trans_le hdn
  have horder : d - 1 < n :=
    (Nat.sub_lt hd (by omega)).trans_le hdn
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (d - 1) (binaryGeneratorPullback G g) hn horder]
  intro u hweight
  by_cases hu : u = 0
  · subst u
    exact isBalanced_iff_walshTransform_zero_eq_zero _ |>.mp
      (isBalanced_binaryGeneratorPullback G g hG.1 hg)
  · apply walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero _ u |>.mpr
    exact lowWeight_vectorFourierCoeff_eq_zero G d hG g u hu hweight

end CryptBoolean
