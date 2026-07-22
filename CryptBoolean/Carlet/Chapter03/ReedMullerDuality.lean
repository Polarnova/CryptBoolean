/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMuller

/-!
# Carlet Chapter 3 Reed--Muller duality

The binary function-space pairing identifies the orthogonal complement of
`R(r,n)` with `R(n-r-1,n)` when `r < n`.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n r : ℕ}

/-- The standard binary pairing on scalar Boolean functions. -/
def booleanFunctionPairing (n : ℕ) :
    LinearMap.BilinForm FABL.𝔽₂ (BooleanFunction n) :=
  (dotProductEquiv FABL.𝔽₂ (FABL.F₂Cube n)).toLinearMap

@[simp] theorem booleanFunctionPairing_apply (f g : BooleanFunction n) :
    booleanFunctionPairing n f g = ∑ x, f x * g x :=
  rfl

/-- The standard binary pairing on Boolean functions is nondegenerate. -/
theorem booleanFunctionPairing_nondegenerate :
    (booleanFunctionPairing n).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro f hf
  apply (dotProductEquiv FABL.𝔽₂ (FABL.F₂Cube n)).injective
  apply LinearMap.ext
  intro g
  change dotProduct f g = dotProduct 0 g
  have hfg : dotProduct f g = 0 := by
    simpa [dotProduct] using hf g
  simpa [dotProduct] using hfg

/-- The orthogonal complement of `R(r,n)` under Carlet's binary pairing. -/
noncomputable def reedMullerDual (r n : ℕ) :
    Submodule FABL.𝔽₂ (BooleanFunction n) :=
  (booleanFunctionPairing n).orthogonal (reedMuller r n)

private theorem sum_booleanFunction_eq_anfCoeff_univ (f : BooleanFunction n) :
    (∑ x, f x) = anfCoeff f Finset.univ := by
  classical
  rw [anfCoeff, Finset.powerset_univ]
  change (∑ x : FABL.F₂Cube n, f x) =
    ∑ S : Finset (Fin n), f (FABL.f₂CubeOfFinset S)
  apply Fintype.sum_equiv (FABL.f₂CubeEquivFinset n)
  intro x
  have hx : FABL.f₂CubeOfFinset (FABL.f₂Support x) = x := by
    simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
  change f x = f (FABL.f₂CubeOfFinset (FABL.f₂Support x))
  rw [hx]

private theorem sum_booleanFunction_eq_zero_of_degree_lt
    (f : BooleanFunction n) (hf : functionAlgebraicDegree f < n) :
    ∑ x, f x = 0 := by
  rw [sum_booleanFunction_eq_anfCoeff_univ]
  by_contra hcoeff
  have hdegree : (Finset.univ : Finset (Fin n)).card ≤
      functionAlgebraicDegree f :=
    (algebraicDegree_le_iff (anfCoeff f) (functionAlgebraicDegree f)).mp
      le_rfl Finset.univ hcoeff
  exact (Nat.not_le_of_lt hf) (by simpa using hdegree)

/-- Functions of complementary Reed--Muller orders are orthogonal. -/
theorem reedMuller_complement_le_dual (h : r < n) :
    reedMuller (n - r - 1) n ≤ reedMullerDual r n := by
  intro g hg
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff]
  intro f hf
  change booleanFunctionPairing n f g = 0
  rw [booleanFunctionPairing_apply]
  rw [mem_reedMuller_iff] at hf hg
  have hsum : functionAlgebraicDegree f + functionAlgebraicDegree g < n := by
    omega
  have hdegree : functionAlgebraicDegree (f * g) < n :=
    (functionAlgebraicDegree_mul_le_add f g).trans_lt hsum
  simpa only [Pi.mul_apply] using
    (sum_booleanFunction_eq_zero_of_degree_lt (f * g) hdegree)

private noncomputable def lowDegreeComplementEquiv (h : r < n) :
    ↥(FABL.lowDegreeFourierFamily n (n - r - 1)) ≃
      {S : Finset (Fin n) // S ∉ FABL.lowDegreeFourierFamily n r} where
  toFun S := ⟨S.1ᶜ, by
    rw [FABL.mem_lowDegreeFourierFamily, not_le]
    have hS := (FABL.mem_lowDegreeFourierFamily S.1 (n - r - 1)).mp S.2
    rw [Finset.card_compl, Fintype.card_fin]
    omega⟩
  invFun S := ⟨S.1ᶜ, by
    rw [FABL.mem_lowDegreeFourierFamily]
    have hS : r < S.1.card := by
      simpa only [FABL.mem_lowDegreeFourierFamily, not_le] using S.2
    rw [Finset.card_compl, Fintype.card_fin]
    omega⟩
  left_inv S := by
    apply Subtype.ext
    simp
  right_inv S := by
    apply Subtype.ext
    simp

private theorem lowDegreeComplement_card (h : r < n) :
    (FABL.lowDegreeFourierFamily n (n - r - 1)).card =
      2 ^ n - (FABL.lowDegreeFourierFamily n r).card := by
  classical
  calc
    (FABL.lowDegreeFourierFamily n (n - r - 1)).card =
        Fintype.card ↥(FABL.lowDegreeFourierFamily n (n - r - 1)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        {S : Finset (Fin n) // S ∉ FABL.lowDegreeFourierFamily n r} :=
      Fintype.card_congr (lowDegreeComplementEquiv h)
    _ = Fintype.card (Finset (Fin n)) -
        Fintype.card
          {S : Finset (Fin n) // S ∈ FABL.lowDegreeFourierFamily n r} := by
      simpa using Fintype.card_subtype_compl
        (fun S : Finset (Fin n) ↦ S ∈ FABL.lowDegreeFourierFamily n r)
    _ = 2 ^ n - (FABL.lowDegreeFourierFamily n r).card := by
      rw [Fintype.card_finset, Fintype.card_fin]
      congr 1
      exact Fintype.card_coe _

private theorem sum_choose_complement (h : r < n) :
    (∑ j ∈ Finset.range (n - r - 1 + 1), Nat.choose n j) =
      2 ^ n - ∑ j ∈ Finset.range (r + 1), Nat.choose n j := by
  rw [← FABL.card_lowDegreeFourierFamily_eq_sum_choose,
    ← FABL.card_lowDegreeFourierFamily_eq_sum_choose]
  exact lowDegreeComplement_card h

/-- Carlet, Chapter 3, Theorem 2: `R(r,n)ᗮ = R(n-r-1,n)` for `r < n`. -/
theorem reedMullerDual_eq (h : r < n) :
    reedMullerDual r n = reedMuller (n - r - 1) n := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (reedMuller_complement_le_dual h)
  rw [reedMuller_finrank, reedMullerDual,
    LinearMap.BilinForm.finrank_orthogonal booleanFunctionPairing_nondegenerate,
    Module.finrank_fintype_fun_eq_card, card_f₂Cube, reedMuller_finrank,
    sum_choose_complement h]

end CryptBoolean
