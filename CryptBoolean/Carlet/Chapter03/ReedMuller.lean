/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import FABL.Chapter06.F₂Polynomials.ExtremalBounds

/-!
# Carlet Chapter 3 Reed--Muller codes

The Reed--Muller family is the subspace of Boolean functions of bounded
algebraic degree. This module closes its dimension, cardinality, and general
minimum-distance formulas, delegating the minimum-weight inequality to FABL's
canonical F₂-polynomial theorem.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n r s : ℕ}

/-- Carlet's Reed--Muller code `R(r,n)`, represented without a redundant
general coding-theory wrapper. -/
noncomputable def reedMuller (r n : ℕ) : Submodule FABL.𝔽₂ (BooleanFunction n) where
  carrier := {f | functionAlgebraicDegree f ≤ r}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (functionAlgebraicDegree_add_le_max f g).trans (max_le hf hg)
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · subst c
      simp
    · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
      subst c
      simpa using hf

/-- Membership in `R(r,n)` is exactly the algebraic-degree bound. -/
@[simp] theorem mem_reedMuller_iff (f : BooleanFunction n) :
    f ∈ reedMuller r n ↔ functionAlgebraicDegree f ≤ r :=
  Iff.rfl

/-- Reed--Muller codes are nested in their order. -/
theorem reedMuller_mono (hrs : r ≤ s) :
    reedMuller r n ≤ reedMuller s n := by
  intro f hf
  exact hf.trans hrs

private theorem anfCoeff_anfEval (c : ANFCoefficients n) :
    anfCoeff (anfEval c) = c := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]

private noncomputable def extendLowDegreeCoefficients
    (r n : ℕ) (c : ↥(FABL.lowDegreeFourierFamily n r) → FABL.𝔽₂) :
    ANFCoefficients n :=
  fun S ↦ if hS : S ∈ FABL.lowDegreeFourierFamily n r then c ⟨S, hS⟩ else 0

private noncomputable def reedMullerAnfEquiv (r n : ℕ) :
    reedMuller r n ≃ₗ[FABL.𝔽₂] (↥(FABL.lowDegreeFourierFamily n r) → FABL.𝔽₂) where
  toFun f S := anfCoeff f.1 S.1
  invFun c :=
    ⟨anfEval (extendLowDegreeCoefficients r n c), by
      rw [mem_reedMuller_iff, functionAlgebraicDegree, anfCoeff_anfEval,
        algebraicDegree_le_iff]
      intro S hS
      by_contra hSr
      have hSmem : S ∉ FABL.lowDegreeFourierFamily n r := by
        simpa using hSr
      exact hS (by simp [extendLowDegreeCoefficients, hSmem])⟩
  left_inv f := by
    apply Subtype.ext
    change anfEval (extendLowDegreeCoefficients r n fun S ↦ anfCoeff f.1 S.1) = f.1
    calc
      _ = anfEval (anfCoeff f.1) := by
        apply congrArg anfEval
        funext S
        by_cases hS : S.card ≤ r
        · have hSmem : S ∈ FABL.lowDegreeFourierFamily n r := by simpa
          simp [extendLowDegreeCoefficients, hSmem]
        · have hcoeff : anfCoeff f.1 S = 0 := by
            by_contra hne
            have := (algebraicDegree_le_iff (anfCoeff f.1) r).mp f.2 S hne
            exact hS this
          have hSmem : S ∉ FABL.lowDegreeFourierFamily n r := by
            simpa only [FABL.mem_lowDegreeFourierFamily, not_le] using (not_le.mp hS)
          simp [extendLowDegreeCoefficients, hSmem, hcoeff]
      _ = f.1 := anfEval_anfCoeff f.1
  right_inv c := by
    funext S
    change anfCoeff (anfEval (extendLowDegreeCoefficients r n c)) S.1 = c S
    rw [anfCoeff_anfEval]
    simp [extendLowDegreeCoefficients]
  map_add' f g := by
    funext S
    change anfCoeff (f.1 + g.1) S.1 = anfCoeff f.1 S.1 + anfCoeff g.1 S.1
    rw [anfCoeff_add]
  map_smul' c f := by
    by_cases hc : c = 0
    · subst c
      funext S
      simp
    · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
      subst c
      simp

/-- Carlet's dimension formula for the Reed--Muller code `R(r,n)`. -/
theorem reedMuller_finrank :
    Module.finrank FABL.𝔽₂ (reedMuller r n) =
      ∑ j ∈ Finset.range (r + 1), Nat.choose n j := by
  rw [LinearEquiv.finrank_eq (reedMullerAnfEquiv r n),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    FABL.card_lowDegreeFourierFamily_eq_sum_choose]

/-- The number of Reed--Muller codewords is `2` raised to the number of
square-free monomials of degree at most `r`. -/
theorem reedMuller_card :
    Nat.card (reedMuller r n) =
      2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) := by
  rw [Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := reedMuller r n),
    Nat.card_zmod, reedMuller_finrank]

/-- Carlet Theorem 1: a nonzero Boolean function of algebraic degree at most `r`
has Hamming weight at least `2^(n-r)`. -/
theorem two_pow_sub_le_hammingWeight_of_degree_le
    (f : BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ r) (hf : f ≠ 0) :
    2 ^ (n - r) ≤ hammingWeight f :=
  FABL.two_pow_sub_le_hammingNorm_of_functionAlgebraicDegree_le f hf hdegree

/-- Carlet Theorem 1 in coding form: distinct words of `R(r,n)` have raw
Hamming distance at least `2^(n-r)`. -/
theorem reedMuller_distance_lower_bound
    {f g : BooleanFunction n} (hf : f ∈ reedMuller r n)
    (hg : g ∈ reedMuller r n) (hfg : f ≠ g) :
    2 ^ (n - r) ≤ hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add]
  apply two_pow_sub_le_hammingWeight_of_degree_le (f + g)
  · exact (functionAlgebraicDegree_add_le_max f g).trans (max_le hf hg)
  · intro hadd
    apply hfg
    funext x
    have hx := congrFun hadd x
    change f x + g x = 0 at hx
    exact (add_eq_zero_iff_eq_neg.mp hx).trans (ZMod.neg_eq_self_mod_two (g x))

/-- Every affine function belongs to the first-order Reed--Muller code. -/
theorem affineFunction_mem_reedMuller_one
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    affineFunction b a ∈ reedMuller 1 n :=
  functionAlgebraicDegree_affineFunction_le_one b a

/-- The weight of the constant-one Boolean function is the cube cardinality. -/
theorem hammingWeight_affineFunction_one_zero :
    hammingWeight (affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n)) = 2 ^ n := by
  classical
  rw [hammingWeight_eq_card_support]
  change
    (Finset.univ.filter fun x : FABL.F₂Cube n ↦
      affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n) x = 1).card = 2 ^ n
  have hfilter :
      (Finset.univ.filter fun x : FABL.F₂Cube n ↦
        affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n) x = 1) = Finset.univ := by
    ext x
    simp [affineFunction, FABL.f₂DotProduct]
  rw [hfilter, Finset.card_univ, card_f₂Cube]

/-- A nonzero Boolean function of degree at most one has weight at least
`2^(n-1)`.  This is Carlet Theorem 1 for first-order Reed--Muller codes. -/
theorem two_pow_sub_one_le_hammingWeight_of_degree_le_one
    (f : BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ 1)
    (hf : f ≠ 0) :
    2 ^ (n - 1) ≤ hammingWeight f :=
  two_pow_sub_le_hammingWeight_of_degree_le f hdegree hf

/-- Distinct first-order Reed--Muller codewords have distance at least
`2^(n-1)`. -/
theorem reedMuller_one_distance_lower_bound
    {f g : BooleanFunction n} (hf : f ∈ reedMuller 1 n)
    (hg : g ∈ reedMuller 1 n) (hfg : f ≠ g) :
    2 ^ (n - 1) ≤ hammingDistance f g :=
  reedMuller_distance_lower_bound hf hg hfg

/-- Distinct Reed--Muller codewords always have positive raw Hamming distance. -/
theorem reedMuller_distance_pos
    {f g : BooleanFunction n} (_hf : f ∈ reedMuller r n)
    (_hg : g ∈ reedMuller r n) (hfg : f ≠ g) :
    0 < hammingDistance f g := by
  rw [hammingDistance, hammingDist_pos]
  exact hfg

end CryptBoolean
