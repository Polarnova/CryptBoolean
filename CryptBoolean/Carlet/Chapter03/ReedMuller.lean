/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine

/-!
# Carlet Chapter 3 Reed--Muller codes

The Reed--Muller family is the subspace of Boolean functions of bounded
algebraic degree.  This module closes the linear-code laws and the minimum
distance theorem for the first-order family.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

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

/-- Every affine function belongs to the first-order Reed--Muller code. -/
theorem affineFunction_mem_reedMuller_one
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    affineFunction b a ∈ reedMuller 1 n :=
  functionAlgebraicDegree_affineFunction_le_one b a

/-- The weight of the constant-one Boolean function is the cube cardinality. -/
theorem hammingWeight_affineFunction_one_zero :
    hammingWeight (affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n)) = 2 ^ n := by
  classical
  rw [hammingWeight, support]
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
    2 ^ (n - 1) ≤ hammingWeight f := by
  obtain ⟨b, a, rfl⟩ :=
    exists_affineFunction_of_functionAlgebraicDegree_le_one f hdegree
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by
      intro hb
      subst b
      apply hf
      funext x
      simp [affineFunction, FABL.f₂DotProduct]
    have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
    subst b
    rw [hammingWeight_affineFunction_one_zero]
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1)
  · rw [hammingWeight_affineFunction_of_ne_zero b a ha]

/-- Distinct first-order Reed--Muller codewords have distance at least
`2^(n-1)`. -/
theorem reedMuller_one_distance_lower_bound
    {f g : BooleanFunction n} (hf : f ∈ reedMuller 1 n)
    (hg : g ∈ reedMuller 1 n) (hfg : f ≠ g) :
    2 ^ (n - 1) ≤ hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add]
  apply two_pow_sub_one_le_hammingWeight_of_degree_le_one (f + g)
  · exact (functionAlgebraicDegree_add_le_max f g).trans (max_le hf hg)
  · intro hadd
    apply hfg
    funext x
    have hx := congrFun hadd x
    change f x + g x = 0 at hx
    exact (add_eq_zero_iff_eq_neg.mp hx).trans (ZMod.neg_eq_self_mod_two (g x))

/-- Distinct Reed--Muller codewords always have positive raw Hamming distance. -/
theorem reedMuller_distance_pos
    {f g : BooleanFunction n} (_hf : f ∈ reedMuller r n)
    (_hg : g ∈ reedMuller r n) (hfg : f ≠ g) :
    0 < hammingDistance f g := by
  rw [hammingDistance, hammingDist_pos]
  exact hfg

end CryptBoolean
