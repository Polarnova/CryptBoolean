/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunity
public import CryptBoolean.Carlet.Chapter03.ReedMuller

/-!
# Carlet Chapter 4 annihilator evaluation system

The low-degree ANF coefficient vector of an annihilator lies in the kernel of evaluation on
the support of the target function. The domain and codomain dimensions give Carlet's counts of
unknowns and equations.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n d : ℕ}

/-- Evaluation on `supp(f)`, with a degree-at-most-`d` Boolean function represented by its
low-degree ANF coefficient vector. -/
noncomputable def annihilatorEvaluationLinearMap (f : BooleanFunction n) (d : ℕ) :
    (↥(FABL.lowDegreeFourierFamily n d) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      (↥(support f) → FABL.𝔽₂) where
  toFun c x := ((reedMullerAnfEquiv d n).symm c).1 x.1
  map_add' c c' := by
    funext x
    exact congrFun (congrArg Subtype.val
      (map_add (reedMullerAnfEquiv d n).symm c c')) x.1
  map_smul' a c := by
    funext x
    exact congrFun (congrArg Subtype.val
      (map_smul (reedMullerAnfEquiv d n).symm a c)) x.1

/-- A low-degree coefficient vector belongs to the evaluation kernel exactly when the
corresponding Boolean function annihilates `f`. -/
theorem mem_ker_annihilatorEvaluationLinearMap_iff
    (f : BooleanFunction n)
    (c : ↥(FABL.lowDegreeFourierFamily n d) → FABL.𝔽₂) :
    c ∈ LinearMap.ker (annihilatorEvaluationLinearMap f d) ↔
      f * ((reedMullerAnfEquiv d n).symm c).1 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hc
    funext x
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hfxone : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
      have hxSupport : x ∈ support f := (mem_support f x).2 hfxone
      have hx := congrFun hc (⟨x, hxSupport⟩ : ↥(support f))
      change ((reedMullerAnfEquiv d n).symm c).1 x = 0 at hx
      simp [hfxone, hx]
  · intro hproduct
    funext x
    have hfx : f x.1 = 1 := (mem_support f x.1).1 x.2
    have hx := congrFun hproduct x.1
    change f x.1 * ((reedMullerAnfEquiv d n).symm c).1 x.1 = 0 at hx
    change ((reedMullerAnfEquiv d n).symm c).1 x.1 = 0
    simpa [hfx] using hx

/-- Carlet's number of low-degree ANF coefficient unknowns. -/
theorem annihilatorEvaluationLinearMap_domain_finrank (n d : ℕ) :
    Module.finrank FABL.𝔽₂
      (↥(FABL.lowDegreeFourierFamily n d) → FABL.𝔽₂) =
        ∑ i ∈ Finset.range (d + 1), Nat.choose n i := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    FABL.card_lowDegreeFourierFamily_eq_sum_choose]

/-- Evaluation on `supp(f)` gives exactly `w_H(f)` scalar equations. -/
theorem annihilatorEvaluationLinearMap_codomain_finrank
    (f : BooleanFunction n) :
    Module.finrank FABL.𝔽₂ (↥(support f) → FABL.𝔽₂) = hammingWeight f := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    hammingWeight_eq_card_support]

end CryptBoolean
