/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.DirectSumDegree
public import CryptBoolean.Carlet.Chapter07.IndirectSum
public import Mathlib.Data.Finset.Sum

/-!
# Algebraic degree of Boolean indirect sums

Carlet Theorem 14: exact algebraic degree of the indirect-sum construction,
including its direct-sum specializations when a difference function is
constant.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- Pointwise product of Boolean functions on two disjoint coordinate
blocks. -/
def booleanBlockProduct (f : BooleanFunction r) (g : BooleanFunction s) :
    BooleanFunction (r + s) :=
  fun z ↦
    let blocks := (Fin.appendEquiv r s).symm z
    f blocks.1 * g blocks.2

@[simp] theorem booleanBlockProduct_append
    (f : BooleanFunction r) (g : BooleanFunction s)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    booleanBlockProduct f g (Fin.append x y) = f x * g y := by
  simp [booleanBlockProduct]

/-- Coordinate subsets in two blocks correspond to coordinate subsets of
the joined cube. -/
private def blockFinsetEquiv (r s : ℕ) :
    Finset (Fin r) × Finset (Fin s) ≃ Finset (Fin (r + s)) :=
  (Finset.sumEquiv :
      Finset (Fin r ⊕ Fin s) ≃o Finset (Fin r) × Finset (Fin s)).toEquiv.symm |>.trans
    finSumFinEquiv.finsetCongr

@[simp] private theorem blockFinsetEquiv_apply
    (S : Finset (Fin r)) (T : Finset (Fin s)) :
    blockFinsetEquiv r s (S, T) =
      (S.disjSum T).map finSumFinEquiv.toEmbedding := by
  simp [blockFinsetEquiv, Equiv.finsetCongr_apply]

@[simp] private theorem card_blockFinsetEquiv
    (S : Finset (Fin r)) (T : Finset (Fin s)) :
    (blockFinsetEquiv r s (S, T)).card = S.card + T.card := by
  simp

private theorem anfMonomial_blockFinsetEquiv_append
    (S : Finset (Fin r)) (T : Finset (Fin s))
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    FABL.anfMonomial (blockFinsetEquiv r s (S, T)) (Fin.append x y) =
      FABL.anfMonomial S x * FABL.anfMonomial T y := by
  classical
  simp [FABL.anfMonomial, Finset.prod_disjSum]

/-- Tensor product of the canonical ANF coefficient families on two
coordinate blocks. -/
private noncomputable def blockANFCoefficients
    (f : BooleanFunction r) (g : BooleanFunction s) :
    FABL.ANFCoefficients (r + s) :=
  fun U ↦
    let blocks := (blockFinsetEquiv r s).symm U
    FABL.anfCoeff f blocks.1 * FABL.anfCoeff g blocks.2

@[simp] private theorem blockANFCoefficients_apply
    (f : BooleanFunction r) (g : BooleanFunction s)
    (S : Finset (Fin r)) (T : Finset (Fin s)) :
    blockANFCoefficients f g (blockFinsetEquiv r s (S, T)) =
      FABL.anfCoeff f S * FABL.anfCoeff g T := by
  change
    FABL.anfCoeff f
          (((blockFinsetEquiv r s).symm
            (blockFinsetEquiv r s (S, T))).1) *
        FABL.anfCoeff g
          (((blockFinsetEquiv r s).symm
            (blockFinsetEquiv r s (S, T))).2) =
      FABL.anfCoeff f S * FABL.anfCoeff g T
  rw [(blockFinsetEquiv r s).symm_apply_apply]

private theorem anfEval_blockANFCoefficients_append
    (f : BooleanFunction r) (g : BooleanFunction s)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    FABL.anfEval (blockANFCoefficients f g) (Fin.append x y) = f x * g y := by
  classical
  rw [FABL.anfEval]
  calc
    ∑ U : Finset (Fin (r + s)),
        blockANFCoefficients f g U *
          FABL.anfMonomial U (Fin.append x y) =
      ∑ ST : Finset (Fin r) × Finset (Fin s),
        blockANFCoefficients f g (blockFinsetEquiv r s ST) *
          FABL.anfMonomial (blockFinsetEquiv r s ST) (Fin.append x y) := by
            exact (blockFinsetEquiv r s).sum_comp _ |>.symm
    _ = ∑ S : Finset (Fin r), ∑ T : Finset (Fin s),
        (FABL.anfCoeff f S * FABL.anfMonomial S x) *
          (FABL.anfCoeff g T * FABL.anfMonomial T y) := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro S _hS
            apply Finset.sum_congr rfl
            intro T _hT
            rw [blockANFCoefficients_apply,
              anfMonomial_blockFinsetEquiv_append]
            ring
    _ = (∑ S : Finset (Fin r),
          FABL.anfCoeff f S * FABL.anfMonomial S x) *
        (∑ T : Finset (Fin s),
          FABL.anfCoeff g T * FABL.anfMonomial T y) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro S _hS
            rw [Finset.mul_sum]
    _ = f x * g y := by
      rw [← FABL.anfEval, ← FABL.anfEval,
        FABL.anfEval_anfCoeff, FABL.anfEval_anfCoeff]

private theorem anfCoeff_booleanBlockProduct
    (f : BooleanFunction r) (g : BooleanFunction s) :
    FABL.anfCoeff (booleanBlockProduct f g) =
      blockANFCoefficients f g := by
  apply FABL.anfEval_injective
  rw [FABL.anfEval_anfCoeff]
  funext z
  let blocks := (Fin.appendEquiv r s).symm z
  have hz : Fin.append blocks.1 blocks.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz, anfEval_blockANFCoefficients_append]
  simp

private theorem exists_top_anfCoeff
    (f : BooleanFunction r) (hf : f ≠ 0) :
    ∃ S : Finset (Fin r),
      FABL.anfCoeff f S ≠ 0 ∧
        S.card = FABL.functionAlgebraicDegree f := by
  classical
  have hsupport : (FABL.anfSupport (FABL.anfCoeff f)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hf
    have hcoeff : FABL.anfCoeff f = 0 := by
      funext S
      by_contra hS
      have hmem : S ∈ FABL.anfSupport (FABL.anfCoeff f) :=
        (FABL.mem_anfSupport _ _).mpr hS
      simp [h] at hmem
    rw [← FABL.anfEval_anfCoeff f, hcoeff]
    funext x
    change FABL.anfEval (fun _ : Finset (Fin r) ↦ 0) x = 0
    exact FABL.anfEval_zero x
  obtain ⟨S, hS, hdegree⟩ := Finset.exists_mem_eq_sup
    (FABL.anfSupport (FABL.anfCoeff f)) hsupport Finset.card
  exact ⟨S, (FABL.mem_anfSupport _ _).mp hS, hdegree.symm⟩

/-- The algebraic degree of a product on disjoint coordinate blocks is the
sum of the factor degrees, provided neither factor is zero. -/
theorem functionAlgebraicDegree_booleanBlockProduct
    (f : BooleanFunction r) (g : BooleanFunction s)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    FABL.functionAlgebraicDegree (booleanBlockProduct f g) =
      FABL.functionAlgebraicDegree f +
        FABL.functionAlgebraicDegree g := by
  classical
  obtain ⟨S, hS, hScard⟩ := exists_top_anfCoeff f hf
  obtain ⟨T, hT, hTcard⟩ := exists_top_anfCoeff g hg
  apply le_antisymm
  · rw [FABL.functionAlgebraicDegree, anfCoeff_booleanBlockProduct,
      FABL.algebraicDegree_le_iff]
    intro U hU
    let blocks := (blockFinsetEquiv r s).symm U
    have hUeq : blockFinsetEquiv r s blocks = U :=
      (blockFinsetEquiv r s).apply_symm_apply U
    have hmul : FABL.anfCoeff f blocks.1 *
        FABL.anfCoeff g blocks.2 ≠ 0 := by
      simpa [blockANFCoefficients, blocks] using hU
    rw [← hUeq, card_blockFinsetEquiv]
    exact Nat.add_le_add
      ((FABL.algebraicDegree_le_iff (FABL.anfCoeff f) _).mp le_rfl _
        (mul_ne_zero_iff.mp hmul).1)
      ((FABL.algebraicDegree_le_iff (FABL.anfCoeff g) _).mp le_rfl _
        (mul_ne_zero_iff.mp hmul).2)
  · rw [← hScard, ← hTcard]
    simp only [FABL.functionAlgebraicDegree]
    rw [anfCoeff_booleanBlockProduct, FABL.algebraicDegree]
    rw [← card_blockFinsetEquiv]
    apply Finset.le_sup
    rw [FABL.mem_anfSupport]
    rw [blockANFCoefficients_apply]
    exact mul_ne_zero hS hT

/-- Fixing the right block is an affine embedding of the left cube. -/
private def fixedRightBlockAffineMap (y : FABL.F₂Cube s) :
    FABL.F₂Cube r →ᵃ[FABL.𝔽₂] FABL.F₂Cube (r + s) where
  toFun x := Fin.append x y
  linear :=
    (cubeSplitLinearEquiv r s).symm.toLinearMap.comp
      (LinearMap.inl FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s))
  map_vadd' p v := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [cubeSplitLinearEquiv]

/-- Fixing the left block is an affine embedding of the right cube. -/
private def fixedLeftBlockAffineMap (x : FABL.F₂Cube r) :
    FABL.F₂Cube s →ᵃ[FABL.𝔽₂] FABL.F₂Cube (r + s) where
  toFun y := Fin.append x y
  linear :=
    (cubeSplitLinearEquiv r s).symm.toLinearMap.comp
      (LinearMap.inr FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s))
  map_vadd' p v := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [cubeSplitLinearEquiv]

private theorem exists_zero_of_ne_one
    (f : BooleanFunction r) (hf : f ≠ 1) :
    ∃ x, f x = 0 := by
  by_contra h
  push Not at h
  apply hf
  funext x
  exact Fin.eq_one_of_ne_zero (f x) (h x)

private theorem indirectSum_eq_directSum_add_blockProduct
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s) :
    indirectSum f₁ f₂ g₁ g₂ =
      booleanDirectSum f₁ g₁ +
        booleanBlockProduct (f₁ + f₂) (g₁ + g₂) := by
  funext z
  let blocks := (Fin.appendEquiv r s).symm z
  have hz : Fin.append blocks.1 blocks.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz]
  simp [booleanDirectSum]

/-- Under the corrected nonconstant-difference hypotheses, the degree of an
indirect sum is the maximum of the two base degrees and the sum of the two
difference degrees. -/
theorem functionAlgebraicDegree_indirectSum
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hfZero : f₁ + f₂ ≠ 0) (hfOne : f₁ + f₂ ≠ 1)
    (hgZero : g₁ + g₂ ≠ 0) (hgOne : g₁ + g₂ ≠ 1) :
    FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) =
      max
        (max (FABL.functionAlgebraicDegree f₁)
          (FABL.functionAlgebraicDegree g₁))
        (FABL.functionAlgebraicDegree (f₁ + f₂) +
          FABL.functionAlgebraicDegree (g₁ + g₂)) := by
  obtain ⟨x₀, hx₀⟩ := exists_zero_of_ne_one (f₁ + f₂) hfOne
  obtain ⟨y₀, hy₀⟩ := exists_zero_of_ne_one (g₁ + g₂) hgOne
  have hdecomp := indirectSum_eq_directSum_add_blockProduct f₁ f₂ g₁ g₂
  have hleftSlice :
      indirectSum f₁ f₂ g₁ g₂ ∘ fixedRightBlockAffineMap y₀ =
        f₁ + fun _ ↦ g₁ y₀ := by
    funext x
    change indirectSum f₁ f₂ g₁ g₂ (Fin.append x y₀) =
      f₁ x + g₁ y₀
    rw [indirectSum_append]
    have hy₀' : g₁ y₀ + g₂ y₀ = 0 := by
      simpa only [Pi.add_apply] using hy₀
    rw [hy₀', mul_zero, add_zero]
  have hrightSlice :
      indirectSum f₁ f₂ g₁ g₂ ∘ fixedLeftBlockAffineMap x₀ =
        g₁ + fun _ ↦ f₁ x₀ := by
    funext y
    change indirectSum f₁ f₂ g₁ g₂ (Fin.append x₀ y) =
      g₁ y + f₁ x₀
    rw [indirectSum_append]
    have hx₀' : f₁ x₀ + f₂ x₀ = 0 := by
      simpa only [Pi.add_apply] using hx₀
    rw [hx₀', zero_mul, add_zero]
    exact add_comm _ _
  have hfLower :
      FABL.functionAlgebraicDegree f₁ ≤
        FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) := by
    have hdegree := functionAlgebraicDegree_comp_affineMap_le_general
      (indirectSum f₁ f₂ g₁ g₂) (fixedRightBlockAffineMap y₀)
    rw [hleftSlice, functionAlgebraicDegree_add_constant_eq] at hdegree
    exact hdegree
  have hgLower :
      FABL.functionAlgebraicDegree g₁ ≤
        FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) := by
    have hdegree := functionAlgebraicDegree_comp_affineMap_le_general
      (indirectSum f₁ f₂ g₁ g₂) (fixedLeftBlockAffineMap x₀)
    rw [hrightSlice, functionAlgebraicDegree_add_constant_eq] at hdegree
    exact hdegree
  have hbaseLower :
      max (FABL.functionAlgebraicDegree f₁)
          (FABL.functionAlgebraicDegree g₁) ≤
        FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) :=
    max_le hfLower hgLower
  have hproductDecomp :
      booleanBlockProduct (f₁ + f₂) (g₁ + g₂) =
        indirectSum f₁ f₂ g₁ g₂ + booleanDirectSum f₁ g₁ := by
    rw [hdecomp]
    funext z
    simp only [Pi.add_apply]
    symm
    calc
      booleanDirectSum f₁ g₁ z +
            booleanBlockProduct (f₁ + f₂) (g₁ + g₂) z +
          booleanDirectSum f₁ g₁ z =
        booleanBlockProduct (f₁ + f₂) (g₁ + g₂) z +
          (booleanDirectSum f₁ g₁ z + booleanDirectSum f₁ g₁ z) := by
            abel
      _ = booleanBlockProduct (f₁ + f₂) (g₁ + g₂) z := by
        rw [ZModModule.add_self, add_zero]
  have hproductLower :
      FABL.functionAlgebraicDegree (f₁ + f₂) +
          FABL.functionAlgebraicDegree (g₁ + g₂) ≤
        FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) := by
    have hdegree := FABL.functionAlgebraicDegree_add_le_max
      (indirectSum f₁ f₂ g₁ g₂) (booleanDirectSum f₁ g₁)
    rw [← hproductDecomp,
      functionAlgebraicDegree_booleanBlockProduct _ _ hfZero hgZero,
      functionAlgebraicDegree_booleanDirectSum,
      Nat.max_eq_left hbaseLower] at hdegree
    exact hdegree
  apply le_antisymm
  · rw [hdecomp]
    refine (FABL.functionAlgebraicDegree_add_le_max _ _).trans ?_
    rw [functionAlgebraicDegree_booleanDirectSum,
      functionAlgebraicDegree_booleanBlockProduct _ _ hfZero hgZero]
  · exact max_le hbaseLower hproductLower

/-- If the left difference vanishes, the indirect sum specializes to the
direct sum of the first functions. -/
theorem functionAlgebraicDegree_indirectSum_of_leftDifference_eq_zero
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hleft : f₁ + f₂ = 0) :
    FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) =
      max (FABL.functionAlgebraicDegree f₁)
        (FABL.functionAlgebraicDegree g₁) := by
  have heq : indirectSum f₁ f₂ g₁ g₂ =
      booleanDirectSum f₁ g₁ := by
    funext z
    let blocks := (Fin.appendEquiv r s).symm z
    have hz : Fin.append blocks.1 blocks.2 = z :=
      (Fin.appendEquiv r s).apply_symm_apply z
    rw [← hz]
    have hleftAt : f₁ blocks.1 + f₂ blocks.1 = 0 := by
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun hleft blocks.1
    simp [booleanDirectSum, hleftAt]
  rw [heq, functionAlgebraicDegree_booleanDirectSum]

/-- If the left difference is one, the indirect sum specializes to the
direct sum of the first left function and second right function. -/
theorem functionAlgebraicDegree_indirectSum_of_leftDifference_eq_one
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hleft : f₁ + f₂ = 1) :
    FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) =
      max (FABL.functionAlgebraicDegree f₁)
        (FABL.functionAlgebraicDegree g₂) := by
  have heq : indirectSum f₁ f₂ g₁ g₂ =
      booleanDirectSum f₁ g₂ := by
    funext z
    let blocks := (Fin.appendEquiv r s).symm z
    have hz : Fin.append blocks.1 blocks.2 = z :=
      (Fin.appendEquiv r s).apply_symm_apply z
    rw [← hz]
    have hleftAt : f₁ blocks.1 + f₂ blocks.1 = 1 := by
      simpa only [Pi.add_apply, Pi.one_apply] using congrFun hleft blocks.1
    simp only [indirectSum_append, hleftAt, one_mul]
    change f₁ blocks.1 + g₁ blocks.2 +
        (g₁ blocks.2 + g₂ blocks.2) =
      booleanDirectSum f₁ g₂ (Fin.append blocks.1 blocks.2)
    rw [show booleanDirectSum f₁ g₂ (Fin.append blocks.1 blocks.2) =
      f₁ blocks.1 + g₂ blocks.2 by simp [booleanDirectSum]]
    calc
      f₁ blocks.1 + g₁ blocks.2 +
            (g₁ blocks.2 + g₂ blocks.2) =
        f₁ blocks.1 +
          (g₁ blocks.2 + g₁ blocks.2) + g₂ blocks.2 := by
            abel
      _ = f₁ blocks.1 + g₂ blocks.2 := by
        rw [ZModModule.add_self, add_zero]
  rw [heq, functionAlgebraicDegree_booleanDirectSum]

/-- If the right difference vanishes, the indirect sum specializes to the
direct sum of the first functions. -/
theorem functionAlgebraicDegree_indirectSum_of_rightDifference_eq_zero
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hright : g₁ + g₂ = 0) :
    FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) =
      max (FABL.functionAlgebraicDegree f₁)
        (FABL.functionAlgebraicDegree g₁) := by
  have heq : indirectSum f₁ f₂ g₁ g₂ =
      booleanDirectSum f₁ g₁ := by
    funext z
    let blocks := (Fin.appendEquiv r s).symm z
    have hz : Fin.append blocks.1 blocks.2 = z :=
      (Fin.appendEquiv r s).apply_symm_apply z
    rw [← hz]
    have hrightAt : g₁ blocks.2 + g₂ blocks.2 = 0 := by
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun hright blocks.2
    simp [booleanDirectSum, hrightAt]
  rw [heq, functionAlgebraicDegree_booleanDirectSum]

/-- If the right difference is one, the indirect sum specializes to the
direct sum of the second left function and first right function. -/
theorem functionAlgebraicDegree_indirectSum_of_rightDifference_eq_one
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hright : g₁ + g₂ = 1) :
    FABL.functionAlgebraicDegree (indirectSum f₁ f₂ g₁ g₂) =
      max (FABL.functionAlgebraicDegree f₂)
        (FABL.functionAlgebraicDegree g₁) := by
  have heq : indirectSum f₁ f₂ g₁ g₂ =
      booleanDirectSum f₂ g₁ := by
    funext z
    let blocks := (Fin.appendEquiv r s).symm z
    have hz : Fin.append blocks.1 blocks.2 = z :=
      (Fin.appendEquiv r s).apply_symm_apply z
    rw [← hz]
    have hrightAt : g₁ blocks.2 + g₂ blocks.2 = 1 := by
      simpa only [Pi.add_apply, Pi.one_apply] using congrFun hright blocks.2
    simp only [indirectSum_append, hrightAt, mul_one]
    change f₁ blocks.1 + g₁ blocks.2 +
        (f₁ blocks.1 + f₂ blocks.1) =
      booleanDirectSum f₂ g₁ (Fin.append blocks.1 blocks.2)
    rw [show booleanDirectSum f₂ g₁ (Fin.append blocks.1 blocks.2) =
      f₂ blocks.1 + g₁ blocks.2 by simp [booleanDirectSum]]
    calc
      f₁ blocks.1 + g₁ blocks.2 +
            (f₁ blocks.1 + f₂ blocks.1) =
        f₂ blocks.1 +
          (f₁ blocks.1 + f₁ blocks.1) + g₁ blocks.2 := by
            abel
      _ = f₂ blocks.1 + g₁ blocks.2 := by
        rw [ZModModule.add_self, add_zero]
  rw [heq, functionAlgebraicDegree_booleanDirectSum]

end CryptBoolean
