/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter06.DirectSum

/-!
# Algebraic degree of Boolean direct sums

Carlet Section 7.5.2: exact algebraic degree for sums on disjoint coordinate
blocks.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- Adding a binary constant does not change the algebraic degree of a
Boolean function. -/
theorem functionAlgebraicDegree_add_constant_eq
    (f : BooleanFunction r) (c : FABL.𝔽₂) :
    FABL.functionAlgebraicDegree (f + fun _ ↦ c) =
      FABL.functionAlgebraicDegree f := by
  by_cases hc : c = 0
  · subst c
    have hzero : (fun _ : FABL.F₂Cube r ↦ (0 : FABL.𝔽₂)) = 0 := rfl
    rw [hzero, add_zero]
  · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
    subst c
    change FABL.functionAlgebraicDegree (f + 1) =
      FABL.functionAlgebraicDegree f
    apply le_antisymm
    · simpa using
        (FABL.functionAlgebraicDegree_add_le_max
          f (1 : BooleanFunction r))
    · have hdegree := FABL.functionAlgebraicDegree_add_le_max
        (f + 1) (1 : BooleanFunction r)
      have hcancel : (f + 1) + 1 = f := by
        funext x
        change f x + 1 + 1 = f x
        rw [add_assoc, ZModModule.add_self, add_zero]
      rw [hcancel] at hdegree
      simpa using hdegree

/-- A Boolean function has algebraic degree zero exactly when it is
constant. -/
theorem functionAlgebraicDegree_eq_zero_iff_exists_constant
    (f : BooleanFunction r) :
    FABL.functionAlgebraicDegree f = 0 ↔
      ∃ c : FABL.𝔽₂, f = fun _ ↦ c := by
  constructor
  · intro hdegree
    refine ⟨FABL.anfCoeff f ∅, ?_⟩
    funext x
    rw [← congrFun (FABL.anfEval_anfCoeff f) x]
    rw [FABL.anfEval]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro S _hS hSne
      have hcard (hne : FABL.anfCoeff f S ≠ 0) :
          S.card ≤ FABL.functionAlgebraicDegree f := by
        simpa [FABL.functionAlgebraicDegree] using
          ((FABL.algebraicDegree_le_iff (FABL.anfCoeff f) _).mp
            le_rfl S hne)
      have hcoeff : FABL.anfCoeff f S = 0 := by
        by_contra hne
        have := hcard hne
        rw [hdegree] at this
        exact hSne (Finset.card_eq_zero.mp (Nat.le_zero.mp this))
      simp [hcoeff]
    · simp
  · rintro ⟨c, rfl⟩
    have hconstant :
        (fun _ : FABL.F₂Cube r ↦ c) =
          (0 : BooleanFunction r) + fun _ ↦ c := by
      funext x
      simp
    rw [hconstant, functionAlgebraicDegree_add_constant_eq,
      FABL.functionAlgebraicDegree_zero]

/-- Adding a strictly lower-degree Boolean function cannot change the
larger algebraic degree. -/
theorem functionAlgebraicDegree_add_eq_right_of_lt
    (f g : BooleanFunction r)
    (hdegree :
      FABL.functionAlgebraicDegree f <
        FABL.functionAlgebraicDegree g) :
    FABL.functionAlgebraicDegree (f + g) =
      FABL.functionAlgebraicDegree g := by
  apply le_antisymm
  · simpa [Nat.max_eq_right hdegree.le] using
      FABL.functionAlgebraicDegree_add_le_max f g
  · have hreverse :=
      FABL.functionAlgebraicDegree_add_le_max (f + g) f
    have hcancel : (f + g) + f = g := by
      funext x
      change f x + g x + f x = g x
      calc
        f x + g x + f x = g x + (f x + f x) := by abel
        _ = g x := by rw [ZModModule.add_self, add_zero]
    rw [hcancel] at hreverse
    by_cases hresult :
        FABL.functionAlgebraicDegree g ≤
          FABL.functionAlgebraicDegree (f + g)
    · exact hresult
    · have hresultLt :
          FABL.functionAlgebraicDegree (f + g) <
            FABL.functionAlgebraicDegree g := Nat.lt_of_not_ge hresult
      omega

/-- Projection from a joined binary cube to its left coordinate block. -/
private def directSumLeftProjection (r s : ℕ) :
    FABL.F₂Cube (r + s) →ₗ[FABL.𝔽₂] FABL.F₂Cube r :=
  (LinearMap.fst FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s)).comp
    (cubeSplitLinearEquiv r s).toLinearMap

/-- Projection from a joined binary cube to its right coordinate block. -/
private def directSumRightProjection (r s : ℕ) :
    FABL.F₂Cube (r + s) →ₗ[FABL.𝔽₂] FABL.F₂Cube s :=
  (LinearMap.snd FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s)).comp
    (cubeSplitLinearEquiv r s).toLinearMap

/-- Embedding of the left coordinate block with a zero right block. -/
private def directSumLeftEmbedding (r s : ℕ) :
    FABL.F₂Cube r →ₗ[FABL.𝔽₂] FABL.F₂Cube (r + s) :=
  (cubeSplitLinearEquiv r s).symm.toLinearMap.comp
    (LinearMap.inl FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s))

/-- Embedding of the right coordinate block with a zero left block. -/
private def directSumRightEmbedding (r s : ℕ) :
    FABL.F₂Cube s →ₗ[FABL.𝔽₂] FABL.F₂Cube (r + s) :=
  (cubeSplitLinearEquiv r s).symm.toLinearMap.comp
    (LinearMap.inr FABL.𝔽₂ (FABL.F₂Cube r) (FABL.F₂Cube s))

/-- A Boolean direct sum has algebraic degree equal to the larger degree of
its two summands. -/
theorem functionAlgebraicDegree_booleanDirectSum
    (f : BooleanFunction r) (g : BooleanFunction s) :
    FABL.functionAlgebraicDegree (booleanDirectSum f g) =
      max (FABL.functionAlgebraicDegree f)
        (FABL.functionAlgebraicDegree g) := by
  have hdecomp :
      booleanDirectSum f g =
        (f ∘ (directSumLeftProjection r s).toAffineMap) +
          (g ∘ (directSumRightProjection r s).toAffineMap) := by
    rfl
  have hleftRestriction :
      booleanDirectSum f g ∘
          (directSumLeftEmbedding r s).toAffineMap =
        f + fun _ ↦ g 0 := by
    funext x
    simp [booleanDirectSum, directSumLeftEmbedding,
      cubeSplitLinearEquiv]
  have hrightRestriction :
      booleanDirectSum f g ∘
          (directSumRightEmbedding r s).toAffineMap =
        g + fun _ ↦ f 0 := by
    funext y
    simp [booleanDirectSum, directSumRightEmbedding,
      cubeSplitLinearEquiv, add_comm]
  apply le_antisymm
  · rw [hdecomp]
    exact (FABL.functionAlgebraicDegree_add_le_max _ _).trans
      (max_le_max
        (functionAlgebraicDegree_comp_affineMap_le_general
          f (directSumLeftProjection r s).toAffineMap)
        (functionAlgebraicDegree_comp_affineMap_le_general
          g (directSumRightProjection r s).toAffineMap))
  · rw [Nat.max_le]
    constructor
    · have hleft := functionAlgebraicDegree_comp_affineMap_le_general
          (booleanDirectSum f g)
          (directSumLeftEmbedding r s).toAffineMap
      rw [hleftRestriction,
        functionAlgebraicDegree_add_constant_eq] at hleft
      exact hleft
    · have hright := functionAlgebraicDegree_comp_affineMap_le_general
          (booleanDirectSum f g)
          (directSumRightEmbedding r s).toAffineMap
      rw [hrightRestriction,
        functionAlgebraicDegree_add_constant_eq] at hright
      exact hright

end CryptBoolean
