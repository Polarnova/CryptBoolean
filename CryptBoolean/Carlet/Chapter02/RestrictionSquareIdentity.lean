/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AffineSubspaceRestrictions
public import CryptBoolean.Carlet.Chapter02.Derivatives
public import CryptBoolean.Carlet.Chapter02.Subspaces

import Mathlib.LinearAlgebra.Projection

/-!
# Walsh square mass of affine-subspace restrictions

Carlet Proposition 9 and Relation (28), with unnormalized Walsh transforms and
affine-coset restrictions represented on their direction subspace.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance restrictionSquareSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

/-- The unnormalized sign imbalance of the restriction of `f` to `a + E`. -/
noncomputable def affineSubspaceRestrictionImbalance
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : ℝ :=
  ∑ x : E, FABL.affineSubspaceRestriction (realSignView f) E a x

private theorem sum_additiveCorrelation_eq_sum_sq
    {G : Type*} [Fintype G] [AddCommGroup G] (φ : G → ℝ) :
    (∑ e : G, ∑ x : G, φ x * φ (x + e)) = (∑ x : G, φ x) ^ 2 := by
  classical
  calc
    (∑ e : G, ∑ x : G, φ x * φ (x + e)) =
        ∑ x : G, ∑ e : G, φ x * φ (x + e) := by
      rw [Finset.sum_comm]
    _ = ∑ x : G, φ x * ∑ y : G, φ y := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.mul_sum]
      congr 1
      simpa [add_comm] using Equiv.sum_comp (Equiv.addRight x) φ
    _ = (∑ x : G, φ x) * ∑ y : G, φ y := by
      rw [Finset.sum_mul]
    _ = (∑ x : G, φ x) ^ 2 := by ring

/-- Summing ambient autocorrelation over `E` separates into the squared
imbalances of the restrictions on the cosets indexed by a complement `E'`. -/
theorem sum_autocorrelation_submodule_eq_sum_affineSubspaceRestrictionImbalance_sq
    (f : BooleanFunction n)
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcompl : IsCompl E E') :
    (∑ e : E, autocorrelation f e.1) =
      ∑ a : E', (affineSubspaceRestrictionImbalance f E a.1) ^ 2 := by
  classical
  have hcoset (e : E) :
      autocorrelation f e.1 =
        ∑ p : E × E',
          FABL.affineSubspaceRestriction (realSignView f) E p.2.1 p.1 *
            FABL.affineSubspaceRestriction (realSignView f) E p.2.1
              (p.1 + e) := by
    rw [autocorrelation]
    simp_rw [realSignView_booleanDerivative]
    rw [← Equiv.sum_comp (E.prodEquivOfIsCompl E' hcompl).toEquiv]
    apply Finset.sum_congr rfl
    intro p _hp
    simp only [FABL.affineSubspaceRestriction_apply, Submodule.coe_add]
    congr 1
    ac_rfl
  calc
    (∑ e : E, autocorrelation f e.1) =
        ∑ e : E, ∑ p : E × E',
          FABL.affineSubspaceRestriction (realSignView f) E p.2.1 p.1 *
            FABL.affineSubspaceRestriction (realSignView f) E p.2.1
              (p.1 + e) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact hcoset e
    _ = ∑ e : E, ∑ x : E, ∑ a : E',
          FABL.affineSubspaceRestriction (realSignView f) E a.1 x *
            FABL.affineSubspaceRestriction (realSignView f) E a.1 (x + e) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ e : E, ∑ a : E', ∑ x : E,
          FABL.affineSubspaceRestriction (realSignView f) E a.1 x *
            FABL.affineSubspaceRestriction (realSignView f) E a.1 (x + e) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.sum_comm]
    _ = ∑ a : E', ∑ e : E, ∑ x : E,
          FABL.affineSubspaceRestriction (realSignView f) E a.1 x *
            FABL.affineSubspaceRestriction (realSignView f) E a.1 (x + e) := by
      rw [Finset.sum_comm]
    _ = ∑ a : E', (affineSubspaceRestrictionImbalance f E a.1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact sum_additiveCorrelation_eq_sum_sq
        (FABL.affineSubspaceRestriction (realSignView f) E a.1)

/-- Carlet Proposition 9, Relation (28): the Walsh square mass on `E`'s
perpendicular is the perpendicular cardinality times the second moment of the
imbalances of the restrictions to the cosets indexed by a complement `E'`. -/
theorem sum_walshTransform_sq_perpendicular_eq_card_mul_sum_restrictionImbalance_sq
    (f : BooleanFunction n)
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcompl : IsCompl E E') :
    (∑ u : FABL.perpendicularSubspace E,
        (walshTransform f u.1 : ℝ) ^ 2) =
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        ∑ a : E', (affineSubspaceRestrictionImbalance f E a.1) ^ 2 := by
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) (FABL.perpendicularSubspace E) 0 0
  rw [FABL.perpendicularSubspace_perpendicularSubspace] at hpoisson
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  have hspectral :
      (∑ u : FABL.perpendicularSubspace E,
          (walshTransform f u.1 : ℝ) ^ 2) =
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          ∑ e : E, autocorrelation f e.1 := by
    simpa using hpoisson
  rw [hspectral,
    sum_autocorrelation_submodule_eq_sum_affineSubspaceRestrictionImbalance_sq
      f E E' hcompl]

end CryptBoolean
