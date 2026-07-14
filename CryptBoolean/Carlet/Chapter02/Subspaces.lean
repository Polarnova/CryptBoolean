/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierOperations

/-!
# Carlet Chapter 2 subspace Fourier formulas

Carlet's unnormalized indicator formula is obtained from FABL's normalized
subspace Fourier API through the explicit raw-transform scaling law.  The
Poisson formula remains delegated to FABL.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance submoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

noncomputable local instance submoduleMembershipDecidable
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : DecidablePred (fun x ↦ x ∈ E) :=
  Classical.decPred _

/-- The raw scaling factor for a subspace is its cardinality. -/
theorem two_pow_mul_inversePerpendicularCard_eq_card
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    (2 ^ n : ℝ) * FABL.inversePerpendicularCard E = Nat.card E := by
  have hrank : Module.finrank FABL.𝔽₂ E ≤ n := by
    simpa using E.finrank_le
  rw [FABL.inversePerpendicularCard, FABL.f₂Codimension,
    FABL.finrank_perpendicularSubspace, FABL.card_submodule_eq_two_pow_finrank]
  push_cast
  have hn : n - Module.finrank FABL.𝔽₂ E +
      Module.finrank FABL.𝔽₂ E = n := Nat.sub_add_cancel hrank
  calc
    (2 : ℝ) ^ n * ((2 : ℝ) ^ (n - Module.finrank FABL.𝔽₂ E))⁻¹ =
        ((2 : ℝ) ^ (n - Module.finrank FABL.𝔽₂ E) *
          (2 : ℝ) ^ Module.finrank FABL.𝔽₂ E) *
          ((2 : ℝ) ^ (n - Module.finrank FABL.𝔽₂ E))⁻¹ := by
      rw [← pow_add, hn]
    _ = (2 : ℝ) ^ Module.finrank FABL.𝔽₂ E := by
      field_simp

/-- Carlet Proposition 7: the raw transform of a subspace indicator is its
cardinality on the perpendicular subspace and zero off it. -/
theorem rawFourierTransform_setIndicator_submodule
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (u : FABL.F₂Cube n) :
    rawFourierTransform (FABL.setIndicator (E : Set (FABL.F₂Cube n))) u =
      if u ∈ FABL.perpendicularSubspace E then (Nat.card E : ℝ) else 0 := by
  classical
  rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  by_cases hu : u ∈ FABL.perpendicularSubspace E
  · rw [if_pos hu, FABL.vectorFourierCoeff_setIndicator_submodule_of_mem E u hu,
      two_pow_mul_inversePerpendicularCard_eq_card]
  · rw [if_neg hu, FABL.vectorFourierCoeff_setIndicator_submodule_of_not_mem E u hu,
      mul_zero]

/-- Carlet Corollary 1, Relation (17): the full raw Poisson summation formula
on affine cosets, with both modulation parameters explicit. -/
theorem rawPoissonSummationFormula
    (φ : FABL.F₂Cube n → ℝ) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a b : FABL.F₂Cube n) :
    (∑ u : E,
        FABL.vectorWalshCharacter b (a + u.1) *
          rawFourierTransform φ (a + u.1)) =
      (Nat.card E : ℝ) * FABL.vectorWalshCharacter b a *
        ∑ x : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter a (b + x.1) * φ (b + x.1) := by
  classical
  have hcomm (x y : FABL.F₂Cube n) :
      FABL.vectorWalshCharacter x y = FABL.vectorWalshCharacter y x := by
    rw [FABL.vectorWalshCharacter_apply, FABL.vectorWalshCharacter_apply]
    congr 1
    exact dotProduct_comm x y
  have hpoisson :
      (𝔼 x : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter a (x.1 + b) * φ (x.1 + b)) =
        ∑ u : E,
          FABL.vectorWalshCharacter u.1 b *
            FABL.vectorFourierCoeff φ (a + u.1) := by
    have h := FABL.poissonSummationFormula
      (fun x ↦ FABL.vectorWalshCharacter a x * φ x)
      (FABL.perpendicularSubspace E) b
    rw [FABL.perpendicularSubspace_perpendicularSubspace] at h
    simpa only [vectorFourierCoeff_mul_vectorWalshCharacter] using h
  have hcardPerp :
      ((Fintype.card (FABL.perpendicularSubspace E) : ℕ) : ℝ) =
        (2 : ℝ) ^ FABL.f₂Codimension E := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast FABL.card_perpendicularSubspace E
  have hinverseCard :
      (((Fintype.card (FABL.perpendicularSubspace E) : ℕ) : ℝ))⁻¹ =
        FABL.inversePerpendicularCard E := by
    rw [hcardPerp, FABL.inversePerpendicularCard]
  have hscale :
      (2 ^ n : ℝ) /
          ((Fintype.card (FABL.perpendicularSubspace E) : ℕ) : ℝ) =
        Nat.card E := by
    rw [div_eq_mul_inv, hinverseCard]
    exact two_pow_mul_inversePerpendicularCard_eq_card E
  simp_rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  calc
    (∑ u : E,
        FABL.vectorWalshCharacter b (a + u.1) *
          ((2 ^ n : ℝ) * FABL.vectorFourierCoeff φ (a + u.1))) =
        (2 ^ n : ℝ) * FABL.vectorWalshCharacter b a *
          ∑ u : E,
            FABL.vectorWalshCharacter u.1 b *
              FABL.vectorFourierCoeff φ (a + u.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [AddChar.map_add_eq_mul, hcomm b u.1]
      ring
    _ = (2 ^ n : ℝ) * FABL.vectorWalshCharacter b a *
          (𝔼 x : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter a (x.1 + b) * φ (x.1 + b)) := by
      rw [hpoisson]
    _ = (Nat.card E : ℝ) * FABL.vectorWalshCharacter b a *
          ∑ x : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter a (b + x.1) * φ (b + x.1) := by
      rw [Fintype.expect_eq_sum_div_card]
      rw [show (∑ x : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter a (x.1 + b) * φ (x.1 + b)) =
          ∑ x : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter a (b + x.1) * φ (b + x.1) by
        apply Finset.sum_congr rfl
        intro x _
        rw [add_comm]]
      rw [div_eq_mul_inv]
      calc
        (2 ^ n : ℝ) * FABL.vectorWalshCharacter b a *
            ((∑ x : FABL.perpendicularSubspace E,
                FABL.vectorWalshCharacter a (b + x.1) * φ (b + x.1)) *
              (((Fintype.card (FABL.perpendicularSubspace E) : ℕ) : ℝ))⁻¹) =
            ((2 ^ n : ℝ) /
                ((Fintype.card (FABL.perpendicularSubspace E) : ℕ) : ℝ)) *
              FABL.vectorWalshCharacter b a *
                ∑ x : FABL.perpendicularSubspace E,
                  FABL.vectorWalshCharacter a (b + x.1) * φ (b + x.1) := by
          ring
        _ = _ := by rw [hscale]

end CryptBoolean
