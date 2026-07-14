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

/-- Carlet's Poisson summation formula in FABL's normalized expectation form. -/
theorem poissonSummationFormula
    (f : FABL.F₂Cube n → ℝ) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (z : FABL.F₂Cube n) :
    (𝔼 h : E, f (h.1 + z)) =
      ∑ u : FABL.perpendicularSubspace E,
        FABL.vectorWalshCharacter u.1 z * FABL.vectorFourierCoeff f u.1 :=
  FABL.poissonSummationFormula f E z

end CryptBoolean
