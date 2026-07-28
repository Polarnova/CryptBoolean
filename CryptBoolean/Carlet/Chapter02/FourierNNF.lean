/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.SpectralSupport
import FABL.Chapter05.DegreeOneWeight

/-!
# Fourier transform of the numerical normal form

Carlet Relation (30): the unnormalized Fourier coefficients of a pseudo-Boolean
function in numerical normal form.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

/-- The raw Fourier coefficient of a numerical monomial. -/
theorem rawFourierTransform_numericalMonomial
    (S : Finset (Fin n)) (u : FABL.F₂Cube n) :
    rawFourierTransform (numericalMonomial S) u =
      if FABL.f₂Support u ⊆ S then
        (-1 : ℝ) ^ (FABL.f₂Support u).card * (2 : ℝ) ^ (n - S.card)
      else 0 := by
  classical
  rw [numericalMonomial_eq_setIndicator_coordinateSubcube,
    FABL.F₂DecisionTree.coordinateSubcube_eq_binaryAffineSubspace,
    rawFourierTransform_setIndicator_binaryAffineSubspace]
  by_cases hu : FABL.f₂Support u ⊆ S
  · have humem :
        u ∈ FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace S) :=
      (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset S u).2 hu
    rw [if_pos humem, if_pos hu]
    have hcharacter :
        FABL.vectorWalshCharacter u (FABL.f₂CubeOfFinset S) =
          (-1 : ℝ) ^ (FABL.f₂Support u).card := by
      rw [FABL.vectorWalshCharacter_apply,
        FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
      change FABL.binarySign
        (∑ i ∈ FABL.f₂Support u, FABL.f₂CubeOfFinset S i) = _
      have hvalues : ∀ i ∈ FABL.f₂Support u,
          FABL.f₂CubeOfFinset S i = 1 := by
        intro i hi
        simp [FABL.f₂CubeOfFinset_apply, hu hi]
      have hsum :
          (∑ i ∈ FABL.f₂Support u, FABL.f₂CubeOfFinset S i) =
            (FABL.f₂Support u).card • (1 : FABL.𝔽₂) := by
        calc
          (∑ i ∈ FABL.f₂Support u, FABL.f₂CubeOfFinset S i) =
              ∑ _i ∈ FABL.f₂Support u, (1 : FABL.𝔽₂) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hvalues i hi
          _ = (FABL.f₂Support u).card • (1 : FABL.𝔽₂) := by
            rw [Finset.sum_const]
      rw [hsum, AddChar.map_nsmul_eq_pow]
      rw [show FABL.binarySign (1 : FABL.𝔽₂) = (-1 : ℝ) by
        change (-1 : ℝ) ^ (1 : FABL.𝔽₂).val = -1
        rw [show (1 : FABL.𝔽₂).val = 1 by decide]
        norm_num]
    have hcard :
        Nat.card (FABL.F₂DecisionTree.coordinateZeroSubspace S) =
          2 ^ (n - S.card) := by
      rw [FABL.card_submodule_eq_two_pow_finrank]
      congr 1
      have hcodimension :=
        FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace S
      rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace] at hcodimension
      have hfinrank :
          Module.finrank FABL.𝔽₂
              (FABL.F₂DecisionTree.coordinateZeroSubspace S) ≤ n := by
        simpa using (FABL.F₂DecisionTree.coordinateZeroSubspace S).finrank_le
      omega
    have hcardReal :
        (Nat.card (FABL.F₂DecisionTree.coordinateZeroSubspace S) : ℝ) =
          (2 : ℝ) ^ (n - S.card) := by
      exact_mod_cast hcard
    rw [hcharacter, hcardReal]
  · have hunotmem :
        u ∉ FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace S) := fun humem ↦
      hu ((FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset S u).1
        humem)
    rw [if_neg hunotmem, if_neg hu, mul_zero]

/-- Carlet Relation (30): the raw Fourier transform of a numerical normal form. -/
theorem rawFourierTransform_numericalEval
    (c : NumericalCoefficients n) (u : FABL.F₂Cube n) :
    rawFourierTransform (numericalEval c) u =
      (-1 : ℝ) ^ (FABL.f₂Support u).card *
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
          FABL.f₂Support u ⊆ S),
          (2 : ℝ) ^ (n - S.card) * c S := by
  classical
  rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
    vectorFourierCoeff_numericalEval, Finset.mul_sum]
  calc
    ∑ S : Finset (Fin n),
        (2 ^ n : ℝ) *
          (c S * FABL.vectorFourierCoeff (numericalMonomial S) u) =
        ∑ S : Finset (Fin n), c S * rawFourierTransform (numericalMonomial S) u := by
      apply Finset.sum_congr rfl
      intro S _
      rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
      ring
    _ = ∑ S : Finset (Fin n),
        if FABL.f₂Support u ⊆ S then
          (-1 : ℝ) ^ (FABL.f₂Support u).card *
            ((2 : ℝ) ^ (n - S.card) * c S)
        else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [rawFourierTransform_numericalMonomial]
      by_cases hS : FABL.f₂Support u ⊆ S <;> simp [hS]
      ring
    _ = ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
        FABL.f₂Support u ⊆ S),
        (-1 : ℝ) ^ (FABL.f₂Support u).card *
          ((2 : ℝ) ^ (n - S.card) * c S) := by
      rw [Finset.sum_filter]
    _ = (-1 : ℝ) ^ (FABL.f₂Support u).card *
        ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
          FABL.f₂Support u ⊆ S),
          (2 : ℝ) ^ (n - S.card) * c S := by
      rw [Finset.mul_sum]

end CryptBoolean
