/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Foundations

/-!
# Carlet Chapter 2 Fourier/Walsh inversion and Parseval

Walsh inversion and the Parseval identity for Carlet's unnormalized Walsh transform,
obtained by composition over FABL's normalized vector-Fourier API through the
`walshTransform_eq_two_pow_mul_vectorFourierCoeff` normalization bridge.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The real sign view is `±1`, so its pointwise square is `1`. -/
theorem realSignView_mul_self (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    realSignView f x * realSignView f x = 1 := by
  rcases FABL.signValue_eq_neg_one_or_one (FABL.signEncodedFunction f x) with h | h <;>
    simp [realSignView, FABL.realSignEncodedFunction, h]

/-- Parseval for the normalized coefficients of the sign view: the spectral squares sum to one. -/
theorem sum_vectorFourierCoeff_realSignView_sq (f : BooleanFunction n) :
    ∑ a, (FABL.vectorFourierCoeff (realSignView f) a) ^ 2 = 1 := by
  classical
  have hpl := FABL.vector_plancherel (realSignView f) (realSignView f)
  have hlhs : (𝔼 x, realSignView f x * realSignView f x) = 1 := by
    simp_rw [realSignView_mul_self]
    exact Fintype.expect_const 1
  have hsum : ∑ a, FABL.vectorFourierCoeff (realSignView f) a *
      FABL.vectorFourierCoeff (realSignView f) a = 1 := hpl.symm.trans hlhs
  simp_rw [pow_two]
  exact hsum

/-- The Walsh-weighted expansion of the sign view: `2^n (-1)^{f(x)} = ∑ₐ W_f(a) χ_a(x)`. -/
theorem two_pow_mul_realSignView_eq_sum_walshTransform_mul_character
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    (2 ^ n : ℝ) * realSignView f x =
      ∑ a, (walshTransform f a : ℝ) * FABL.vectorWalshCharacter a x := by
  classical
  rw [FABL.vector_fourier_expansion (realSignView f) x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  ring

/-- Carlet's Walsh inversion for the sign view: `(-1)^{f(x)} = 2^{-n} ∑ₐ W_f(a) χ_a(x)`. -/
theorem realSignView_eq_inv_two_pow_mul_sum_walshTransform_mul_character
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    realSignView f x =
      (2 ^ n : ℝ)⁻¹ * ∑ a, (walshTransform f a : ℝ) * FABL.vectorWalshCharacter a x := by
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [← two_pow_mul_realSignView_eq_sum_walshTransform_mul_character]
  field_simp

/-- Parseval for Carlet's raw integer Walsh transform: `∑ₐ W_f(a)² = (2^n)²`. -/
theorem sum_walshTransform_sq_eq_two_pow_sq (f : BooleanFunction n) :
    ∑ a, (walshTransform f a : ℝ) ^ 2 = ((2 : ℝ) ^ n) ^ 2 := by
  classical
  calc
    ∑ a, (walshTransform f a : ℝ) ^ 2
        = ∑ a, ((2 : ℝ) ^ n) ^ 2 *
            (FABL.vectorFourierCoeff (realSignView f) a) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff]
          ring
    _ = ((2 : ℝ) ^ n) ^ 2 *
        ∑ a, (FABL.vectorFourierCoeff (realSignView f) a) ^ 2 := by
          rw [← Finset.mul_sum]
    _ = ((2 : ℝ) ^ n) ^ 2 := by
          rw [sum_vectorFourierCoeff_realSignView_sq]
          ring

end CryptBoolean
