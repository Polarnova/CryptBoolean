/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Fourier

/-!
# Carlet Chapter 2 Fourier operations

The unnormalized Fourier transform of real-valued functions on the binary cube,
with translation, inversion, convolution, and Plancherel obtained by explicit
scaling from FABL's normalized vector Fourier API.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Carlet's unnormalized Fourier transform of a pseudo-Boolean function. -/
noncomputable def rawFourierTransform (φ : FABL.F₂Cube n → ℝ)
    (a : FABL.F₂Cube n) : ℝ :=
  ∑ x, φ x * FABL.vectorWalshCharacter a x

/-- Carlet's raw transform is the cardinality-scaled normalized FABL coefficient. -/
theorem rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff
    (φ : FABL.F₂Cube n → ℝ) (a : FABL.F₂Cube n) :
    rawFourierTransform φ a =
      (2 ^ n : ℝ) * FABL.vectorFourierCoeff φ a := by
  rw [rawFourierTransform, FABL.vectorFourierCoeff_eq_expect,
    Fintype.expect_eq_sum_div_card, card_f₂Cube]
  norm_num
  field_simp

/-- Multiplying by a Walsh character shifts the normalized Fourier index. -/
theorem vectorFourierCoeff_mul_vectorWalshCharacter
    (φ : FABL.F₂Cube n → ℝ) (a u : FABL.F₂Cube n) :
    FABL.vectorFourierCoeff
        (fun x ↦ FABL.vectorWalshCharacter a x * φ x) u =
      FABL.vectorFourierCoeff φ (a + u) := by
  rw [FABL.vectorFourierCoeff_eq_expect, FABL.vectorFourierCoeff_eq_expect]
  apply Finset.expect_congr rfl
  intro x _
  have hχ := congrArg (fun χ : AddChar (FABL.F₂Cube n) ℝ ↦ χ x)
    (FABL.vectorWalshCharacter_mul a u)
  change FABL.vectorWalshCharacter a x * FABL.vectorWalshCharacter u x =
    FABL.vectorWalshCharacter (a + u) x at hχ
  calc
    FABL.vectorWalshCharacter a x * φ x * FABL.vectorWalshCharacter u x =
        φ x * (FABL.vectorWalshCharacter a x * FABL.vectorWalshCharacter u x) := by ring
    _ = φ x * FABL.vectorWalshCharacter (a + u) x := by rw [hχ]

/-- Carlet Proposition 6: modulation and translation shift the raw spectrum. -/
theorem rawFourierTransform_modulate_translate
    (φ : FABL.F₂Cube n → ℝ) (a b u : FABL.F₂Cube n) :
    rawFourierTransform
        (fun x ↦ FABL.vectorWalshCharacter a x * φ (x + b)) u =
      FABL.vectorWalshCharacter (a + u) b * rawFourierTransform φ (a + u) := by
  rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
    vectorFourierCoeff_mul_vectorWalshCharacter,
    FABL.vectorFourierCoeff_translate_add,
    rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  ring

/-- Carlet Corollary 2: applying the raw Fourier transform twice multiplies by `2^n`. -/
theorem rawFourierTransform_involution
    (φ : FABL.F₂Cube n → ℝ) (x : FABL.F₂Cube n) :
    rawFourierTransform (rawFourierTransform φ) x = (2 ^ n : ℝ) * φ x := by
  rw [rawFourierTransform]
  simp_rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  calc
    ∑ a, (2 ^ n : ℝ) * FABL.vectorFourierCoeff φ a *
        FABL.vectorWalshCharacter x a =
        (2 ^ n : ℝ) * ∑ a, FABL.vectorFourierCoeff φ a *
          FABL.vectorWalshCharacter a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have hchar : FABL.vectorWalshCharacter x a =
          FABL.vectorWalshCharacter a x := by
        rw [FABL.vectorWalshCharacter_apply, FABL.vectorWalshCharacter_apply]
        congr 1
        exact dotProduct_comm x a
      rw [hchar]
      ring
    _ = (2 ^ n : ℝ) * φ x := by rw [← FABL.vector_fourier_expansion φ x]

/-- Carlet's unnormalized convolution on the additive binary cube. -/
noncomputable def rawConvolution (φ ψ : FABL.F₂Cube n → ℝ)
    (x : FABL.F₂Cube n) : ℝ :=
  ∑ y, φ y * ψ (x + y)

/-- Raw convolution is the cardinality-scaled normalized FABL convolution. -/
theorem rawConvolution_eq_two_pow_mul_convolution
    (φ ψ : FABL.F₂Cube n → ℝ) (x : FABL.F₂Cube n) :
    rawConvolution φ ψ x = (2 ^ n : ℝ) * FABL.convolution φ ψ x := by
  rw [rawConvolution, FABL.convolution_apply_add,
    Fintype.expect_eq_sum_div_card, card_f₂Cube]
  norm_num
  field_simp

/-- Carlet Proposition 8: the raw Fourier transform sends raw convolution to pointwise product. -/
theorem rawFourierTransform_rawConvolution
    (φ ψ : FABL.F₂Cube n → ℝ) (a : FABL.F₂Cube n) :
    rawFourierTransform (rawConvolution φ ψ) a =
      rawFourierTransform φ a * rawFourierTransform ψ a := by
  rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hconv : rawConvolution φ ψ =
      fun x ↦ (2 ^ n : ℝ) * FABL.convolution φ ψ x := by
    funext x
    exact rawConvolution_eq_two_pow_mul_convolution φ ψ x
  rw [hconv, FABL.vectorFourierCoeff_const_mul]
  rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
    rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  change _ = _
  rw [show FABL.vectorFourierCoeff (FABL.convolution φ ψ) a =
      FABL.vectorFourierCoeff φ a * FABL.vectorFourierCoeff ψ a by
    simpa [FABL.vectorFourierCoeff] using
      FABL.binaryFourierCoeff_convolution φ ψ (FABL.f₂Support a)]
  ring

/-- Carlet Corollary 3: Plancherel for the unnormalized transform. -/
theorem sum_rawFourierTransform_mul
    (φ ψ : FABL.F₂Cube n → ℝ) :
    ∑ a, rawFourierTransform φ a * rawFourierTransform ψ a =
      (2 ^ n : ℝ) * ∑ x, φ x * ψ x := by
  have hpl := FABL.vector_plancherel φ ψ
  simp_rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  calc
    ∑ a, (2 ^ n : ℝ) * FABL.vectorFourierCoeff φ a *
        ((2 ^ n : ℝ) * FABL.vectorFourierCoeff ψ a) =
        ((2 ^ n : ℝ) ^ 2) *
          ∑ a, FABL.vectorFourierCoeff φ a * FABL.vectorFourierCoeff ψ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((2 ^ n : ℝ) ^ 2) * (𝔼 x, φ x * ψ x) := by rw [hpl]
    _ = (2 ^ n : ℝ) * ∑ x, φ x * ψ x := by
      rw [Fintype.expect_eq_sum_div_card, card_f₂Cube]
      norm_num
      field_simp

end CryptBoolean
