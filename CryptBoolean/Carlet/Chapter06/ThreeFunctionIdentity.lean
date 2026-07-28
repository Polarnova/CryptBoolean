/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.CoveringSequences
public import FABL.Chapter06.F₂Polynomials.BentDegree

/-!
# Carlet Chapter 6 three-function identity

Carlet Proposition 22 and relation (50) for three Boolean functions.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The first elementary symmetric function of three Boolean functions. -/
def threeFunctionSum
    (f₁ f₂ f₃ : BooleanFunction n) : BooleanFunction n :=
  f₁ + f₂ + f₃

/-- The second elementary symmetric function of three Boolean functions. -/
def threeFunctionPairwiseProductSum
    (f₁ f₂ f₃ : BooleanFunction n) : BooleanFunction n :=
  f₁ * f₂ + f₁ * f₃ + f₂ * f₃

private theorem bitValueInt_threeBitIdentity (b₁ b₂ b₃ : FABL.𝔽₂) :
    bitValueInt b₁ + bitValueInt b₂ + bitValueInt b₃ =
      bitValueInt (b₁ + b₂ + b₃) +
        2 * bitValueInt (b₁ * b₂ + b₁ * b₃ + b₂ * b₃) := by
  fin_cases b₁ <;> fin_cases b₂ <;> fin_cases b₃ <;>
    decide

/-- Carlet Proposition 22: the ordinary integer sum of three bits is their
first elementary symmetric function plus twice their second. -/
theorem bitValueInt_threeFunctionIdentity
    (f₁ f₂ f₃ : BooleanFunction n) :
    (fun x ↦ bitValueInt (f₁ x) + bitValueInt (f₂ x) + bitValueInt (f₃ x)) =
      fun x ↦ bitValueInt (threeFunctionSum f₁ f₂ f₃ x) +
        2 * bitValueInt (threeFunctionPairwiseProductSum f₁ f₂ f₃ x) := by
  funext x
  simpa [threeFunctionSum, threeFunctionPairwiseProductSum] using
    bitValueInt_threeBitIdentity (f₁ x) (f₂ x) (f₃ x)

private theorem booleanRealEmbedding_threeFunctionIdentity
    (f₁ f₂ f₃ : BooleanFunction n) :
    FABL.booleanRealEmbedding f₁ + FABL.booleanRealEmbedding f₂ +
        FABL.booleanRealEmbedding f₃ =
      FABL.booleanRealEmbedding (threeFunctionSum f₁ f₂ f₃) +
        fun x ↦ 2 *
          FABL.booleanRealEmbedding
            (threeFunctionPairwiseProductSum f₁ f₂ f₃) x := by
  funext x
  have h := congrFun (bitValueInt_threeFunctionIdentity f₁ f₂ f₃) x
  have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hcast
  have hembedding (f : BooleanFunction n) :
      (bitValueInt (f x) : ℝ) = FABL.booleanRealEmbedding f x := by
    by_cases hf : f x = 1 <;>
      simp [bitValueInt, FABL.booleanRealEmbedding, hf]
  rw [hembedding f₁, hembedding f₂, hembedding f₃,
    hembedding (threeFunctionSum f₁ f₂ f₃),
    hembedding (threeFunctionPairwiseProductSum f₁ f₂ f₃)] at hcast
  simpa only [Pi.add_apply] using hcast

/-- Applying the raw pseudo-Boolean Fourier transform to Proposition 22
preserves the three-function identity. -/
theorem rawFourierTransform_threeFunctionIdentity
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n) :
    rawFourierTransform (FABL.booleanRealEmbedding f₁) a +
        rawFourierTransform (FABL.booleanRealEmbedding f₂) a +
        rawFourierTransform (FABL.booleanRealEmbedding f₃) a =
      rawFourierTransform
          (FABL.booleanRealEmbedding (threeFunctionSum f₁ f₂ f₃)) a +
        2 * rawFourierTransform
          (FABL.booleanRealEmbedding
            (threeFunctionPairwiseProductSum f₁ f₂ f₃)) a := by
  have hcoeff := congrArg
    (fun φ : FABL.F₂Cube n → ℝ ↦ FABL.vectorFourierCoeff φ a)
    (booleanRealEmbedding_threeFunctionIdentity f₁ f₂ f₃)
  simp only [FABL.vectorFourierCoeff_add,
    FABL.vectorFourierCoeff_const_mul] at hcoeff
  simp_rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff]
  calc
    (2 ^ n : ℝ) * FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₁) a +
          (2 ^ n : ℝ) * FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₂) a +
          (2 ^ n : ℝ) * FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₃) a =
        (2 ^ n : ℝ) *
          (FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₁) a +
            FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₂) a +
            FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f₃) a) := by ring
    _ = (2 ^ n : ℝ) *
          (FABL.vectorFourierCoeff
              (FABL.booleanRealEmbedding (threeFunctionSum f₁ f₂ f₃)) a +
            2 * FABL.vectorFourierCoeff
              (FABL.booleanRealEmbedding
                (threeFunctionPairwiseProductSum f₁ f₂ f₃)) a) := by
      rw [hcoeff]
    _ = (2 ^ n : ℝ) * FABL.vectorFourierCoeff
          (FABL.booleanRealEmbedding (threeFunctionSum f₁ f₂ f₃)) a +
        2 * ((2 ^ n : ℝ) * FABL.vectorFourierCoeff
          (FABL.booleanRealEmbedding
            (threeFunctionPairwiseProductSum f₁ f₂ f₃)) a) := by ring

theorem walshTransform_cast_eq_rawFourierTransform_sub_two_mul
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (walshTransform f a : ℝ) =
      rawFourierTransform (fun _ ↦ 1) a -
        2 * rawFourierTransform (FABL.booleanRealEmbedding f) a := by
  calc
    (walshTransform f a : ℝ) = rawFourierTransform (realSignView f) a := by
      simpa [rawFourierTransform] using
        walshTransform_cast_eq_sum_realSignView_mul_character f a
    _ = rawFourierTransform
        (fun x ↦ 1 - 2 * FABL.booleanRealEmbedding f x) a := by
      rw [show realSignView f =
          (fun x ↦ 1 - 2 * FABL.booleanRealEmbedding f x) from
        FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding f]
    _ = rawFourierTransform (fun _ ↦ 1) a -
        2 * rawFourierTransform (FABL.booleanRealEmbedding f) a := by
      rw [rawFourierTransform, rawFourierTransform, rawFourierTransform,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- Carlet relation (50): the raw Walsh transforms of three Boolean functions
satisfy the same first-and-second symmetric-function identity. -/
theorem walshTransform_threeFunctionIdentity
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n) :
    walshTransform f₁ a + walshTransform f₂ a + walshTransform f₃ a =
      walshTransform (threeFunctionSum f₁ f₂ f₃) a +
        2 * walshTransform (threeFunctionPairwiseProductSum f₁ f₂ f₃) a := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [walshTransform_cast_eq_rawFourierTransform_sub_two_mul,
    walshTransform_cast_eq_rawFourierTransform_sub_two_mul,
    walshTransform_cast_eq_rawFourierTransform_sub_two_mul,
    walshTransform_cast_eq_rawFourierTransform_sub_two_mul,
    walshTransform_cast_eq_rawFourierTransform_sub_two_mul]
  have hfourier := rawFourierTransform_threeFunctionIdentity f₁ f₂ f₃ a
  linarith

end CryptBoolean
