/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AutocorrelationIndicators

/-!
# Carlet Chapter 4 autocorrelation identities

Second derivatives express the sum-of-squares indicator, while raw Plancherel and the
Wiener--Khintchine identity relate it to the fourth moment of the Walsh spectrum.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Carlet's second-order derivative `D_a D_e f`. -/
def secondBooleanDerivative (f : BooleanFunction n) (a e : FABL.F₂Cube n) :
    BooleanFunction n :=
  FABL.booleanDerivative (FABL.booleanDerivative f e) a

/-- The second-order derivative is the four-term binary difference displayed by Carlet. -/
theorem secondBooleanDerivative_apply
    (f : BooleanFunction n) (a e x : FABL.F₂Cube n) :
    secondBooleanDerivative f a e x =
      f x + f (x + a) + f (x + e) + f (x + a + e) := by
  simp only [secondBooleanDerivative, FABL.booleanDerivative]
  abel

/-- Carlet's second-derivative expression for the sum-of-squares indicator. -/
theorem sumOfSquaresIndicator_eq_sum_secondBooleanDerivative
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f =
      ∑ a, ∑ e, ∑ x, realSignView (secondBooleanDerivative f a e) x := by
  classical
  rw [sumOfSquaresIndicator]
  calc
    ∑ e, autocorrelation f e ^ 2 =
        ∑ e, ∑ a, autocorrelation (FABL.booleanDerivative f e) a := by
      apply Finset.sum_congr rfl
      intro e _
      rw [sum_autocorrelation_eq_walshTransform_zero_sq]
      congr 1
      rw [autocorrelation, walshTransform_cast_eq_sum_realSignView_mul_character]
      simp
    _ = ∑ a, ∑ e, autocorrelation (FABL.booleanDerivative f e) a :=
      Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ x, realSignView (secondBooleanDerivative f a e) x := by
      simp only [autocorrelation, secondBooleanDerivative]

/-- Carlet Relation (39): shifted Walsh-spectrum squares are the transform of squared
autocorrelation. -/
theorem sum_walshTransform_sq_mul_add_sq_eq
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    ∑ e, (walshTransform f e : ℝ) ^ 2 *
        (walshTransform f (a + e) : ℝ) ^ 2 =
      (2 : ℝ) ^ n * ∑ e, autocorrelation f e ^ 2 *
        FABL.vectorWalshCharacter a e := by
  classical
  let φ : FABL.F₂Cube n → ℝ := autocorrelation f
  let ψ : FABL.F₂Cube n → ℝ :=
    fun e ↦ FABL.vectorWalshCharacter a e * φ e
  have hshift (e : FABL.F₂Cube n) :
      rawFourierTransform ψ e = rawFourierTransform φ (a + e) := by
    simpa [ψ] using rawFourierTransform_modulate_translate φ a 0 e
  calc
    ∑ e, (walshTransform f e : ℝ) ^ 2 *
        (walshTransform f (a + e) : ℝ) ^ 2 =
        ∑ e, rawFourierTransform φ e * rawFourierTransform φ (a + e) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [rawFourierTransform_autocorrelation,
        rawFourierTransform_autocorrelation]
    _ = ∑ e, rawFourierTransform φ e * rawFourierTransform ψ e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hshift]
    _ = (2 : ℝ) ^ n * ∑ e, φ e * ψ e :=
      sum_rawFourierTransform_mul φ ψ
    _ = (2 : ℝ) ^ n * ∑ e, autocorrelation f e ^ 2 *
        FABL.vectorWalshCharacter a e := by
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      simp only [φ, ψ]
      ring

/-- The zero-shift specialization of Relation (39): the fourth Walsh moment is `2^n V(f)`. -/
theorem sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator
    (f : BooleanFunction n) :
    ∑ e, (walshTransform f e : ℝ) ^ 4 =
      (2 : ℝ) ^ n * sumOfSquaresIndicator f := by
  have h := sum_walshTransform_sq_mul_add_sq_eq f 0
  rw [sumOfSquaresIndicator]
  calc
    ∑ e, (walshTransform f e : ℝ) ^ 4 =
        ∑ e, (walshTransform f e : ℝ) ^ 2 *
          (walshTransform f e : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (2 : ℝ) ^ n * ∑ e, autocorrelation f e ^ 2 := by
      simpa using h

end CryptBoolean
