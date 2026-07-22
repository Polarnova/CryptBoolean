/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierOperations
public import FABL.Chapter06.FoolingF₂Polynomials.DirectionalDerivatives

/-!
# Carlet Chapter 2 derivatives and autocorrelation

The shared binary directional derivative comes from FABL Chapter 6. This module retains Carlet's
sign bridge, raw autocorrelation, and Wiener--Khintchine identities.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The derivative sign is the product of the two translated function signs. -/
theorem realSignView_booleanDerivative
    (f : BooleanFunction n) (b x : FABL.F₂Cube n) :
    realSignView (FABL.booleanDerivative f b) x =
      realSignView f x * realSignView f (x + b) := by
  change FABL.signValue (FABL.signEncode (f x + f (x + b))) =
    FABL.signValue (FABL.signEncode (f x)) *
      FABL.signValue (FABL.signEncode (f (x + b)))
  rw [FABL.signValue_signEncode_eq_binarySign,
    FABL.signValue_signEncode_eq_binarySign,
    FABL.signValue_signEncode_eq_binarySign]
  exact AddChar.map_add_eq_mul FABL.binarySign (f x) (f (x + b))

/-- Carlet's autocorrelation value `Δ_f(b) = ∑ₓ (-1)^(D_b f(x))`. -/
def autocorrelation (f : BooleanFunction n) (b : FABL.F₂Cube n) : ℝ :=
  ∑ x, realSignView (FABL.booleanDerivative f b) x

/-- Autocorrelation is the raw self-convolution of the sign view. -/
theorem autocorrelation_eq_rawConvolution_realSignView
    (f : BooleanFunction n) (b : FABL.F₂Cube n) :
    autocorrelation f b = rawConvolution (realSignView f) (realSignView f) b := by
  apply Finset.sum_congr rfl
  intro x _
  rw [realSignView_booleanDerivative]
  rw [add_comm b x]

/-- Wiener--Khintchine: the raw transform of autocorrelation is the squared Walsh spectrum. -/
theorem rawFourierTransform_autocorrelation
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    rawFourierTransform (autocorrelation f) a = (walshTransform f a : ℝ) ^ 2 := by
  have hauto : autocorrelation f =
      rawConvolution (realSignView f) (realSignView f) := by
    funext b
    exact autocorrelation_eq_rawConvolution_realSignView f b
  rw [hauto, rawFourierTransform_rawConvolution, pow_two]
  congr 1 <;>
    exact (walshTransform_cast_eq_sum_realSignView_mul_character f a).symm

/-- The total autocorrelation is the square of the zero-frequency Walsh value. -/
theorem sum_autocorrelation_eq_walshTransform_zero_sq
    (f : BooleanFunction n) :
    ∑ b, autocorrelation f b = (walshTransform f 0 : ℝ) ^ 2 := by
  have h := rawFourierTransform_autocorrelation f 0
  simpa [rawFourierTransform] using h

end CryptBoolean
