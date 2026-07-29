/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.PropagationCriteria

/-!
# Walsh characterization of propagation criteria

The Wiener--Khintchine characterization of propagation criteria by squared raw
Walsh coefficients.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Fourier inversion expresses autocorrelation as the character-weighted sum of
squared raw Walsh coefficients. -/
theorem sum_vectorWalshCharacter_mul_walshTransform_sq
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (∑ u, FABL.vectorWalshCharacter a u * (walshTransform f u : ℝ) ^ 2) =
      (2 : ℝ) ^ n * autocorrelation f a := by
  have hinvolution := rawFourierTransform_involution (autocorrelation f) a
  rw [rawFourierTransform] at hinvolution
  simp_rw [rawFourierTransform_autocorrelation] at hinvolution
  simpa [mul_comm] using hinvolution

/-- Carlet Chapter 8.1.1: `PC(l)` is equivalent to vanishing of every
low-weight nontrivial character sum of the squared raw Walsh spectrum. -/
theorem satisfiesPropagationCriterion_iff_sum_vectorWalshCharacter_mul_walshTransform_sq_eq_zero
    (l : ℕ) (f : BooleanFunction n) :
    SatisfiesPropagationCriterion l f ↔
      ∀ a : FABL.F₂Cube n, a ≠ 0 → (FABL.f₂Support a).card ≤ l →
        (∑ u, FABL.vectorWalshCharacter a u *
          (walshTransform f u : ℝ) ^ 2) = 0 := by
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero]
  constructor
  · intro h a ha hweight
    rw [sum_vectorWalshCharacter_mul_walshTransform_sq, h a ha hweight, mul_zero]
  · intro h a ha hweight
    have hproduct : (2 : ℝ) ^ n * autocorrelation f a = 0 := by
      rw [← sum_vectorWalshCharacter_mul_walshTransform_sq]
      exact h a ha hweight
    exact (mul_eq_zero.mp hproduct).resolve_left (by positivity)

end CryptBoolean
