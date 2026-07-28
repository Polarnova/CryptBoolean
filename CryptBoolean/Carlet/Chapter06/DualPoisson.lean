/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter06.Dual

/-!
# Poisson summation for a bent function and its dual

Carlet Relation (46).
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

attribute [local instance] submoduleFintype

/-- Carlet Relation (46): Poisson summation exchanges a bent function and
its dual across perpendicular affine subspaces. -/
theorem bentDual_poissonSummationFormula
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a b : FABL.F₂Cube n) :
    (∑ u : E,
        realSignView (bentDual f) (a + u.1) *
          FABL.vectorWalshCharacter b (a + u.1)) =
      ((2 : ℝ) ^ (n / 2))⁻¹ * (Nat.card E : ℝ) *
        FABL.vectorWalshCharacter b a *
          ∑ x : FABL.perpendicularSubspace E,
            realSignView f (b + x.1) *
              FABL.vectorWalshCharacter a (b + x.1) := by
  classical
  let p : ℝ := (2 : ℝ) ^ (n / 2)
  have hp : p ≠ 0 := by
    dsimp [p]
    positivity
  have hrawFourier (u : FABL.F₂Cube n) :
      rawFourierTransform (realSignView f) u =
        (walshTransform f u : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hwalsh (u : FABL.F₂Cube n) :
      (walshTransform f u : ℝ) = p * realSignView (bentDual f) u := by
    have hraw := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf u)
    have hsign :
        (bitSignInt (bentDual f u) : ℝ) = realSignView (bentDual f) u := by
      rw [bitSignInt_cast]
      simp [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hsign, p] using hraw
  have hpoisson := rawPoissonSummationFormula (realSignView f) E a b
  simp_rw [hrawFourier, hwalsh] at hpoisson
  have hscaled :
      p * (∑ u : E,
          realSignView (bentDual f) (a + u.1) *
            FABL.vectorWalshCharacter b (a + u.1)) =
        (Nat.card E : ℝ) * FABL.vectorWalshCharacter b a *
          ∑ x : FABL.perpendicularSubspace E,
            realSignView f (b + x.1) *
              FABL.vectorWalshCharacter a (b + x.1) := by
    calc
      p * (∑ u : E,
          realSignView (bentDual f) (a + u.1) *
            FABL.vectorWalshCharacter b (a + u.1)) =
          ∑ u : E,
            FABL.vectorWalshCharacter b (a + u.1) *
              (p * realSignView (bentDual f) (a + u.1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        ring
      _ = (Nat.card E : ℝ) * FABL.vectorWalshCharacter b a *
          ∑ x : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter a (b + x.1) *
              realSignView f (b + x.1) := hpoisson
      _ = (Nat.card E : ℝ) * FABL.vectorWalshCharacter b a *
          ∑ x : FABL.perpendicularSubspace E,
            realSignView f (b + x.1) *
              FABL.vectorWalshCharacter a (b + x.1) := by
        apply congrArg
        apply Finset.sum_congr rfl
        intro x _hx
        ring
  apply mul_left_cancel₀ hp
  rw [hscaled]
  simp only [p]
  field_simp

end CryptBoolean
