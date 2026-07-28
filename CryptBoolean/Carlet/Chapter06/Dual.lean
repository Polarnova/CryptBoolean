/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness
public import FABL.Chapter06.Constructions.BentDual

/-!
# Duals of bent Boolean functions

Carlet Section 6.1: the bit-valued dual, its raw Walsh relation, bentness, and involution.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The bit-valued dual selected by the sign of the raw Walsh coefficient. -/
noncomputable def bentDual (f : BooleanFunction n) : BooleanFunction n :=
  fun a ↦ if 0 ≤ walshTransform f a then 0 else 1

/-- For a bent function, the raw Walsh coefficient is its dual sign scaled by
`2^(n/2)`. -/
theorem walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
    (f : BooleanFunction n) (hf : IsBent f) (a : FABL.F₂Cube n) :
    walshTransform f a =
      (2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f a) := by
  have hmagnitude :=
    natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a
  rcases Int.natAbs_eq_iff.mp hmagnitude with hpositive | hnegative
  · have hnonnegative : 0 ≤ walshTransform f a := by
      rw [hpositive]
      positivity
    rw [bentDual, if_pos hnonnegative, hpositive]
    simp [bitSignInt_eq_if_one]
  · have hnegative' : ¬ 0 ≤ walshTransform f a := by
      rw [hnegative]
      have hpower : (0 : ℤ) < 2 ^ (n / 2) := by positivity
      exact not_le.mpr (neg_neg_of_pos hpower)
    rw [bentDual, if_neg hnegative', hnegative]
    simp [bitSignInt_eq_if_one]

/-- The real sign view of Carlet's bit-valued dual is FABL's normalized
Fourier dual. -/
theorem realSignView_bentDual
    (f : BooleanFunction n) (hf : IsBent f) :
    realSignView (bentDual f) = FABL.bentDual (realSignView f) := by
  funext a
  have hn := even_of_isBent f hf
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hrawInt :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf a
  have hraw := congrArg (fun z : ℤ ↦ (z : ℝ)) hrawInt
  have hsign :
      (bitSignInt (bentDual f a) : ℝ) = realSignView (bentDual f) a := by
    rw [bitSignInt_cast]
    simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hraw
  rw [hsign] at hraw
  have hfourier := walshTransform_eq_two_pow_mul_vectorFourierCoeff f a
  have hpow :
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2 + n / 2) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hsplit
      _ = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := pow_add _ _ _
  apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (n / 2) ≠ 0)
  calc
    (2 : ℝ) ^ (n / 2) * realSignView (bentDual f) a =
        (walshTransform f a : ℝ) := hraw.symm
    _ = (2 : ℝ) ^ n * FABL.vectorFourierCoeff (realSignView f) a :=
      hfourier
    _ = (2 : ℝ) ^ (n / 2) *
        ((2 : ℝ) ^ (n / 2) *
          FABL.vectorFourierCoeff (realSignView f) a) := by
      rw [hpow]
      ring
    _ = (2 : ℝ) ^ (n / 2) * FABL.bentDual (realSignView f) a := rfl

/-- The dual of a bent Boolean function is bent. -/
theorem isBent_bentDual
    (f : BooleanFunction n) (hf : IsBent f) : IsBent (bentDual f) := by
  change FABL.IsBent (realSignView (bentDual f))
  rw [realSignView_bentDual f hf]
  exact (FABL.IsBent.bentDual (even_of_isBent f hf) hf
    (FABL.isSignValued_realSignEncodedFunction f)).2

/-- The raw Walsh transform of the dual recovers the original sign. -/
theorem walshTransform_bentDual
    (f : BooleanFunction n) (hf : IsBent f) (a : FABL.F₂Cube n) :
    walshTransform (bentDual f) a =
      (2 ^ (n / 2) : ℤ) * bitSignInt (f a) := by
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    realSignView_bentDual f hf,
    FABL.vectorFourierCoeff_bentDual (even_of_isBent f hf)]
  have hsign : (bitSignInt (f a) : ℝ) = realSignView f a := by
    rw [bitSignInt_cast]
    simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
  have hsplit : n = n / 2 + n / 2 := by
    rcases even_of_isBent f hf with ⟨k, hk⟩
    omega
  have hpow :
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2 + n / 2) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hsplit
      _ = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := pow_add _ _ _
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [hsign]
  rw [hpow]
  field_simp

/-- Duality is an involution on bent Boolean functions. -/
theorem bentDual_bentDual
    (f : BooleanFunction n) (hf : IsBent f) : bentDual (bentDual f) = f := by
  funext a
  rw [bentDual, walshTransform_bentDual f hf a]
  by_cases hfa : f a = 1
  · simp [hfa, bitSignInt_eq_if_one]
  · have hfaZero : f a = 0 := by
      by_contra hzero
      exact hfa (Fin.eq_one_of_ne_zero (f a) hzero)
    simp [hfaZero, bitSignInt_eq_if_one]

end CryptBoolean
