/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierOperations
public import CryptBoolean.Carlet.Chapter06.Dual

/-!
# Isometry of bent duality

Carlet Relation (44): duality preserves pairwise Hamming distance.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The sign view sends binary addition to pointwise multiplication. -/
theorem realSignView_add
    (f g : BooleanFunction n) (x : FABL.F₂Cube n) :
    realSignView (f + g) x = realSignView f x * realSignView g x := by
  simp only [realSignView, FABL.realSignEncodedFunction,
    FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
  exact AddChar.map_add_eq_mul FABL.binarySign (f x) (g x)

/-- Carlet Relation (44): the imbalance of the sum of two bent duals equals
the imbalance of the original sum. -/
theorem walshTransform_zero_bentDual_add
    (f g : BooleanFunction n) (hf : IsBent f) (hg : IsBent g) :
    walshTransform (bentDual f + bentDual g) 0 =
      walshTransform (f + g) 0 := by
  classical
  let p : ℝ := (2 : ℝ) ^ (n / 2)
  have hn := even_of_isBent f hf
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hpow : p ^ 2 = (2 : ℝ) ^ n := by
    dsimp [p]
    rw [pow_two]
    calc
      (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) =
          (2 : ℝ) ^ (n / 2 + n / 2) := (pow_add _ _ _).symm
      _ = (2 : ℝ) ^ n :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hsplit.symm
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hrawFourier (h : BooleanFunction n) (u : FABL.F₂Cube n) :
      rawFourierTransform (realSignView h) u =
        (walshTransform h u : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hwalshF (u : FABL.F₂Cube n) :
      (walshTransform f u : ℝ) = p * realSignView (bentDual f) u := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf u)
    have hsign :
        (bitSignInt (bentDual f u) : ℝ) = realSignView (bentDual f) u := by
      rw [bitSignInt_cast]
      simp [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hsign, p] using h
  have hwalshG (u : FABL.F₂Cube n) :
      (walshTransform g u : ℝ) = p * realSignView (bentDual g) u := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual g hg u)
    have hsign :
        (bitSignInt (bentDual g u) : ℝ) = realSignView (bentDual g) u := by
      rw [bitSignInt_cast]
      simp [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hsign, p] using h
  have hplancherel :=
    sum_rawFourierTransform_mul (realSignView f) (realSignView g)
  simp_rw [hrawFourier, hwalshF, hwalshG] at hplancherel
  have hscaled :
      p ^ 2 *
          (∑ x, realSignView (bentDual f) x * realSignView (bentDual g) x) =
        (2 : ℝ) ^ n *
          ∑ x, realSignView f x * realSignView g x := by
    calc
      p ^ 2 *
          (∑ x, realSignView (bentDual f) x * realSignView (bentDual g) x) =
          ∑ x, (p * realSignView (bentDual f) x) *
            (p * realSignView (bentDual g) x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = (2 : ℝ) ^ n * ∑ x, realSignView f x * realSignView g x :=
        hplancherel
  rw [hpow] at hscaled
  have hsums :
      (∑ x, realSignView (bentDual f) x * realSignView (bentDual g) x) =
        ∑ x, realSignView f x * realSignView g x :=
    mul_left_cancel₀ hp hscaled
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_cast_eq_sum_realSignView_mul_character,
    walshTransform_cast_eq_sum_realSignView_mul_character]
  simp_rw [realSignView_add]
  simpa using hsums

/-- Bent duality preserves Hamming distance. -/
theorem hammingDistance_bentDual
    (f g : BooleanFunction n) (hf : IsBent f) (hg : IsBent g) :
    hammingDistance (bentDual f) (bentDual g) = hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add,
    hammingDistance_eq_hammingWeight_add]
  have hzero := walshTransform_zero_bentDual_add f g hf hg
  rw [walshTransform_zero_eq_two_pow_sub_two_weight,
    walshTransform_zero_eq_two_pow_sub_two_weight] at hzero
  omega

end CryptBoolean
