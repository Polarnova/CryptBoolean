/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierNNF
public import CryptBoolean.Carlet.Chapter06.Dual
public import CryptBoolean.Carlet.Chapter06.ThreeFunctionIdentity

/-!
# Numerical normal form of the bent dual

Carlet Section 6.1: the pointwise relation deriving the numerical normal form
of the dual from the numerical coefficients of a bent function.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The zero-one embedding of the dual is an affine rescaling of the raw
Fourier transform of the zero-one embedding of the original bent function. -/
theorem booleanRealEmbedding_bentDual_eq_rawFourierTransform
    (f : BooleanFunction n) (hf : IsBent f) (x : FABL.F₂Cube n) :
    FABL.booleanRealEmbedding (bentDual f) x =
      (1 : ℝ) / 2 -
        (if x = 0 then (2 : ℝ) ^ (n / 2) / 2 else 0) +
        rawFourierTransform (FABL.booleanRealEmbedding f) x /
          (2 : ℝ) ^ (n / 2) := by
  have hn := even_of_isBent f hf
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hpow : (2 : ℝ) ^ n =
      (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2 + n / 2) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hsplit
      _ = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := pow_add _ _ _
  have hrawInt :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf x
  have hraw := congrArg (fun z : ℤ ↦ (z : ℝ)) hrawInt
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hraw
  have hsign :
      (bitSignInt (bentDual f x) : ℝ) = realSignView (bentDual f) x := by
    rw [bitSignInt_cast]
    simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
  rw [hsign] at hraw
  have hdualEmbedding := congrFun
    (FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding
      (bentDual f)) x
  change realSignView (bentDual f) x =
    1 - 2 * FABL.booleanRealEmbedding (bentDual f) x at hdualEmbedding
  rw [hdualEmbedding] at hraw
  have hwalsh :=
    walshTransform_cast_eq_rawFourierTransform_sub_two_mul f x
  rw [rawFourierTransform_one] at hwalsh
  by_cases hx : x = 0
  · rw [if_pos hx] at hwalsh ⊢
    rw [hpow] at hwalsh
    rw [hwalsh] at hraw
    field_simp
    nlinarith
  · rw [if_neg hx] at hwalsh ⊢
    rw [hwalsh] at hraw
    field_simp
    nlinarith

/-- Carlet's dual-NNF relation in the canonical coefficient notation. -/
theorem booleanRealEmbedding_bentDual_eq_numericalCoeff_sum
    (f : BooleanFunction n) (hf : IsBent f) (x : FABL.F₂Cube n) :
    FABL.booleanRealEmbedding (bentDual f) x =
      (1 : ℝ) / 2 -
        (if x = 0 then (2 : ℝ) ^ (n / 2) / 2 else 0) +
        ((-1 : ℝ) ^ (FABL.f₂Support x).card *
          ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
            FABL.f₂Support x ⊆ S),
              (2 : ℝ) ^ (n - S.card) *
                FABL.numericalCoeff (FABL.booleanRealEmbedding f) S) /
          (2 : ℝ) ^ (n / 2) := by
  rw [booleanRealEmbedding_bentDual_eq_rawFourierTransform f hf x]
  have heval :=
    FABL.numericalEval_numericalCoeff (FABL.booleanRealEmbedding f)
  nth_rewrite 1 [← heval]
  rw [rawFourierTransform_numericalEval]

end CryptBoolean
