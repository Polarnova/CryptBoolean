/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Fourier
public import FABL.Chapter06.F₂Polynomials.BentDegree

/-!
# Walsh divisibility and algebraic degree

Carlet Proposition 11.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The normalized Fourier coefficient of the zero-one embedding is obtained
from the sign embedding by the affine relation `f = (1-χ_f)/2`. -/
theorem vectorFourierCoeff_booleanRealEmbedding_eq
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    FABL.vectorFourierCoeff (FABL.booleanRealEmbedding f) a =
      ((if FABL.f₂Support a = ∅ then 1 else 0) -
        FABL.vectorFourierCoeff (realSignView f) a) / 2 := by
  rw [FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
    FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
  rw [show
      FABL.binaryFunctionOnSignCube (FABL.booleanRealEmbedding f) =
        fun x ↦
          (1 - FABL.binaryFunctionOnSignCube (realSignView f) x) / 2 by
    funext x
    change FABL.booleanRealEmbedding f ((FABL.binaryCubeSignEquiv n).symm x) =
      (1 - FABL.realSignEncodedFunction f
        ((FABL.binaryCubeSignEquiv n).symm x)) / 2
    rw [FABL.realSignEncodedFunction_eq_one_sub_two_booleanRealEmbedding]
    ring]
  exact FABL.fourierCoeff_one_sub_div_two
    (FABL.binaryFunctionOnSignCube (realSignView f)) (FABL.f₂Support a)

/-- Carlet Proposition 11: divisibility of every raw Walsh coefficient by
`2^k` forces algebraic degree at most `n-k+1`. -/
theorem functionAlgebraicDegree_le_of_two_pow_dvd_walshTransform
    (f : BooleanFunction n) (k : ℕ) (_hn : 2 ≤ n) (_hk : 1 ≤ k)
    (hkn : k ≤ n)
    (hdiv : ∀ a : FABL.F₂Cube n, (2 : ℤ) ^ k ∣ walshTransform f a) :
    FABL.functionAlgebraicDegree f ≤ n - k + 1 := by
  apply
    FABL.functionAlgebraicDegree_le_of_isVectorFourierGranular_booleanRealEmbedding
  rw [FABL.isVectorFourierGranular_iff]
  intro a
  obtain ⟨z, hz⟩ := hdiv a
  have hwalsh := walshTransform_eq_two_pow_mul_vectorFourierCoeff f a
  rw [hz] at hwalsh
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hwalsh
  have hpow :
      (2 : ℝ) ^ n = (2 : ℝ) ^ k * (2 : ℝ) ^ (n - k) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (k + (n - k)) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ k * (2 : ℝ) ^ (n - k) := pow_add _ _ _
  rw [hpow] at hwalsh
  have hscale :
      FABL.vectorFourierCoeff (realSignView f) a =
        (z : ℝ) * ((2 : ℝ) ^ (n - k))⁻¹ := by
    have hcancel :
        (z : ℝ) = (2 : ℝ) ^ (n - k) *
          FABL.vectorFourierCoeff (realSignView f) a := by
      apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ k ≠ 0)
      calc
        (2 : ℝ) ^ k * (z : ℝ) =
            (2 : ℝ) ^ k * (2 : ℝ) ^ (n - k) *
              FABL.vectorFourierCoeff (realSignView f) a := hwalsh
        _ = (2 : ℝ) ^ k *
            ((2 : ℝ) ^ (n - k) *
              FABL.vectorFourierCoeff (realSignView f) a) := by ring
    apply (eq_div_iff (by positivity : (2 : ℝ) ^ (n - k) ≠ 0)).2
    calc
      FABL.vectorFourierCoeff (realSignView f) a * (2 : ℝ) ^ (n - k) =
          (2 : ℝ) ^ (n - k) *
            FABL.vectorFourierCoeff (realSignView f) a := mul_comm _ _
      _ = (z : ℝ) := hcancel.symm
  rw [vectorFourierCoeff_booleanRealEmbedding_eq, hscale]
  by_cases ha : FABL.f₂Support a = ∅
  · refine ⟨(2 : ℤ) ^ (n - k) - z, ?_⟩
    rw [if_pos ha]
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    rw [pow_succ]
    field_simp
  · refine ⟨-z, ?_⟩
    rw [if_neg ha]
    simp only [Int.cast_neg]
    rw [pow_succ]
    field_simp
    ring

end CryptBoolean
