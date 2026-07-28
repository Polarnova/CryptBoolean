/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.TracePairing
public import CryptBoolean.Carlet.Chapter04.Nonlinearity

/-!
# Trace-pairing reduction for finite-field Walsh bounds

This module isolates the representation step reducing raw Walsh coefficients of binary trace
polynomials to complete additive-character sums. The analytic character-sum estimate is an
explicit hypothesis.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance binaryGaloisFieldFintype :
    Fintype (BinaryGaloisField n) :=
  Fintype.ofFinite (BinaryGaloisField n)

/-- The Boolean function obtained by applying the binary absolute trace to a scaled polynomial. -/
noncomputable def tracePolynomialBooleanFunction
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (P : (BinaryGaloisField n)[X]) :
    BooleanFunction n :=
  fun x ↦ absoluteTrace n (a * P.eval (theta x))

/-- The unnormalized integer additive-character sum attached to a scaled finite-field polynomial. -/
noncomputable def tracePolynomialCharacterSum
    (a : BinaryGaloisField n) (P : (BinaryGaloisField n)[X]) : ℤ :=
  ∑ y : BinaryGaloisField n, bitSignInt (absoluteTrace n (a * P.eval y))

/-- A raw Walsh coefficient of a binary trace polynomial is a complete additive-character sum;
the Walsh linear term becomes `b / a` times `X`. -/
theorem exists_tracePolynomialCharacterSum_eq_walshTransform
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (ha : a ≠ 0)
    (P : (BinaryGaloisField n)[X]) (u : FABL.F₂Cube n) :
    ∃ b : BinaryGaloisField n,
      (∀ x, FABL.f₂DotProduct u x = absoluteTrace n (b * theta x)) ∧
      walshTransform (tracePolynomialBooleanFunction theta a P) u =
        tracePolynomialCharacterSum a (P + C (b / a) * X) := by
  obtain ⟨b, hb, _hbUnique⟩ := existsUnique_tracePairingCoefficient theta u
  refine ⟨b, hb, ?_⟩
  unfold walshTransform tracePolynomialCharacterSum
  apply Fintype.sum_equiv theta.toEquiv
  intro x
  unfold walshTerm tracePolynomialBooleanFunction
  rw [hb x]
  congr 1
  rw [← map_add]
  congr 1
  simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [mul_add, ← mul_assoc, mul_div_cancel₀ b ha]
  rfl

/-- A uniform bound for every linear perturbation of a finite-field polynomial bounds the maximum
raw Walsh magnitude of its binary trace function. -/
theorem maxWalshMagnitude_tracePolynomialBooleanFunction_le
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (ha : a ≠ 0)
    (P : (BinaryGaloisField n)[X]) (B : ℝ)
    (hcharacter : ∀ c : BinaryGaloisField n,
      |(tracePolynomialCharacterSum a (P + C c * X) : ℝ)| ≤ B) :
    (maxWalshMagnitude (tracePolynomialBooleanFunction theta a P) : ℝ) ≤ B := by
  rw [maxWalshMagnitude, Nat.cast_finsetSup']
  apply Finset.sup'_le
  intro u _hu
  obtain ⟨b, _hb, hwalsh⟩ :=
    exists_tracePolynomialCharacterSum_eq_walshTransform theta a ha P u
  rw [Nat.cast_natAbs, Int.cast_abs, hwalsh]
  exact hcharacter (b / a)

/-- Division-free nonlinearity lower bound obtained from a uniform complete character-sum bound. -/
theorem two_pow_le_two_mul_nonlinearity_add_of_tracePolynomialCharacterSum_le
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (ha : a ≠ 0)
    (P : (BinaryGaloisField n)[X]) (B : ℝ)
    (hcharacter : ∀ c : BinaryGaloisField n,
      |(tracePolynomialCharacterSum a (P + C c * X) : ℝ)| ≤ B) :
    (2 ^ n : ℝ) ≤
      2 * (nonlinearity (tracePolynomialBooleanFunction theta a P) : ℝ) + B := by
  have hmax :=
    maxWalshMagnitude_tracePolynomialBooleanFunction_le theta a ha P B hcharacter
  have hrelation := congrArg (fun k : ℕ ↦ (k : ℝ))
    (two_mul_nonlinearity_add_maxWalshMagnitude
      (tracePolynomialBooleanFunction theta a P))
  push_cast at hrelation
  linarith

/-- Real-valued half-factor form of the nonlinearity reduction. -/
theorem tracePolynomialCharacterSum_nonlinearity_lower_bound
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (ha : a ≠ 0)
    (P : (BinaryGaloisField n)[X]) (B : ℝ)
    (hcharacter : ∀ c : BinaryGaloisField n,
      |(tracePolynomialCharacterSum a (P + C c * X) : ℝ)| ≤ B) :
    (2 ^ n : ℝ) / 2 - B / 2 ≤
      (nonlinearity (tracePolynomialBooleanFunction theta a P) : ℝ) := by
  have h :=
    two_pow_le_two_mul_nonlinearity_add_of_tracePolynomialCharacterSum_le
      theta a ha P B hcharacter
  linarith

end CryptBoolean
