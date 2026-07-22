/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AlgebraicDegree
public import FABL.Chapter06.F₂Polynomials.Affine

/-!
# Carlet Chapter 2 affine Boolean functions

FABL Chapter 6 owns affine functions, their canonical ANF, the degree-one characterization, and
affine invariance. This module retains Carlet's sign, balancedness, weight, and raw-distance
consequences.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The real sign view of an affine function is a constant sign times a Walsh character. -/
theorem realSignView_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (x : FABL.F₂Cube n) :
    realSignView (FABL.affineFunction b a) x =
      FABL.binarySign b * FABL.vectorWalshCharacter a x := by
  rw [realSignView, FABL.realSignEncodedFunction, FABL.signEncodedFunction,
    FABL.affineFunction, FABL.signValue_signEncode_eq_binarySign,
    FABL.vectorWalshCharacter_apply]
  exact AddChar.map_add_eq_mul FABL.binarySign b (FABL.f₂DotProduct a x)

/-- A nonconstant affine Boolean function is balanced. -/
theorem isBalanced_affineFunction_of_ne_zero
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    IsBalanced (FABL.affineFunction b a) := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, walshTransform_cast_eq_sum_realSignView_mul_character]
  simp_rw [realSignView_affineFunction]
  have hexpect := FABL.expect_vectorWalshCharacter a
  rw [if_neg ha] at hexpect
  rw [Fintype.expect_eq_sum_div_card] at hexpect
  have hsum : ∑ x, FABL.vectorWalshCharacter a x = 0 := by
    have hcard : (Fintype.card (FABL.F₂Cube n) : ℝ) ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp hexpect).resolve_right hcard
  calc
    ∑ x, FABL.binarySign b * FABL.vectorWalshCharacter a x *
        FABL.vectorWalshCharacter 0 x =
        FABL.binarySign b * ∑ x, FABL.vectorWalshCharacter a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = 0 := by rw [hsum, mul_zero]

/-- A nonconstant affine Boolean function has weight `2^(n-1)`. -/
theorem hammingWeight_affineFunction_of_ne_zero
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    hammingWeight (FABL.affineFunction b a) = 2 ^ (n - 1) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    apply ha
    funext i
    exact Fin.elim0 i
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hbalanced := isBalanced_affineFunction_of_ne_zero b a ha
  change 2 * hammingWeight (FABL.affineFunction b a) = 2 ^ (m + 1) at hbalanced
  rw [pow_succ] at hbalanced
  simp only [Nat.succ_sub_one]
  omega

/-- Raw distance scales FABL's relative Hamming distance by the cube cardinality. -/
theorem hammingDistance_eq_two_pow_mul_relativeHammingDist
    (f g : BooleanFunction n) :
    (hammingDistance f g : ℝ) =
      (2 ^ n : ℝ) * FABL.relativeHammingDist f g := by
  rw [hammingDistance, FABL.relativeHammingDist, card_f₂Cube]
  norm_num
  field_simp

end CryptBoolean
