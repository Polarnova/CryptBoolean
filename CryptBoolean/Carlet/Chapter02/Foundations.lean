/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.BooleanFunction
public import FABL.Chapter06.F₂Polynomials.ANF

/-!
# Carlet Chapter 2 foundations

Initial representation, weight, and Walsh-transform declarations for Carlet Chapter 2.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The support of a Boolean function, as the finite set on which it is one. -/
abbrev support (f : BooleanFunction n) : Finset (FABL.F₂Cube n) :=
  FABL.f₂OneSupport f

/-- The Hamming weight of a Boolean function. -/
abbrev hammingWeight (f : BooleanFunction n) : ℕ :=
  hammingNorm f

/-- The integer sign `(-1)^b` used in Carlet's raw Walsh sums. -/
def bitSignInt (b : FABL.𝔽₂) : ℤ :=
  (FABL.signEncode b : ℤ)

/-- The real cast of Carlet's integer sign is FABL's additive character. -/
theorem bitSignInt_cast (b : FABL.𝔽₂) :
    (bitSignInt b : ℝ) = FABL.binarySign b := by
  rw [← FABL.signValue_signEncode_eq_binarySign]
  rfl

/-- Casting an integer sign value to `ℝ` agrees with the real sign view. -/
theorem bitSignInt_cast_eq_realSignView
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    (bitSignInt (f x) : ℝ) = realSignView f x := by
  rw [bitSignInt_cast]
  simp [realSignView, FABL.realSignEncodedFunction,
    FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]

/-- The summand `(-1)^{f(x)+a·x}` in Carlet's Walsh transform. -/
def walshTerm (f : BooleanFunction n) (a x : FABL.F₂Cube n) : ℤ :=
  bitSignInt (f x + FABL.f₂DotProduct a x)

/-- Carlet's unnormalized integer Walsh transform. -/
def walshTransform (f : BooleanFunction n) (a : FABL.F₂Cube n) : ℤ :=
  ∑ x, walshTerm f a x

/-- A Boolean function is balanced when exactly half of the binary cube is in its support. -/
def IsBalanced (f : BooleanFunction n) : Prop :=
  2 * hammingWeight f = 2 ^ n

/-- The support predicate is extensionally the one-set of the Boolean function. -/
@[simp] theorem mem_support (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    x ∈ support f ↔ f x = 1 := by
  simp [support, FABL.f₂OneSupport]

/-- On binary-valued functions, Mathlib's Hamming norm is the cardinality of the one-set. -/
theorem hammingWeight_eq_card_support (f : BooleanFunction n) :
    hammingWeight f = (support f).card := by
  exact FABL.hammingNorm_eq_card_f₂OneSupport f

/-- The natural-valued Hamming weight of a binary scalar. -/
def f₂BitWeight (b : FABL.𝔽₂) : ℕ :=
  if b ≠ 0 then 1 else 0

/-- Hamming norm is the sum of the scalar binary weights. -/
theorem hammingNorm_eq_sum_f₂BitWeight
    {ι : Type*} [Fintype ι] (x : ι → FABL.𝔽₂) :
    hammingNorm x = ∑ i, f₂BitWeight (x i) := by
  simp [hammingNorm, f₂BitWeight, Finset.card_filter]

/-- Hamming weight decomposes into the symmetric-difference weight and twice
the common-support weight. -/
theorem hammingNorm_add_restrictSupport_identity
    {ι : Type*} [Fintype ι] (x y : ι → FABL.𝔽₂) :
    hammingNorm (x + y) +
        2 * hammingNorm (fun j : {i : ι // x i ≠ 0} ↦ y j.1) =
      hammingNorm x + hammingNorm y := by
  classical
  have hrestricted :
      (∑ i, if x i ≠ 0 then f₂BitWeight (y i) else 0) =
        hammingNorm (fun j : {i : ι // x i ≠ 0} ↦ y j.1) := by
    rw [hammingNorm_eq_sum_f₂BitWeight, ← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun i ↦ x i ≠ 0)
      (by simp) (fun i ↦ f₂BitWeight (y i))
  rw [hammingNorm_eq_sum_f₂BitWeight (x + y),
    hammingNorm_eq_sum_f₂BitWeight x, hammingNorm_eq_sum_f₂BitWeight y,
    ← hrestricted, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    ∑ i, (f₂BitWeight ((x + y) i) +
        2 * (if x i ≠ 0 then f₂BitWeight (y i) else 0)) =
        ∑ i, (f₂BitWeight (x i) + f₂BitWeight (y i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hx : x i = 0
      · by_cases hy : y i = 0
        · simp [hx, hy, f₂BitWeight]
        · have hyOne : y i = 1 := Fin.eq_one_of_ne_zero _ hy
          simp [hx, hyOne, f₂BitWeight]
      · have hxOne : x i = 1 := Fin.eq_one_of_ne_zero _ hx
        by_cases hy : y i = 0
        · simp [hxOne, hy, f₂BitWeight]
        · have hyOne : y i = 1 := Fin.eq_one_of_ne_zero _ hy
          simp [hxOne, hyOne, f₂BitWeight]
    _ = (∑ i, f₂BitWeight (x i)) + ∑ i, f₂BitWeight (y i) :=
      Finset.sum_add_distrib

/-- The binary cube has cardinality `2^n`. -/
theorem card_f₂Cube (n : ℕ) :
    Fintype.card (FABL.F₂Cube n) = 2 ^ n := by
  exact FABL.card_f₂Cube n

/-- The integer sign encoding is `-1` at one and `1` at zero. -/
theorem bitSignInt_eq_if_one (b : FABL.𝔽₂) :
    bitSignInt b = if b = 1 then -1 else 1 := by
  by_cases hb : b = 1
  · simp [bitSignInt, hb]
  · have hb_zero : b = 0 := by
      by_contra hzero
      exact hb (Fin.eq_one_of_ne_zero b hzero)
    simp [bitSignInt, hb_zero]

/-- The integer sign encoding distinguishes the two binary values. -/
theorem bitSignInt_injective : Function.Injective bitSignInt := by
  intro p q hpq
  apply FABL.binarySign_injective
  rw [← FABL.signValue_signEncode_eq_binarySign,
    ← FABL.signValue_signEncode_eq_binarySign]
  have hunit : FABL.signEncode p = FABL.signEncode q := by
    apply Units.ext
    exact hpq
  exact congrArg FABL.signValue hunit

/-- The integer sign encoding sends binary addition to multiplication. -/
theorem bitSignInt_add (a b : FABL.𝔽₂) :
    bitSignInt (a + b) = bitSignInt a * bitSignInt b := by
  unfold bitSignInt
  rw [FABL.signEncode_add]
  rfl

/-- At zero frequency the Walsh summand is just the sign of the function value. -/
theorem walshTerm_zero (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    walshTerm f 0 x = bitSignInt (f x) := by
  simp [walshTerm, FABL.f₂DotProduct]

/-- The real cast of a raw Walsh summand is the product of the encoded function and character. -/
theorem walshTerm_cast_eq_realSignView_mul_character
    (f : BooleanFunction n) (a x : FABL.F₂Cube n) :
    (walshTerm f a x : ℝ) = realSignView f x * FABL.vectorWalshCharacter a x := by
  rw [walshTerm, bitSignInt, realSignView, FABL.realSignEncodedFunction,
    FABL.signEncodedFunction, FABL.vectorWalshCharacter_apply]
  change FABL.signValue (FABL.signEncode (f x + FABL.f₂DotProduct a x)) =
    FABL.signValue (FABL.signEncode (f x)) * FABL.binarySign (FABL.f₂DotProduct a x)
  rw [FABL.signValue_signEncode_eq_binarySign, FABL.signValue_signEncode_eq_binarySign]
  exact AddChar.map_add_eq_mul FABL.binarySign (f x) (FABL.f₂DotProduct a x)

/-- Carlet's raw Walsh sum equals the unnormalized character-correlation sum. -/
theorem walshTransform_cast_eq_sum_realSignView_mul_character
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (walshTransform f a : ℝ) =
      ∑ x, realSignView f x * FABL.vectorWalshCharacter a x := by
  classical
  simp [walshTransform, walshTerm_cast_eq_realSignView_mul_character]

/-- Carlet's raw Walsh transform is `2^n` times FABL's normalized Fourier coefficient. -/
theorem walshTransform_eq_two_pow_mul_vectorFourierCoeff
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (walshTransform f a : ℝ) =
      (2 ^ n : ℝ) * FABL.vectorFourierCoeff (realSignView f) a := by
  classical
  rw [walshTransform_cast_eq_sum_realSignView_mul_character]
  rw [FABL.vectorFourierCoeff_eq_expect]
  rw [Fintype.expect_eq_sum_div_card]
  rw [card_f₂Cube]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The zero-frequency Walsh value is support complement size minus support size. -/
theorem walshTransform_zero_eq_card_sub_two_weight (f : BooleanFunction n) :
    walshTransform f 0 = (Fintype.card (FABL.F₂Cube n) : ℤ) - 2 * hammingWeight f := by
  classical
  rw [walshTransform]
  calc
    ∑ x, walshTerm f 0 x = ∑ x, (if f x = 1 then (-1 : ℤ) else 1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [walshTerm_zero, bitSignInt_eq_if_one]
    _ = ∑ x : FABL.F₂Cube n, ((1 : ℤ) - 2 * (if f x = 1 then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = 1 <;> simp [hx]
    _ = (∑ _x : FABL.F₂Cube n, (1 : ℤ)) -
        ∑ x : FABL.F₂Cube n, 2 * (if f x = 1 then (1 : ℤ) else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = (Fintype.card (FABL.F₂Cube n) : ℤ) -
        2 * (∑ x : FABL.F₂Cube n, if f x = 1 then (1 : ℤ) else 0) := by
      rw [← Finset.mul_sum]
      simp
    _ = (Fintype.card (FABL.F₂Cube n) : ℤ) - 2 * hammingWeight f := by
      congr 2
      rw [hammingWeight_eq_card_support]
      rw [← Finset.sum_filter]
      simp [support, FABL.f₂OneSupport]

/-- The zero-frequency Walsh value is `2^n - 2 wt(f)`. -/
theorem walshTransform_zero_eq_two_pow_sub_two_weight (f : BooleanFunction n) :
    walshTransform f 0 = (2 ^ n : ℤ) - 2 * hammingWeight f := by
  rw [walshTransform_zero_eq_card_sub_two_weight, card_f₂Cube]
  rfl

/-- A Boolean function is balanced exactly when the zero-frequency Walsh coefficient vanishes. -/
theorem isBalanced_iff_walshTransform_zero_eq_zero (f : BooleanFunction n) :
    IsBalanced f ↔ walshTransform f 0 = 0 := by
  rw [IsBalanced, walshTransform_zero_eq_two_pow_sub_two_weight]
  constructor
  · intro h
    have h' : (2 ^ n : ℤ) = 2 * (hammingWeight f : ℤ) := by
      exact_mod_cast h.symm
    omega
  · intro h
    have h' : (2 * hammingWeight f : ℤ) = (2 ^ n : ℤ) := by
      omega
    exact_mod_cast h'

end CryptBoolean
