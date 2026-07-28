/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Derivatives

/-!
# Carlet Chapter 5 covering sequences

Integer-valued covering and partial covering sequences, together with their raw Walsh identities.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The canonical integer value of a binary scalar. -/
def bitValueInt (b : FABL.𝔽₂) : ℤ :=
  if b = 1 then 1 else 0

/-- The unnormalized integer Walsh transform of an integer-valued cube function. -/
def integerWalshTransform (coeff : FABL.F₂Cube n → ℤ) (b : FABL.F₂Cube n) : ℤ :=
  ∑ a, coeff a * bitSignInt (FABL.f₂DotProduct a b)

/-- The integer sum of the derivatives weighted by a sequence. -/
def weightedDerivativeSum (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ)
    (x : FABL.F₂Cube n) : ℤ :=
  ∑ a, coeff a * bitValueInt (FABL.booleanDerivative f a x)

/-- An integer sequence covers `f` at level `ρ` when its weighted derivative sum is constant. -/
def IsCoveringSequence (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ) : Prop :=
  ∀ x, weightedDerivativeSum f coeff x = ρ

/-- A partial covering sequence has a weighted derivative sum taking at most two levels. -/
def IsPartialCoveringSequence (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ)
    (ρ ρ' : ℤ) : Prop :=
  ∀ x, weightedDerivativeSum f coeff x = ρ ∨ weightedDerivativeSum f coeff x = ρ'

/-- The exceptional level set in Carlet's partial-covering identity. -/
def partialCoveringExceptionalSet (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ)
    (ρ ρ' : ℤ) : Finset (FABL.F₂Cube n) :=
  if ρ' = ρ then ∅ else Finset.univ.filter fun x ↦ weightedDerivativeSum f coeff x = ρ'

/-- The sequence-weighted sum of translated signs used in the covering proofs. -/
def weightedTranslatedSignSum (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ)
    (x : FABL.F₂Cube n) : ℤ :=
  ∑ a, coeff a * bitSignInt (f (x + a))

theorem bitSignInt_eq_one_sub_two_mul_bitValueInt (b : FABL.𝔽₂) :
    bitSignInt b = 1 - 2 * bitValueInt b := by
  rw [bitSignInt_eq_if_one]
  by_cases hb : b = 1 <;> simp [bitValueInt, hb]

@[simp] theorem bitSignInt_mul_self (b : FABL.𝔽₂) :
    bitSignInt b * bitSignInt b = 1 := by
  fin_cases b <;> rfl

@[simp] theorem integerWalshTransform_zero (coeff : FABL.F₂Cube n → ℤ) :
    integerWalshTransform coeff 0 = ∑ a, coeff a := by
  simp [integerWalshTransform, FABL.f₂DotProduct, bitSignInt]

theorem bitSignInt_booleanDerivative_mul_left
    (f : BooleanFunction n) (a x : FABL.F₂Cube n) :
    bitSignInt (f (x + a)) =
      bitSignInt (f x) * bitSignInt (FABL.booleanDerivative f a x) := by
  rw [FABL.booleanDerivative, bitSignInt_add]
  rw [← mul_assoc, bitSignInt_mul_self, one_mul]

/-- The shared pointwise sign identity underlying both covering theorems. -/
theorem weightedTranslatedSignSum_eq
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (x : FABL.F₂Cube n) :
    weightedTranslatedSignSum f coeff x =
      bitSignInt (f x) *
        (integerWalshTransform coeff 0 - 2 * weightedDerivativeSum f coeff x) := by
  classical
  rw [weightedTranslatedSignSum, weightedDerivativeSum, integerWalshTransform_zero]
  calc
    ∑ a, coeff a * bitSignInt (f (x + a)) =
        ∑ a, coeff a *
          (bitSignInt (f x) * bitSignInt (FABL.booleanDerivative f a x)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [bitSignInt_booleanDerivative_mul_left]
    _ = bitSignInt (f x) *
        ∑ a, coeff a * bitSignInt (FABL.booleanDerivative f a x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = bitSignInt (f x) *
        ((∑ a, coeff a) - 2 * ∑ a, coeff a *
          bitValueInt (FABL.booleanDerivative f a x)) := by
      congr 1
      simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt]
      calc
        ∑ a, coeff a *
            (1 - 2 * bitValueInt (FABL.booleanDerivative f a x)) =
            ∑ a, (coeff a - 2 *
              (coeff a * bitValueInt (FABL.booleanDerivative f a x))) := by
          apply Finset.sum_congr rfl
          intro a _ha
          ring
        _ = (∑ a, coeff a) - 2 * ∑ a, coeff a *
            bitValueInt (FABL.booleanDerivative f a x) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Transforming a sign-weighted integer function inserts the Walsh summand. -/
theorem integerWalshTransform_mul_bitSignInt
    (f : BooleanFunction n) (κ : FABL.F₂Cube n → ℤ) (b : FABL.F₂Cube n) :
    integerWalshTransform (fun x ↦ κ x * bitSignInt (f x)) b =
      ∑ x, κ x * walshTerm f b x := by
  classical
  unfold integerWalshTransform walshTerm
  apply Finset.sum_congr rfl
  intro x _hx
  rw [bitSignInt_add]
  rw [show FABL.f₂DotProduct x b = FABL.f₂DotProduct b x by
    exact dotProduct_comm x b]
  ring

private theorem sum_translated_bitSignInt_mul_character
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) :
    (∑ x, bitSignInt (f (x + a)) *
        bitSignInt (FABL.f₂DotProduct x b)) =
      bitSignInt (FABL.f₂DotProduct a b) * walshTransform f b := by
  classical
  rw [← Equiv.sum_comp (Equiv.addRight a)]
  apply Eq.trans _ (Finset.mul_sum _ _ _).symm
  apply Finset.sum_congr rfl
  intro x _hx
  change bitSignInt (f ((x + a) + a)) *
      bitSignInt (FABL.f₂DotProduct (x + a) b) =
    bitSignInt (FABL.f₂DotProduct a b) * walshTerm f b x
  rw [show (x + a) + a = x by
    rw [add_assoc, ZModModule.add_self, add_zero]]
  rw [show FABL.f₂DotProduct (x + a) b =
      FABL.f₂DotProduct x b + FABL.f₂DotProduct a b by
    exact add_dotProduct x a b]
  rw [bitSignInt_add, walshTerm, bitSignInt_add]
  rw [show FABL.f₂DotProduct x b = FABL.f₂DotProduct b x by
    exact dotProduct_comm x b]
  ring

/-- The Walsh transform of the weighted translated-sign sum factors pointwise. -/
theorem integerWalshTransform_weightedTranslatedSignSum
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (b : FABL.F₂Cube n) :
    integerWalshTransform (weightedTranslatedSignSum f coeff) b =
      integerWalshTransform coeff b * walshTransform f b := by
  classical
  unfold integerWalshTransform weightedTranslatedSignSum
  calc
    ∑ x, (∑ a, coeff a * bitSignInt (f (x + a))) *
        bitSignInt (FABL.f₂DotProduct x b) =
        ∑ x, ∑ a, coeff a * bitSignInt (f (x + a)) *
          bitSignInt (FABL.f₂DotProduct x b) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ x, coeff a * bitSignInt (f (x + a)) *
        bitSignInt (FABL.f₂DotProduct x b) := by
      rw [Finset.sum_comm]
    _ =
        ∑ a, coeff a *
          (∑ x, bitSignInt (f (x + a)) *
            bitSignInt (FABL.f₂DotProduct x b)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ a, coeff a *
        (bitSignInt (FABL.f₂DotProduct a b) * walshTransform f b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [sum_translated_bitSignInt_mul_character]
    _ = (∑ a, coeff a * bitSignInt (FABL.f₂DotProduct a b)) *
        walshTransform f b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

/-- Multiplying the sign of a Boolean function by a constant scales its Walsh transform. -/
theorem integerWalshTransform_const_mul_bitSignInt
    (f : BooleanFunction n) (c : ℤ) (b : FABL.F₂Cube n) :
    integerWalshTransform (fun x ↦ c * bitSignInt (f x)) b =
      c * walshTransform f b := by
  rw [integerWalshTransform_mul_bitSignInt]
  rw [← Finset.mul_sum]
  rfl

private theorem bitSignInt_f₂DotProduct_cast
    (a b : FABL.F₂Cube n) :
    (bitSignInt (FABL.f₂DotProduct a b) : ℝ) =
      FABL.vectorWalshCharacter b a := by
  rw [show FABL.f₂DotProduct a b = FABL.f₂DotProduct b a by
    exact dotProduct_comm a b]
  rw [FABL.vectorWalshCharacter_apply]
  rw [bitSignInt, ← FABL.signValue_signEncode_eq_binarySign]
  rfl

/-- Casting the integer transform to the reals recovers Chapter 2's raw transform. -/
theorem integerWalshTransform_cast_eq_rawFourierTransform
    (coeff : FABL.F₂Cube n → ℤ) (b : FABL.F₂Cube n) :
    (integerWalshTransform coeff b : ℝ) =
      rawFourierTransform (fun x ↦ (coeff x : ℝ)) b := by
  classical
  rw [integerWalshTransform, rawFourierTransform]
  push_cast
  apply Finset.sum_congr rfl
  intro x _hx
  rw [bitSignInt_f₂DotProduct_cast]

/-- The integer Walsh transform is involutive up to multiplication by the cube cardinality. -/
theorem integerWalshTransform_involution
    (coeff : FABL.F₂Cube n → ℤ) (x : FABL.F₂Cube n) :
    integerWalshTransform (integerWalshTransform coeff) x =
      (2 ^ n : ℤ) * coeff x := by
  apply Int.cast_injective (α := ℝ)
  rw [integerWalshTransform_cast_eq_rawFourierTransform]
  have hfun : (fun b ↦ (integerWalshTransform coeff b : ℝ)) =
      rawFourierTransform (fun y ↦ (coeff y : ℝ)) := by
    funext b
    exact integerWalshTransform_cast_eq_rawFourierTransform coeff b
  rw [hfun, rawFourierTransform_involution]
  norm_num

/-- Equality of integer Walsh transforms implies equality of the original functions. -/
theorem integerWalshTransform_injective :
    Function.Injective
      (integerWalshTransform : (FABL.F₂Cube n → ℤ) → FABL.F₂Cube n → ℤ) := by
  intro coeff₁ coeff₂ htransform
  funext x
  have hinvolutive := congrFun
    (congrArg (integerWalshTransform :
      (FABL.F₂Cube n → ℤ) → FABL.F₂Cube n → ℤ) htransform) x
  rw [integerWalshTransform_involution, integerWalshTransform_involution] at hinvolutive
  exact mul_left_cancel₀ (by positivity : (2 ^ n : ℤ) ≠ 0) hinvolutive

/-- Carlet's Walsh-support characterization of a covering sequence. -/
theorem isCoveringSequence_iff_integerWalshTransform
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ) :
    IsCoveringSequence f coeff ρ ↔
      ∀ b, (integerWalshTransform coeff b - integerWalshTransform coeff 0 + 2 * ρ) *
        walshTransform f b = 0 := by
  constructor
  · intro hcover b
    have hpoint : weightedTranslatedSignSum f coeff =
        fun x ↦ (integerWalshTransform coeff 0 - 2 * ρ) * bitSignInt (f x) := by
      funext x
      rw [weightedTranslatedSignSum_eq, hcover x]
      ring
    have htransform := congrArg (fun g : FABL.F₂Cube n → ℤ ↦
      integerWalshTransform g b) hpoint
    rw [integerWalshTransform_weightedTranslatedSignSum,
      integerWalshTransform_const_mul_bitSignInt] at htransform
    calc
      (integerWalshTransform coeff b - integerWalshTransform coeff 0 + 2 * ρ) *
          walshTransform f b =
          integerWalshTransform coeff b * walshTransform f b -
            (integerWalshTransform coeff 0 - 2 * ρ) * walshTransform f b := by ring
      _ = 0 := sub_eq_zero.mpr htransform
  · intro hspectrum
    let c : ℤ := integerWalshTransform coeff 0 - 2 * ρ
    have hpoint : weightedTranslatedSignSum f coeff =
        fun x ↦ c * bitSignInt (f x) := by
      apply integerWalshTransform_injective
      funext b
      rw [integerWalshTransform_weightedTranslatedSignSum,
        integerWalshTransform_const_mul_bitSignInt]
      have hb := hspectrum b
      dsimp [c]
      linear_combination hb
    intro x
    have hx := congrFun hpoint x
    rw [weightedTranslatedSignSum_eq] at hx
    have hsign : bitSignInt (f x) ≠ 0 := by
      intro hzero
      have hsquare := bitSignInt_mul_self (f x)
      rw [hzero] at hsquare
      norm_num at hsquare
    have hinner :
        integerWalshTransform coeff 0 - 2 * weightedDerivativeSum f coeff x = c := by
      apply mul_left_cancel₀ hsign
      simpa [mul_comm] using hx
    dsimp [c] at hinner
    omega

/-- Conditional form of the covering characterization on the Walsh support. -/
theorem isCoveringSequence_iff_transform_eq_on_walshSupport
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ) :
    IsCoveringSequence f coeff ρ ↔
      ∀ b, walshTransform f b ≠ 0 →
        integerWalshTransform coeff b = integerWalshTransform coeff 0 - 2 * ρ := by
  rw [isCoveringSequence_iff_integerWalshTransform]
  constructor
  · intro hspectrum b hb
    have hproduct := hspectrum b
    have hzero := (mul_eq_zero.mp hproduct).resolve_right hb
    omega
  · intro hsupport b
    by_cases hb : walshTransform f b = 0
    · simp [hb]
    · rw [hsupport b hb]
      ring

private theorem weightedTranslatedSignSum_eq_partial
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ ρ' : ℤ)
    (hpartial : IsPartialCoveringSequence f coeff ρ ρ')
    (x : FABL.F₂Cube n) :
    weightedTranslatedSignSum f coeff x =
      (integerWalshTransform coeff 0 - 2 * ρ) * bitSignInt (f x) +
        2 * (ρ - ρ') *
          (if x ∈ partialCoveringExceptionalSet f coeff ρ ρ' then
            bitSignInt (f x) else 0) := by
  rw [weightedTranslatedSignSum_eq]
  by_cases hlevels : ρ' = ρ
  · have hsum : weightedDerivativeSum f coeff x = ρ :=
      (hpartial x).elim id fun h ↦ h.trans hlevels
    rw [hsum]
    simp [partialCoveringExceptionalSet, hlevels]
    ring
  · by_cases hexceptional : weightedDerivativeSum f coeff x = ρ'
    · rw [hexceptional]
      simp [partialCoveringExceptionalSet, hlevels, hexceptional]
      ring
    · have hsum : weightedDerivativeSum f coeff x = ρ :=
        (hpartial x).resolve_right hexceptional
      rw [hsum]
      simp [partialCoveringExceptionalSet, hlevels, hexceptional]
      ring

private theorem integerWalshTransform_partialSign
    (f : BooleanFunction n) (A : Finset (FABL.F₂Cube n))
    (c d : ℤ) (b : FABL.F₂Cube n) :
    integerWalshTransform
        (fun x ↦ c * bitSignInt (f x) +
          d * (if x ∈ A then bitSignInt (f x) else 0)) b =
      c * walshTransform f b + d * ∑ x ∈ A, walshTerm f b x := by
  classical
  rw [show (fun x ↦ c * bitSignInt (f x) +
      d * (if x ∈ A then bitSignInt (f x) else 0)) =
      fun x ↦ (c + if x ∈ A then d else 0) * bitSignInt (f x) by
    funext x
    by_cases hx : x ∈ A
    · simp only [hx, if_pos]
      ring
    · simp only [hx, if_false, mul_zero, add_zero]]
  rw [integerWalshTransform_mul_bitSignInt]
  calc
    ∑ x, (c + if x ∈ A then d else 0) * walshTerm f b x =
        ∑ x, (c * walshTerm f b x +
          if x ∈ A then d * walshTerm f b x else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : x ∈ A
      · simp only [hx, if_pos]
        ring
      · simp only [hx, if_false, add_zero]
    _ = c * walshTransform f b + d * ∑ x ∈ A, walshTerm f b x := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [walshTransform, Finset.mul_sum]

/-- Carlet Theorem 6: the raw spectral identity supplied by a partial covering sequence. -/
theorem theorem_6_partialCoveringSequence
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ ρ' : ℤ)
    (hpartial : IsPartialCoveringSequence f coeff ρ ρ')
    (b : FABL.F₂Cube n) :
    (integerWalshTransform coeff b - integerWalshTransform coeff 0 + 2 * ρ) *
        walshTransform f b =
      2 * (ρ - ρ') *
        ∑ x ∈ partialCoveringExceptionalSet f coeff ρ ρ', walshTerm f b x := by
  have hpoint : weightedTranslatedSignSum f coeff =
      fun x ↦ (integerWalshTransform coeff 0 - 2 * ρ) * bitSignInt (f x) +
        2 * (ρ - ρ') *
          (if x ∈ partialCoveringExceptionalSet f coeff ρ ρ' then
            bitSignInt (f x) else 0) := by
    funext x
    exact weightedTranslatedSignSum_eq_partial f coeff ρ ρ' hpartial x
  have htransform := congrArg (fun g : FABL.F₂Cube n → ℤ ↦
    integerWalshTransform g b) hpoint
  rw [integerWalshTransform_weightedTranslatedSignSum,
    integerWalshTransform_partialSign] at htransform
  linear_combination htransform

/-- Division-free form of the weight consequence of Carlet Theorem 6. -/
theorem theorem_6_weight_identity
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ ρ' : ℤ)
    (hpartial : IsPartialCoveringSequence f coeff ρ ρ') :
    ρ * walshTransform f 0 =
      (ρ - ρ') *
        ∑ x ∈ partialCoveringExceptionalSet f coeff ρ ρ', bitSignInt (f x) := by
  have hzero := theorem_6_partialCoveringSequence f coeff ρ ρ' hpartial 0
  simp_rw [walshTerm_zero] at hzero
  simp only [integerWalshTransform_zero] at hzero
  have hdouble :
      2 * (ρ * walshTransform f 0) =
        2 * ((ρ - ρ') *
          ∑ x ∈ partialCoveringExceptionalSet f coeff ρ ρ', bitSignInt (f x)) := by
    linear_combination hzero
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hdouble

end CryptBoolean
