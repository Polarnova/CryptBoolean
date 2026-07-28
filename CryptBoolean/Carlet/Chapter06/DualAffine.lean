/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.DualIsometry
import CryptBoolean.Carlet.Chapter05.Affine

/-!
# Bent duals under affine input and output shifts

Carlet Section 6.1: the affine action on bent duals and Relation (45).
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Translating the input of a bent Boolean function preserves bentness. -/
theorem isBent_domainTranslate
    (f : BooleanFunction n) (hf : IsBent f) (b : FABL.F₂Cube n) :
    IsBent (FABL.domainTranslate f b) := by
  have h := (isBent_comp_affineEquiv_iff f
    (AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube n) b)).2 hf
  convert h using 1
  funext x
  simp [FABL.domainTranslate_apply, add_comm]

/-- Translating a bent function and adding a linear function preserves bentness. -/
theorem isBent_domainTranslate_add_linear
    (f : BooleanFunction n) (hf : IsBent f) (b a : FABL.F₂Cube n) :
    IsBent (FABL.domainTranslate f b + FABL.affineFunction 0 a) :=
  (isBent_add_affineFunction_iff (FABL.domainTranslate f b) 0 a).2
    (isBent_domainTranslate f hf b)

/-- Carlet's affine action on bent duals. -/
theorem bentDual_domainTranslate_add_linear
    (f : BooleanFunction n) (hf : IsBent f) (b a x : FABL.F₂Cube n) :
    bentDual (FABL.domainTranslate f b + FABL.affineFunction 0 a) x =
      bentDual f (x + a) + FABL.f₂DotProduct b (x + a) := by
  let g := FABL.domainTranslate f b + FABL.affineFunction 0 a
  have hg : IsBent g := isBent_domainTranslate_add_linear f hf b a
  have hshift :
      walshTransform g x =
        walshTransform (FABL.domainTranslate f b) (x + a) := by
    dsimp [g]
    rw [walshTransform_add_affineFunction]
    simp [bitSignInt_eq_if_one]
  have hshiftReal :
      (walshTransform g x : ℝ) =
        (walshTransform (FABL.domainTranslate f b) (x + a) : ℝ) :=
    congrArg (fun z : ℤ ↦ (z : ℝ)) hshift
  have htranslate := walshTransform_domainTranslate_cast f b (x + a)
  have hdualG := congrArg (fun z : ℤ ↦ (z : ℝ))
    (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual g hg x)
  have hdualF := congrArg (fun z : ℤ ↦ (z : ℝ))
    (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf (x + a))
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hdualG hdualF
  have hcharacter :
      FABL.vectorWalshCharacter (x + a) b =
        (bitSignInt (FABL.f₂DotProduct b (x + a)) : ℝ) := by
    rw [FABL.vectorWalshCharacter_apply]
    rw [show FABL.f₂DotProduct (x + a) b =
        FABL.f₂DotProduct b (x + a) by exact dotProduct_comm _ _]
    exact (bitSignInt_cast _).symm
  have hscaled :
      (2 : ℝ) ^ (n / 2) * (bitSignInt (bentDual g x) : ℝ) =
        (2 : ℝ) ^ (n / 2) *
          (bitSignInt
            (bentDual f (x + a) + FABL.f₂DotProduct b (x + a)) : ℝ) := by
    calc
      (2 : ℝ) ^ (n / 2) * (bitSignInt (bentDual g x) : ℝ) =
          (walshTransform g x : ℝ) := hdualG.symm
      _ = (walshTransform (FABL.domainTranslate f b) (x + a) : ℝ) := hshiftReal
      _ = FABL.vectorWalshCharacter (x + a) b *
          (walshTransform f (x + a) : ℝ) := htranslate
      _ = (bitSignInt (FABL.f₂DotProduct b (x + a)) : ℝ) *
          ((2 : ℝ) ^ (n / 2) *
            (bitSignInt (bentDual f (x + a)) : ℝ)) := by
        rw [hcharacter, hdualF]
      _ = (2 : ℝ) ^ (n / 2) *
          ((bitSignInt (bentDual f (x + a)) : ℝ) *
            (bitSignInt (FABL.f₂DotProduct b (x + a)) : ℝ)) := by
        ring
      _ = (2 : ℝ) ^ (n / 2) *
          (bitSignInt
            (bentDual f (x + a) + FABL.f₂DotProduct b (x + a)) : ℝ) := by
        rw [bitSignInt_add]
        push_cast
        rfl
  have hsignReal :
      (bitSignInt (bentDual g x) : ℝ) =
        (bitSignInt
          (bentDual f (x + a) + FABL.f₂DotProduct b (x + a)) : ℝ) :=
    mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (n / 2) ≠ 0) hscaled
  apply bitSignInt_injective
  exact_mod_cast hsignReal

/-- Carlet Relation (45): the two derivative-linear sums have equal imbalance. -/
theorem walshTransform_zero_bentDual_derivative_add_linear
    (f : BooleanFunction n) (hf : IsBent f) (a b : FABL.F₂Cube n) :
    walshTransform
        (FABL.booleanDerivative (bentDual f) a + FABL.affineFunction 0 b) 0 =
      walshTransform (FABL.booleanDerivative f b + FABL.affineFunction 0 a) 0 := by
  let translated := FABL.domainTranslate f b
  let linearShift := f + FABL.affineFunction 0 a
  have htranslated : IsBent translated := isBent_domainTranslate f hf b
  have hlinearShift : IsBent linearShift :=
    (isBent_add_affineFunction_iff f 0 a).2 hf
  have hrelation := walshTransform_zero_bentDual_add
    translated linearShift htranslated hlinearShift
  have hdualTranslated :
      bentDual translated = bentDual f + FABL.affineFunction 0 b := by
    funext x
    have h := bentDual_domainTranslate_add_linear f hf b 0 x
    have hinput :
        FABL.domainTranslate f b + FABL.affineFunction 0 0 =
          FABL.domainTranslate f b := by
      funext y
      simp [FABL.affineFunction, FABL.f₂DotProduct]
    rw [hinput] at h
    simpa [translated, FABL.affineFunction] using h
  have hdualLinearShift :
      bentDual linearShift = FABL.domainTranslate (bentDual f) a := by
    funext x
    have h := bentDual_domainTranslate_add_linear f hf 0 a x
    have hinput :
        FABL.domainTranslate f 0 + FABL.affineFunction 0 a =
          f + FABL.affineFunction 0 a := by
      funext y
      simp [FABL.domainTranslate_apply]
    rw [hinput] at h
    simpa [linearShift, FABL.affineFunction, FABL.domainTranslate,
      FABL.f₂DotProduct] using h
  have hleft :
      bentDual translated + bentDual linearShift =
        FABL.booleanDerivative (bentDual f) a + FABL.affineFunction 0 b := by
    funext x
    rw [hdualTranslated, hdualLinearShift]
    simp only [Pi.add_apply, FABL.booleanDerivative, FABL.domainTranslate_apply,
      FABL.affineFunction, zero_add]
    ac_rfl
  have hright :
      translated + linearShift =
        FABL.booleanDerivative f b + FABL.affineFunction 0 a := by
    funext x
    simp only [translated, linearShift, Pi.add_apply, FABL.domainTranslate_apply,
      FABL.booleanDerivative, FABL.affineFunction, zero_add]
    ac_rfl
  rw [hleft, hright] at hrelation
  exact hrelation

end CryptBoolean
