/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine

/-!
# Carlet Chapter 5 affine Walsh spectra

The raw Walsh spectrum of an affine Boolean function is supported at its linear coefficient.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Carlet's Chapter 5 Maiorana--McFarland functions: each restriction to the first block is
affine. -/
def IsMaioranaMcFarland {r s : ℕ}
    (f : BooleanFunction (r + s)) : Prop :=
  ∀ y : FABL.F₂Cube s, ∃ b : FABL.𝔽₂, ∃ a : FABL.F₂Cube r,
    ∀ x : FABL.F₂Cube r, f (Fin.append x y) = FABL.affineFunction b a x

/-- The raw Walsh transform of an affine Boolean function is supported at its linear part. -/
theorem walshTransform_affineFunction
    (b : FABL.𝔽₂) (a u : FABL.F₂Cube n) :
    walshTransform (FABL.affineFunction b a) u =
      if u = a then bitSignInt b * (2 ^ n : ℤ) else 0 := by
  classical
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_cast_eq_sum_realSignView_mul_character]
  simp_rw [realSignView_affineFunction]
  have hcast : (bitSignInt b : ℝ) = FABL.binarySign b := by
    rw [bitSignInt, ← FABL.signValue_signEncode_eq_binarySign]
    rfl
  calc
    ∑ x, FABL.binarySign b * FABL.vectorWalshCharacter a x *
        FABL.vectorWalshCharacter u x =
        FABL.binarySign b *
          ∑ x, FABL.vectorWalshCharacter a x * FABL.vectorWalshCharacter u x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = FABL.binarySign b *
        ((Fintype.card (FABL.F₂Cube n) : ℝ) *
          (𝔼 x, FABL.vectorWalshCharacter a x * FABL.vectorWalshCharacter u x)) := by
      rw [Fintype.card_mul_expect]
    _ = ((if u = a then bitSignInt b * (2 ^ n : ℤ) else 0 : ℤ) : ℝ) := by
      rw [FABL.expect_vectorWalshCharacter_mul, card_f₂Cube]
      by_cases h : u = a
      · subst u
        simp [hcast]
      · simp [h, Ne.symm h]

/-- Adding an affine Boolean function translates the raw Walsh spectrum and
multiplies it by the sign of the constant term. -/
theorem walshTransform_add_affineFunction
    (f : BooleanFunction n) (b : FABL.𝔽₂)
    (a u : FABL.F₂Cube n) :
    walshTransform (f + FABL.affineFunction b a) u =
      bitSignInt b * walshTransform f (u + a) := by
  classical
  unfold walshTransform walshTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [Pi.add_apply, FABL.affineFunction]
  rw [← bitSignInt_add]
  congr 1
  simp only [FABL.f₂DotProduct, add_dotProduct]
  ac_rfl

/-- Adding an affine Boolean function preserves every raw Walsh magnitude up
to the corresponding frequency translation. -/
theorem walshTransform_add_affineFunction_natAbs
    (f : BooleanFunction n) (b : FABL.𝔽₂)
    (a u : FABL.F₂Cube n) :
    (walshTransform (f + FABL.affineFunction b a) u).natAbs =
      (walshTransform f (u + a)).natAbs := by
  rw [walshTransform_add_affineFunction]
  rw [Int.natAbs_mul]
  have hsign : (bitSignInt b).natAbs = 1 := by
    rw [bitSignInt_eq_if_one]
    split <;> simp
  rw [hsign, one_mul]

end CryptBoolean
