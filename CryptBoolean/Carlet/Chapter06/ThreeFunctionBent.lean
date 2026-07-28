/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Dual
public import CryptBoolean.Carlet.Chapter06.ThreeFunctionIdentity
public import CryptBoolean.Carlet.Chapter06.WalshCongruence

/-!
# Bentness from three Boolean functions

Carlet Corollary 4 for the first two elementary symmetric functions of three
bent Boolean functions.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem bitSignInt_threeFunctionIdentity
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n) :
    bitSignInt (f₁ a) + bitSignInt (f₂ a) + bitSignInt (f₃ a) =
      bitSignInt (threeFunctionSum f₁ f₂ f₃ a) +
        2 * bitSignInt (threeFunctionPairwiseProductSum f₁ f₂ f₃ a) := by
  have h := congrFun (bitValueInt_threeFunctionIdentity f₁ f₂ f₃) a
  simp only [threeFunctionSum, threeFunctionPairwiseProductSum,
    Pi.add_apply, Pi.mul_apply] at h ⊢
  simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt]
  linarith

private theorem walshTransform_threeFunctionPairwiseProductSum_eq
    (f₁ f₂ f₃ : BooleanFunction n)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂) (hf₃ : IsBent f₃)
    (hsum : IsBent (threeFunctionSum f₁ f₂ f₃))
    (hdual : bentDual (threeFunctionSum f₁ f₂ f₃) =
      bentDual f₁ + bentDual f₂ + bentDual f₃)
    (a : FABL.F₂Cube n) :
    walshTransform (threeFunctionPairwiseProductSum f₁ f₂ f₃) a =
      (2 ^ (n / 2) : ℤ) *
        bitSignInt
          (threeFunctionPairwiseProductSum
            (bentDual f₁) (bentDual f₂) (bentDual f₃) a) := by
  have hwalsh := walshTransform_threeFunctionIdentity f₁ f₂ f₃ a
  rw [walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f₁ hf₁ a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f₂ hf₂ a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f₃ hf₃ a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      (threeFunctionSum f₁ f₂ f₃) hsum a] at hwalsh
  have hsign := bitSignInt_threeFunctionIdentity
    (bentDual f₁) (bentDual f₂) (bentDual f₃) a
  rw [threeFunctionSum, ← hdual] at hsign
  have hscaled :
      (2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f₁ a) +
          (2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f₂ a) +
          (2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f₃ a) =
        (2 ^ (n / 2) : ℤ) *
            bitSignInt (bentDual (threeFunctionSum f₁ f₂ f₃) a) +
          2 * ((2 ^ (n / 2) : ℤ) *
            bitSignInt
              (threeFunctionPairwiseProductSum
                (bentDual f₁) (bentDual f₂) (bentDual f₃) a)) := by
    calc
      _ = (2 ^ (n / 2) : ℤ) *
          (bitSignInt (bentDual f₁ a) + bitSignInt (bentDual f₂ a) +
            bitSignInt (bentDual f₃ a)) := by ring
      _ = (2 ^ (n / 2) : ℤ) *
          (bitSignInt (bentDual (threeFunctionSum f₁ f₂ f₃) a) +
            2 * bitSignInt
              (threeFunctionPairwiseProductSum
                (bentDual f₁) (bentDual f₂) (bentDual f₃) a)) := by
        rw [hsign]
      _ = _ := by ring
  have htwice :
      2 * walshTransform (threeFunctionPairwiseProductSum f₁ f₂ f₃) a =
        2 * ((2 ^ (n / 2) : ℤ) *
          bitSignInt
            (threeFunctionPairwiseProductSum
              (bentDual f₁) (bentDual f₂) (bentDual f₃) a)) :=
    add_left_cancel (hwalsh.symm.trans hscaled)
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwice

/-- Carlet Corollary 4, first assertion: when the dual of the bent sum is the
sum of the three duals, the second elementary symmetric function is bent and
its dual is the second elementary symmetric function of the three duals. -/
theorem isBent_threeFunctionPairwiseProductSum_and_bentDual_eq
    (f₁ f₂ f₃ : BooleanFunction n)
    (_hnEven : Even n) (_hnTwo : 2 ≤ n)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂) (hf₃ : IsBent f₃)
    (hsum : IsBent (threeFunctionSum f₁ f₂ f₃))
    (hdual : bentDual (threeFunctionSum f₁ f₂ f₃) =
      bentDual f₁ + bentDual f₂ + bentDual f₃) :
    IsBent (threeFunctionPairwiseProductSum f₁ f₂ f₃) ∧
      bentDual (threeFunctionPairwiseProductSum f₁ f₂ f₃) =
        threeFunctionPairwiseProductSum
          (bentDual f₁) (bentDual f₂) (bentDual f₃) := by
  have hwalsh (a : FABL.F₂Cube n) :=
    walshTransform_threeFunctionPairwiseProductSum_eq
      f₁ f₂ f₃ hf₁ hf₂ hf₃ hsum hdual a
  have hbent : IsBent (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
    apply
      (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
        (threeFunctionPairwiseProductSum f₁ f₂ f₃)).2
    intro a
    rw [hwalsh a, Int.natAbs_mul]
    rw [bitSignInt_eq_if_one]
    split <;> simp
  refine ⟨hbent, ?_⟩
  funext a
  rw [bentDual, hwalsh a]
  by_cases hvalue :
      threeFunctionPairwiseProductSum
        (bentDual f₁) (bentDual f₂) (bentDual f₃) a = 1
  · have hnegative : ¬ (0 : ℤ) ≤
        (2 ^ (n / 2) : ℤ) *
          bitSignInt
            (threeFunctionPairwiseProductSum
              (bentDual f₁) (bentDual f₂) (bentDual f₃) a) := by
      simp [hvalue, bitSignInt_eq_if_one]
    rw [if_neg hnegative, hvalue]
  · have hzero :
        threeFunctionPairwiseProductSum
          (bentDual f₁) (bentDual f₂) (bentDual f₃) a = 0 := by
      by_contra hne
      exact hvalue (Fin.eq_one_of_ne_zero _ hne)
    have hnonnegative : (0 : ℤ) ≤
        (2 ^ (n / 2) : ℤ) *
          bitSignInt
            (threeFunctionPairwiseProductSum
              (bentDual f₁) (bentDual f₂) (bentDual f₃) a) := by
      simp [hzero, bitSignInt_eq_if_one]
    rw [if_pos hnonnegative, hzero]

/-- Carlet Corollary 4, second assertion: in even dimension at least two, if
every Walsh coefficient of the second elementary symmetric function is
divisible by `2^(n/2)`, then the first elementary symmetric function is bent. -/
theorem isBent_threeFunctionSum_of_two_pow_half_dvd_walshTransform
    (f₁ f₂ f₃ : BooleanFunction n)
    (hnEven : Even n) (hnTwo : 2 ≤ n)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂) (hf₃ : IsBent f₃)
    (hdiv : ∀ a : FABL.F₂Cube n,
      (2 ^ (n / 2) : ℤ) ∣
        walshTransform (threeFunctionPairwiseProductSum f₁ f₂ f₃) a) :
    IsBent (threeFunctionSum f₁ f₂ f₃) := by
  apply
    (isBent_iff_forall_walshTransform_modeq
      (threeFunctionSum f₁ f₂ f₃) hnEven hnTwo).2
  intro a
  have hf₁Modeq :=
    ((isBent_iff_forall_walshTransform_modeq f₁ hnEven hnTwo).1 hf₁) a
  have hf₂Modeq :=
    ((isBent_iff_forall_walshTransform_modeq f₂ hnEven hnTwo).1 hf₂) a
  have hf₃Modeq :=
    ((isBent_iff_forall_walshTransform_modeq f₃ hnEven hnTwo).1 hf₃) a
  have hpairwiseModeq :
      Int.ModEq (2 ^ (n / 2 + 1))
        (2 * walshTransform
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) a) 0 := by
    rw [Int.modEq_zero_iff_dvd]
    obtain ⟨z, hz⟩ := hdiv a
    rw [hz, pow_succ]
    refine ⟨z, ?_⟩
    ring
  have hsumModeq := (hf₁Modeq.add hf₂Modeq).add hf₃Modeq
  have hwalsh := walshTransform_threeFunctionIdentity f₁ f₂ f₃ a
  rw [hwalsh] at hsumModeq
  have hcleared := hsumModeq.sub hpairwiseModeq
  simp only [add_sub_cancel_right, sub_zero] at hcleared
  have hperiod :
      Int.ModEq (2 ^ (n / 2 + 1))
        ((2 ^ (n / 2) : ℤ) + 2 ^ (n / 2) + 2 ^ (n / 2))
        (2 ^ (n / 2)) := by
    rw [Int.modEq_iff_dvd, pow_succ]
    refine ⟨-1, ?_⟩
    ring
  exact hcleared.trans hperiod

end CryptBoolean
