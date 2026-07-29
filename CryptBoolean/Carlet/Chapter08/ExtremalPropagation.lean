/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.AdditionalDecompositions
public import CryptBoolean.Carlet.Chapter06.PartiallyBent
public import CryptBoolean.Carlet.Chapter08.AffineFlatWalshCharacterization
public import CryptBoolean.Carlet.Chapter08.WalshCharacterization

import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Extremal propagation criteria

The extremal even- and odd-dimensional propagation classifications from
Carlet Section 8.1.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

private def FourSquarePeak (k : ℕ) (x₀ x₁ x₂ x₃ : ℤ) : Prop :=
  (x₀.natAbs = 2 ^ k ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∨
  (x₁.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∨
  (x₂.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₁ = 0 ∧ x₃ = 0) ∨
  (x₃.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0)

private def FourSquareFlat (k : ℕ) (x₀ x₁ x₂ x₃ : ℤ) : Prop :=
  x₀.natAbs = 2 ^ k ∧ x₁.natAbs = 2 ^ k ∧
    x₂.natAbs = 2 ^ k ∧ x₃.natAbs = 2 ^ k

private def FourSquarePair (k : ℕ) (x₀ x₁ x₂ x₃ : ℤ) : Prop :=
  (x₀.natAbs = 2 ^ k ∧ x₁.natAbs = 2 ^ k ∧ x₂ = 0 ∧ x₃ = 0) ∨
  (x₀.natAbs = 2 ^ k ∧ x₂.natAbs = 2 ^ k ∧ x₁ = 0 ∧ x₃ = 0) ∨
  (x₀.natAbs = 2 ^ k ∧ x₃.natAbs = 2 ^ k ∧ x₁ = 0 ∧ x₂ = 0) ∨
  (x₁.natAbs = 2 ^ k ∧ x₂.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₃ = 0) ∨
  (x₁.natAbs = 2 ^ k ∧ x₃.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₂ = 0) ∨
  (x₂.natAbs = 2 ^ k ∧ x₃.natAbs = 2 ^ k ∧ x₀ = 0 ∧ x₁ = 0)

private theorem zmod_four_sq_zero_or_one (a : ZMod 4) :
    a ^ 2 = 0 ∨ a ^ 2 = 1 := by
  fin_cases a <;> decide

private theorem zmod_four_sq_sum_zero
    (a b c d : ZMod 4)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0) :
    (a ^ 2 = 0 ∧ b ^ 2 = 0 ∧ c ^ 2 = 0 ∧ d ^ 2 = 0) ∨
      (a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ d ^ 2 = 1) := by
  rcases zmod_four_sq_zero_or_one a with ha | ha <;>
    rcases zmod_four_sq_zero_or_one b with hb | hb <;>
    rcases zmod_four_sq_zero_or_one c with hc | hc <;>
    rcases zmod_four_sq_zero_or_one d with hd | hd
  all_goals
    rw [ha, hb, hc, hd] at h ⊢
  all_goals first
    | exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    | exfalso; revert h; decide

private theorem even_of_intCast_zmod_four_sq_eq_zero
    (x : ℤ) (h : (x : ZMod 4) ^ 2 = 0) : Even x := by
  rcases Int.even_or_odd x with hx | hx
  · exact hx
  · obtain ⟨y, rfl⟩ := hx
    have hsquare : (((2 * y + 1 : ℤ) : ZMod 4) ^ 2) = 1 := by
      push_cast
      ring_nf
      rw [show (4 : ZMod 4) = 0 by decide]
      simp
    rw [hsquare] at h
    exact ((by decide : (1 : ZMod 4) ≠ 0) h).elim

private theorem odd_of_intCast_zmod_four_sq_eq_one
    (x : ℤ) (h : (x : ZMod 4) ^ 2 = 1) : Odd x := by
  rcases Int.even_or_odd x with hx | hx
  · obtain ⟨y, rfl⟩ := hx
    have hsquare : (((y + y : ℤ) : ZMod 4) ^ 2) = 0 := by
      push_cast
      ring_nf
      rw [show (4 : ZMod 4) = 0 by decide]
      simp
    rw [hsquare] at h
    exact ((by decide : (0 : ZMod 4) ≠ 1) h).elim
  · exact hx

private theorem fourSquarePeak_zero
    (x₀ x₁ x₂ x₃ : ℤ)
    (h : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 1) :
    FourSquarePeak 0 x₀ x₁ x₂ x₃ := by
  have hx₀Lower : -1 ≤ x₀ := by
    nlinarith [sq_nonneg (x₀ + 1), sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₀Upper : x₀ ≤ 1 := by
    nlinarith [sq_nonneg (x₀ - 1), sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Lower : -1 ≤ x₁ := by
    nlinarith [sq_nonneg x₀, sq_nonneg (x₁ + 1), sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Upper : x₁ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg (x₁ - 1), sq_nonneg x₂, sq_nonneg x₃]
  have hx₂Lower : -1 ≤ x₂ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg (x₂ + 1), sq_nonneg x₃]
  have hx₂Upper : x₂ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg (x₂ - 1), sq_nonneg x₃]
  have hx₃Lower : -1 ≤ x₃ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg (x₃ + 1)]
  have hx₃Upper : x₃ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg (x₃ - 1)]
  interval_cases x₀ <;> interval_cases x₁ <;>
    interval_cases x₂ <;> interval_cases x₃
  all_goals norm_num at h
  all_goals norm_num [FourSquarePeak]

private theorem fourSquareClassification_one
    (x₀ x₁ x₂ x₃ : ℤ)
    (h : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 4) :
    FourSquarePeak 1 x₀ x₁ x₂ x₃ ∨
      FourSquareFlat 0 x₀ x₁ x₂ x₃ := by
  have hx₀Lower : -2 ≤ x₀ := by
    nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₀Upper : x₀ ≤ 2 := by
    nlinarith [sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Lower : -2 ≤ x₁ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Upper : x₁ ≤ 2 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₂, sq_nonneg x₃]
  have hx₂Lower : -2 ≤ x₂ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₃]
  have hx₂Upper : x₂ ≤ 2 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₃]
  have hx₃Lower : -2 ≤ x₃ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂]
  have hx₃Upper : x₃ ≤ 2 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂]
  interval_cases x₀ <;> interval_cases x₁ <;>
    interval_cases x₂ <;> interval_cases x₃
  all_goals norm_num at h
  all_goals norm_num [FourSquarePeak, FourSquareFlat]

private theorem fourSquarePair_zero
    (x₀ x₁ x₂ x₃ : ℤ)
    (h : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = 2) :
    FourSquarePair 0 x₀ x₁ x₂ x₃ := by
  have hx₀Lower : -1 ≤ x₀ := by
    nlinarith [sq_nonneg (x₀ + 1), sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₀Upper : x₀ ≤ 1 := by
    nlinarith [sq_nonneg (x₀ - 1), sq_nonneg x₁, sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Lower : -1 ≤ x₁ := by
    nlinarith [sq_nonneg x₀, sq_nonneg (x₁ + 1), sq_nonneg x₂, sq_nonneg x₃]
  have hx₁Upper : x₁ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg (x₁ - 1), sq_nonneg x₂, sq_nonneg x₃]
  have hx₂Lower : -1 ≤ x₂ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg (x₂ + 1), sq_nonneg x₃]
  have hx₂Upper : x₂ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg (x₂ - 1), sq_nonneg x₃]
  have hx₃Lower : -1 ≤ x₃ := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg (x₃ + 1)]
  have hx₃Upper : x₃ ≤ 1 := by
    nlinarith [sq_nonneg x₀, sq_nonneg x₁, sq_nonneg x₂, sq_nonneg (x₃ - 1)]
  interval_cases x₀ <;> interval_cases x₁ <;>
    interval_cases x₂ <;> interval_cases x₃
  all_goals norm_num at h
  all_goals norm_num [FourSquarePair]

private theorem fourSquarePairClassification
    (k : ℕ) (x₀ x₁ x₂ x₃ : ℤ)
    (h : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 =
      (2 : ℤ) ^ (2 * k + 1)) :
    FourSquarePair k x₀ x₁ x₂ x₃ := by
  induction k generalizing x₀ x₁ x₂ x₃ with
  | zero =>
      apply fourSquarePair_zero x₀ x₁ x₂ x₃
      simpa using h
  | succ k ih =>
      have hmodFour :
          (x₀ : ZMod 4) ^ 2 + (x₁ : ZMod 4) ^ 2 +
              (x₂ : ZMod 4) ^ 2 + (x₃ : ZMod 4) ^ 2 = 0 := by
        have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 4)) h
        have hpow : (((2 : ℤ) ^ (2 * (k + 1) + 1) : ℤ) : ZMod 4) = 0 := by
          rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by omega, pow_add]
          push_cast
          rw [show (4 : ZMod 4) = 0 by decide, zero_mul]
        rw [hpow] at hcast
        simpa only [Int.cast_add, Int.cast_pow] using hcast
      rcases zmod_four_sq_sum_zero _ _ _ _ hmodFour with heven | hodd
      · obtain ⟨y₀, hy₀⟩ := even_of_intCast_zmod_four_sq_eq_zero x₀ heven.1
        obtain ⟨y₁, hy₁⟩ := even_of_intCast_zmod_four_sq_eq_zero x₁ heven.2.1
        obtain ⟨y₂, hy₂⟩ := even_of_intCast_zmod_four_sq_eq_zero x₂ heven.2.2.1
        obtain ⟨y₃, hy₃⟩ := even_of_intCast_zmod_four_sq_eq_zero x₃ heven.2.2.2
        rw [← two_mul] at hy₀ hy₁ hy₂ hy₃
        subst x₀
        subst x₁
        subst x₂
        subst x₃
        have h' : y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 =
            (2 : ℤ) ^ (2 * k + 1) := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
            pow_add] at h
          norm_num at h ⊢
          nlinarith
        have hp := ih y₀ y₁ y₂ y₃ h'
        rcases hp with hp | hp | hp | hp | hp | hp
        · left
          rcases hp with ⟨h₀, h₁, h₂, h₃⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
        · right; left
          rcases hp with ⟨h₀, h₂, h₁, h₃⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
        · right; right; left
          rcases hp with ⟨h₀, h₃, h₁, h₂⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
        · right; right; right; left
          rcases hp with ⟨h₁, h₂, h₀, h₃⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
        · right; right; right; right; left
          rcases hp with ⟨h₁, h₃, h₀, h₂⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
        · right; right; right; right; right
          rcases hp with ⟨h₂, h₃, h₀, h₁⟩
          simp [Int.natAbs_mul, h₀, h₁, h₂, h₃,
            pow_succ, Nat.mul_comm]
      · have h₀ := Int.eight_dvd_sq_sub_one_of_odd
            (odd_of_intCast_zmod_four_sq_eq_one x₀ hodd.1)
        have h₁ := Int.eight_dvd_sq_sub_one_of_odd
            (odd_of_intCast_zmod_four_sq_eq_one x₁ hodd.2.1)
        have h₂ := Int.eight_dvd_sq_sub_one_of_odd
            (odd_of_intCast_zmod_four_sq_eq_one x₂ hodd.2.2.1)
        have h₃ := Int.eight_dvd_sq_sub_one_of_odd
            (odd_of_intCast_zmod_four_sq_eq_one x₃ hodd.2.2.2)
        have hleft : (8 : ℤ) ∣
            x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - 4 := by
          have hsum := dvd_add (dvd_add (dvd_add h₀ h₁) h₂) h₃
          rw [show (x₀ ^ 2 - 1) + (x₁ ^ 2 - 1) +
              (x₂ ^ 2 - 1) + (x₃ ^ 2 - 1) =
                x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - 4 by ring] at hsum
          exact hsum
        have hright : (8 : ℤ) ∣ (2 : ℤ) ^ (2 * (k + 1) + 1) := by
          rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add]
          norm_num
        have hfour : (8 : ℤ) ∣ 4 := by
          rw [h] at hleft
          simpa using dvd_sub hright hleft
        norm_num at hfour

private theorem fourSquareClassification
    (k : ℕ) (x₀ x₁ x₂ x₃ : ℤ)
    (h : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 =
      (2 : ℤ) ^ (2 * k)) :
    FourSquarePeak k x₀ x₁ x₂ x₃ ∨
      (0 < k ∧ FourSquareFlat (k - 1) x₀ x₁ x₂ x₃) := by
  induction k using Nat.strong_induction_on generalizing x₀ x₁ x₂ x₃ with
  | h k ih =>
      rcases k with _ | k
      · left
        apply fourSquarePeak_zero x₀ x₁ x₂ x₃
        simpa using h
      · rcases k with _ | k
        · rcases fourSquareClassification_one x₀ x₁ x₂ x₃ (by
              norm_num at h ⊢
              exact h) with hpeak | hflat
          · exact Or.inl hpeak
          · exact Or.inr ⟨by omega, by simpa using hflat⟩
        · have hmodFour :
              (x₀ : ZMod 4) ^ 2 + (x₁ : ZMod 4) ^ 2 +
                  (x₂ : ZMod 4) ^ 2 + (x₃ : ZMod 4) ^ 2 = 0 := by
            have hcast := congrArg (fun z : ℤ ↦ (z : ZMod 4)) h
            have hpow : (((2 : ℤ) ^ (2 * (k + 2)) : ℤ) : ZMod 4) = 0 := by
              rw [show 2 * (k + 2) = 2 + 2 * (k + 1) by omega, pow_add]
              push_cast
              rw [show (4 : ZMod 4) = 0 by decide, zero_mul]
            rw [show k + 1 + 1 = k + 2 by omega, hpow] at hcast
            simpa only [Int.cast_add, Int.cast_pow] using hcast
          rcases zmod_four_sq_sum_zero _ _ _ _ hmodFour with heven | hodd
          · obtain ⟨y₀, hy₀⟩ := even_of_intCast_zmod_four_sq_eq_zero x₀ heven.1
            obtain ⟨y₁, hy₁⟩ := even_of_intCast_zmod_four_sq_eq_zero x₁ heven.2.1
            obtain ⟨y₂, hy₂⟩ := even_of_intCast_zmod_four_sq_eq_zero x₂ heven.2.2.1
            obtain ⟨y₃, hy₃⟩ := even_of_intCast_zmod_four_sq_eq_zero x₃ heven.2.2.2
            rw [← two_mul] at hy₀ hy₁ hy₂ hy₃
            subst x₀
            subst x₁
            subst x₂
            subst x₃
            have h' : y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 =
                (2 : ℤ) ^ (2 * (k + 1)) := by
              rw [show 2 * (k + 2) = 2 * (k + 1) + 2 by omega,
                pow_add] at h
              norm_num at h ⊢
              nlinarith
            rcases ih (k + 1) (by omega) y₀ y₁ y₂ y₃ h' with hpeak | hflat
            · left
              rcases hpeak with h₀ | h₁ | h₂ | h₃
              · left
                rcases h₀ with ⟨habs, h₁, h₂, h₃⟩
                simp [Int.natAbs_mul, habs, h₁, h₂, h₃,
                  pow_succ, Nat.mul_comm]
              · right; left
                rcases h₁ with ⟨habs, h₀, h₂, h₃⟩
                simp [Int.natAbs_mul, habs, h₀, h₂, h₃,
                  pow_succ, Nat.mul_comm]
              · right; right; left
                rcases h₂ with ⟨habs, h₀, h₁, h₃⟩
                simp [Int.natAbs_mul, habs, h₀, h₁, h₃,
                  pow_succ, Nat.mul_comm]
              · right; right; right
                rcases h₃ with ⟨habs, h₀, h₁, h₂⟩
                simp [Int.natAbs_mul, habs, h₀, h₁, h₂,
                  pow_succ, Nat.mul_comm]
            · right
              refine ⟨by omega, ?_⟩
              rcases hflat with ⟨_hk, h₀, h₁, h₂, h₃⟩
              constructor
              · simp [Int.natAbs_mul, h₀, pow_succ, Nat.mul_comm]
              constructor
              · simp [Int.natAbs_mul, h₁, pow_succ, Nat.mul_comm]
              constructor
              · simp [Int.natAbs_mul, h₂, pow_succ, Nat.mul_comm]
              · simp [Int.natAbs_mul, h₃, pow_succ, Nat.mul_comm]
          · have h₀ := Int.eight_dvd_sq_sub_one_of_odd
                (odd_of_intCast_zmod_four_sq_eq_one x₀ hodd.1)
            have h₁ := Int.eight_dvd_sq_sub_one_of_odd
                (odd_of_intCast_zmod_four_sq_eq_one x₁ hodd.2.1)
            have h₂ := Int.eight_dvd_sq_sub_one_of_odd
                (odd_of_intCast_zmod_four_sq_eq_one x₂ hodd.2.2.1)
            have h₃ := Int.eight_dvd_sq_sub_one_of_odd
                (odd_of_intCast_zmod_four_sq_eq_one x₃ hodd.2.2.2)
            have hleft : (8 : ℤ) ∣
                x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - 4 := by
              have hsum := dvd_add (dvd_add (dvd_add h₀ h₁) h₂) h₃
              rw [show (x₀ ^ 2 - 1) + (x₁ ^ 2 - 1) +
                  (x₂ ^ 2 - 1) + (x₃ ^ 2 - 1) =
                    x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 - 4 by ring] at hsum
              exact hsum
            have hright : (8 : ℤ) ∣ (2 : ℤ) ^ (2 * (k + 2)) := by
              rw [show 2 * (k + 2) = 3 + (2 * k + 1) by omega, pow_add]
              norm_num
            have hfour : (8 : ℤ) ∣ 4 := by
              have hsum : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 =
                  (2 : ℤ) ^ (2 * (k + 2)) := by simpa only [show k + 1 + 1 = k + 2 by omega] using h
              rw [hsum] at hleft
              simpa using dvd_sub hright hleft
            norm_num at hfour

def coordinateDirection (i : Fin n) : FABL.F₂Cube n :=
  FABL.f₂CubeOfFinset {i}

private def coordinatePairDirection (i j : Fin n) : FABL.F₂Cube n :=
  FABL.f₂CubeOfFinset {i, j}

@[simp] private theorem f₂Support_coordinateDirection (i : Fin n) :
    FABL.f₂Support (coordinateDirection i) = {i} := by
  exact (FABL.f₂CubeEquivFinset n).right_inv {i}

@[simp] private theorem f₂Support_coordinatePairDirection (i j : Fin n) :
    FABL.f₂Support (coordinatePairDirection i j) = {i, j} := by
  exact (FABL.f₂CubeEquivFinset n).right_inv {i, j}

private theorem coordinatePairDirection_eq_add
    (i j : Fin n) (hij : i ≠ j) :
    coordinatePairDirection i j = coordinateDirection i + coordinateDirection j := by
  funext q
  by_cases hqi : q = i
  · subst q
    simp [coordinatePairDirection, coordinateDirection,
      FABL.f₂CubeOfFinset_apply, hij]
  · by_cases hqj : q = j
    · subst q
      simp [coordinatePairDirection, coordinateDirection,
        FABL.f₂CubeOfFinset_apply, hqi]
    · simp [coordinatePairDirection, coordinateDirection,
        FABL.f₂CubeOfFinset_apply, hqi, hqj]

private theorem coordinateDirection_ne_zero (i : Fin n) :
    coordinateDirection i ≠ 0 := by
  intro h
  have hs := congrArg FABL.f₂Support h
  have hzero : FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
    ext q
    simp [FABL.mem_f₂Support]
  rw [f₂Support_coordinateDirection, hzero] at hs
  have hi : i ∈ ({i} : Finset (Fin n)) := by simp
  rw [hs] at hi
  simp at hi

private theorem coordinateDirection_ne_coordinateDirection
    {i j : Fin n} (hij : i ≠ j) :
    coordinateDirection i ≠ coordinateDirection j := by
  intro h
  have hs := congrArg FABL.f₂Support h
  simp only [f₂Support_coordinateDirection] at hs
  exact hij (Finset.singleton_injective hs)

private theorem coordinatePairDirection_ne_zero
    (i j : Fin n) : coordinatePairDirection i j ≠ 0 := by
  intro h
  have hs := congrArg FABL.f₂Support h
  have hzero : FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
    ext q
    simp [FABL.mem_f₂Support]
  rw [f₂Support_coordinatePairDirection, hzero] at hs
  have hi : i ∈ ({i, j} : Finset (Fin n)) := by simp
  rw [hs] at hi
  simp at hi

private theorem coordinatePairDirection_ne_coordinateDirection_left
    {i j : Fin n} (hij : i ≠ j) :
    coordinatePairDirection i j ≠ coordinateDirection i := by
  intro h
  have hs := congrArg FABL.f₂Support h
  simp only [f₂Support_coordinatePairDirection,
    f₂Support_coordinateDirection] at hs
  have hj : j ∈ ({i} : Finset (Fin n)) := by
    rw [← hs]
    simp
  have hji : j = i := by simpa only [Finset.mem_singleton] using hj
  exact hij hji.symm

private theorem coordinatePairDirection_ne_coordinateDirection_right
    {i j : Fin n} (hij : i ≠ j) :
    coordinatePairDirection i j ≠ coordinateDirection j := by
  intro h
  have hs := congrArg FABL.f₂Support h
  simp only [f₂Support_coordinatePairDirection,
    f₂Support_coordinateDirection] at hs
  have hi : i ∈ ({j} : Finset (Fin n)) := by
    rw [← hs]
    simp
  exact hij (by simpa only [Finset.mem_singleton] using hi)

private theorem finset_subset_pair_cases
    (S : Finset (Fin n)) (i j : Fin n) (hS : S ⊆ {i, j}) :
    S = ∅ ∨ S = {i} ∨ S = {j} ∨ S = {i, j} := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · right; right; right
    apply Finset.Subset.antisymm hS
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hi
    · exact hj
  · right; left
    apply Finset.Subset.antisymm
    · intro q hq
      have hqPair := hS hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqPair ⊢
      rcases hqPair with hqi | hqj
      · exact hqi
      · subst q
        exact (hj hq).elim
    · intro q hq
      have hqi : q = i := by simpa only [Finset.mem_singleton] using hq
      subst q
      exact hi
  · right; right; left
    apply Finset.Subset.antisymm
    · intro q hq
      have hqPair := hS hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqPair ⊢
      rcases hqPair with hqi | hqj
      · subst q
        exact (hi hq).elim
      · exact hqj
    · intro q hq
      have hqj : q = j := by simpa only [Finset.mem_singleton] using hq
      subst q
      exact hj
  · left
    exact Finset.eq_empty_iff_forall_notMem.mpr (by
      intro q hq
      have hqPair := hS hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqPair
      rcases hqPair with hqi | hqj
      · exact hi (hqi ▸ hq)
      · exact hj (hqj ▸ hq))

private theorem supportPrecedes_coordinatePairDirection_cases
    (w : FABL.F₂Cube n) (i j : Fin n)
    (hw : w ≼ coordinatePairDirection i j) :
    w = 0 ∨ w = coordinateDirection i ∨ w = coordinateDirection j ∨
      w = coordinatePairDirection i j := by
  have hsupport : FABL.f₂Support w ⊆ {i, j} := by
    simpa [supportPrecedes] using hw
  have hwrepr : FABL.f₂CubeOfFinset (FABL.f₂Support w) = w :=
    (FABL.f₂CubeEquivFinset n).left_inv w
  rcases finset_subset_pair_cases (FABL.f₂Support w) i j hsupport with
      hzero | hi | hj | hij
  · left
    rw [← hwrepr, hzero]
    rfl
  · right; left
    rw [← hwrepr, hi]
    rfl
  · right; right; left
    rw [← hwrepr, hj]
    rfl
  · right; right; right
    rw [← hwrepr, hij]
    rfl

private theorem predecessor_coordinatePairDirection
    (i j : Fin n) :
    (Finset.univ.filter fun w : FABL.F₂Cube n ↦
      w ≼ coordinatePairDirection i j) =
        {0, coordinateDirection i, coordinateDirection j,
          coordinatePairDirection i j} := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact supportPrecedes_coordinatePairDirection_cases w i j
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl
    · have hzero : FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
        ext q
        simp [FABL.mem_f₂Support]
      rw [supportPrecedes, hzero]
      exact Finset.empty_subset _
    · simp [supportPrecedes]
    · simp [supportPrecedes]
    · exact Finset.Subset.rfl

private theorem predecessorWalshSquareSum_coordinatePairDirection
    (f : BooleanFunction n) (i j : Fin n) (hij : i ≠ j)
    (v : FABL.F₂Cube n) :
    predecessorWalshSquareSum f (coordinatePairDirection i j) v =
      (walshTransform f v : ℝ) ^ 2 +
      (walshTransform f (v + coordinateDirection i) : ℝ) ^ 2 +
      (walshTransform f (v + coordinateDirection j) : ℝ) ^ 2 +
      (walshTransform f (v + coordinatePairDirection i j) : ℝ) ^ 2 := by
  classical
  unfold predecessorWalshSquareSum
  rw [predecessor_coordinatePairDirection]
  have hi0 := coordinateDirection_ne_zero i
  have hj0 := coordinateDirection_ne_zero j
  have hijDirections := coordinateDirection_ne_coordinateDirection hij
  have hp0 := coordinatePairDirection_ne_zero i j
  have hpi := coordinatePairDirection_ne_coordinateDirection_left hij
  have hpj := coordinatePairDirection_ne_coordinateDirection_right hij
  have hzeroMem :
      (0 : FABL.F₂Cube n) ∉
        ({coordinateDirection i, coordinateDirection j,
          coordinatePairDirection i j} : Finset (FABL.F₂Cube n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hi0.symm, hj0.symm, hp0.symm⟩
  have hiMem : coordinateDirection i ∉
      ({coordinateDirection j, coordinatePairDirection i j} :
        Finset (FABL.F₂Cube n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hijDirections, hpi.symm⟩
  have hjMem : coordinateDirection j ∉
      ({coordinatePairDirection i j} : Finset (FABL.F₂Cube n)) := by
    simpa only [Finset.mem_singleton] using hpj.symm
  rw [Finset.sum_insert hzeroMem, Finset.sum_insert hiMem,
    Finset.sum_insert hjMem, Finset.sum_singleton]
  simp only [zero_add]
  ring_nf

private theorem walshSquareFace_eq_of_satisfiesPropagationCriterion_pred_two
    (f : BooleanFunction n) (hn : 2 ≤ n)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n) :
    walshTransform f v ^ 2 +
      walshTransform f (v + coordinateDirection i) ^ 2 +
      walshTransform f (v + coordinateDirection j) ^ 2 +
      walshTransform f (v + coordinatePairDirection i j) ^ 2 =
        (2 : ℤ) ^ (n + 2) := by
  have hsum :=
    (satisfiesPropagationCriterion_iff_predecessorWalshSquareSum
      (n - 2) f).mp hpc (coordinatePairDirection i j) v (by
        rw [f₂Support_coordinatePairDirection]
        rw [Finset.card_pair hij]
        omega)
  rw [predecessorWalshSquareSum_coordinatePairDirection f i j hij v] at hsum
  rw [f₂Support_coordinatePairDirection] at hsum
  rw [Finset.card_pair hij] at hsum
  exact_mod_cast hsum

private theorem walshFace_peak_or_flat
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n) :
    FourSquarePeak (k + 1)
        (walshTransform f v)
        (walshTransform f (v + coordinateDirection i))
        (walshTransform f (v + coordinateDirection j))
        (walshTransform f (v + coordinatePairDirection i j)) ∨
      FourSquareFlat k
        (walshTransform f v)
        (walshTransform f (v + coordinateDirection i))
        (walshTransform f (v + coordinateDirection j))
        (walshTransform f (v + coordinatePairDirection i j)) := by
  have hsum :=
    walshSquareFace_eq_of_satisfiesPropagationCriterion_pred_two
      f (by omega) hpc i j hij v
  have hsum' :
      walshTransform f v ^ 2 +
        walshTransform f (v + coordinateDirection i) ^ 2 +
        walshTransform f (v + coordinateDirection j) ^ 2 +
        walshTransform f (v + coordinatePairDirection i j) ^ 2 =
          (2 : ℤ) ^ (2 * (k + 1)) := by
    rw [show n + 2 = 2 * (k + 1) by omega] at hsum
    exact hsum
  rcases fourSquareClassification (k + 1) _ _ _ _ hsum' with
    hpeak | hflat
  · exact Or.inl hpeak
  · exact Or.inr (by simpa only [Nat.add_sub_cancel] using hflat.2)

private theorem walshFace_neighbors_eq_zero_of_peak
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n)
    (hv : (walshTransform f v).natAbs = 2 ^ (k + 1)) :
    walshTransform f (v + coordinateDirection i) = 0 ∧
      walshTransform f (v + coordinateDirection j) = 0 ∧
      walshTransform f (v + coordinatePairDirection i j) = 0 := by
  rcases walshFace_peak_or_flat f k hn hpc i j hij v with hpeak | hflat
  · rcases hpeak with h₀ | h₁ | h₂ | h₃
    · exact ⟨h₀.2.1, h₀.2.2.1, h₀.2.2.2⟩
    · rw [h₁.2.1] at hv
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [h₂.2.1] at hv
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [h₃.2.1] at hv
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
  · have heq := hv.symm.trans hflat.1
    rw [pow_succ] at heq
    have hpositive := Nat.two_pow_pos k
    omega

private theorem walshFace_fourth_is_peak_of_three_zeros
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n)
    (h₀ : walshTransform f v = 0)
    (h₁ : walshTransform f (v + coordinateDirection i) = 0)
    (h₂ : walshTransform f (v + coordinateDirection j) = 0) :
    (walshTransform f (v + coordinatePairDirection i j)).natAbs =
      2 ^ (k + 1) := by
  rcases walshFace_peak_or_flat f k hn hpc i j hij v with hpeak | hflat
  · rcases hpeak with hp₀ | hp₁ | hp₂ | hp₃
    · rw [h₀] at hp₀
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [h₁] at hp₁
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [h₂] at hp₂
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · exact hp₃.1
  · rw [h₀] at hflat
    have hne : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by omega)
    exact (hne hflat.1.symm).elim

private theorem exists_peak_walsh_of_not_flat
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n)
    (hv : (walshTransform f v).natAbs ≠ 2 ^ k) :
    ∃ u : FABL.F₂Cube n,
      (walshTransform f u).natAbs = 2 ^ (k + 1) := by
  rcases walshFace_peak_or_flat f k hn hpc i j hij v with hpeak | hflat
  · rcases hpeak with h₀ | h₁ | h₂ | h₃
    · exact ⟨v, h₀.1⟩
    · exact ⟨v + coordinateDirection i, h₁.1⟩
    · exact ⟨v + coordinateDirection j, h₂.1⟩
    · exact ⟨v + coordinatePairDirection i j, h₃.1⟩
  · exact (hv hflat.1).elim

private theorem add_coordinateDirection_coordinateDirection
    (v : FABL.F₂Cube n) (i j : Fin n) (hij : i ≠ j) :
    (v + coordinateDirection i) + coordinateDirection j =
      v + coordinatePairDirection i j := by
  rw [coordinatePairDirection_eq_add i j hij]
  abel

private theorem add_coordinateDirection_pair_eq_add_pair_coordinateDirection
    (v : FABL.F₂Cube n) (i j q : Fin n)
    (hij : i ≠ j) (hjq : j ≠ q) :
    (v + coordinateDirection i) + coordinatePairDirection j q =
      (v + coordinatePairDirection i j) + coordinateDirection q := by
  rw [coordinatePairDirection_eq_add j q hjq,
    coordinatePairDirection_eq_add i j hij]
  abel

/-- In even dimension at least four, `PC(n-2)` already forces bentness. -/
theorem isBent_of_satisfiesPropagationCriterion_pred_two_of_even
    (f : BooleanFunction n) (hn : 4 ≤ n) (heven : Even n)
    (hpc : SatisfiesPropagationCriterion (n - 2) f) :
    IsBent f := by
  obtain ⟨k, hk⟩ := heven
  have hnEq : n = 2 * k := by omega
  have hhalf : n / 2 = k := by omega
  apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half f).2
  intro v
  rw [hhalf]
  by_contra hv
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  let i₃ : Fin n := ⟨3, by omega⟩
  have h₀₁ : i₀ ≠ i₁ := by simp [i₀, i₁]
  have h₀₂ : i₀ ≠ i₂ := by simp [i₀, i₂]
  have h₀₃ : i₀ ≠ i₃ := by simp [i₀, i₃]
  have h₁₂ : i₁ ≠ i₂ := by simp [i₁, i₂]
  have h₁₃ : i₁ ≠ i₃ := by simp [i₁, i₃]
  have h₂₃ : i₂ ≠ i₃ := by simp [i₂, i₃]
  obtain ⟨u, hu⟩ := exists_peak_walsh_of_not_flat
    f k hnEq hpc i₀ i₁ h₀₁ v hv
  have hu₀₁ := walshFace_neighbors_eq_zero_of_peak
    f k hnEq hpc i₀ i₁ h₀₁ u hu
  have hu₀₂ := walshFace_neighbors_eq_zero_of_peak
    f k hnEq hpc i₀ i₂ h₀₂ u hu
  have hu₀₃ := walshFace_neighbors_eq_zero_of_peak
    f k hnEq hpc i₀ i₃ h₀₃ u hu
  let b := u + coordinateDirection i₀
  have hb₀ : walshTransform f b = 0 := hu₀₁.1
  have hb₁ : walshTransform f (b + coordinateDirection i₁) = 0 := by
    rw [add_coordinateDirection_coordinateDirection u i₀ i₁ h₀₁]
    exact hu₀₁.2.2
  have hb₂ : walshTransform f (b + coordinateDirection i₂) = 0 := by
    rw [add_coordinateDirection_coordinateDirection u i₀ i₂ h₀₂]
    exact hu₀₂.2.2
  have hb₃ : walshTransform f (b + coordinateDirection i₃) = 0 := by
    rw [add_coordinateDirection_coordinateDirection u i₀ i₃ h₀₃]
    exact hu₀₃.2.2
  have hpeak₂ := walshFace_fourth_is_peak_of_three_zeros
    f k hnEq hpc i₁ i₂ h₁₂ b hb₀ hb₁ hb₂
  have hpeak₃ := walshFace_fourth_is_peak_of_three_zeros
    f k hnEq hpc i₁ i₃ h₁₃ b hb₀ hb₁ hb₃
  let c := u + coordinatePairDirection i₀ i₁
  have hc₀ : walshTransform f c = 0 := hu₀₁.2.2
  have hc₂ :
      (walshTransform f (c + coordinateDirection i₂)).natAbs =
        2 ^ (k + 1) := by
    rw [← add_coordinateDirection_pair_eq_add_pair_coordinateDirection
      u i₀ i₁ i₂ h₀₁ h₁₂]
    exact hpeak₂
  have hc₃ :
      (walshTransform f (c + coordinateDirection i₃)).natAbs =
        2 ^ (k + 1) := by
    rw [← add_coordinateDirection_pair_eq_add_pair_coordinateDirection
      u i₀ i₁ i₃ h₀₁ h₁₃]
    exact hpeak₃
  rcases walshFace_peak_or_flat f k hnEq hpc i₂ i₃ h₂₃ c with
    hpeak | hflat
  · rcases hpeak with hp₀ | hp₂ | hp₃ | hp₂₃
    · rw [hc₀] at hp₀
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [hp₂.2.2.1] at hc₃
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [hp₃.2.2.1] at hc₂
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
    · rw [hp₂₃.2.2.1] at hc₂
      have hpositive := Nat.two_pow_pos (k + 1)
      omega
  · rw [hc₀] at hflat
    have hne : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by omega)
    exact (hne hflat.1.symm).elim

/-- In even dimension at least four, `PC(n-2)` is equivalent to bentness. -/
theorem satisfiesPropagationCriterion_pred_two_iff_isBent_of_even
    (f : BooleanFunction n) (hn : 4 ≤ n) (heven : Even n) :
    SatisfiesPropagationCriterion (n - 2) f ↔ IsBent f := by
  constructor
  · exact isBent_of_satisfiesPropagationCriterion_pred_two_of_even f hn heven
  · intro hf
    exact ((isBent_iff_satisfiesPropagationCriterion_dimension f).1 hf).mono (by omega)

/-- In even dimension at least four, `PC(n-2)` upgrades to `PC(n)`. -/
theorem satisfiesPropagationCriterion_dimension_of_pred_two_of_even
    (f : BooleanFunction n) (hn : 4 ≤ n) (heven : Even n)
    (hf : SatisfiesPropagationCriterion (n - 2) f) :
    SatisfiesPropagationCriterion n f :=
  (isBent_iff_satisfiesPropagationCriterion_dimension f).1
    (isBent_of_satisfiesPropagationCriterion_pred_two_of_even f hn heven hf)

/-- No balanced Boolean function in even dimension at least four satisfies `PC(n-2)`. -/
theorem not_satisfiesPropagationCriterion_pred_two_of_even_of_isBalanced
    (f : BooleanFunction n) (hn : 4 ≤ n) (heven : Even n)
    (hf : IsBalanced f) :
    ¬ SatisfiesPropagationCriterion (n - 2) f := by
  intro hpc
  exact not_isBalanced_of_isBent f
    (isBent_of_satisfiesPropagationCriterion_pred_two_of_even f hn heven hpc) hf

/-- The full-weight direction in the binary cube. -/
def fullDirection (n : ℕ) : FABL.F₂Cube n :=
  FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))

@[simp] theorem fullDirection_apply (i : Fin n) :
    fullDirection n i = 1 := by
  simp [fullDirection]

@[simp] theorem f₂Support_fullDirection :
    FABL.f₂Support (fullDirection n) = Finset.univ := by
  ext i
  simp [FABL.mem_f₂Support, fullDirection]

@[simp] theorem card_f₂Support_fullDirection :
    (FABL.f₂Support (fullDirection n)).card = n := by
  simp

theorem fullDirection_ne_zero (hn : 0 < n) :
    fullDirection n ≠ 0 := by
  intro h
  have hi := congrFun h (⟨0, hn⟩ : Fin n)
  simp at hi

/-- The diagonal quotient map
`(x₁,…,xₘ,xₘ₊₁) ↦ (x₁+xₘ₊₁,…,xₘ+xₘ₊₁)`. -/
def oddDiagonalProjection (m : ℕ) :
    FABL.F₂Cube (m + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube m where
  toFun x i := x i.castSucc + x (Fin.last m)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    abel
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact (mul_add c _ _).symm

@[simp] theorem oddDiagonalProjection_apply
    (m : ℕ) (x : FABL.F₂Cube (m + 1)) (i : Fin m) :
    oddDiagonalProjection m x i = x i.castSucc + x (Fin.last m) :=
  rfl

@[simp] theorem oddDiagonalProjection_fullDirection :
    oddDiagonalProjection m (fullDirection (m + 1)) = 0 := by
  funext i
  simp only [oddDiagonalProjection_apply, fullDirection_apply, Pi.zero_apply]
  exact ZModModule.add_self 1

theorem oddDiagonalProjection_eq_zero_iff
    (x : FABL.F₂Cube (m + 1)) :
    oddDiagonalProjection m x = 0 ↔
      x = 0 ∨ x = fullDirection (m + 1) := by
  constructor
  · intro hx
    by_cases hlast : x (Fin.last m) = 0
    · left
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact hlast
      · have hcoordinate := congrFun hx j
        change x j.castSucc + x (Fin.last m) = 0 at hcoordinate
        rw [hlast, add_zero] at hcoordinate
        exact hcoordinate
    · right
      have hlastOne : x (Fin.last m) = 1 :=
        Fin.eq_one_of_ne_zero _ hlast
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa using hlastOne
      · have hcoordinate := congrFun hx j
        change x j.castSucc + x (Fin.last m) = 0 at hcoordinate
        rw [hlastOne] at hcoordinate
        have hvalue := eq_neg_of_add_eq_zero_left hcoordinate
        simpa using hvalue
  · rintro (rfl | rfl)
    · exact (oddDiagonalProjection m).map_zero
    · exact oddDiagonalProjection_fullDirection

private def oddDiagonalCoordinateLinearMap (m : ℕ) :
    FABL.F₂Cube (m + 1) →ₗ[FABL.𝔽₂]
      (FABL.F₂Cube m × FABL.𝔽₂) where
  toFun x := (oddDiagonalProjection m x, x (Fin.last m))
  map_add' x y := by
    apply Prod.ext
    · exact (oddDiagonalProjection m).map_add x y
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · exact (oddDiagonalProjection m).map_smul c x
    · rfl

private theorem oddDiagonalCoordinateLinearMap_bijective (m : ℕ) :
    Function.Bijective (oddDiagonalCoordinateLinearMap m) := by
  constructor
  · intro x y hxy
    have hprojection := congrArg Prod.fst hxy
    have hlast := congrArg Prod.snd hxy
    change x (Fin.last m) = y (Fin.last m) at hlast
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact hlast
    · have hcoordinate := congrFun hprojection j
      change x j.castSucc + x (Fin.last m) =
        y j.castSucc + y (Fin.last m) at hcoordinate
      rw [hlast] at hcoordinate
      exact add_right_cancel hcoordinate
  · rintro ⟨y, z⟩
    let x : FABL.F₂Cube (m + 1) := Fin.snoc (fun i ↦ y i + z) z
    refine ⟨x, ?_⟩
    apply Prod.ext
    · funext i
      simp only [oddDiagonalCoordinateLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        oddDiagonalProjection, x, Fin.snoc_castSucc, Fin.snoc_last]
      rw [add_assoc, ZModModule.add_self, add_zero]
    · simp only [oddDiagonalCoordinateLinearMap, LinearMap.coe_mk,
        AddHom.coe_mk, x, Fin.snoc_last]

private noncomputable def oddDiagonalCoordinateLinearEquiv (m : ℕ) :
    FABL.F₂Cube (m + 1) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube m × FABL.𝔽₂) :=
  LinearEquiv.ofBijective (oddDiagonalCoordinateLinearMap m)
    (oddDiagonalCoordinateLinearMap_bijective m)

@[simp] private theorem oddDiagonalProjection_symm_coordinateLinearEquiv
    (p : FABL.F₂Cube m × FABL.𝔽₂) :
    oddDiagonalProjection m ((oddDiagonalCoordinateLinearEquiv m).symm p) = p.1 := by
  have h := (oddDiagonalCoordinateLinearEquiv m).apply_symm_apply p
  exact congrArg Prod.fst h

private theorem walshTransform_zero_comp_oddDiagonalProjection
    (g : BooleanFunction m) :
    walshTransform (fun x ↦ g (oddDiagonalProjection m x)) 0 =
      2 * walshTransform g 0 := by
  classical
  unfold walshTransform
  calc
    ∑ x : FABL.F₂Cube (m + 1),
        walshTerm (fun x ↦ g (oddDiagonalProjection m x)) 0 x =
        ∑ p : FABL.F₂Cube m × FABL.𝔽₂,
          walshTerm (fun x ↦ g (oddDiagonalProjection m x)) 0
            ((oddDiagonalCoordinateLinearEquiv m).symm p) := by
      exact (Fintype.sum_equiv (oddDiagonalCoordinateLinearEquiv m).symm.toEquiv
        (fun p ↦ walshTerm (fun x ↦ g (oddDiagonalProjection m x)) 0
          ((oddDiagonalCoordinateLinearEquiv m).symm p))
        (fun x ↦ walshTerm (fun x ↦ g (oddDiagonalProjection m x)) 0 x)
        (fun _ ↦ rfl)).symm
    _ = ∑ p : FABL.F₂Cube m × FABL.𝔽₂, bitSignInt (g p.1) := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [walshTerm, FABL.f₂DotProduct]
    _ = ∑ y : FABL.F₂Cube m, ∑ _z : FABL.𝔽₂, bitSignInt (g y) := by
      rw [Fintype.sum_prod_type]
    _ = 2 * ∑ y : FABL.F₂Cube m, bitSignInt (g y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [show (Finset.univ : Finset FABL.𝔽₂) = {0, 1} by rfl]
      simp
    _ = 2 * ∑ y : FABL.F₂Cube m, walshTerm g 0 y := by
      congr 1
      apply Finset.sum_congr rfl
      intro y _hy
      simp [walshTerm, FABL.f₂DotProduct]

private theorem isBalanced_comp_oddDiagonalProjection
    (g : BooleanFunction m) (hg : IsBalanced g) :
    IsBalanced (fun x ↦ g (oddDiagonalProjection m x)) := by
  apply (isBalanced_iff_walshTransform_zero_eq_zero _).2
  rw [walshTransform_zero_comp_oddDiagonalProjection,
    (isBalanced_iff_walshTransform_zero_eq_zero g).1 hg, mul_zero]

/-- Adding a Boolean constant preserves balancedness. -/
theorem isBalanced_add_constant_iff
    (g : BooleanFunction m) (c : FABL.𝔽₂) :
    IsBalanced (fun x ↦ g x + c) ↔ IsBalanced g := by
  have hfunction : (fun x ↦ g x + c) = g + FABL.affineFunction c 0 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct]
  rw [hfunction, isBalanced_iff_walshTransform_zero_eq_zero,
    isBalanced_iff_walshTransform_zero_eq_zero,
    walshTransform_add_affineFunction]
  simp only [add_zero]
  have hsign : bitSignInt c ≠ 0 := by
    fin_cases c <;> simp [bitSignInt]
  rw [mul_eq_zero]
  simp only [hsign, false_or]

/-- Adding an affine function preserves every propagation criterion. -/
theorem satisfiesPropagationCriterion_add_affineFunction_iff
    (l : ℕ) (f : BooleanFunction n) (c : FABL.𝔽₂)
    (u : FABL.F₂Cube n) :
    SatisfiesPropagationCriterion l (f + FABL.affineFunction c u) ↔
      SatisfiesPropagationCriterion l f := by
  constructor
  · intro h a ha
    have hb := h a ha
    change IsBalanced
      (FABL.booleanDerivative
        (fun x ↦ f x + FABL.affineFunction c u x) a) at hb
    rw [booleanDerivative_add_affineFunction] at hb
    exact (isBalanced_add_constant_iff
      (FABL.booleanDerivative f a) (FABL.f₂DotProduct u a)).1 hb
  · intro h a ha
    change IsBalanced
      (FABL.booleanDerivative
        (fun x ↦ f x + FABL.affineFunction c u x) a)
    rw [booleanDerivative_add_affineFunction]
    exact (isBalanced_add_constant_iff
      (FABL.booleanDerivative f a) (FABL.f₂DotProduct u a)).2 (h a ha)

private theorem twoSquareClassification_evenPower
    (k : ℕ) (x y : ℤ)
    (h : x ^ 2 + y ^ 2 = (2 : ℤ) ^ (2 * k)) :
    (x = 0 ∧ y.natAbs = 2 ^ k) ∨
      (y = 0 ∧ x.natAbs = 2 ^ k) := by
  have hsumDifference :
      (x + y) ^ 2 + (x - y) ^ 2 = (2 : ℤ) ^ (2 * k + 1) := by
    calc
      (x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by ring
      _ = 2 * (2 : ℤ) ^ (2 * k) := by rw [h]
      _ = (2 : ℤ) ^ (2 * k + 1) := by
        rw [pow_succ]
        ring
  have habs := natAbs_eq_two_pow_of_sq_add_sq_eq_two_pow_odd
    k (x + y) (x - y) hsumDifference
  have hsquares : (x + y) ^ 2 = (x - y) ^ 2 :=
    Int.natAbs_eq_iff_sq_eq.mp (habs.1.trans habs.2.symm)
  have hproduct : x * y = 0 := by nlinarith
  rcases mul_eq_zero.mp hproduct with hx | hy
  · left
    subst x
    refine ⟨rfl, ?_⟩
    simpa only [zero_add] using habs.1
  · right
    subst y
    refine ⟨rfl, ?_⟩
    simpa only [add_zero] using habs.1

private theorem autocorrelation_eq_zero_of_pc_pred_one_of_ne_fullDirection
    (f : BooleanFunction n)
    (hpc : SatisfiesPropagationCriterion (n - 1) f)
    (a : FABL.F₂Cube n) (haZero : a ≠ 0)
    (haFull : a ≠ fullDirection n) :
    autocorrelation f a = 0 := by
  apply (satisfiesPropagationCriterion_iff_autocorrelation_eq_zero
    (n - 1) f).1 hpc a haZero
  have hcardLe : (FABL.f₂Support a).card ≤ n := by
    calc
      (FABL.f₂Support a).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hcardNe : (FABL.f₂Support a).card ≠ n := by
    intro hcard
    have hsupport : FABL.f₂Support a = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hcard
    apply haFull
    apply (FABL.f₂CubeEquivFinset n).injective
    change FABL.f₂Support a = FABL.f₂Support (fullDirection n)
    rw [hsupport, f₂Support_fullDirection]
  omega

private theorem autocorrelation_eq_two_spikes_of_pc_pred_one
    (f : BooleanFunction n) (hn : 0 < n)
    (hpc : SatisfiesPropagationCriterion (n - 1) f) :
    autocorrelation f = fun a ↦
      if a = 0 then (2 : ℝ) ^ n
      else if a = fullDirection n then autocorrelation f (fullDirection n)
      else 0 := by
  funext a
  by_cases haZero : a = 0
  · subst a
    simp [autocorrelation_zero]
  · by_cases haFull : a = fullDirection n
    · subst a
      simp [fullDirection_ne_zero hn]
    · rw [if_neg haZero, if_neg haFull]
      exact autocorrelation_eq_zero_of_pc_pred_one_of_ne_fullDirection
        f hpc a haZero haFull

private theorem walshTransform_sq_eq_two_pow_add_fullAutocorrelation
    (f : BooleanFunction n) (hn : 0 < n)
    (hpc : SatisfiesPropagationCriterion (n - 1) f)
    (u : FABL.F₂Cube n) :
    (walshTransform f u : ℝ) ^ 2 =
      (2 : ℝ) ^ n +
        FABL.vectorWalshCharacter u (fullDirection n) *
          autocorrelation f (fullDirection n) := by
  have hauto := autocorrelation_eq_two_spikes_of_pc_pred_one f hn hpc
  have hfullNe := fullDirection_ne_zero hn
  let A : ℝ := autocorrelation f (fullDirection n)
  have hautoA : autocorrelation f = fun a ↦
      if a = 0 then (2 : ℝ) ^ n
      else if a = fullDirection n then A else 0 := by
    simpa only [A] using hauto
  change (walshTransform f u : ℝ) ^ 2 =
    (2 : ℝ) ^ n + FABL.vectorWalshCharacter u (fullDirection n) * A
  calc
    (walshTransform f u : ℝ) ^ 2 =
        rawFourierTransform (autocorrelation f) u :=
      (rawFourierTransform_autocorrelation f u).symm
    _ = (2 : ℝ) ^ n +
        FABL.vectorWalshCharacter u (fullDirection n) *
          A := by
      rw [rawFourierTransform, hautoA]
      calc
        (∑ x, (if x = 0 then (2 : ℝ) ^ n
            else if x = fullDirection n then
              A else 0) *
              FABL.vectorWalshCharacter u x) =
            ∑ x, (
              (if x = 0 then
                (2 : ℝ) ^ n * FABL.vectorWalshCharacter u x else 0) +
              (if x = fullDirection n then
                A *
                  FABL.vectorWalshCharacter u x else 0)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hxZero : x = 0
          · subst x
            simp [Ne.symm hfullNe]
          · simp [hxZero]
        _ = (2 : ℝ) ^ n * FABL.vectorWalshCharacter u 0 +
              A *
                FABL.vectorWalshCharacter u (fullDirection n) := by
          rw [Finset.sum_add_distrib,
            Fintype.sum_ite_eq', Fintype.sum_ite_eq']
        _ = (2 : ℝ) ^ n +
              FABL.vectorWalshCharacter u (fullDirection n) *
                A := by
          simp
          ring

private theorem isLinearStructure_fullDirection_of_pc_pred_one_of_odd
    (f : BooleanFunction n) (hn : 0 < n) (hodd : Odd n)
    (hpc : SatisfiesPropagationCriterion (n - 1) f) :
    IsLinearStructure f (fullDirection n) := by
  let i : Fin n := ⟨0, hn⟩
  have hcharZero :
      FABL.vectorWalshCharacter (0 : FABL.F₂Cube n) (fullDirection n) = 1 := by
    simp
  have hcharCoordinate :
      FABL.vectorWalshCharacter (coordinateDirection i) (fullDirection n) =
        (-1 : ℝ) := by
    rw [coordinateDirection,
      FABL.vectorWalshCharacter_f₂CubeOfFinset_singleton,
      fullDirection_apply, FABL.binarySign_one]
  have hsqZero :=
    walshTransform_sq_eq_two_pow_add_fullAutocorrelation f hn hpc 0
  have hsqCoordinate :=
    walshTransform_sq_eq_two_pow_add_fullAutocorrelation
      f hn hpc (coordinateDirection i)
  rw [hcharZero, one_mul] at hsqZero
  rw [hcharCoordinate, neg_one_mul] at hsqCoordinate
  have hsumReal :
      (walshTransform f 0 : ℝ) ^ 2 +
          (walshTransform f (coordinateDirection i) : ℝ) ^ 2 =
        (2 : ℝ) ^ (n + 1) := by
    calc
      (walshTransform f 0 : ℝ) ^ 2 +
          (walshTransform f (coordinateDirection i) : ℝ) ^ 2 =
          2 * (2 : ℝ) ^ n := by rw [hsqZero, hsqCoordinate]; ring
      _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  have hsumInt :
      walshTransform f 0 ^ 2 +
          walshTransform f (coordinateDirection i) ^ 2 =
        (2 : ℤ) ^ (n + 1) := by
    exact_mod_cast hsumReal
  obtain ⟨k, hk⟩ := hodd
  have hexponent : n + 1 = 2 * (k + 1) := by omega
  rw [hexponent] at hsumInt
  rcases twoSquareClassification_evenPower (k + 1)
      (walshTransform f 0)
      (walshTransform f (coordinateDirection i)) hsumInt with
    hzero | hcoordinate
  · apply (isLinearStructure_iff_abs_autocorrelation_eq_two_pow
      f (fullDirection n)).2
    have hzeroCast : (walshTransform f 0 : ℝ) = 0 := by
      exact_mod_cast hzero.1
    rw [hzeroCast, zero_pow (by norm_num)] at hsqZero
    have hauto :
        autocorrelation f (fullDirection n) = -((2 : ℝ) ^ n) := by
      linarith
    rw [hauto, abs_neg, abs_of_pos (by positivity)]
  · apply (isLinearStructure_iff_abs_autocorrelation_eq_two_pow
      f (fullDirection n)).2
    have hcoordinateCast :
        (walshTransform f (coordinateDirection i) : ℝ) = 0 := by
      exact_mod_cast hcoordinate.1
    rw [hcoordinateCast, zero_pow (by norm_num)] at hsqCoordinate
    have hauto :
        autocorrelation f (fullDirection n) = (2 : ℝ) ^ n := by
      linarith
    rw [hauto, abs_of_pos (by positivity)]

/-- Pulling a Boolean function back along the odd diagonal quotient. -/
def oddDiagonalBentLift (g : BooleanFunction m) : BooleanFunction (m + 1) :=
  fun x ↦ g (oddDiagonalProjection m x)

/-- The source-facing diagonal bent normal form in odd dimension. -/
def HasOddDiagonalBentNormalForm (f : BooleanFunction (m + 1)) : Prop :=
  ∃ (g : BooleanFunction m), IsBent g ∧
    ∃ (c : FABL.𝔽₂) (u : FABL.F₂Cube (m + 1)),
      f = oddDiagonalBentLift g + FABL.affineFunction c u

private def oddDiagonalSection (y : FABL.F₂Cube m) :
    FABL.F₂Cube (m + 1) :=
  Fin.snoc y 0

private theorem oddDiagonalSection_add_last_smul_fullDirection
    (x : FABL.F₂Cube (m + 1)) :
    oddDiagonalSection (oddDiagonalProjection m x) +
        x (Fin.last m) • fullDirection (m + 1) = x := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [oddDiagonalSection]
  · simp only [oddDiagonalSection, Fin.snoc_castSucc,
      oddDiagonalProjection_apply, Pi.add_apply, Pi.smul_apply,
      fullDirection_apply, smul_eq_mul, mul_one]
    rw [add_assoc, ZModModule.add_self, add_zero]

private theorem value_eq_oddDiagonalSection_add_last_mul
    (f : BooleanFunction (m + 1)) (epsilon : FABL.𝔽₂)
    (hlinear : ∀ x,
      FABL.booleanDerivative f (fullDirection (m + 1)) x = epsilon)
    (x : FABL.F₂Cube (m + 1)) :
    f x = f (oddDiagonalSection (oddDiagonalProjection m x)) +
      epsilon * x (Fin.last m) := by
  let y := oddDiagonalSection (oddDiagonalProjection m x)
  change f x = f y + epsilon * x (Fin.last m)
  have hx := oddDiagonalSection_add_last_smul_fullDirection x
  by_cases hlast : x (Fin.last m) = 0
  · have hxy : y = x := by
      simpa [y, hlast] using hx
    rw [hxy, hlast, mul_zero, add_zero]
  · have hlastOne : x (Fin.last m) = 1 :=
      Fin.eq_one_of_ne_zero _ hlast
    have hxy : y + fullDirection (m + 1) = x := by
      simpa [y, hlastOne] using hx
    have hderivative := hlinear y
    rw [FABL.booleanDerivative, hxy] at hderivative
    rw [hlastOne, mul_one]
    calc
      f x = (f y + f y) + f x := by rw [ZModModule.add_self, zero_add]
      _ = f y + (f y + f x) := by abel
      _ = f y + epsilon := by rw [hderivative]

private theorem booleanDerivative_oddDiagonalBentLift
    (g : BooleanFunction m) (a : FABL.F₂Cube (m + 1)) :
    FABL.booleanDerivative (oddDiagonalBentLift g) a =
      fun x ↦ FABL.booleanDerivative g (oddDiagonalProjection m a)
        (oddDiagonalProjection m x) := by
  funext x
  simp only [FABL.booleanDerivative, oddDiagonalBentLift]
  rw [(oddDiagonalProjection m).map_add]

private theorem f₂DotProduct_coordinateDirection
    (i : Fin n) (x : FABL.F₂Cube n) :
    FABL.f₂DotProduct (coordinateDirection i) x = x i := by
  rw [coordinateDirection, FABL.f₂DotProduct_f₂CubeOfFinset]
  simp [FABL.coordinateSum]

/-- In odd dimension at least three, `PC(n-1)` is exactly the diagonal
pullback of a bent function, up to an arbitrary affine summand. -/
theorem satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1)) :
    SatisfiesPropagationCriterion (2 * k) f ↔
      HasOddDiagonalBentNormalForm f := by
  constructor
  · intro hpc
    have hpcPred :
        SatisfiesPropagationCriterion ((2 * k + 1) - 1) f := by
      simpa only [Nat.add_sub_cancel] using hpc
    have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
    obtain ⟨epsilon, hlinear⟩ :=
      isLinearStructure_fullDirection_of_pc_pred_one_of_odd
        f (by omega) hodd hpcPred
    let L : FABL.F₂Cube (2 * k + 1) ≃ₗ[FABL.𝔽₂]
        FABL.F₂Cube (2 * k + 1) :=
      LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube (2 * k + 1))
    have hbalanced (a : FABL.F₂Cube (2 * k)) (ha : a ≠ 0) :
        IsBalanced
          (FABL.booleanDerivative f
            (L (Fin.append a (singletonF₂Cube 0)))) := by
      apply hpc
      constructor
      · change Fin.append a (singletonF₂Cube 0) ≠ 0
        intro hzero
        apply ha
        funext i
        have hi := congrFun hzero (Fin.castAdd 1 i)
        simpa using hi
      · change (FABL.f₂Support
          (Fin.append a (singletonF₂Cube 0))).card ≤ 2 * k
        rw [card_f₂Support_append]
        have hcard : (FABL.f₂Support a).card ≤ 2 * k := by
          calc
            (FABL.f₂Support a).card ≤
                (Finset.univ : Finset (Fin (2 * k))).card :=
              Finset.card_le_card (Finset.subset_univ _)
            _ = 2 * k := by simp
        have htail :
            (FABL.f₂Support (singletonF₂Cube 0)).card = 0 := by
          apply Finset.card_eq_zero.mpr
          ext i
          simp [FABL.mem_f₂Support, singletonF₂Cube]
        rw [htail, Nat.add_zero]
        exact hcard
    have hrestrictionBent :=
      isBent_linearHyperplaneRestriction_of_balanced_derivatives
        k f L hbalanced 0
    let g : BooleanFunction (2 * k) :=
      fun y ↦ f (oddDiagonalSection y)
    have hg : IsBent g := by
      have hrestriction : linearHyperplaneRestriction f L 0 = g := by
        funext y
        simp [linearHyperplaneRestriction, firstBlockSlice, L, g,
          oddDiagonalSection, Fin.append_right_eq_snoc]
      rw [← hrestriction]
      exact hrestrictionBent
    let lastDirection : FABL.F₂Cube (2 * k + 1) :=
      epsilon • coordinateDirection (Fin.last (2 * k))
    refine ⟨g, hg, 0, lastDirection, ?_⟩
    funext x
    have hvalue := value_eq_oddDiagonalSection_add_last_mul
      f epsilon hlinear x
    have haffine :
        FABL.affineFunction 0 lastDirection x =
          epsilon * x (Fin.last (2 * k)) := by
      simp only [FABL.affineFunction, zero_add, lastDirection,
        FABL.f₂DotProduct, smul_dotProduct]
      rw [show dotProduct (coordinateDirection (Fin.last (2 * k))) x =
          x (Fin.last (2 * k)) from
        f₂DotProduct_coordinateDirection (Fin.last (2 * k)) x]
      rw [smul_eq_mul]
    change f x = g (oddDiagonalProjection (2 * k) x) +
      FABL.affineFunction 0 lastDirection x
    rw [haffine]
    exact hvalue
  · rintro ⟨g, hg, c, u, rfl⟩
    apply (satisfiesPropagationCriterion_add_affineFunction_iff
      (2 * k) (oddDiagonalBentLift g) c u).2
    intro a ha
    have hprojectionNe : oddDiagonalProjection (2 * k) a ≠ 0 := by
      intro hzero
      rcases (oddDiagonalProjection_eq_zero_iff a).1 hzero with
        haZero | haFull
      · exact ha.1 haZero
      · have hweight : (FABL.f₂Support a).card = 2 * k + 1 := by
          rw [haFull, card_f₂Support_fullDirection]
        have hle := ha.2
        rw [hweight] at hle
        omega
    rw [booleanDerivative_oddDiagonalBentLift]
    exact isBalanced_comp_oddDiagonalProjection
      (FABL.booleanDerivative g (oddDiagonalProjection (2 * k) a))
      ((isBent_iff_forall_nonzero_derivative_isBalanced g).1
        hg (oddDiagonalProjection (2 * k) a) hprojectionNe)

private theorem walshFace_pair_of_satisfiesPropagationCriterion_pred_two
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n) :
    FourSquarePair (k + 1)
      (walshTransform f v)
      (walshTransform f (v + coordinateDirection i))
      (walshTransform f (v + coordinateDirection j))
      (walshTransform f (v + coordinatePairDirection i j)) := by
  have hsum :=
    walshSquareFace_eq_of_satisfiesPropagationCriterion_pred_two
      f (by omega) hpc i j hij v
  have hexponent : n + 2 = 2 * (k + 1) + 1 := by omega
  rw [hexponent] at hsum
  exact fourSquarePairClassification (k + 1) _ _ _ _ hsum

private def walshNonzeroIndicator (f : BooleanFunction n) : BooleanFunction n :=
  fun v ↦ if walshTransform f v = 0 then 0 else 1

private theorem ne_zero_of_natAbs_eq_two_pow
    {x : ℤ} {k : ℕ} (h : x.natAbs = 2 ^ k) : x ≠ 0 := by
  intro hx
  rw [hx, Int.natAbs_zero] at h
  have hpositive := Nat.two_pow_pos k
  omega

private theorem walshNonzeroIndicator_face_sum_eq_zero
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n) :
    walshNonzeroIndicator f v +
        walshNonzeroIndicator f (v + coordinateDirection i) +
        walshNonzeroIndicator f (v + coordinateDirection j) +
        walshNonzeroIndicator f (v + coordinatePairDirection i j) = 0 := by
  rcases walshFace_pair_of_satisfiesPropagationCriterion_pred_two
      f k hn hpc i j hij v with hp | hp | hp | hp | hp | hp
  · have h₀ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₁ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₀, h₁, hp.2.2.1, hp.2.2.2]
  · have h₀ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₂ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₀, h₂, hp.2.2.1, hp.2.2.2]
  · have h₀ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₃ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₀, h₃, hp.2.2.1, hp.2.2.2]
  · have h₁ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₂ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₁, h₂, hp.2.2.1, hp.2.2.2]
  · have h₁ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₃ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₁, h₃, hp.2.2.1, hp.2.2.2]
  · have h₂ := ne_zero_of_natAbs_eq_two_pow hp.1
    have h₃ := ne_zero_of_natAbs_eq_two_pow hp.2.1
    simp [walshNonzeroIndicator, h₂, h₃, hp.2.2.1, hp.2.2.2]

private theorem f₂CubeOfFinset_insert
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    FABL.f₂CubeOfFinset (insert i S) =
      FABL.f₂CubeOfFinset S + coordinateDirection i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hi]
  · simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hji]

/-- A Boolean function whose derivative vanishes in every coordinate
direction is constant. -/
theorem eq_constant_of_coordinateDerivatives_eq_zero
    (h : BooleanFunction n)
    (hderivative : ∀ i : Fin n,
      FABL.booleanDerivative h (coordinateDirection i) = 0) :
    ∀ x, h x = h 0 := by
  have hsets : ∀ S : Finset (Fin n),
      h (FABL.f₂CubeOfFinset S) = h 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | @insert i S hi ih =>
        have hd := congrFun (hderivative i) (FABL.f₂CubeOfFinset S)
        rw [FABL.booleanDerivative, ← f₂CubeOfFinset_insert S i hi] at hd
        change h (FABL.f₂CubeOfFinset S) +
          h (FABL.f₂CubeOfFinset (insert i S)) = 0 at hd
        calc
          h (FABL.f₂CubeOfFinset (insert i S)) =
              (h (FABL.f₂CubeOfFinset S) +
                h (FABL.f₂CubeOfFinset S)) +
                  h (FABL.f₂CubeOfFinset (insert i S)) := by
            rw [ZModModule.add_self, zero_add]
          _ = h (FABL.f₂CubeOfFinset S) +
              (h (FABL.f₂CubeOfFinset S) +
                h (FABL.f₂CubeOfFinset (insert i S))) := by abel
          _ = h (FABL.f₂CubeOfFinset S) := by rw [hd, add_zero]
          _ = h 0 := ih
  intro x
  have hx := (FABL.f₂CubeEquivFinset n).left_inv x
  rw [← hx]
  exact hsets (FABL.f₂Support x)

private theorem secondBooleanDerivative_walshNonzeroIndicator_coordinate_eq_zero
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) :
    secondBooleanDerivative (walshNonzeroIndicator f)
      (coordinateDirection i) (coordinateDirection j) = 0 := by
  funext v
  by_cases hij : i = j
  · subst j
    rw [secondBooleanDerivative_apply]
    have harg :
        v + coordinateDirection i + coordinateDirection i = v := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    rw [harg]
    calc
      walshNonzeroIndicator f v +
            walshNonzeroIndicator f (v + coordinateDirection i) +
          walshNonzeroIndicator f (v + coordinateDirection i) +
        walshNonzeroIndicator f v =
          (walshNonzeroIndicator f v + walshNonzeroIndicator f v) +
            (walshNonzeroIndicator f (v + coordinateDirection i) +
              walshNonzeroIndicator f (v + coordinateDirection i)) := by abel
      _ = 0 := by rw [ZModModule.add_self, ZModModule.add_self, add_zero]
  · rw [secondBooleanDerivative_apply]
    have hsum := walshNonzeroIndicator_face_sum_eq_zero
      f k hn hpc i j hij v
    have hfourth :
        v + coordinateDirection i + coordinateDirection j =
          v + coordinatePairDirection i j := by
      rw [coordinatePairDirection_eq_add i j hij]
      abel
    rw [hfourth]
    exact hsum

private theorem coordinateDerivative_walshNonzeroIndicator_eq_constant
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i : Fin n) :
    FABL.booleanDerivative (walshNonzeroIndicator f) (coordinateDirection i) =
      fun _ ↦ FABL.booleanDerivative (walshNonzeroIndicator f)
        (coordinateDirection i) 0 := by
  funext v
  apply eq_constant_of_coordinateDerivatives_eq_zero
    (FABL.booleanDerivative (walshNonzeroIndicator f) (coordinateDirection i))
  intro j
  exact secondBooleanDerivative_walshNonzeroIndicator_coordinate_eq_zero
    f k hn hpc j i

private theorem exists_affineFunction_eq_walshNonzeroIndicator
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f) :
    ∃ (b : FABL.𝔽₂) (q : FABL.F₂Cube n),
      walshNonzeroIndicator f = FABL.affineFunction b q := by
  let s := walshNonzeroIndicator f
  let b := s 0
  let q : FABL.F₂Cube n := fun i ↦
    FABL.booleanDerivative s (coordinateDirection i) 0
  let r : BooleanFunction n := s + FABL.affineFunction b q
  have hconstant (i : Fin n) :
      FABL.booleanDerivative s (coordinateDirection i) = fun _ ↦ q i := by
    exact coordinateDerivative_walshNonzeroIndicator_eq_constant
      f k hn hpc i
  have hrDerivative (i : Fin n) :
      FABL.booleanDerivative r (coordinateDirection i) = 0 := by
    funext x
    change FABL.booleanDerivative
      (fun y ↦ s y + FABL.affineFunction b q y)
        (coordinateDirection i) x = 0
    rw [congrFun (booleanDerivative_add_affineFunction
      s b q (coordinateDirection i)) x]
    rw [congrFun (hconstant i) x]
    have hdot : FABL.f₂DotProduct q (coordinateDirection i) = q i := by
      rw [FABL.f₂DotProduct, dotProduct_comm]
      exact f₂DotProduct_coordinateDirection i q
    rw [hdot, ZModModule.add_self]
  have hrConstant := eq_constant_of_coordinateDerivatives_eq_zero r hrDerivative
  have hrZero : r 0 = 0 := by
    change s 0 + (b + FABL.f₂DotProduct q 0) = 0
    have hdot : FABL.f₂DotProduct q 0 = 0 := by
      simp [FABL.f₂DotProduct]
    rw [hdot, add_zero]
    change s 0 + s 0 = 0
    exact ZModModule.add_self _
  refine ⟨b, q, ?_⟩
  funext x
  have hx := hrConstant x
  rw [hrZero] at hx
  change s x + FABL.affineFunction b q x = 0 at hx
  have hneg := eq_neg_of_add_eq_zero_left hx
  simpa using hneg

@[simp] private theorem walshNonzeroIndicator_eq_zero_iff
    (f : BooleanFunction n) (v : FABL.F₂Cube n) :
    walshNonzeroIndicator f v = 0 ↔ walshTransform f v = 0 := by
  unfold walshNonzeroIndicator
  by_cases hzero : walshTransform f v = 0
  · simp [hzero]
  · simp [hzero]

@[simp] private theorem walshNonzeroIndicator_eq_one_iff
    (f : BooleanFunction n) (v : FABL.F₂Cube n) :
    walshNonzeroIndicator f v = 1 ↔ walshTransform f v ≠ 0 := by
  unfold walshNonzeroIndicator
  by_cases hzero : walshTransform f v = 0
  · simp [hzero]
  · simp [hzero]

private theorem walshNonzeroIndicator_face_not_constant
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f)
    (i j : Fin n) (hij : i ≠ j) (v : FABL.F₂Cube n) :
    ¬ (walshNonzeroIndicator f v =
          walshNonzeroIndicator f (v + coordinateDirection i) ∧
        walshNonzeroIndicator f v =
          walshNonzeroIndicator f (v + coordinateDirection j) ∧
        walshNonzeroIndicator f v =
          walshNonzeroIndicator f (v + coordinatePairDirection i j)) := by
  intro hconstant
  rcases walshFace_pair_of_satisfiesPropagationCriterion_pred_two
      f k hn hpc i j hij v with hp | hp | hp | hp | hp | hp
  · have hv := walshNonzeroIndicator_eq_one_iff f v |>.2
      (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hvj := walshNonzeroIndicator_eq_zero_iff
      f (v + coordinateDirection j) |>.2 hp.2.2.1
    exact one_ne_zero (hv.symm.trans (hconstant.2.1.trans hvj))
  · have hv := walshNonzeroIndicator_eq_one_iff f v |>.2
      (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hvi := walshNonzeroIndicator_eq_zero_iff
      f (v + coordinateDirection i) |>.2 hp.2.2.1
    exact one_ne_zero (hv.symm.trans (hconstant.1.trans hvi))
  · have hv := walshNonzeroIndicator_eq_one_iff f v |>.2
      (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hvi := walshNonzeroIndicator_eq_zero_iff
      f (v + coordinateDirection i) |>.2 hp.2.2.1
    exact one_ne_zero (hv.symm.trans (hconstant.1.trans hvi))
  · have hvi := walshNonzeroIndicator_eq_one_iff
      f (v + coordinateDirection i) |>.2
        (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hv := walshNonzeroIndicator_eq_zero_iff f v |>.2 hp.2.2.1
    exact one_ne_zero (hvi.symm.trans (hconstant.1.symm.trans hv))
  · have hvi := walshNonzeroIndicator_eq_one_iff
      f (v + coordinateDirection i) |>.2
        (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hv := walshNonzeroIndicator_eq_zero_iff f v |>.2 hp.2.2.1
    exact one_ne_zero (hvi.symm.trans (hconstant.1.symm.trans hv))
  · have hvj := walshNonzeroIndicator_eq_one_iff
      f (v + coordinateDirection j) |>.2
        (ne_zero_of_natAbs_eq_two_pow hp.1)
    have hv := walshNonzeroIndicator_eq_zero_iff f v |>.2 hp.2.2.1
    exact one_ne_zero (hvj.symm.trans (hconstant.2.1.symm.trans hv))

private theorem exists_affineFunction_eq_walshNonzeroIndicator_highWeight
    (f : BooleanFunction n) (k : ℕ) (hn : n = 2 * k + 1)
    (hpc : SatisfiesPropagationCriterion (n - 2) f) :
    ∃ (b : FABL.𝔽₂) (q : FABL.F₂Cube n),
      walshNonzeroIndicator f = FABL.affineFunction b q ∧
        n - 1 ≤ (FABL.f₂Support q).card := by
  obtain ⟨b, q, hq⟩ :=
    exists_affineFunction_eq_walshNonzeroIndicator f k hn hpc
  have hnoPair (i j : Fin n) (hij : i ≠ j)
      (hi : q i = 0) (hj : q j = 0) : False := by
    apply walshNonzeroIndicator_face_not_constant
      f k hn hpc i j hij 0
    have hdotI : dotProduct q (coordinateDirection i) = 0 := by
      rw [dotProduct_comm]
      rw [show dotProduct (coordinateDirection i) q = q i from
        f₂DotProduct_coordinateDirection i q, hi]
    have hdotJ : dotProduct q (coordinateDirection j) = 0 := by
      rw [dotProduct_comm]
      rw [show dotProduct (coordinateDirection j) q = q j from
        f₂DotProduct_coordinateDirection j q, hj]
    have hdotPair :
        dotProduct q (coordinatePairDirection i j) = 0 := by
      rw [coordinatePairDirection_eq_add i j hij,
        dotProduct_add, hdotI, hdotJ, add_zero]
    rw [hq]
    constructor
    · simp [FABL.affineFunction, FABL.f₂DotProduct, hdotI]
    constructor
    · simp [FABL.affineFunction, FABL.f₂DotProduct, hdotJ]
    · simp [FABL.affineFunction, FABL.f₂DotProduct, hdotPair]
  have hcomplement : ((FABL.f₂Support q)ᶜ).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have hiNot : i ∉ FABL.f₂Support q := by simpa using hi
    have hjNot : j ∉ FABL.f₂Support q := by simpa using hj
    have hiZero : q i = 0 := by
      by_contra hne
      exact hiNot ((FABL.mem_f₂Support q i).2 hne)
    have hjZero : q j = 0 := by
      by_contra hne
      exact hjNot ((FABL.mem_f₂Support q j).2 hne)
    exact hnoPair i j hij hiZero hjZero
  rw [Finset.card_compl, Fintype.card_fin] at hcomplement
  refine ⟨b, q, hq, ?_⟩
  have hcard : (FABL.f₂Support q).card ≤ n := by
    calc
      (FABL.f₂Support q).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

private theorem walshTransform_natAbs_eq_zero_or_two_pow_of_pc_pred_two_odd
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hpc : SatisfiesPropagationCriterion (2 * k - 1) f)
    (v : FABL.F₂Cube (2 * k + 1)) :
    (walshTransform f v).natAbs = 0 ∨
      (walshTransform f v).natAbs = 2 ^ (k + 1) := by
  let i : Fin (2 * k + 1) := ⟨0, by omega⟩
  let j : Fin (2 * k + 1) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [i, j] at hval
    omega
  have hpc' :
      SatisfiesPropagationCriterion ((2 * k + 1) - 2) f := by
    simpa only [show (2 * k + 1) - 2 = 2 * k - 1 by omega] using hpc
  rcases walshFace_pair_of_satisfiesPropagationCriterion_pred_two
      f k rfl hpc' i j hij v with hp | hp | hp | hp | hp | hp
  · exact Or.inr hp.1
  · exact Or.inr hp.1
  · exact Or.inr hp.1
  · exact Or.inl (by rw [hp.2.2.1, Int.natAbs_zero])
  · exact Or.inl (by rw [hp.2.2.1, Int.natAbs_zero])
  · exact Or.inl (by rw [hp.2.2.1, Int.natAbs_zero])

private theorem intCast_sq_eq_natAbsCast_sq_extremal (z : ℤ) :
    (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
  calc
    (z : ℝ) ^ 2 = |(z : ℝ)| ^ 2 := (sq_abs _).symm
    _ = (z.natAbs : ℝ) ^ 2 := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]

private theorem walshTransform_sq_eq_two_pow_mul_one_sub_realSignView_indicator
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hpc : SatisfiesPropagationCriterion (2 * k - 1) f)
    (v : FABL.F₂Cube (2 * k + 1)) :
    (walshTransform f v : ℝ) ^ 2 =
      (2 : ℝ) ^ (2 * k + 1) *
        (1 - realSignView (walshNonzeroIndicator f) v) := by
  by_cases hzero : walshTransform f v = 0
  · simp [hzero, walshNonzeroIndicator, realSignView,
      FABL.realSignEncodedFunction, FABL.signEncodedFunction]
  · have habs :=
      (walshTransform_natAbs_eq_zero_or_two_pow_of_pc_pred_two_odd
        k hk f hpc v).resolve_left (by
          intro h
          have := Int.natAbs_eq_zero.mp h
          exact hzero this)
    rw [intCast_sq_eq_natAbsCast_sq_extremal, habs]
    have hindicator : walshNonzeroIndicator f v = 1 := by
      simp [walshNonzeroIndicator, hzero]
    have hsign : realSignView (walshNonzeroIndicator f) v = -1 := by
      rw [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, hindicator,
        FABL.signValue_signEncode_eq_binarySign, FABL.binarySign_one]
    rw [hsign]
    norm_num [Nat.cast_pow]
    rw [pow_two, ← pow_add, ← pow_succ]
    congr 1
    omega

private theorem autocorrelation_eq_zero_of_pc_pred_two_odd_of_ne_zero_ne_slope
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hpc : SatisfiesPropagationCriterion (2 * k - 1) f)
    (b : FABL.𝔽₂) (q : FABL.F₂Cube (2 * k + 1))
    (hq : walshNonzeroIndicator f = FABL.affineFunction b q)
    (a : FABL.F₂Cube (2 * k + 1)) (ha : a ≠ 0) (haq : a ≠ q) :
    autocorrelation f a = 0 := by
  have hcharacter :
      (∑ u : FABL.F₂Cube (2 * k + 1),
        FABL.vectorWalshCharacter a u) = 0 :=
    by
      have h := rawFourierTransform_one (n := 2 * k + 1) a
      rw [if_neg ha] at h
      simpa [rawFourierTransform] using h
  have haffineWalsh : walshTransform (FABL.affineFunction b q) a = 0 := by
    rw [walshTransform_affineFunction, if_neg haq]
  have hsignCharacter :
      (∑ u : FABL.F₂Cube (2 * k + 1),
        realSignView (walshNonzeroIndicator f) u *
          FABL.vectorWalshCharacter a u) = 0 := by
    rw [hq]
    rw [← walshTransform_cast_eq_sum_realSignView_mul_character,
      haffineWalsh, Int.cast_zero]
  have hsum :
      (∑ u : FABL.F₂Cube (2 * k + 1),
        FABL.vectorWalshCharacter a u *
          (walshTransform f u : ℝ) ^ 2) = 0 := by
    simp_rw [walshTransform_sq_eq_two_pow_mul_one_sub_realSignView_indicator
      k hk f hpc]
    calc
      (∑ u : FABL.F₂Cube (2 * k + 1),
          FABL.vectorWalshCharacter a u *
            ((2 : ℝ) ^ (2 * k + 1) *
              (1 - realSignView (walshNonzeroIndicator f) u))) =
          (2 : ℝ) ^ (2 * k + 1) *
            ∑ u : FABL.F₂Cube (2 * k + 1),
              FABL.vectorWalshCharacter a u *
                (1 - realSignView (walshNonzeroIndicator f) u) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _hu
            ring
      _ =
          (2 : ℝ) ^ (2 * k + 1) *
            ((∑ u : FABL.F₂Cube (2 * k + 1),
                FABL.vectorWalshCharacter a u) -
              ∑ u : FABL.F₂Cube (2 * k + 1),
                realSignView (walshNonzeroIndicator f) u *
                  FABL.vectorWalshCharacter a u) := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro u _hu
            ring
      _ = 0 := by rw [hcharacter, hsignCharacter, sub_zero, mul_zero]
  rw [sum_vectorWalshCharacter_mul_walshTransform_sq] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (by positivity)

private theorem isLinearStructure_slope_of_walshNonzeroIndicator_eq_affine
    (f : BooleanFunction n) (b : FABL.𝔽₂) (q : FABL.F₂Cube n)
    (hq : walshNonzeroIndicator f = FABL.affineFunction b q)
    (hqne : q ≠ 0) :
    IsLinearStructure f q := by
  have hsupportValue (u : FABL.F₂Cube n)
      (hu : u ∈ walshSupport f) :
      FABL.affineFunction b q u = 1 := by
    have hnonzero := (mem_walshSupport f u).mp hu
    have hindicator := (walshNonzeroIndicator_eq_one_iff f u).mpr hnonzero
    exact (congrFun hq u).symm.trans hindicator
  by_cases hb : b = 0
  · have hsubset :
        (↑(walshSupport f) : Set (FABL.F₂Cube n)) ⊆
          (walshHyperplane q : Set (FABL.F₂Cube n))ᶜ := by
      intro u hu
      change u ∉ walshHyperplane q
      intro huHyperplane
      have hdotZero := (mem_walshHyperplane_iff q u).mp huHyperplane
      have hvalue := hsupportValue u hu
      rw [hb] at hvalue
      have hvalue' : FABL.f₂DotProduct q u = 1 := by
        simpa only [FABL.affineFunction, zero_add] using hvalue
      have hdotOne : FABL.f₂DotProduct u q = 1 := by
        rw [FABL.f₂DotProduct, dotProduct_comm]
        exact hvalue'
      rw [hdotZero] at hdotOne
      exact zero_ne_one hdotOne
    have hderivative :=
      (booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl
        f q hqne).mpr hsubset
    exact ⟨1, fun x ↦ congrFun hderivative x⟩
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
    have hsubset :
        (↑(walshSupport f) : Set (FABL.F₂Cube n)) ⊆
          (walshHyperplane q : Set (FABL.F₂Cube n)) := by
      intro u hu
      apply (mem_walshHyperplane_iff q u).mpr
      have hvalue := hsupportValue u hu
      rw [hbOne] at hvalue
      simp only [FABL.affineFunction] at hvalue
      have hdotZero : FABL.f₂DotProduct q u = 0 := by
        apply add_left_cancel (a := (1 : FABL.𝔽₂))
        simpa only [add_zero] using hvalue
      rw [FABL.f₂DotProduct, dotProduct_comm]
      exact hdotZero
    have hderivative :=
      (booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane
        f q hqne).mpr hsubset
    exact ⟨0, fun x ↦ congrFun hderivative x⟩

/-- A Boolean function has one distinguished nonzero linear structure of
weight at least `n-1`, and every other nonzero derivative is balanced. -/
def HasUniqueHighWeightLinearStructure (f : BooleanFunction n) : Prop :=
  ∃ q : FABL.F₂Cube n,
    q ≠ 0 ∧ n - 1 ≤ (FABL.f₂Support q).card ∧
      IsLinearStructure f q ∧
        ∀ a : FABL.F₂Cube n, a ≠ 0 → a ≠ q →
          IsBalanced (FABL.booleanDerivative f a)

/-- In odd dimension at least three, `PC(n-2)` is equivalent to having one
high-weight nonzero linear structure and balanced derivatives in every other
nonzero direction. -/
theorem satisfiesPropagationCriterion_pred_two_iff_hasUniqueHighWeightLinearStructure
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1)) :
    SatisfiesPropagationCriterion (2 * k - 1) f ↔
      HasUniqueHighWeightLinearStructure f := by
  constructor
  · intro hpc
    obtain ⟨b, q, hq, hweight⟩ :=
      exists_affineFunction_eq_walshNonzeroIndicator_highWeight
        f k rfl (by
          simpa only [show (2 * k + 1) - 2 = 2 * k - 1 by omega] using hpc)
    have hqne : q ≠ 0 := by
      intro hzero
      subst q
      have hsupportZero :
          FABL.f₂Support (0 : FABL.F₂Cube (2 * k + 1)) = ∅ := by
        ext i
        simp [FABL.mem_f₂Support]
      rw [hsupportZero] at hweight
      simp only [Finset.card_empty] at hweight
      omega
    refine ⟨q, hqne, ?_,
      isLinearStructure_slope_of_walshNonzeroIndicator_eq_affine
        f b q hq hqne, ?_⟩
    · simpa only [show (2 * k + 1) - 1 = 2 * k by omega] using hweight
    · intro a ha haq
      apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).mpr
      exact autocorrelation_eq_zero_of_pc_pred_two_odd_of_ne_zero_ne_slope
        k hk f hpc b q hq a ha haq
  · rintro ⟨q, hqne, hweight, hlinear, hbalanced⟩
    intro a ha
    apply hbalanced a ha.1
    intro haq
    subst a
    have hupper := ha.2
    have hlower : 2 * k ≤ (FABL.f₂Support q).card := by
      simpa only [show (2 * k + 1) - 1 = 2 * k by omega] using hweight
    omega

private theorem hammingWeight_comp_linearEquiv_extremal
    (h : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    hammingWeight (h ∘ L) = hammingWeight h := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  simp only [support, FABL.f₂OneSupport, Function.comp_apply]
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp L.toEquiv
    (fun x ↦ if h x = 1 then (1 : ℕ) else 0)

private theorem isBalanced_comp_linearEquiv_iff_extremal
    (h : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    IsBalanced (h ∘ L) ↔ IsBalanced h := by
  unfold IsBalanced
  rw [hammingWeight_comp_linearEquiv_extremal]

private theorem isBalanced_booleanDerivative_comp_linearEquiv_iff_extremal
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (a : FABL.F₂Cube n) :
    IsBalanced (FABL.booleanDerivative (f ∘ L) a) ↔
      IsBalanced (FABL.booleanDerivative f (L a)) := by
  have hderivative :
      FABL.booleanDerivative (f ∘ L) a =
        FABL.booleanDerivative f (L a) ∘ L := by
    funext x
    simp only [FABL.booleanDerivative, Function.comp_apply, L.map_add]
  rw [hderivative]
  exact isBalanced_comp_linearEquiv_iff_extremal
    (FABL.booleanDerivative f (L a)) L

def puncturedDiagonalShearLinearMap (m : ℕ) (i : Fin m) :
    FABL.F₂Cube (m + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1) where
  toFun x := x + x (Fin.last m) • coordinateDirection i.castSucc
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [add_smul]
    abel
  map_smul' c x := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [mul_add, mul_assoc]

theorem puncturedDiagonalShearLinearMap_involutive
    (m : ℕ) (i : Fin m) :
    Function.Involutive (puncturedDiagonalShearLinearMap m i) := by
  intro x
  funext j
  simp only [puncturedDiagonalShearLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hlast : coordinateDirection i.castSucc (Fin.last m) = 0 := by
    have hne : Fin.last m ≠ i.castSucc := Ne.symm i.castSucc_ne_last
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hne]
  rw [hlast, mul_zero, add_zero]
  rw [add_assoc, ZModModule.add_self, add_zero]

def puncturedDiagonalShearLinearEquiv (m : ℕ) (i : Fin m) :
    FABL.F₂Cube (m + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1) :=
  LinearEquiv.ofInvolutive (puncturedDiagonalShearLinearMap m i)
    (puncturedDiagonalShearLinearMap_involutive m i)

@[simp] private theorem puncturedDiagonalShearLinearEquiv_apply
    (m : ℕ) (i : Fin m) (x : FABL.F₂Cube (m + 1)) :
    puncturedDiagonalShearLinearEquiv m i x =
      x + x (Fin.last m) • coordinateDirection i.castSucc :=
  by
    change puncturedDiagonalShearLinearMap m i x = _
    rfl

/-- The second odd-dimensional quotient family: one of the first coordinates
is retained and every other first coordinate is added to the last one. -/
def oddPuncturedDiagonalProjection (m : ℕ) (i : Fin m) :
    FABL.F₂Cube (m + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube m :=
  (oddDiagonalProjection m).comp
    (puncturedDiagonalShearLinearEquiv m i).toLinearMap

@[simp] theorem oddPuncturedDiagonalProjection_apply_same
    (m : ℕ) (i : Fin m) (x : FABL.F₂Cube (m + 1)) :
    oddPuncturedDiagonalProjection m i x i = x i.castSucc := by
  have hne : Fin.last m ≠ i.castSucc := Ne.symm i.castSucc_ne_last
  simp [oddPuncturedDiagonalProjection, coordinateDirection,
    FABL.f₂CubeOfFinset_apply, hne, add_assoc,
    ZModModule.add_self]

theorem oddPuncturedDiagonalProjection_apply_of_ne
    (m : ℕ) (i j : Fin m) (hji : j ≠ i)
    (x : FABL.F₂Cube (m + 1)) :
    oddPuncturedDiagonalProjection m i x j =
      x j.castSucc + x (Fin.last m) := by
  have hne : Fin.last m ≠ i.castSucc := Ne.symm i.castSucc_ne_last
  have hcast : j.castSucc ≠ i.castSucc := by
    exact fun h ↦ hji (Fin.castSucc_injective _ h)
  simp [oddPuncturedDiagonalProjection, coordinateDirection,
    FABL.f₂CubeOfFinset_apply, hne, hcast]

/-- Reindexing binary-cube coordinates by a transposition. -/
def coordinateSwapLinearEquiv (i j : Fin n) :
    FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun x t := x (Equiv.swap i j t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x t := x (Equiv.swap i j t)
  left_inv x := by
    funext t
    simp
  right_inv x := by
    funext t
    simp

@[simp] theorem coordinateSwapLinearEquiv_apply
    (i j : Fin n) (x : FABL.F₂Cube n) (t : Fin n) :
    coordinateSwapLinearEquiv i j x t = x (Equiv.swap i j t) :=
  rfl

/-- A terminal-coordinate quotient with a designated retained output
coordinate. -/
def oddTerminalDiagonalProjectionAt (m : ℕ) (i : Fin m) :
    FABL.F₂Cube (m + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube m :=
  (oddDiagonalProjection m).comp
    ((puncturedDiagonalShearLinearEquiv m i).toLinearMap.comp
      (coordinateSwapLinearEquiv i.castSucc (Fin.last m)).toLinearMap)

@[simp] theorem oddTerminalDiagonalProjectionAt_apply_same
    (m : ℕ) (i : Fin m) (x : FABL.F₂Cube (m + 1)) :
    oddTerminalDiagonalProjectionAt m i x i = x (Fin.last m) := by
  have hiLast : i.castSucc ≠ Fin.last m := i.castSucc_ne_last
  simp [oddTerminalDiagonalProjectionAt, oddDiagonalProjection,
    puncturedDiagonalShearLinearEquiv_apply,
    coordinateDirection, FABL.f₂CubeOfFinset_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Ne.symm hiLast, add_assoc, ZModModule.add_self]

theorem oddTerminalDiagonalProjectionAt_apply_of_ne
    (m : ℕ) (i j : Fin m) (hji : j ≠ i)
    (x : FABL.F₂Cube (m + 1)) :
    oddTerminalDiagonalProjectionAt m i x j =
      x j.castSucc + x i.castSucc := by
  have hjI : j.castSucc ≠ i.castSucc := by
    exact fun h ↦ hji (Fin.castSucc_injective _ h)
  have hjLast : j.castSucc ≠ Fin.last m := j.castSucc_ne_last
  have hiLast : i.castSucc ≠ Fin.last m := i.castSucc_ne_last
  simp [oddTerminalDiagonalProjectionAt, oddDiagonalProjection,
    puncturedDiagonalShearLinearEquiv_apply,
    coordinateDirection, FABL.f₂CubeOfFinset_apply,
    Equiv.swap_apply_of_ne_of_ne hjI hjLast,
    Equiv.swap_apply_right, Ne.symm hiLast, hji]

/-- The third odd-dimensional quotient family: the first `r` coordinates
are added to the next coordinate, while the final coordinate is retained. -/
def oddTerminalDiagonalProjection (r : ℕ) :
    FABL.F₂Cube (r + 2) →ₗ[FABL.𝔽₂] FABL.F₂Cube (r + 1) :=
  oddTerminalDiagonalProjectionAt (r + 1) (Fin.last r)

@[simp] theorem oddTerminalDiagonalProjection_apply_castSucc
    (r : ℕ) (x : FABL.F₂Cube (r + 2)) (j : Fin r) :
    oddTerminalDiagonalProjection r x j.castSucc =
      x j.castSucc.castSucc + x (Fin.last r).castSucc := by
  apply oddTerminalDiagonalProjectionAt_apply_of_ne
  exact j.castSucc_ne_last

@[simp] theorem oddTerminalDiagonalProjection_apply_last
    (r : ℕ) (x : FABL.F₂Cube (r + 2)) :
    oddTerminalDiagonalProjection r x (Fin.last r) =
      x (Fin.last (r + 1)) := by
  exact oddTerminalDiagonalProjectionAt_apply_same
    (r + 1) (Fin.last r) x

private theorem f₂Support_fullDirection_add_coordinateDirection
    (i : Fin n) :
    FABL.f₂Support (fullDirection n + coordinateDirection i) =
      Finset.univ.erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [FABL.mem_f₂Support, fullDirection, coordinateDirection,
      FABL.f₂CubeOfFinset_apply, ZModModule.add_self]
  · simp [FABL.mem_f₂Support, fullDirection, coordinateDirection,
      FABL.f₂CubeOfFinset_apply, hji]

private theorem eq_fullDirection_or_fullDirection_add_coordinateDirection
    (q : FABL.F₂Cube n)
    (hweight : n - 1 ≤ (FABL.f₂Support q).card) :
    q = fullDirection n ∨
      ∃ i : Fin n, q = fullDirection n + coordinateDirection i := by
  have hcomplement : ((FABL.f₂Support q)ᶜ).card ≤ 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    have hcard : (FABL.f₂Support q).card ≤ n := by
      calc
        (FABL.f₂Support q).card ≤
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    omega
  by_cases hempty : (FABL.f₂Support q)ᶜ = ∅
  · left
    apply (FABL.f₂CubeEquivFinset n).injective
    change FABL.f₂Support q = FABL.f₂Support (fullDirection n)
    rw [f₂Support_fullDirection]
    ext j
    have hj : j ∉ (FABL.f₂Support q)ᶜ := by rw [hempty]; simp
    simpa using hj
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hsingleton : (FABL.f₂Support q)ᶜ = {i} := by
      apply Finset.Subset.antisymm
      · intro j hj
        have hji := (Finset.card_le_one.mp hcomplement) j hj i hi
        simp [hji]
      · exact Finset.singleton_subset_iff.mpr hi
    refine ⟨i, ?_⟩
    apply (FABL.f₂CubeEquivFinset n).injective
    change FABL.f₂Support q =
      FABL.f₂Support (fullDirection n + coordinateDirection i)
    rw [f₂Support_fullDirection_add_coordinateDirection]
    ext j
    have hj := congrArg (fun S : Finset (Fin n) ↦ j ∈ S) hsingleton
    simp only [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto

/-- Pullback along the second explicit odd-dimensional quotient. -/
def oddPuncturedDiagonalBentLift
    (i : Fin m) (g : BooleanFunction m) : BooleanFunction (m + 1) :=
  fun x ↦ g (oddPuncturedDiagonalProjection m i x)

/-- Pullback along a terminal-coordinate quotient. -/
def oddTerminalDiagonalBentLiftAt
    (i : Fin m) (g : BooleanFunction m) : BooleanFunction (m + 1) :=
  fun x ↦ g (oddTerminalDiagonalProjectionAt m i x)

/-- The penultimate coordinate among `2k+1` input coordinates. -/
def oddPenultimateIndex (k : ℕ) (hk : 1 ≤ k) : Fin (2 * k) :=
  ⟨2 * k - 1, by omega⟩

/-- The three source-facing bent quotient normal forms for odd-dimensional
`PC(n-2)`. -/
def HasOddPredTwoBentNormalForm
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1)) : Prop :=
  HasOddDiagonalBentNormalForm f ∨
    (∃ (i : Fin (2 * k)) (g : BooleanFunction (2 * k)),
      IsBent g ∧
        ∃ (c : FABL.𝔽₂) (u : FABL.F₂Cube (2 * k + 1)),
          f = oddPuncturedDiagonalBentLift i g + FABL.affineFunction c u) ∨
    ∃ (g : BooleanFunction (2 * k)), IsBent g ∧
      ∃ (c : FABL.𝔽₂) (u : FABL.F₂Cube (2 * k + 1)),
        f = oddTerminalDiagonalBentLiftAt (oddPenultimateIndex k hk) g +
          FABL.affineFunction c u

private def terminalDiagonalQuotientEquiv (m : ℕ) (i : Fin m) :
    FABL.F₂Cube (m + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1) :=
  (coordinateSwapLinearEquiv i.castSucc (Fin.last m)).trans
    (puncturedDiagonalShearLinearEquiv m i)

private theorem oddTerminalDiagonalProjectionAt_eq_diagonal_comp_equiv
    (m : ℕ) (i : Fin m) (x : FABL.F₂Cube (m + 1)) :
    oddTerminalDiagonalProjectionAt m i x =
      oddDiagonalProjection m (terminalDiagonalQuotientEquiv m i x) :=
  rfl

private theorem puncturedDiagonalShearLinearEquiv_fullDirection
    (m : ℕ) (i : Fin m) :
    puncturedDiagonalShearLinearEquiv m i (fullDirection (m + 1)) =
      fullDirection (m + 1) + coordinateDirection i.castSucc := by
  rw [puncturedDiagonalShearLinearEquiv_apply]
  simp only [fullDirection_apply, one_smul]

private theorem coordinateSwapLinearEquiv_fullDirection
    (i j : Fin n) :
    coordinateSwapLinearEquiv i j (fullDirection n) = fullDirection n := by
  funext t
  simp [coordinateSwapLinearEquiv, fullDirection]

private theorem coordinateSwapLinearEquiv_coordinateDirection_right
    (i j : Fin n) :
    coordinateSwapLinearEquiv i j (coordinateDirection j) =
      coordinateDirection i := by
  funext t
  by_cases hti : t = i
  · subst t
    simp [coordinateSwapLinearEquiv, coordinateDirection,
      FABL.f₂CubeOfFinset_apply, Equiv.swap_apply_def]
  · by_cases htj : t = j
    · subst t
      have hij : i ≠ j := Ne.symm hti
      simp [coordinateSwapLinearEquiv, coordinateDirection,
        FABL.f₂CubeOfFinset_apply, Equiv.swap_apply_def, hti, hij]
    · simp_all [coordinateSwapLinearEquiv, coordinateDirection,
        FABL.f₂CubeOfFinset_apply, Equiv.swap_apply_def]

private theorem terminalDiagonalQuotientEquiv_symm_fullDirection
    (m : ℕ) (i : Fin m) :
    (terminalDiagonalQuotientEquiv m i).symm (fullDirection (m + 1)) =
      fullDirection (m + 1) +
        coordinateDirection (Fin.last m) := by
  apply (terminalDiagonalQuotientEquiv m i).injective
  rw [(terminalDiagonalQuotientEquiv m i).apply_symm_apply]
  symm
  change puncturedDiagonalShearLinearEquiv m i
      (coordinateSwapLinearEquiv i.castSucc (Fin.last m)
        (fullDirection (m + 1) + coordinateDirection (Fin.last m))) =
    fullDirection (m + 1)
  rw [map_add, coordinateSwapLinearEquiv_fullDirection,
    coordinateSwapLinearEquiv_coordinateDirection_right]
  rw [← puncturedDiagonalShearLinearEquiv_fullDirection]
  change puncturedDiagonalShearLinearMap m i
      (puncturedDiagonalShearLinearMap m i (fullDirection (m + 1))) = _
  exact puncturedDiagonalShearLinearMap_involutive m i
    (fullDirection (m + 1))

private theorem satisfiesPropagationCriterion_pred_one_comp_linearEquiv_of_unique
    (k : ℕ) (f : BooleanFunction (2 * k + 1))
    (q : FABL.F₂Cube (2 * k + 1))
    (hbalanced : ∀ a : FABL.F₂Cube (2 * k + 1),
      a ≠ 0 → a ≠ q → IsBalanced (FABL.booleanDerivative f a))
    (L : FABL.F₂Cube (2 * k + 1) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (2 * k + 1))
    (hLfull : L (fullDirection (2 * k + 1)) = q) :
    SatisfiesPropagationCriterion (2 * k) (f ∘ L) := by
  intro a ha
  apply (isBalanced_booleanDerivative_comp_linearEquiv_iff_extremal
    f L a).mpr
  apply hbalanced (L a)
  · intro hzero
    apply ha.1
    apply L.injective
    rw [hzero, L.map_zero]
  · intro hq
    have hafull : a = fullDirection (2 * k + 1) := by
      apply L.injective
      rw [hq, hLfull]
    have hweight := ha.2
    rw [hafull, card_f₂Support_fullDirection] at hweight
    omega

private theorem satisfiesPropagationCriterion_pred_two_diagonal_comp_linearEquiv
    (k : ℕ) (hk : 1 ≤ k) (g : BooleanFunction (2 * k)) (hg : IsBent g)
    (M : FABL.F₂Cube (2 * k + 1) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (2 * k + 1))
    (hkernelWeight :
      (FABL.f₂Support
        (M.symm (fullDirection (2 * k + 1)))).card = 2 * k) :
    SatisfiesPropagationCriterion (2 * k - 1)
      (oddDiagonalBentLift g ∘ M) := by
  intro a ha
  apply (isBalanced_booleanDerivative_comp_linearEquiv_iff_extremal
    (oddDiagonalBentLift g) M a).mpr
  have hprojectionNe : oddDiagonalProjection (2 * k) (M a) ≠ 0 := by
    intro hzero
    rcases (oddDiagonalProjection_eq_zero_iff (M a)).mp hzero with
      hMaZero | hMaFull
    · apply ha.1
      apply M.injective
      rw [hMaZero, M.map_zero]
    · have haKernel : a = M.symm (fullDirection (2 * k + 1)) := by
        calc
          a = M.symm (M a) := (M.symm_apply_apply a).symm
          _ = M.symm (fullDirection (2 * k + 1)) := by rw [hMaFull]
      have hupper := ha.2
      rw [haKernel, hkernelWeight] at hupper
      omega
  rw [booleanDerivative_oddDiagonalBentLift]
  exact isBalanced_comp_oddDiagonalProjection
    (FABL.booleanDerivative g (oddDiagonalProjection (2 * k) (M a)))
    ((isBent_iff_forall_nonzero_derivative_isBalanced g).mp hg
      (oddDiagonalProjection (2 * k) (M a)) hprojectionNe)

/-- Every odd-dimensional `PC(n-2)` function has one of the three explicit
bent quotient normal forms. -/
theorem hasOddPredTwoBentNormalForm_of_satisfiesPropagationCriterion
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hpc : SatisfiesPropagationCriterion (2 * k - 1) f) :
    HasOddPredTwoBentNormalForm k hk f := by
  rcases
      (satisfiesPropagationCriterion_pred_two_iff_hasUniqueHighWeightLinearStructure
        k hk f).mp hpc with
    ⟨q, hqne, hweight, hlinear, hbalanced⟩
  rcases eq_fullDirection_or_fullDirection_add_coordinateDirection q hweight with
    hqFull | ⟨r, hqCoordinate⟩
  · left
    apply (satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm
      k hk f).mp
    intro a ha
    apply hbalanced a ha.1
    intro haq
    have hupper := ha.2
    rw [haq, hqFull, card_f₂Support_fullDirection] at hupper
    omega
  · revert hqCoordinate
    refine Fin.lastCases ?_ (fun i ↦ ?_) r
    · intro hqCoordinate
      right; right
      let p : Fin (2 * k) := oddPenultimateIndex k hk
      let M := terminalDiagonalQuotientEquiv (2 * k) p
      let L := M.symm
      have hLfull : L (fullDirection (2 * k + 1)) = q := by
        change M.symm (fullDirection (2 * k + 1)) = q
        rw [terminalDiagonalQuotientEquiv_symm_fullDirection]
        exact hqCoordinate.symm
      have hpcComp :=
        satisfiesPropagationCriterion_pred_one_comp_linearEquiv_of_unique
          k f q hbalanced L hLfull
      rcases
          (satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm
            k hk (f ∘ L)).mp hpcComp with
        ⟨g, hg, c, u, hrepresentation⟩
      obtain ⟨c', u', haffine⟩ :=
        exists_affineFunction_comp_affineEquiv c u M.toAffineEquiv
      refine ⟨g, hg, c', u', ?_⟩
      funext x
      have hx := congrFun hrepresentation (M x)
      have haffineX := congrFun haffine x
      simp only [Function.comp_apply, Pi.add_apply,
        oddDiagonalBentLift] at hx haffineX
      change f (L (M x)) =
        g (oddDiagonalProjection (2 * k) (M x)) +
          FABL.affineFunction c u (M x) at hx
      rw [show L (M x) = x from M.symm_apply_apply x] at hx
      change f x =
        oddTerminalDiagonalBentLiftAt p g x +
          FABL.affineFunction c' u' x
      rw [← haffineX, oddTerminalDiagonalBentLiftAt,
        oddTerminalDiagonalProjectionAt_eq_diagonal_comp_equiv]
      exact hx
    · intro hqCoordinate
      right; left
      let L := puncturedDiagonalShearLinearEquiv (2 * k) i
      have hLfull : L (fullDirection (2 * k + 1)) = q := by
        change puncturedDiagonalShearLinearEquiv (2 * k) i
          (fullDirection (2 * k + 1)) = q
        rw [puncturedDiagonalShearLinearEquiv_fullDirection]
        exact hqCoordinate.symm
      have hpcComp :=
        satisfiesPropagationCriterion_pred_one_comp_linearEquiv_of_unique
          k f q hbalanced L hLfull
      rcases
          (satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm
            k hk (f ∘ L)).mp hpcComp with
        ⟨g, hg, c, u, hrepresentation⟩
      obtain ⟨c', u', haffine⟩ :=
        exists_affineFunction_comp_affineEquiv c u L.toAffineEquiv
      refine ⟨i, g, hg, c', u', ?_⟩
      funext x
      have hx := congrFun hrepresentation (L x)
      have haffineX := congrFun haffine x
      simp only [Function.comp_apply, Pi.add_apply,
        oddDiagonalBentLift] at hx haffineX
      change f (L (L x)) =
        g (oddDiagonalProjection (2 * k) (L x)) +
          FABL.affineFunction c u (L x) at hx
      rw [show L (L x) = x from
        puncturedDiagonalShearLinearMap_involutive (2 * k) i x] at hx
      change f x =
        oddPuncturedDiagonalBentLift i g x +
          FABL.affineFunction c' u' x
      rw [← haffineX]
      exact hx

/-- Each of the three explicit bent quotient normal forms satisfies
odd-dimensional `PC(n-2)`. -/
theorem satisfiesPropagationCriterion_of_hasOddPredTwoBentNormalForm
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1))
    (hform : HasOddPredTwoBentNormalForm k hk f) :
    SatisfiesPropagationCriterion (2 * k - 1) f := by
  rcases hform with hdiagonal | hpunctured | hterminal
  · exact
      ((satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm
        k hk f).mpr hdiagonal).mono (by omega)
  · rcases hpunctured with ⟨i, g, hg, c, u, rfl⟩
    apply (satisfiesPropagationCriterion_add_affineFunction_iff
      (2 * k - 1) (oddPuncturedDiagonalBentLift i g) c u).mpr
    let M := puncturedDiagonalShearLinearEquiv (2 * k) i
    change SatisfiesPropagationCriterion (2 * k - 1)
      (oddDiagonalBentLift g ∘ M)
    apply satisfiesPropagationCriterion_pred_two_diagonal_comp_linearEquiv
      k hk g hg M
    have hkernel :
        M.symm (fullDirection (2 * k + 1)) =
          fullDirection (2 * k + 1) + coordinateDirection i.castSucc := by
      apply M.injective
      rw [M.apply_symm_apply]
      symm
      change puncturedDiagonalShearLinearEquiv (2 * k) i
          (fullDirection (2 * k + 1) + coordinateDirection i.castSucc) =
        fullDirection (2 * k + 1)
      rw [← puncturedDiagonalShearLinearEquiv_fullDirection]
      change puncturedDiagonalShearLinearMap (2 * k) i
          (puncturedDiagonalShearLinearMap (2 * k) i
            (fullDirection (2 * k + 1))) = _
      exact puncturedDiagonalShearLinearMap_involutive (2 * k) i _
    rw [hkernel, f₂Support_fullDirection_add_coordinateDirection]
    simp
  · rcases hterminal with ⟨g, hg, c, u, rfl⟩
    let p : Fin (2 * k) := oddPenultimateIndex k hk
    apply (satisfiesPropagationCriterion_add_affineFunction_iff
      (2 * k - 1) (oddTerminalDiagonalBentLiftAt p g) c u).mpr
    let M := terminalDiagonalQuotientEquiv (2 * k) p
    change SatisfiesPropagationCriterion (2 * k - 1)
      (oddDiagonalBentLift g ∘ M)
    apply satisfiesPropagationCriterion_pred_two_diagonal_comp_linearEquiv
      k hk g hg M
    rw [terminalDiagonalQuotientEquiv_symm_fullDirection,
      f₂Support_fullDirection_add_coordinateDirection]
    simp

/-- The three explicit bent quotient normal forms classify
odd-dimensional `PC(n-2)`. -/
theorem satisfiesPropagationCriterion_pred_two_iff_hasOddPredTwoBentNormalForm
    (k : ℕ) (hk : 1 ≤ k) (f : BooleanFunction (2 * k + 1)) :
    SatisfiesPropagationCriterion (2 * k - 1) f ↔
      HasOddPredTwoBentNormalForm k hk f := by
  constructor
  · exact hasOddPredTwoBentNormalForm_of_satisfiesPropagationCriterion k hk f
  · exact satisfiesPropagationCriterion_of_hasOddPredTwoBentNormalForm k hk f

end CryptBoolean
