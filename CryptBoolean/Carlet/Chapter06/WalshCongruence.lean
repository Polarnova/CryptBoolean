/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness

/-!
# Carlet Chapter 6 Walsh congruence

Carlet Lemma 2: a congruence characterization of bent Boolean functions.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem exists_odd_factor_of_walsh_modeq
    (k : ℕ) (w : ℤ)
    (h : Int.ModEq (2 ^ (k + 1)) w (2 ^ k)) :
    ∃ z : ℤ, w = (2 : ℤ) ^ k * z ∧ Int.ModEq 2 z 1 := by
  let p : ℤ := (2 : ℤ) ^ k
  have h' : Int.ModEq (p * 2) w p := by
    simpa [p, pow_succ] using h
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp h'
  refine ⟨1 - 2 * t, ?_, ?_⟩
  · have hw : w = p - (p * 2) * t := eq_sub_of_add_eq ht.symm
    rw [hw]
    ring
  · rw [Int.modEq_iff_dvd]
    refine ⟨t, ?_⟩
    ring

/-- Carlet Lemma 2: in even dimension at least two, bentness is equivalent
to every raw Walsh coefficient being congruent to `2^(n/2)` modulo
`2^(n/2+1)`. -/
theorem isBent_iff_forall_walshTransform_modeq
    (f : BooleanFunction n) (hn : Even n) (_hnTwo : 2 ≤ n) :
    IsBent f ↔
      ∀ a : FABL.F₂Cube n,
        Int.ModEq (2 ^ (n / 2 + 1))
          (walshTransform f a) (2 ^ (n / 2)) := by
  constructor
  · intro hf a
    have hmagnitude :=
      natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a
    rcases Int.natAbs_eq_iff.mp hmagnitude with hpositive | hnegative
    · rw [hpositive]
      norm_num
    · rw [hnegative, Int.modEq_iff_dvd]
      rw [pow_succ]
      refine ⟨1, ?_⟩
      simp only [sub_neg_eq_add, mul_one, Nat.cast_pow, Nat.cast_ofNat]
      ring
  · intro hmodeq
    have hexists (a : FABL.F₂Cube n) :
        ∃ z : ℤ, walshTransform f a = (2 : ℤ) ^ (n / 2) * z ∧
          Int.ModEq 2 z 1 :=
      exists_odd_factor_of_walsh_modeq (n / 2) (walshTransform f a) (hmodeq a)
    choose z hz hodd using hexists
    have hz_ne (a : FABL.F₂Cube n) : z a ≠ 0 := by
      intro ha
      have haOdd := hodd a
      rw [ha] at haOdd
      norm_num [Int.modEq_iff_dvd] at haOdd
    have hz_sq_lower (a : FABL.F₂Cube n) :
        (1 : ℝ) ≤ (z a : ℝ) ^ 2 := by
      have hpositive : (0 : ℤ) < z a ^ 2 := sq_pos_of_ne_zero (hz_ne a)
      have hone : (1 : ℤ) ≤ z a ^ 2 := by omega
      exact_mod_cast hone
    have hsplit : n = n / 2 + n / 2 := by
      rcases hn with ⟨k, hk⟩
      omega
    have hhalfSquare : ((2 : ℝ) ^ (n / 2)) ^ 2 = (2 : ℝ) ^ n := by
      rw [pow_two, ← pow_add, ← hsplit]
    have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
    simp_rw [hz] at hparseval
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hparseval
    have hsumFactor :
        (∑ a : FABL.F₂Cube n,
            ((2 : ℝ) ^ (n / 2) * (z a : ℝ)) ^ 2) =
          ((2 : ℝ) ^ (n / 2)) ^ 2 *
            ∑ a : FABL.F₂Cube n, (z a : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    have hsumz :
        ∑ a : FABL.F₂Cube n, (z a : ℝ) ^ 2 = (2 : ℝ) ^ n := by
      apply mul_left_cancel₀
        (by positivity : ((2 : ℝ) ^ (n / 2)) ^ 2 ≠ 0)
      calc
        ((2 : ℝ) ^ (n / 2)) ^ 2 *
              ∑ a : FABL.F₂Cube n, (z a : ℝ) ^ 2 =
            ∑ a : FABL.F₂Cube n,
              ((2 : ℝ) ^ (n / 2) * (z a : ℝ)) ^ 2 := hsumFactor.symm
        _ = ((2 : ℝ) ^ n) ^ 2 := hparseval
        _ = ((2 : ℝ) ^ (n / 2)) ^ 2 * (2 : ℝ) ^ n := by
          rw [hhalfSquare]
          ring
    have hsumOne :
        (∑ _a : FABL.F₂Cube n, (1 : ℝ)) = (2 : ℝ) ^ n := by
      rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
        nsmul_eq_mul]
      norm_num
    apply (hasFlatWalshSpectrum_iff_isBent f).1
    intro a
    have hz_sq_upper : (z a : ℝ) ^ 2 ≤ 1 := by
      by_contra hnot
      have hstrict : (1 : ℝ) < (z a : ℝ) ^ 2 := lt_of_not_ge hnot
      have hsumStrict :
          (∑ _u : FABL.F₂Cube n, (1 : ℝ)) <
            ∑ u : FABL.F₂Cube n, (z u : ℝ) ^ 2 :=
        Finset.sum_lt_sum (fun u _hu ↦ hz_sq_lower u)
          ⟨a, Finset.mem_univ a, hstrict⟩
      rw [hsumOne, hsumz] at hsumStrict
      exact (lt_irrefl ((2 : ℝ) ^ n)) hsumStrict
    have hz_sq : (z a : ℝ) ^ 2 = 1 :=
      le_antisymm hz_sq_upper (hz_sq_lower a)
    have hz_abs := congrArg Real.sqrt hz_sq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_one] at hz_abs
    have hwalsh := congrArg (fun w : ℤ ↦ (w : ℝ)) (hz a)
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hwalsh
    rw [hwalsh, abs_mul, abs_of_pos (by positivity), hz_abs, mul_one,
      sqrt_two_pow_eq_pow_half hn]

end CryptBoolean
