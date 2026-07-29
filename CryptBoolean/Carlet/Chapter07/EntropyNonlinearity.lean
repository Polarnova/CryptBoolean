/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.NonlinearityBounds
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import CryptBoolean.Carlet.Chapter05.QuadraticValues

/-!
# Entropy refinement of the resilient nonlinearity bound

The finite binomial estimate underlying Carlet Relation (58), with binary
entropy normalized in bits, and its specialization of Relation (57).
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Binary entropy measured in bits. -/
noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

private theorem two_rpow_mul_binaryEntropyBaseTwo
    (p : ℝ) (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBaseTwo p) =
      Real.exp ((n : ℝ) * Real.binEntropy p) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold binaryEntropyBaseTwo
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

private theorem exp_mul_binEntropy_natRatio
    (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((m : ℝ) / n)) =
      (n : ℝ) ^ n /
        ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)) := by
  have hn : 0 < n := hm.trans hmn
  have hnm : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  have hmReal : (m : ℝ) ≠ 0 := by positivity
  have hnmReal : ((n - m : ℕ) : ℝ) ≠ 0 := by positivity
  have hpInv : (((m : ℝ) / n)⁻¹) = (n : ℝ) / m := by
    field_simp
  have honeSub :
      1 - (m : ℝ) / n = ((n - m : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hmn.le]
    field_simp
  have honeSubInv :
      (1 - (m : ℝ) / n)⁻¹ = (n : ℝ) / (n - m : ℕ) := by
    rw [honeSub]
    field_simp
  have hpLog :
      -Real.log ((m : ℝ) / n) = Real.log ((n : ℝ) / m) := by
    rw [← Real.log_inv, hpInv]
  have honeSubLog :
      -Real.log (1 - (m : ℝ) / n) =
        Real.log ((n : ℝ) / (n - m : ℕ)) := by
    rw [← Real.log_inv, honeSubInv]
  have hexponent :
      (n : ℝ) * Real.binEntropy ((m : ℝ) / n) =
        (m : ℝ) * Real.log ((n : ℝ) / m) +
          ((n - m : ℕ) : ℝ) *
            Real.log ((n : ℝ) / (n - m : ℕ)) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    change (n : ℝ) *
      (-((m : ℝ) / n) * Real.log ((m : ℝ) / n) +
        -(1 - (m : ℝ) / n) * Real.log (1 - (m : ℝ) / n)) = _
    rw [show -((m : ℝ) / n) * Real.log ((m : ℝ) / n) =
        ((m : ℝ) / n) * (-Real.log ((m : ℝ) / n)) by ring,
      show -(1 - (m : ℝ) / n) * Real.log (1 - (m : ℝ) / n) =
        (1 - (m : ℝ) / n) *
          (-Real.log (1 - (m : ℝ) / n)) by ring,
      hpLog, honeSubLog, honeSub, Nat.cast_sub hmn.le]
    field_simp
  rw [hexponent, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity : 0 < (n : ℝ) / m),
    Real.exp_log (by positivity : 0 < (n : ℝ) / (n - m : ℕ)),
    div_pow, div_pow]
  field_simp
  rw [← pow_add, show m + (n - m) = n by omega]

private theorem binaryEntropyPower_eq_powerRatio
    (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    (2 : ℝ) ^
        ((n : ℝ) * binaryEntropyBaseTwo ((m : ℝ) / n)) =
      (n : ℝ) ^ n /
        ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)) := by
  rw [two_rpow_mul_binaryEntropyBaseTwo]
  exact exp_mul_binEntropy_natRatio m n hm hmn

private theorem stirlingSeq_two :
    Stirling.stirlingSeq 2 = Real.exp 1 ^ 2 / 4 := by
  rw [Stirling.stirlingSeq]
  norm_num [div_pow]
  field_simp

private theorem stirlingSeq_three :
    Stirling.stirlingSeq 3 =
      2 * Real.exp 1 ^ 3 / (9 * Real.sqrt 6) := by
  rw [Stirling.stirlingSeq]
  norm_num [div_pow]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

private theorem one_seventy_seven_lt_sqrt_pi :
    (177 : ℝ) / 100 < Real.sqrt Real.pi := by
  apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt Real.pi_pos.le]
  nlinarith [Real.pi_gt_d2]

private theorem stirlingSeq_two_mul_self_lt_two_sqrt_pi :
    Stirling.stirlingSeq 2 * Stirling.stirlingSeq 2 <
      2 * Real.sqrt Real.pi := by
  rw [stirlingSeq_two]
  have he : Real.exp 1 < (2719 : ℝ) / 1000 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have heFour : Real.exp 1 ^ 4 < ((2719 : ℝ) / 1000) ^ 4 :=
    pow_lt_pow_left₀ he (by positivity) (by norm_num)
  calc
    (Real.exp 1 ^ 2 / 4) * (Real.exp 1 ^ 2 / 4) =
        Real.exp 1 ^ 4 / 16 := by ring
    _ < (((2719 : ℝ) / 1000) ^ 4) / 16 :=
      div_lt_div_of_pos_right heFour (by norm_num)
    _ < 2 * ((177 : ℝ) / 100) := by norm_num
    _ < 2 * Real.sqrt Real.pi := by
      nlinarith [one_seventy_seven_lt_sqrt_pi]

private theorem stirlingSeq_one_lt :
    Stirling.stirlingSeq 1 < (193 : ℝ) / 100 := by
  rw [Stirling.stirlingSeq_one]
  have hsqrtTwo : (1414 : ℝ) / 1000 < Real.sqrt 2 := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  apply (div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
  calc
    Real.exp 1 < (2719 : ℝ) / 1000 :=
      Real.exp_one_lt_d9.trans (by norm_num)
    _ < (193 / 100 : ℝ) * Real.sqrt 2 := by
      nlinarith

private theorem stirlingSeq_three_lt :
    Stirling.stirlingSeq 3 < (183 : ℝ) / 100 := by
  rw [stirlingSeq_three]
  have hsqrtSix : (2449 : ℝ) / 1000 < Real.sqrt 6 := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  have he : Real.exp 1 < (2719 : ℝ) / 1000 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have heThree : Real.exp 1 ^ 3 < ((2719 : ℝ) / 1000) ^ 3 :=
    pow_lt_pow_left₀ he (by positivity) (by norm_num)
  apply (div_lt_iff₀ (by positivity : 0 < 9 * Real.sqrt 6)).2
  calc
    2 * Real.exp 1 ^ 3 < 2 * ((2719 : ℝ) / 1000) ^ 3 := by
      exact mul_lt_mul_of_pos_left heThree (by norm_num)
    _ < (183 / 100 : ℝ) * (9 * Real.sqrt 6) := by
      nlinarith

private theorem stirlingSeq_one_mul_three_lt_two_sqrt_pi :
    Stirling.stirlingSeq 1 * Stirling.stirlingSeq 3 <
      2 * Real.sqrt Real.pi := by
  have hsThreePos : 0 < Stirling.stirlingSeq 3 := by
    simpa using Stirling.stirlingSeq'_pos 2
  calc
    Stirling.stirlingSeq 1 * Stirling.stirlingSeq 3 <
        (193 / 100 : ℝ) * Stirling.stirlingSeq 3 :=
      mul_lt_mul_of_pos_right stirlingSeq_one_lt hsThreePos
    _ < (193 / 100 : ℝ) * (183 / 100 : ℝ) :=
      mul_lt_mul_of_pos_left stirlingSeq_three_lt (by norm_num)
    _ < 2 * ((177 : ℝ) / 100) := by norm_num
    _ < 2 * Real.sqrt Real.pi := by
      nlinarith [one_seventy_seven_lt_sqrt_pi]

private theorem stirlingSeq_le_two_of_two_le
    (k : ℕ) (hk : 2 ≤ k) :
    Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 2 := by
  have h := Stirling.stirlingSeq'_antitone
    (show 1 ≤ k - 1 by omega)
  simpa [Function.comp_apply, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

private theorem stirlingSeq_le_three_of_three_le
    (k : ℕ) (hk : 3 ≤ k) :
    Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 3 := by
  have h := Stirling.stirlingSeq'_antitone
    (show 2 ≤ k - 1 by omega)
  simpa [Function.comp_apply, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

private theorem stirlingSeq_pos_of_pos (k : ℕ) (hk : 0 < k) :
    0 < Stirling.stirlingSeq k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa [Nat.succ_eq_add_one] using Stirling.stirlingSeq'_pos j

private theorem stirlingSeq_product_le_two_sqrt_pi
    (m k : ℕ) (hm : 0 < m) (hmk : m ≤ k) (hsum : 4 ≤ m + k) :
    Stirling.stirlingSeq m * Stirling.stirlingSeq k ≤
      2 * Real.sqrt Real.pi := by
  by_cases hmOne : m = 1
  · subst m
    have hkThree : 3 ≤ k := by omega
    calc
      Stirling.stirlingSeq 1 * Stirling.stirlingSeq k ≤
          Stirling.stirlingSeq 1 * Stirling.stirlingSeq 3 := by
        exact mul_le_mul_of_nonneg_left
          (stirlingSeq_le_three_of_three_le k hkThree)
          (stirlingSeq_pos_of_pos 1 (by norm_num)).le
      _ ≤ 2 * Real.sqrt Real.pi :=
        stirlingSeq_one_mul_three_lt_two_sqrt_pi.le
  · have hmTwo : 2 ≤ m := by omega
    have hkTwo : 2 ≤ k := hmTwo.trans hmk
    calc
      Stirling.stirlingSeq m * Stirling.stirlingSeq k ≤
          Stirling.stirlingSeq 2 * Stirling.stirlingSeq k :=
        mul_le_mul_of_nonneg_right
          (stirlingSeq_le_two_of_two_le m hmTwo)
          (stirlingSeq_pos_of_pos k (by omega)).le
      _ ≤ Stirling.stirlingSeq 2 * Stirling.stirlingSeq 2 :=
        mul_le_mul_of_nonneg_left
          (stirlingSeq_le_two_of_two_le k hkTwo)
          (stirlingSeq_pos_of_pos 2 (by norm_num)).le
      _ ≤ 2 * Real.sqrt Real.pi :=
        stirlingSeq_two_mul_self_lt_two_sqrt_pi.le

private theorem factorial_cast_eq_stirlingSeq_mul
    (k : ℕ) (hk : 0 < k) :
    (k.factorial : ℝ) = Stirling.stirlingSeq k *
      (Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
  symm
  unfold Stirling.stirlingSeq
  exact div_mul_cancel₀ _ (by positivity)

private theorem choose_eq_stirling_ratio_mul_powerRatio
    (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    (n.choose m : ℝ) =
      (Stirling.stirlingSeq n /
          (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
        (Real.sqrt (2 * (n : ℝ)) /
          (Real.sqrt (2 * (m : ℝ)) *
            Real.sqrt (2 * ((n - m : ℕ) : ℝ)))) *
        ((n : ℝ) ^ n /
          ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) := by
  have hn : 0 < n := hm.trans hmn
  have hnm : 0 < n - m := Nat.sub_pos_of_lt hmn
  rw [Nat.cast_choose ℝ hmn.le,
    factorial_cast_eq_stirlingSeq_mul n hn,
    factorial_cast_eq_stirlingSeq_mul m hm,
    factorial_cast_eq_stirlingSeq_mul (n - m) hnm]
  simp only [div_pow]
  field_simp
  rw [mul_assoc, ← pow_add, show m + (n - m) = n by omega]

private theorem stirling_sqrt_factor_mul_entropy_denominator
    (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    (Real.sqrt (2 * (n : ℝ)) /
        (Real.sqrt (2 * (m : ℝ)) *
          Real.sqrt (2 * ((n - m : ℕ) : ℝ)))) *
      Real.sqrt
        (8 * (m : ℝ) * (1 - (m : ℝ) / n)) = 2 := by
  have hn : 0 < n := hm.trans hmn
  have hnm : 0 < n - m := Nat.sub_pos_of_lt hmn
  have honeSub :
      1 - (m : ℝ) / n = ((n - m : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hmn.le]
    field_simp
  rw [honeSub]
  refine (sq_eq_sq₀ (by positivity) (by norm_num)).mp ?_
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * m),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (n - m : ℕ)),
    Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 8 * m * ((n - m : ℕ) / n))]
  field_simp
  ring

private theorem entropyPower_div_sqrt_le_choose_of_four_le
    (m n : ℕ) (hm : 1 ≤ m) (hmhalf : m ≤ n / 2) (hnFour : 4 ≤ n) :
    (2 : ℝ) ^
          ((n : ℝ) * binaryEntropyBaseTwo ((m : ℝ) / n)) /
        Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n)) ≤
      (n.choose m : ℝ) := by
  have hmn : m < n := by omega
  have hnm : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hmk : m ≤ n - m := by omega
  have hsProduct :
      Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m) ≤
        2 * Real.sqrt Real.pi :=
    stirlingSeq_product_le_two_sqrt_pi m (n - m) hm hmk (by omega)
  have hsN : Real.sqrt Real.pi ≤ Stirling.stirlingSeq n :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hsProductPos :
      0 < Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m) :=
    mul_pos (stirlingSeq_pos_of_pos m hm)
      (stirlingSeq_pos_of_pos (n - m) hnm)
  have hratio :
      (1 : ℝ) / 2 ≤
        Stirling.stirlingSeq n /
          (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m)) := by
    apply (le_div_iff₀ hsProductPos).2
    nlinarith
  have hpowerRatioPos :
      0 < (n : ℝ) ^ n /
        ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)) := by
    positivity
  have hscaledRatio :
      (n : ℝ) ^ n /
          ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)) ≤
        (Stirling.stirlingSeq n /
            (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
          2 *
          ((n : ℝ) ^ n /
            ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) := by
    have h := mul_le_mul_of_nonneg_right hratio hpowerRatioPos.le
    nlinarith
  have hdenominatorPos :
      0 < Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n)) := by
    apply Real.sqrt_pos.2
    have hn : (0 : ℝ) < n := by positivity
    have hmLt : (m : ℝ) < n := by exact_mod_cast hmn
    have hratioLt : (m : ℝ) / n < 1 := (div_lt_one hn).2 hmLt
    exact mul_pos (mul_pos (by norm_num) (by positivity)) (sub_pos.2 hratioLt)
  apply (div_le_iff₀ hdenominatorPos).2
  rw [binaryEntropyPower_eq_powerRatio m n hm hmn,
    choose_eq_stirling_ratio_mul_powerRatio m n hm hmn]
  calc
    (n : ℝ) ^ n /
          ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m)) ≤
        (Stirling.stirlingSeq n /
            (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
          2 *
          ((n : ℝ) ^ n /
            ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) :=
      hscaledRatio
    _ = (Stirling.stirlingSeq n /
            (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
          ((n : ℝ) ^ n /
            ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) * 2 := by
      ring
    _ = (Stirling.stirlingSeq n /
            (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
          ((n : ℝ) ^ n /
            ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) *
          ((Real.sqrt (2 * (n : ℝ)) /
              (Real.sqrt (2 * (m : ℝ)) *
                Real.sqrt (2 * ((n - m : ℕ) : ℝ)))) *
            Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n))) := by
      rw [stirling_sqrt_factor_mul_entropy_denominator m n hm hmn]
    _ = ((Stirling.stirlingSeq n /
            (Stirling.stirlingSeq m * Stirling.stirlingSeq (n - m))) *
          (Real.sqrt (2 * (n : ℝ)) /
            (Real.sqrt (2 * (m : ℝ)) *
              Real.sqrt (2 * ((n - m : ℕ) : ℝ)))) *
          ((n : ℝ) ^ n /
            ((m : ℝ) ^ m * ((n - m : ℕ) : ℝ) ^ (n - m))) *
          Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n))) := by
      ring

/-- The finite binomial lower bound used in Carlet Relation (58), with
binary entropy normalized in bits. -/
theorem entropyPower_div_sqrt_le_choose
    (m n : ℕ) (hm : 1 ≤ m) (hmhalf : m ≤ n / 2) :
    (2 : ℝ) ^
          ((n : ℝ) * binaryEntropyBaseTwo ((m : ℝ) / n)) /
        Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n)) ≤
      (n.choose m : ℝ) := by
  by_cases hnFour : 4 ≤ n
  · exact entropyPower_div_sqrt_le_choose_of_four_le m n hm hmhalf hnFour
  · have hnTwo : 2 ≤ n := by omega
    interval_cases n <;> interval_cases m
    · rw [binaryEntropyPower_eq_powerRatio 1 2 (by norm_num) (by norm_num)]
      norm_num
    · rw [binaryEntropyPower_eq_powerRatio 1 3 (by norm_num) (by norm_num)]
      norm_num
      have hsqrtThreePos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      have hsqrtThreeLe : Real.sqrt 3 ≤ (16 : ℝ) / 9 := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      calc
        (27 : ℝ) / 4 / (4 / Real.sqrt 3) =
            27 * Real.sqrt 3 / 16 := by field_simp; norm_num
        _ ≤ 27 * ((16 : ℝ) / 9) / 16 := by gcongr
        _ = 3 := by norm_num

/-- Carlet Relation (58): the entropy estimate for a finite binomial tail
specializes the Parseval resilient nonlinearity bound. -/
theorem nonlinearity_le_entropy_resilient_bound
    (f : BooleanFunction n) (m : ℕ) (hm : 1 ≤ m) (hmhalf : m ≤ n / 2)
    (hf : IsResilient m f) :
    nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (m + 1) *
        ⌈((2 : ℝ) ^ ((n : ℝ) - (m : ℝ) - 2) /
          Real.sqrt
            ((2 : ℝ) ^ n -
              (2 : ℝ) ^
                  ((n : ℝ) *
                    binaryEntropyBaseTwo ((m : ℝ) / n)) /
                Real.sqrt
                  (8 * (m : ℝ) * (1 - (m : ℝ) / n))))⌉₊ := by
  classical
  by_cases hnThree : 3 ≤ n
  · have hsub :
        (n : ℝ) - (m : ℝ) - 2 = ((n - m - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ n - m),
        Nat.cast_sub (by omega : m ≤ n)]
      norm_num
    have hpower :
        (2 : ℝ) ^ ((n : ℝ) - (m : ℝ) - 2) =
          (2 : ℝ) ^ (n - m - 2) := by
      rw [hsub, Real.rpow_natCast]
    rw [hpower]
    let L : ℕ :=
      ∑ i ∈ Finset.range (m + 1), Nat.choose n i
    let E : ℝ :=
      (2 : ℝ) ^
          ((n : ℝ) * binaryEntropyBaseTwo ((m : ℝ) / n)) /
        Real.sqrt (8 * (m : ℝ) * (1 - (m : ℝ) / n))
    let N : ℕ := 2 ^ n - L
    have hmn : m < n := by omega
    have hrelation :
        nonlinearity f ≤
          2 ^ (n - 1) - 2 ^ (m + 1) *
            ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ := by
      simpa [N, L] using
        nonlinearity_le_parseval_resilient_bound f m (by omega) hf
    have hentropyChoose : E ≤ (n.choose m : ℝ) := by
      simpa [E] using entropyPower_div_sqrt_le_choose m n hm hmhalf
    have hchooseLow : n.choose m ≤ L := by
      dsimp [L]
      exact Finset.single_le_sum
        (fun i _hi ↦ Nat.zero_le (n.choose i)) (by simp)
    have hentropyLow : E ≤ (L : ℝ) := by
      exact hentropyChoose.trans (by exact_mod_cast hchooseLow)
    have hlowLt : L < 2 ^ n := by
      have hsubset :
          Finset.range (m + 1) ⊆ Finset.range (n + 1) :=
        Finset.range_mono (by omega)
      have hlt :
          (∑ i ∈ Finset.range (m + 1), Nat.choose n i) <
            ∑ i ∈ Finset.range (n + 1), Nat.choose n i := by
        exact Finset.sum_lt_sum_of_subset hsubset
          (show n ∈ Finset.range (n + 1) by simp)
          (show n ∉ Finset.range (m + 1) by simp; omega)
          (show 0 < Nat.choose n n by simp)
          (fun i _hi _hnot ↦ Nat.zero_le (Nat.choose n i))
      simpa [L, Nat.sum_range_choose] using hlt
    have hNPos : 0 < N := by
      dsimp [N]
      omega
    have hNCast :
        (N : ℝ) = (2 : ℝ) ^ n - (L : ℝ) := by
      dsimp [N]
      rw [Nat.cast_sub hlowLt.le]
      norm_num
    have hradicand :
        (N : ℝ) ≤ (2 : ℝ) ^ n - E := by
      rw [hNCast]
      linarith
    have hsqrtNPos : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hNPos)
    have hquotient :
        (2 : ℝ) ^ (n - m - 2) /
            Real.sqrt ((2 : ℝ) ^ n - E) ≤
          (2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hsqrtNPos
        (Real.sqrt_le_sqrt hradicand)
    have hceil :
        ⌈((2 : ℝ) ^ (n - m - 2) /
          Real.sqrt ((2 : ℝ) ^ n - E))⌉₊ ≤
        ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ :=
      Nat.ceil_mono hquotient
    change nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (m + 1) *
        ⌈((2 : ℝ) ^ (n - m - 2) /
          Real.sqrt ((2 : ℝ) ^ n - E))⌉₊
    calc
      nonlinearity f ≤
          2 ^ (n - 1) - 2 ^ (m + 1) *
            ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ :=
        hrelation
      _ ≤ 2 ^ (n - 1) - 2 ^ (m + 1) *
            ⌈((2 : ℝ) ^ (n - m - 2) /
              Real.sqrt ((2 : ℝ) ^ n - E))⌉₊ :=
        Nat.sub_le_sub_left (Nat.mul_le_mul_left _ hceil) _
  · have hnTwo : 2 ≤ n := by omega
    have hnEq : n = 2 := by omega
    subst n
    have hmEq : m = 1 := by omega
    subst m
    obtain ⟨b, a, hfa⟩ :=
      exists_affineFunction_of_isResilient_natPred f (by norm_num)
        (by simpa using hf)
    rw [hfa, nonlinearity_affineFunction]
    exact Nat.zero_le _

end CryptBoolean
