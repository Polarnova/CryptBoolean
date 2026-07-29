/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter05.RandomNonnormality

/-!
# Algebraic immunity does not force normality

The asymptotic random-nonnormality theorem is combined with the universal
algebraic-immunity bound to make Carlet's converse failure explicit.
-/

open scoped BooleanCube Topology

@[expose] public section

namespace CryptBoolean

/-- Carlet's logarithmic normality dimension is sublinear. -/
theorem tendsto_carletNonnormalityDimension_div
    {α : ℝ} (hα : 1 < α) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (carletNonnormalityDimension α n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
  have hlog : Filter.Tendsto
      (fun x : ℝ ↦ Real.log x / x) Filter.atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hscaled : Filter.Tendsto
      (fun x : ℝ ↦ α * Real.logb 2 x / x)
      Filter.atTop (𝓝 0) := by
    have hconstant : α / Real.log 2 ≠ 0 := by
      exact div_ne_zero (by linarith) (ne_of_gt (Real.log_pos (by norm_num)))
    convert hlog.const_mul (α / Real.log 2) using 1
    · funext x
      rw [Real.logb]
      ring
    · simp
  have hscaledNat := hscaled.comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscaledNat
  · filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    positivity
  · filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogb : 0 ≤ Real.logb 2 (n : ℝ) := by
      rw [Real.logb]
      positivity
    have hfloor :
        (carletNonnormalityDimension α n : ℝ) ≤
          α * Real.logb 2 (n : ℝ) := by
      exact Nat.floor_le (mul_nonneg (by linarith) hlogb)
    exact div_le_div_of_nonneg_right hfloor hnR.le

/-- Eventually the universal ceiling-half algebraic-immunity bound is no
larger than `n` minus Carlet's logarithmic normality dimension. -/
theorem eventually_ceilingHalf_le_sub_carletNonnormalityDimension
    {α : ℝ} (hα : 1 < α) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n + 1) / 2 ≤ n - carletNonnormalityDimension α n := by
  have hratio := tendsto_carletNonnormalityDimension_div hα
  have hthird : ∀ᶠ n : ℕ in Filter.atTop,
      (carletNonnormalityDimension α n : ℝ) / (n : ℝ) < 1 / 3 :=
    (tendsto_order.1 hratio).2 _ (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 3, hthird] with n hn hbound
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hscaled :
      (3 : ℝ) * carletNonnormalityDimension α n < n := by
    have := (div_lt_iff₀ hnR).mp hbound
    nlinarith
  have hscaledNat : 3 * carletNonnormalityDimension α n ≤ n := by
    exact_mod_cast hscaled.le
  omega

private theorem exists_not_isKNormal_of_nonnormalityProbability_pos
    (n k : ℕ) (hpositive : 0 < nonnormalityProbability n k) :
    ∃ f : BooleanFunction n, ¬ IsKNormal f k := by
  by_contra h
  push Not at h
  let e : BooleanFunction n ≃ {f : BooleanFunction n // IsKNormal f k} :=
    { toFun := fun f ↦ ⟨f, h f⟩
      invFun := fun f ↦ f.1
      left_inv := fun _ ↦ rfl
      right_inv := by intro f; exact Subtype.ext rfl }
  have hcard :
      Nat.card {f : BooleanFunction n // IsKNormal f k} =
        Nat.card (BooleanFunction n) :=
    Nat.card_congr e.symm
  have hcardPositive : (0 : ℝ) < Nat.card (BooleanFunction n) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (BooleanFunction n))
  have hzero : nonnormalityProbability n k = 0 := by
    rw [nonnormalityProbability, normalityProbability, hcard]
    rw [div_self hcardPositive.ne']
    norm_num
  linarith

/-- For every `α>1`, in all sufficiently large dimensions there exists a function whose
universal algebraic-immunity upper bound does not imply
`floor (α log₂ n)`-normality. -/
theorem eventually_exists_algebraicImmunity_le_sub_not_isKNormal
    {α : ℝ} (hα : 1 < α) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ f : BooleanFunction n,
        algebraicImmunity f ≤ n - carletNonnormalityDimension α n ∧
          ¬ IsKNormal f (carletNonnormalityDimension α n) := by
  have hprobability := tendsto_carletNonnormalityProbability hα
  have hpositive : ∀ᶠ n : ℕ in Filter.atTop,
      0 < nonnormalityProbability n (carletNonnormalityDimension α n) :=
    hprobability.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [eventually_ceilingHalf_le_sub_carletNonnormalityDimension hα,
      hpositive] with n hceiling hprob
  obtain ⟨f, hfNormal⟩ :=
    exists_not_isKNormal_of_nonnormalityProbability_pos
      n (carletNonnormalityDimension α n) hprob
  exact ⟨f, (algebraicImmunity_le_ceiling_half f).trans hceiling, hfNormal⟩

end CryptBoolean
