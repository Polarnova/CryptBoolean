/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.RodierSharpInterval

/-!
# Rodier's sharp random-nonlinearity asymptotics

The asymptotic estimates closing Rodier's second-moment argument and the
simultaneous two-sided random-nonlinearity interval.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal Topology

namespace CryptBoolean

local instance rodierSharpAsymptoticsSignMeasurableSpace : MeasurableSpace FABL.Sign := ⊤

local instance rodierSharpAsymptoticsSignMeasurableSingletonClass :
    MeasurableSingletonClass FABL.Sign where
  measurableSet_singleton _ := by simp

private theorem tendsto_rodierSharpLogDivNat :
    Filter.Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def] using h.tendsto_div_nhds_zero

private theorem rodierAsymptoticDelta_inv_sq {n : ℕ} (hn : 0 < n) :
    (rodierAsymptoticDelta n)⁻¹ ^ 2 =
      (n : ℝ) / rodierAsymptoticQ n := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnℝ)
  have hqne : Real.sqrt (rodierAsymptoticQ n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (rodierAsymptoticQ_pos n))
  unfold rodierAsymptoticDelta
  rw [inv_div, div_pow, Real.sq_sqrt hnℝ.le,
    Real.sq_sqrt (rodierAsymptoticQ_pos n).le]

private theorem rodierAsymptoticDelta_inv_fourth {n : ℕ} (hn : 0 < n) :
    (rodierAsymptoticDelta n)⁻¹ ^ 4 =
      ((n : ℝ) / rodierAsymptoticQ n) ^ 2 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, rodierAsymptoticDelta_inv_sq hn]

private theorem rodierAsymptoticDelta_inv_sixth {n : ℕ} (hn : 0 < n) :
    (rodierAsymptoticDelta n)⁻¹ ^ 6 =
      ((n : ℝ) / rodierAsymptoticQ n) ^ 3 := by
  rw [show 6 = 2 * 3 by norm_num, pow_mul, rodierAsymptoticDelta_inv_sq hn]

private theorem rodierAsymptoticDelta_inv_eighth {n : ℕ} (hn : 0 < n) :
    (rodierAsymptoticDelta n)⁻¹ ^ 8 =
      ((n : ℝ) / rodierAsymptoticQ n) ^ 4 := by
  rw [show 8 = 2 * 4 by norm_num, pow_mul, rodierAsymptoticDelta_inv_sq hn]

private theorem eventually_rodierAsymptoticCenter_lower :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) ≤
        rodierAsymptoticM n := by
  have hscaled : Filter.Tendsto
      (fun n : ℕ => 5 * (Real.log (n : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_rodierSharpLogDivNat.const_mul 5
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      5 * (Real.log (n : ℝ) / (n : ℝ)) < (1 / 10 : ℝ) :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  filter_upwards [hsmall] with n hn
  have hc : (11 / 10 : ℝ) < Real.sqrt (2 * Real.log 2) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 11 / 10)]
    nlinarith [Real.log_two_gt_d9]
  have ha : (1 : ℝ) ≤ Real.sqrt (2 * Real.log 2) -
      5 * Real.log (n : ℝ) / (n : ℝ) := by
    have hn' : 5 * Real.log (n : ℝ) / (n : ℝ) < (1 / 10 : ℝ) := by
      calc
        _ = 5 * (Real.log (n : ℝ) / (n : ℝ)) := by ring
        _ < _ := hn
    linarith
  unfold rodierAsymptoticM
  calc
    _ = Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)

private theorem rodierAsymptoticCenter_exp_upper {n : ℕ} (hn : 0 < n)
    (hcenter : Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) ≤
      rodierAsymptoticM n) :
    Real.exp (-(rodierAsymptoticM n ^ 2) /
        (2 * rodierAsymptoticQ n)) ≤
      Real.exp (-(n : ℝ) / 2) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < rodierAsymptoticQ n := rodierAsymptoticQ_pos n
  have hbase : 0 ≤
      Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) := by positivity
  have hMnonneg : 0 ≤ rodierAsymptoticM n := hbase.trans hcenter
  have hsq : rodierAsymptoticQ n * (n : ℝ) ≤
      rodierAsymptoticM n ^ 2 := by
    have h := (sq_le_sq₀ hbase hMnonneg).2 hcenter
    rw [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hnℝ.le] at h
    exact h
  apply Real.exp_le_exp.mpr
  have hdiv : (n : ℝ) / 2 ≤
      rodierAsymptoticM n ^ 2 / (2 * rodierAsymptoticQ n) := by
    exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (by positivity : (0 : ℝ) < 2 * rodierAsymptoticQ n)).2 (by
        nlinarith [hsq])
  simpa [neg_div] using neg_le_neg hdiv

private theorem rodierAsymptoticM_mul_delta_inv_le {n : ℕ} (hn : 0 < n) :
    rodierAsymptoticM n * (rodierAsymptoticDelta n)⁻¹ ≤
      2 * (n : ℝ) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hc : Real.sqrt (2 * Real.log 2) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.log_two_lt_d9]
  have ha : Real.sqrt (2 * Real.log 2) -
      5 * Real.log (n : ℝ) / (n : ℝ) ≤ 2 := by
    have : 0 ≤ 5 * Real.log (n : ℝ) / (n : ℝ) := by positivity
    linarith
  have hnroot : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnℝ)
  have hqroot : Real.sqrt (rodierAsymptoticQ n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (rodierAsymptoticQ_pos n))
  have hid : rodierAsymptoticM n * (rodierAsymptoticDelta n)⁻¹ =
      (n : ℝ) * (Real.sqrt (2 * Real.log 2) -
        5 * Real.log (n : ℝ) / (n : ℝ)) := by
    unfold rodierAsymptoticM rodierAsymptoticDelta
    rw [inv_div]
    field_simp [hnroot, hqroot]
    rw [Real.sq_sqrt hnℝ.le]
  rw [hid]
  nlinarith

private theorem rodierAsymptoticOffDiagonalPairError_algebra
    (x q z C₂ C₄ K₁ K₂ Kᵣ R₁ R₂ a₂ a₄ d : ℝ)
    (hx : 1 ≤ x) (hq : 0 < q) (hxq : x ≤ q)
    (hzdef : z = Real.exp (-x / 2)) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (_hC₂ : 0 ≤ C₂) (_hC₄ : 0 ≤ C₄)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hKᵣ : 0 ≤ Kᵣ)
    (hR₁nonneg : 0 ≤ R₁) (ha₂ : 0 ≤ a₂) (ha₄ : 0 ≤ a₄)
    (hd : 0 ≤ d)
    (hR₁ : R₁ ≤ K₁ * x ^ 4 / q ^ 2)
    (hR₂ : R₂ ≤ K₂ * x ^ 5 / q ^ 2)
    (ha₂bound : a₂ ≤ C₂ * (x / q) * z)
    (ha₄bound : a₄ ≤ C₄ * (x / q) ^ 2 * z)
    (hdbound : d ≤ Kᵣ * x ^ 2) :
    R₂ + 6 * (q / 12) * a₂ ^ 2 + (q / 12) ^ 2 * a₄ ^ 2 +
        R₁ * (2 * d + R₁) ≤
      (K₂ + C₄ ^ 2 + 2 * K₁ * Kᵣ + K₁ ^ 2 + C₂ ^ 2) *
        (x ^ 6 / q ^ 2 + (x ^ 4 / q) * Real.exp (-x)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hx2q2 : x ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hx0 hq.le).2 hxq
  have hzsq : z ^ 2 = Real.exp (-x) := by
    rw [hzdef, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hA₂term : 6 * (q / 12) * a₂ ^ 2 ≤
      C₂ ^ 2 * (x ^ 4 / q) * Real.exp (-x) := by
    calc
      6 * (q / 12) * a₂ ^ 2 ≤ q * a₂ ^ 2 := by
        gcongr
        nlinarith [hq.le]
      _ ≤ q * (C₂ * (x / q) * z) ^ 2 := by gcongr
      _ = C₂ ^ 2 * (x ^ 2 / q) * Real.exp (-x) := by
        rw [show (C₂ * (x / q) * z) ^ 2 =
          (C₂ * (x / q)) ^ 2 * z ^ 2 by ring, hzsq]
        field_simp
      _ ≤ C₂ ^ 2 * (x ^ 4 / q) * Real.exp (-x) := by
        gcongr
        nlinarith [sq_nonneg x]
  have hA₄term : (q / 12) ^ 2 * a₄ ^ 2 ≤
      C₄ ^ 2 * x ^ 6 / q ^ 2 := by
    calc
      (q / 12) ^ 2 * a₄ ^ 2 ≤
          q ^ 2 * (C₄ * (x / q) ^ 2 * z) ^ 2 := by
        gcongr
        exact div_le_self hq.le (by norm_num : (1 : ℝ) ≤ 12)
      _ = C₄ ^ 2 * x ^ 4 / q ^ 2 * z ^ 2 := by
        field_simp
      _ ≤ C₄ ^ 2 * x ^ 6 / q ^ 2 := by
        have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
        have hx46 : x ^ 4 ≤ x ^ 6 := by
          calc
            x ^ 4 = x ^ 4 * 1 := by ring
            _ ≤ x ^ 4 * x ^ 2 :=
              mul_le_mul_of_nonneg_left hx2 (by positivity)
            _ = x ^ 6 := by ring
        have hzsq1 : z ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
        calc
          C₄ ^ 2 * x ^ 4 / q ^ 2 * z ^ 2 ≤
              C₄ ^ 2 * x ^ 6 / q ^ 2 * z ^ 2 := by gcongr
          _ ≤ C₄ ^ 2 * x ^ 6 / q ^ 2 * 1 := by
            gcongr
          _ = _ := by ring
  have hR₁square : R₁ * (2 * d + R₁) ≤
      (2 * K₁ * Kᵣ + K₁ ^ 2) * x ^ 6 / q ^ 2 := by
    calc
      R₁ * (2 * d + R₁) ≤
          (K₁ * x ^ 4 / q ^ 2) *
            (2 * (Kᵣ * x ^ 2) + K₁ * x ^ 4 / q ^ 2) := by
        gcongr
      _ = 2 * K₁ * Kᵣ * x ^ 6 / q ^ 2 +
          K₁ ^ 2 * x ^ 8 / q ^ 4 := by ring
      _ ≤ 2 * K₁ * Kᵣ * x ^ 6 / q ^ 2 +
          K₁ ^ 2 * x ^ 6 / q ^ 2 := by
        have hratio : x ^ 8 / q ^ 4 ≤ x ^ 6 / q ^ 2 := by
          calc
            x ^ 8 / q ^ 4 = (x ^ 6 / q ^ 2) * (x ^ 2 / q ^ 2) := by
              field_simp
            _ ≤ (x ^ 6 / q ^ 2) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact (div_le_one (sq_pos_of_pos hq)).2 hx2q2
            _ = _ := by ring
        have hmul : K₁ ^ 2 * x ^ 8 / q ^ 4 ≤
            K₁ ^ 2 * x ^ 6 / q ^ 2 := by
          calc
            K₁ ^ 2 * x ^ 8 / q ^ 4 = K₁ ^ 2 * (x ^ 8 / q ^ 4) := by ring
            _ ≤ K₁ ^ 2 * (x ^ 6 / q ^ 2) :=
              mul_le_mul_of_nonneg_left hratio (sq_nonneg K₁)
            _ = K₁ ^ 2 * x ^ 6 / q ^ 2 := by ring
        exact add_le_add (le_refl _) hmul
      _ = _ := by ring
  have hx56 : x ^ 5 ≤ x ^ 6 := by
    calc
      x ^ 5 = x ^ 5 * 1 := by ring
      _ ≤ x ^ 5 * x := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = x ^ 6 := by ring
  have hpoly : 0 ≤ x ^ 6 / q ^ 2 := by positivity
  have hexpnonneg : 0 ≤ (x ^ 4 / q) * Real.exp (-x) := by positivity
  calc
    _ ≤ K₂ * x ^ 5 / q ^ 2 +
        C₂ ^ 2 * (x ^ 4 / q) * Real.exp (-x) +
        C₄ ^ 2 * x ^ 6 / q ^ 2 +
        (2 * K₁ * Kᵣ + K₁ ^ 2) * x ^ 6 / q ^ 2 := by
      gcongr
    _ ≤ K₂ * (x ^ 6 / q ^ 2) +
        C₂ ^ 2 * ((x ^ 4 / q) * Real.exp (-x)) +
        C₄ ^ 2 * (x ^ 6 / q ^ 2) +
        (2 * K₁ * Kᵣ + K₁ ^ 2) * (x ^ 6 / q ^ 2) := by
      have hfirst : K₂ * x ^ 5 / q ^ 2 ≤
          K₂ * (x ^ 6 / q ^ 2) := by
        calc
          K₂ * x ^ 5 / q ^ 2 = K₂ * (x ^ 5 / q ^ 2) := by ring
          _ ≤ K₂ * (x ^ 6 / q ^ 2) := by gcongr
      let B : ℝ := C₂ ^ 2 * ((x ^ 4 / q) * Real.exp (-x)) +
        C₄ ^ 2 * (x ^ 6 / q ^ 2) +
        (2 * K₁ * Kᵣ + K₁ ^ 2) * (x ^ 6 / q ^ 2)
      calc
        _ = K₂ * x ^ 5 / q ^ 2 + B := by dsimp [B]; ring
        _ ≤ K₂ * (x ^ 6 / q ^ 2) + B :=
          add_le_add hfirst (le_refl B)
        _ = _ := by dsimp [B]; ring
    _ ≤ (K₂ + C₄ ^ 2 + 2 * K₁ * Kᵣ + K₁ ^ 2 + C₂ ^ 2) *
        (x ^ 6 / q ^ 2 + (x ^ 4 / q) * Real.exp (-x)) := by
      rw [show
        (K₂ + C₄ ^ 2 + 2 * K₁ * Kᵣ + K₁ ^ 2 + C₂ ^ 2) *
            (x ^ 6 / q ^ 2 + (x ^ 4 / q) * Real.exp (-x)) =
          (K₂ * (x ^ 6 / q ^ 2) +
            C₂ ^ 2 * ((x ^ 4 / q) * Real.exp (-x)) +
            C₄ ^ 2 * (x ^ 6 / q ^ 2) +
            (2 * K₁ * Kᵣ + K₁ ^ 2) * (x ^ 6 / q ^ 2)) +
          ((K₂ + C₄ ^ 2 + 2 * K₁ * Kᵣ + K₁ ^ 2) *
            ((x ^ 4 / q) * Real.exp (-x)) +
            C₂ ^ 2 * (x ^ 6 / q ^ 2)) by ring]
      exact le_add_of_nonneg_right (add_nonneg (mul_nonneg (by positivity) hexpnonneg)
        (mul_nonneg (sq_nonneg C₂) hpoly))

/-- Rodier's off-diagonal pair error has a uniform polynomial-exponential
majorant at the sharp cutoff scale. -/
theorem exists_rodierAsymptoticOffDiagonalPairError_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (hM : 0 < rodierAsymptoticM n)
          (hΔ : 0 < rodierAsymptoticDelta n),
          rodierOffDiagonalPairError n
              (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ ≤
            C * (((n : ℝ) ^ 6 / rodierAsymptoticQ n ^ 2) +
              ((n : ℝ) ^ 4 / rodierAsymptoticQ n) *
                Real.exp (-(n : ℝ))) := by
  obtain ⟨C₀, hC₀, hm₀⟩ := exists_rodierCutoffFourierDensity_totalMass_bound
  obtain ⟨C₂, hC₂, hm₂⟩ :=
    exists_rodierGaussianWeightedDensityMoment_second_exponential_bound
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierGaussianWeightedDensityMoment_fourth_exponential_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound
  let K₁ : ℝ := 3 * C₆ + 3 * C₈
  let K₂ : ℝ := 2 * K₁ + 384 * C₀ * C₆ + 1536 * C₀ * C₈
  let Kᵣ : ℝ := 1 + K₁
  let C : ℝ := K₂ + C₄ ^ 2 + 2 * K₁ * Kᵣ + K₁ ^ 2 + C₂ ^ 2
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hKᵣ : 0 ≤ Kᵣ := by dsimp [Kᵣ]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_rodierAsymptotic_parameters,
    eventually_rodierAsymptoticCenter_lower] with n hp hcenter
  intro hM hΔ
  let x : ℝ := n
  let q : ℝ := rodierAsymptoticQ n
  let z : ℝ := Real.exp (-x / 2)
  let I₀ : ℝ := ∫ t : ℝ,
    ‖rodierCutoffFourierDensity (rodierAsymptoticM n)
      (rodierAsymptoticDelta n) hM hΔ t‖
  let I₆ : ℝ := ∫ t : ℝ, |t| ^ 6 *
    ‖rodierCutoffFourierDensity (rodierAsymptoticM n)
      (rodierAsymptoticDelta n) hM hΔ t‖
  let I₈ : ℝ := ∫ t : ℝ, |t| ^ 8 *
    ‖rodierCutoffFourierDensity (rodierAsymptoticM n)
      (rodierAsymptoticDelta n) hM hΔ t‖
  let A₂ : ℂ := rodierGaussianWeightedDensityMoment n 2
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  let A₄ : ℂ := rodierGaussianWeightedDensityMoment n 4
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  let G : ℂ := rodierCutoffGaussianIntegral n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  let R₁ : ℝ := rodierSingleQuarticRemainder n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  let R₂ : ℝ := rodierPairQuarticRemainder n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  have hn : 0 < n := hp.1
  have hx : (1 : ℝ) ≤ x := by
    have : 1 ≤ n := hn
    dsimp [x]
    exact_mod_cast this
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hq : 0 < q := by exact rodierAsymptoticQ_pos n
  have hq1 : 1 ≤ q := by
    dsimp [q, rodierAsymptoticQ]
    exact one_le_pow₀ (by norm_num)
  have hxq : x ≤ q := by
    dsimp [x, q, rodierAsymptoticQ]
    exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact Real.exp_le_one_iff.mpr (by dsimp [x] at hx0 ⊢; nlinarith)
  have hexp := rodierAsymptoticCenter_exp_upper hn hcenter
  have hI₀ : I₀ ≤ 2 * C₀ * x := by
    calc
      I₀ ≤ C₀ * rodierAsymptoticM n *
          (rodierAsymptoticDelta n)⁻¹ :=
        (hm₀ (rodierAsymptoticM n) (rodierAsymptoticDelta n)
          hM hΔ hp.2.2.2).2
      _ = C₀ * (rodierAsymptoticM n *
          (rodierAsymptoticDelta n)⁻¹) := by ring
      _ ≤ C₀ * (2 * x) := mul_le_mul_of_nonneg_left
        (by simpa [x] using rodierAsymptoticM_mul_delta_inv_le hn) hC₀
      _ = _ := by ring
  have hI₆ : I₆ ≤ C₆ * (x / q) ^ 3 := by
    calc
      I₆ ≤ C₆ * (rodierAsymptoticDelta n)⁻¹ ^ 6 :=
        (hm₆ (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).2
      _ = _ := by rw [rodierAsymptoticDelta_inv_sixth hn]
  have hI₈ : I₈ ≤ C₈ * (x / q) ^ 4 := by
    calc
      I₈ ≤ C₈ * (rodierAsymptoticDelta n)⁻¹ ^ 8 :=
        (hm₈ (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).2
      _ = _ := by rw [rodierAsymptoticDelta_inv_eighth hn]
  have hA₂ : ‖A₂‖ ≤ C₂ * (x / q) * z := by
    calc
      ‖A₂‖ ≤ C₂ * (rodierAsymptoticDelta n)⁻¹ ^ 2 *
          Real.exp (-(rodierAsymptoticM n ^ 2) /
            (2 * rodierAsymptoticQ n)) :=
        hm₂ n (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
      _ ≤ C₂ * (rodierAsymptoticDelta n)⁻¹ ^ 2 * z := by
        exact mul_le_mul_of_nonneg_left (by simpa [z, x] using hexp)
          (mul_nonneg hC₂ (by positivity))
      _ = _ := by rw [rodierAsymptoticDelta_inv_sq hn]
  have hA₄ : ‖A₄‖ ≤ C₄ * (x / q) ^ 2 * z := by
    calc
      ‖A₄‖ ≤ C₄ * (rodierAsymptoticDelta n)⁻¹ ^ 4 *
          Real.exp (-(rodierAsymptoticM n ^ 2) /
            (2 * rodierAsymptoticQ n)) :=
        hm₄ n (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
      _ ≤ C₄ * (rodierAsymptoticDelta n)⁻¹ ^ 4 * z := by
        exact mul_le_mul_of_nonneg_left (by simpa [z, x] using hexp)
          (mul_nonneg hC₄ (by positivity))
      _ = _ := by rw [rodierAsymptoticDelta_inv_fourth hn]
  have hR₁ : R₁ ≤ K₁ * x ^ 4 / q ^ 2 := by
    dsimp [R₁, rodierSingleQuarticRemainder, I₆, I₈]
    calc
      3 * q * I₆ + 3 * q ^ 2 * I₈ ≤
          3 * q * (C₆ * (x / q) ^ 3) +
            3 * q ^ 2 * (C₈ * (x / q) ^ 4) := by gcongr
      _ = (3 * C₆ * x ^ 3 + 3 * C₈ * x ^ 4) / q ^ 2 := by
        field_simp
      _ ≤ K₁ * x ^ 4 / q ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg q)
        dsimp [K₁]
        have hx34 : x ^ 3 ≤ x ^ 4 := by nlinarith [mul_self_nonneg (x ^ 2)]
        nlinarith
  have hR₁nonneg : 0 ≤ R₁ := by
    dsimp [R₁, rodierSingleQuarticRemainder]
    positivity
  have hR₂ : R₂ ≤ K₂ * x ^ 5 / q ^ 2 := by
    have hR₂def : R₂ = 2 * R₁ + 192 * q * I₆ * I₀ +
        768 * q ^ 2 * I₈ * I₀ := by
      dsimp [R₂, R₁, I₆, I₈, I₀,
        rodierPairQuarticRemainder, rodierSingleQuarticRemainder,
        q, rodierAsymptoticQ]
      ring
    rw [hR₂def]
    calc
      2 * R₁ + 192 * q * I₆ * I₀ + 768 * q ^ 2 * I₈ * I₀ ≤
          2 * (K₁ * x ^ 4 / q ^ 2) +
            192 * q * (C₆ * (x / q) ^ 3) * (2 * C₀ * x) +
            768 * q ^ 2 * (C₈ * (x / q) ^ 4) * (2 * C₀ * x) := by
        gcongr
      _ = (2 * K₁ * x ^ 4 + 384 * C₀ * C₆ * x ^ 4 +
          1536 * C₀ * C₈ * x ^ 5) / q ^ 2 := by
        field_simp
        ring
      _ ≤ K₂ * x ^ 5 / q ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg q)
        dsimp [K₂]
        have hx45 : x ^ 4 ≤ x ^ 5 := by nlinarith [mul_self_nonneg (x ^ 2)]
        calc
          2 * K₁ * x ^ 4 + 384 * C₀ * C₆ * x ^ 4 +
              1536 * C₀ * C₈ * x ^ 5 ≤
            2 * K₁ * x ^ 5 + 384 * C₀ * C₆ * x ^ 5 +
              1536 * C₀ * C₈ * x ^ 5 := by gcongr
          _ = (2 * K₁ + 384 * C₀ * C₆ + 1536 * C₀ * C₈) *
              x ^ 5 := by ring
  let E : ℂ := rodierSingleCutoffExpectation (∅ : Finset (Fin n))
    (rodierAsymptoticM n) (rodierAsymptoticDelta n)
  let Eᵣ : ℝ := Finset.expect Finset.univ
    (fun f : FABL.BooleanFunction n ↦
      rodierCutoff (rodierAsymptoticM n) (rodierAsymptoticDelta n)
        (rodierRawWalshCoefficient (∅ : Finset (Fin n)) f))
  let D : ℂ := G - (q / 12 : ℝ) * A₄
  have hEeq : (Eᵣ : ℂ) = E := by
    dsimp [Eᵣ, E]
    exact ofReal_expect_rodierCutoff_eq_singleCutoffExpectation
      (∅ : Finset (Fin n)) (rodierAsymptoticM n) (rodierAsymptoticDelta n)
  have hEᵣnonneg : 0 ≤ Eᵣ := by
    dsimp [Eᵣ]
    rw [Fintype.expect_eq_sum_div_card]
    exact div_nonneg (Finset.sum_nonneg fun f _ =>
      rodierCutoff_nonneg _ _ hM hΔ _) (by positivity)
  have hEᵣone : Eᵣ ≤ 1 := by
    dsimp [Eᵣ]
    rw [Fintype.expect_eq_sum_div_card]
    have hcard : (0 : ℝ) < Fintype.card (FABL.BooleanFunction n) := by positivity
    apply (div_le_one hcard).2
    calc
      (∑ f : FABL.BooleanFunction n,
          rodierCutoff (rodierAsymptoticM n) (rodierAsymptoticDelta n)
            (rodierRawWalshCoefficient (∅ : Finset (Fin n)) f)) ≤
          ∑ _f : FABL.BooleanFunction n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro f _
        exact rodierCutoff_le_one _ _ hM hΔ _
      _ = Fintype.card (FABL.BooleanFunction n) := by simp
  have hEnorm : ‖E‖ ≤ 1 := by
    rw [← hEeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEᵣnonneg]
    exact hEᵣone
  have hED : ‖E - D‖ ≤ R₁ := by
    have hsingle :=
      norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
        hn (∅ : Finset (Fin n)) (rodierAsymptoticM n)
          (rodierAsymptoticDelta n) hM hΔ hp.2.2.2
    simpa [E, D, G, A₄, q, rodierAsymptoticQ, R₁,
      rodierSingleQuarticRemainder] using hsingle
  have hx2q2 : x ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hx0 hq.le).2 hxq
  have hx4q2 : x ^ 4 / q ^ 2 ≤ x ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hq)).2
    calc
      x ^ 4 = x ^ 2 * x ^ 2 := by ring
      _ ≤ x ^ 2 * q ^ 2 :=
        mul_le_mul_of_nonneg_left hx2q2 (sq_nonneg x)
  have hDnorm : ‖D‖ ≤ Kᵣ * x ^ 2 := by
    calc
      ‖D‖ = ‖E - (E - D)‖ := by ring_nf
      _ ≤ ‖E‖ + ‖E - D‖ := norm_sub_le _ _
      _ ≤ 1 + R₁ := add_le_add hEnorm hED
      _ ≤ 1 + K₁ * x ^ 2 := by
        apply add_le_add (le_refl 1)
        refine hR₁.trans ?_
        calc
          K₁ * x ^ 4 / q ^ 2 = K₁ * (x ^ 4 / q ^ 2) := by ring
          _ ≤ K₁ * x ^ 2 := mul_le_mul_of_nonneg_left hx4q2 hK₁
      _ ≤ Kᵣ * x ^ 2 := by
        dsimp [Kᵣ]
        nlinarith [sq_nonneg x]
  change R₂ + 6 * (q / 12) * ‖A₂‖ ^ 2 +
      (q / 12) ^ 2 * ‖A₄‖ ^ 2 +
      R₁ * (2 * ‖D‖ + R₁) ≤ _
  dsimp [C]
  exact rodierAsymptoticOffDiagonalPairError_algebra x q z C₂ C₄ K₁ K₂ Kᵣ R₁ R₂
    ‖A₂‖ ‖A₄‖ ‖D‖ hx hq hxq (by rfl) hz0 hz1 hC₂ hC₄
    hK₁ hK₂ hKᵣ hR₁nonneg (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hR₁ hR₂ hA₂ hA₄ hDnorm

private theorem exists_rodierAsymptoticSingleCorrection_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (hM : 0 < rodierAsymptoticM n)
          (hΔ : 0 < rodierAsymptoticDelta n),
          rodierAsymptoticQ n *
              (rodierAsymptoticQ n / 12 *
                  ‖rodierGaussianWeightedDensityMoment n 4
                    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ‖ +
                rodierSingleQuarticRemainder n
                  (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ) ≤
            C * (((n : ℝ) ^ 4 / rodierAsymptoticQ n) +
              (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 2)) := by
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierGaussianWeightedDensityMoment_fourth_exponential_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound
  let K₁ : ℝ := 3 * C₆ + 3 * C₈
  let C : ℝ := C₄ + K₁
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_rodierAsymptotic_parameters,
    eventually_rodierAsymptoticCenter_lower] with n hp hcenter
  intro hM hΔ
  let x : ℝ := n
  let q : ℝ := rodierAsymptoticQ n
  let z : ℝ := Real.exp (-x / 2)
  let I₆ : ℝ := ∫ t : ℝ, |t| ^ 6 *
    ‖rodierCutoffFourierDensity (rodierAsymptoticM n)
      (rodierAsymptoticDelta n) hM hΔ t‖
  let I₈ : ℝ := ∫ t : ℝ, |t| ^ 8 *
    ‖rodierCutoffFourierDensity (rodierAsymptoticM n)
      (rodierAsymptoticDelta n) hM hΔ t‖
  let A₄ : ℂ := rodierGaussianWeightedDensityMoment n 4
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  let R₁ : ℝ := rodierSingleQuarticRemainder n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  have hn : 0 < n := hp.1
  have hx : (1 : ℝ) ≤ x := by
    have : 1 ≤ n := hn
    dsimp [x]
    exact_mod_cast this
  have hq : 0 < q := rodierAsymptoticQ_pos n
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hexp := rodierAsymptoticCenter_exp_upper hn hcenter
  have hI₆ : I₆ ≤ C₆ * (x / q) ^ 3 := by
    calc
      I₆ ≤ C₆ * (rodierAsymptoticDelta n)⁻¹ ^ 6 :=
        (hm₆ (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).2
      _ = _ := by rw [rodierAsymptoticDelta_inv_sixth hn]
  have hI₈ : I₈ ≤ C₈ * (x / q) ^ 4 := by
    calc
      I₈ ≤ C₈ * (rodierAsymptoticDelta n)⁻¹ ^ 8 :=
        (hm₈ (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).2
      _ = _ := by rw [rodierAsymptoticDelta_inv_eighth hn]
  have hA₄ : ‖A₄‖ ≤ C₄ * (x / q) ^ 2 * z := by
    calc
      ‖A₄‖ ≤ C₄ * (rodierAsymptoticDelta n)⁻¹ ^ 4 *
          Real.exp (-(rodierAsymptoticM n ^ 2) /
            (2 * rodierAsymptoticQ n)) :=
        hm₄ n (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
      _ ≤ C₄ * (rodierAsymptoticDelta n)⁻¹ ^ 4 * z := by
        exact mul_le_mul_of_nonneg_left (by simpa [z, x] using hexp)
          (mul_nonneg hC₄ (by positivity))
      _ = _ := by rw [rodierAsymptoticDelta_inv_fourth hn]
  have hR₁ : R₁ ≤ K₁ * x ^ 4 / q ^ 2 := by
    dsimp [R₁, rodierSingleQuarticRemainder, I₆, I₈]
    calc
      3 * q * I₆ + 3 * q ^ 2 * I₈ ≤
          3 * q * (C₆ * (x / q) ^ 3) +
            3 * q ^ 2 * (C₈ * (x / q) ^ 4) := by gcongr
      _ = (3 * C₆ * x ^ 3 + 3 * C₈ * x ^ 4) / q ^ 2 := by
        field_simp
      _ ≤ K₁ * x ^ 4 / q ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg q)
        dsimp [K₁]
        have hx34 : x ^ 3 ≤ x ^ 4 := by
          calc
            x ^ 3 = x ^ 3 * 1 := by ring
            _ ≤ x ^ 3 * x := mul_le_mul_of_nonneg_left hx (by positivity)
            _ = x ^ 4 := by ring
        calc
          3 * C₆ * x ^ 3 + 3 * C₈ * x ^ 4 ≤
              3 * C₆ * x ^ 4 + 3 * C₈ * x ^ 4 := by gcongr
          _ = (3 * C₆ + 3 * C₈) * x ^ 4 := by ring
  change q * (q / 12 * ‖A₄‖ + R₁) ≤
    C * (x ^ 4 / q + x ^ 2 * Real.exp (-x / 2))
  calc
    q * (q / 12 * ‖A₄‖ + R₁) ≤
        q * (q * (C₄ * (x / q) ^ 2 * z) + K₁ * x ^ 4 / q ^ 2) := by
      gcongr
      exact div_le_self hq.le (by norm_num : (1 : ℝ) ≤ 12)
    _ = C₄ * x ^ 2 * z + K₁ * x ^ 4 / q := by
      field_simp
    _ ≤ C * (x ^ 4 / q + x ^ 2 * Real.exp (-x / 2)) := by
      dsimp [C, z]
      rw [show (C₄ + K₁) * (x ^ 4 / q + x ^ 2 * Real.exp (-x / 2)) =
        C₄ * x ^ 2 * Real.exp (-x / 2) + K₁ * x ^ 4 / q +
          (C₄ * (x ^ 4 / q) + K₁ * (x ^ 2 * Real.exp (-x / 2))) by ring]
      exact le_add_of_nonneg_right (add_nonneg (by positivity) (by positivity))

private theorem tendsto_natPow_div_rodierAsymptoticQ (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ k / rodierAsymptoticQ n)
      Filter.atTop (nhds 0) := by
  have h := ((isLittleO_pow_exp_pos_mul_atTop k
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, mul_comm, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    rodierAsymptoticQ] using h

private theorem tendsto_natPow_mul_exp_neg_mul
    (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-b * (n : ℝ)))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) b hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast] using h

private noncomputable def rodierAsymptoticSingleCorrectionEnvelope (n : ℕ) : ℝ :=
  (n : ℝ) ^ 4 / rodierAsymptoticQ n +
    (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 2)

private theorem tendsto_rodierAsymptoticSingleCorrectionEnvelope :
    Filter.Tendsto rodierAsymptoticSingleCorrectionEnvelope Filter.atTop (nhds 0) := by
  have h₁ := tendsto_natPow_div_rodierAsymptoticQ 4
  have h₂ := tendsto_natPow_mul_exp_neg_mul 2 (1 / 2 : ℝ) (by norm_num)
  have heq : (fun n : ℕ => (n : ℝ) ^ 4 / rodierAsymptoticQ n +
      (n : ℝ) ^ 2 * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) =ᶠ[Filter.atTop]
      rodierAsymptoticSingleCorrectionEnvelope := by
    filter_upwards [] with n
    dsimp [rodierAsymptoticSingleCorrectionEnvelope]
    congr 2
    ring
  simpa only [zero_add] using (h₁.add h₂).congr' heq

private noncomputable def rodierAsymptoticOffDiagonalPairEnvelope (n : ℕ) : ℝ :=
  (n : ℝ) ^ 6 / rodierAsymptoticQ n ^ 2 +
    ((n : ℝ) ^ 4 / rodierAsymptoticQ n) * Real.exp (-(n : ℝ))

private noncomputable def rodierAsymptoticGaussianLower (n : ℕ) : ℝ :=
  Real.exp (-5) * (n : ℝ) ^ 5 /
    (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ))

private theorem rodierAsymptoticQ_mul_exp_neg (n : ℕ) :
    rodierAsymptoticQ n * Real.exp (-(n : ℝ)) =
      Real.exp (-(1 - Real.log 2) * (n : ℝ)) := by
  have hpow : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [rodierAsymptoticQ, hpow, ← Real.exp_add]
  congr 1
  ring

private theorem tendsto_rodierAsymptoticOffDiagonalPairEnvelope_scaled :
    Filter.Tendsto
      (fun n : ℕ => rodierAsymptoticQ n ^ 2 * rodierAsymptoticOffDiagonalPairEnvelope n /
        rodierAsymptoticGaussianLower n ^ 2)
      Filter.atTop (nhds 0) := by
  let c : ℝ := Real.exp (-5) / Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hInvThree : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) Filter.atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [inv_pow] using hinv.pow 3
  have hExp : Filter.Tendsto
      (fun n : ℕ => rodierAsymptoticQ n * Real.exp (-(n : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_natPow_mul_exp_neg_mul 0
      (1 - Real.log 2) (by nlinarith [Real.log_two_lt_d9])
    apply h.congr'
    filter_upwards [] with n
    rw [pow_zero, one_mul, rodierAsymptoticQ_mul_exp_neg]
  have hInvFive : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) ^ 5)⁻¹) Filter.atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [inv_pow] using hinv.pow 5
  have hExpDiv : Filter.Tendsto
      (fun n : ℕ => rodierAsymptoticQ n * Real.exp (-(n : ℝ)) /
        (n : ℝ) ^ 5) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hExp.mul hInvFive
  have hmodel : Filter.Tendsto
      (fun n : ℕ => (c ^ 2)⁻¹ *
        (((n : ℝ) ^ 3)⁻¹ +
          rodierAsymptoticQ n * Real.exp (-(n : ℝ)) / (n : ℝ) ^ 5))
      Filter.atTop (nhds 0) := by
    simpa using (hInvThree.add hExpDiv).const_mul (c ^ 2)⁻¹
  apply hmodel.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnℝ.le
  have hcne : c ≠ 0 := ne_of_gt hc
  have hqne : rodierAsymptoticQ n ≠ 0 := ne_of_gt (rodierAsymptoticQ_pos n)
  dsimp [rodierAsymptoticOffDiagonalPairEnvelope, rodierAsymptoticGaussianLower, c]
  rw [show Real.exp (-5) * (n : ℝ) ^ 5 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) =
      (Real.exp (-5) / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ 5 /
        Real.sqrt (n : ℝ) by ring]
  field_simp [hcne, hqne, hsqrt, hnℝ.ne']
  rw [hsqrt]
  ring

private noncomputable def rodierAsymptoticSingleCutoffMean (n : ℕ) : ℝ :=
  (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
    (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re

private theorem eventually_rodierAsymptoticSingleCutoffMean_lower :
    ∀ᶠ n : ℕ in Filter.atTop,
      rodierAsymptoticGaussianLower n / 2 ≤
        rodierAsymptoticQ n * rodierAsymptoticSingleCutoffMean n := by
  obtain ⟨C, hC, hcorrection⟩ := exists_rodierAsymptoticSingleCorrection_bound
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      C * rodierAsymptoticSingleCorrectionEnvelope n < 1 := by
    have ht : Filter.Tendsto (fun n => C * rodierAsymptoticSingleCorrectionEnvelope n)
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_rodierAsymptoticSingleCorrectionEnvelope.const_mul C
    exact ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ rodierAsymptoticGaussianLower n := by
    exact tendsto_rodierScaledGaussianLower_atTop.eventually
      (Filter.eventually_ge_atTop 2)
  filter_upwards [eventually_rodierAsymptotic_parameters,
    eventually_rodierCutoffGaussianIntegral_scaled_lower_bound,
    hcorrection, hsmall, hlarge] with n hp hmain hcorr hsmalln hlargen
  let q : ℝ := rodierAsymptoticQ n
  let E : ℂ := rodierSingleCutoffExpectation (∅ : Finset (Fin n))
    (rodierAsymptoticM n) (rodierAsymptoticDelta n)
  let G : ℂ := rodierCutoffGaussianIntegral n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hp.2.1 hp.2.2.1
  let A₄ : ℂ := rodierGaussianWeightedDensityMoment n 4
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hp.2.1 hp.2.2.1
  let R₁ : ℝ := rodierSingleQuarticRemainder n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hp.2.1 hp.2.2.1
  let D : ℂ := G - (q / 12 : ℝ) * A₄
  have hq : 0 < q := rodierAsymptoticQ_pos n
  have hED : ‖E - D‖ ≤ R₁ := by
    have hsingle :=
      norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
        hp.1 (∅ : Finset (Fin n)) (rodierAsymptoticM n)
          (rodierAsymptoticDelta n) hp.2.1 hp.2.2.1 hp.2.2.2
    simpa [E, D, G, A₄, q, rodierAsymptoticQ, R₁,
      rodierSingleQuarticRemainder] using hsingle
  have hEDre : D.re - R₁ ≤ E.re := by
    have habs : |(E - D).re| ≤ R₁ :=
      (Complex.abs_re_le_norm _).trans hED
    have := (abs_le.mp habs).1
    change -R₁ ≤ E.re - D.re at this
    linarith
  have hA₄re : A₄.re ≤ ‖A₄‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hDre : G.re - q / 12 * ‖A₄‖ ≤ D.re := by
    dsimp [D]
    simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hscale : 0 ≤ q / 12 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hA₄re hscale
    exact sub_le_sub_left hmul G.re
  have hE : G.re - q / 12 * ‖A₄‖ - R₁ ≤ E.re :=
    (sub_le_sub_right hDre R₁).trans hEDre
  have hcorr' : q * (q / 12 * ‖A₄‖ + R₁) < 1 := by
    exact (hcorr hp.2.1 hp.2.2.1).trans_lt (by
      simpa [rodierAsymptoticSingleCorrectionEnvelope] using hsmalln)
  have hmain' : rodierAsymptoticGaussianLower n ≤ q * G.re := by
    simpa [rodierAsymptoticGaussianLower, q] using hmain hp.2.1 hp.2.2.1
  change rodierAsymptoticGaussianLower n / 2 ≤ q * E.re
  have hscaledE : q * G.re - q * (q / 12 * ‖A₄‖ + R₁) ≤
      q * E.re := by
    have := mul_le_mul_of_nonneg_left hE hq.le
    nlinarith
  nlinarith

private theorem tendsto_rodierAsymptoticSecondMomentFailureBound
    (C : ℝ) (hC : 0 ≤ C) :
    Filter.Tendsto
      (rodierAsymptoticSecondMomentFailureBound
        (fun n ↦ C * rodierAsymptoticOffDiagonalPairEnvelope n))
      Filter.atTop (nhds 0) := by
  have hInvLower : Filter.Tendsto
      (fun n : ℕ ↦ (rodierAsymptoticGaussianLower n)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_rodierScaledGaussianLower_atTop
  have hFirst : Filter.Tendsto
      (fun n : ℕ ↦ 2 / rodierAsymptoticGaussianLower n)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hInvLower.const_mul 2
  have hSecond : Filter.Tendsto
      (fun n : ℕ ↦ 4 * C *
        (rodierAsymptoticQ n ^ 2 * rodierAsymptoticOffDiagonalPairEnvelope n /
          rodierAsymptoticGaussianLower n ^ 2))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_rodierAsymptoticOffDiagonalPairEnvelope_scaled.const_mul (4 * C)
  have hmodel : Filter.Tendsto
      (fun n : ℕ ↦ 2 / rodierAsymptoticGaussianLower n + 4 * C *
        (rodierAsymptoticQ n ^ 2 * rodierAsymptoticOffDiagonalPairEnvelope n /
          rodierAsymptoticGaussianLower n ^ 2))
      Filter.atTop (nhds 0) := by
    simpa only [zero_add] using hFirst.add hSecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmodel
  · filter_upwards [eventually_rodierAsymptotic_parameters,
      eventually_rodierAsymptoticSingleCutoffMean_lower] with n hp hmean
    let q : ℝ := rodierAsymptoticQ n
    let e : ℝ := rodierAsymptoticSingleCutoffMean n
    let ε : ℝ := C * rodierAsymptoticOffDiagonalPairEnvelope n
    have hq : 0 < q := rodierAsymptoticQ_pos n
    have hL : 0 < rodierAsymptoticGaussianLower n := by
      have hnℝ : (0 : ℝ) < n := by exact_mod_cast hp.1
      dsimp [rodierAsymptoticGaussianLower]
      positivity
    have he : 0 < e := by
      have hprod : 0 < q * e := lt_of_lt_of_le
        (half_pos hL) hmean
      exact pos_of_mul_pos_right hprod hq.le
    have hpairEnvelope : 0 ≤ rodierAsymptoticOffDiagonalPairEnvelope n := by
      dsimp [rodierAsymptoticOffDiagonalPairEnvelope]
      positivity
    have hε : 0 ≤ ε := mul_nonneg hC hpairEnvelope
    dsimp [rodierAsymptoticSecondMomentFailureBound,
      rodierSecondMomentFailureBound]
    exact div_nonneg (add_nonneg (div_nonneg he.le hq.le) hε)
      (sq_nonneg e)
  · filter_upwards [eventually_rodierAsymptotic_parameters,
      eventually_rodierAsymptoticSingleCutoffMean_lower] with n hp hmean
    let q : ℝ := rodierAsymptoticQ n
    let e : ℝ := rodierAsymptoticSingleCutoffMean n
    let ε : ℝ := C * rodierAsymptoticOffDiagonalPairEnvelope n
    let L : ℝ := rodierAsymptoticGaussianLower n
    have hq : 0 < q := rodierAsymptoticQ_pos n
    have hL : 0 < L := by
      have hnℝ : (0 : ℝ) < n := by exact_mod_cast hp.1
      dsimp [L, rodierAsymptoticGaussianLower]
      positivity
    have he : 0 < e := by
      have hprod : 0 < q * e := lt_of_lt_of_le
        (half_pos hL) hmean
      exact pos_of_mul_pos_right hprod hq.le
    have hpairEnvelope : 0 ≤ rodierAsymptoticOffDiagonalPairEnvelope n := by
      dsimp [rodierAsymptoticOffDiagonalPairEnvelope]
      positivity
    have hε : 0 ≤ ε := mul_nonneg hC hpairEnvelope
    have hscaled : L ≤ 2 * (q * e) := by
      dsimp [L, q, e]
      nlinarith
    have htermOne : (e / q) / e ^ 2 ≤ 2 / L := by
      calc
        (e / q) / e ^ 2 = 1 / (q * e) := by field_simp
        _ ≤ 2 / L :=
          (div_le_div_iff₀ (mul_pos hq he) hL).2 (by simpa using hscaled)
    have hsquare : L ^ 2 ≤ 4 * q ^ 2 * e ^ 2 := by
      nlinarith [sq_nonneg (2 * q * e - L)]
    have hinvSquare : 1 / e ^ 2 ≤ 4 * q ^ 2 / L ^ 2 :=
      (div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hL)).2 (by
        simpa [mul_assoc] using hsquare)
    have htermTwo : ε / e ^ 2 ≤ 4 * q ^ 2 * ε / L ^ 2 := by
      calc
        ε / e ^ 2 = ε * (1 / e ^ 2) := by ring
        _ ≤ ε * (4 * q ^ 2 / L ^ 2) :=
          mul_le_mul_of_nonneg_left hinvSquare hε
        _ = 4 * q ^ 2 * ε / L ^ 2 := by ring
    change ((e / q + ε) / e ^ 2) ≤ _
    calc
      (e / q + ε) / e ^ 2 = (e / q) / e ^ 2 + ε / e ^ 2 := by
        rw [add_div]
      _ ≤ 2 / L + 4 * q ^ 2 * ε / L ^ 2 :=
        add_le_add htermOne htermTwo
      _ = 2 / rodierAsymptoticGaussianLower n + 4 * C *
          (rodierAsymptoticQ n ^ 2 * rodierAsymptoticOffDiagonalPairEnvelope n /
            rodierAsymptoticGaussianLower n ^ 2) := by
        dsimp [L, q, ε]
        ring

/-- Rodier's sharp lower spectral-amplitude event has probability tending to
one for uniformly random Boolean functions. -/
theorem tendsto_rodierRandomFourierLowerProbability :
    Filter.Tendsto rodierRandomFourierLowerProbability
      Filter.atTop (nhds 1) := by
  obtain ⟨C, hC, herror⟩ := exists_rodierAsymptoticOffDiagonalPairError_bound
  let ε : ℕ → ℝ := fun n ↦ C * rodierAsymptoticOffDiagonalPairEnvelope n
  apply tendsto_rodierRandomFourierLowerProbability_of_secondMoment ε
  · filter_upwards [eventually_rodierAsymptotic_parameters] with n hp
    exact hp.2.1
  · filter_upwards with n
    exact mul_nonneg hC (by
      dsimp [rodierAsymptoticOffDiagonalPairEnvelope]
      exact add_nonneg
        (div_nonneg (by positivity) (sq_nonneg _))
        (mul_nonneg
          (div_nonneg (by positivity) (rodierAsymptoticQ_pos n).le)
          (Real.exp_pos _).le))
  · filter_upwards [eventually_rodierAsymptotic_parameters,
      eventually_rodierAsymptoticSingleCutoffMean_lower] with n hp hmean
    have hL : 0 < rodierAsymptoticGaussianLower n := by
      have hnℝ : (0 : ℝ) < n := by exact_mod_cast hp.1
      dsimp [rodierAsymptoticGaussianLower]
      positivity
    have hprod : 0 < rodierAsymptoticQ n * rodierAsymptoticSingleCutoffMean n :=
      lt_of_lt_of_le (half_pos hL) hmean
    have he : 0 < rodierAsymptoticSingleCutoffMean n :=
      pos_of_mul_pos_right hprod (rodierAsymptoticQ_pos n).le
    simpa [rodierAsymptoticSingleCutoffMean] using he
  · filter_upwards [eventually_rodierAsymptotic_parameters,
      herror] with n hp herr
    intro S T hST
    have hfinite :=
      rodierPairCutoffExpectation_re_le_single_sq_add_offDiagonalPairError
        hp.1 (n := n) (S₀ := (∅ : Finset (Fin n))) hST
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)
        hp.2.1 hp.2.2.1 hp.2.2.2
    calc
      _ ≤ (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
            (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ^ 2 +
          rodierOffDiagonalPairError n
            (rodierAsymptoticM n) (rodierAsymptoticDelta n)
              hp.2.1 hp.2.2.1 := hfinite
      _ ≤ (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
            (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ^ 2 +
          C * rodierAsymptoticOffDiagonalPairEnvelope n := by
        gcongr
        simpa [rodierAsymptoticOffDiagonalPairEnvelope] using herr hp.2.1 hp.2.2.1
      _ = _ := by rfl
  · simpa [ε] using tendsto_rodierAsymptoticSecondMomentFailureBound C hC

/-- The probability that a uniformly random Boolean function lies strictly
between both endpoints of Rodier's sharp nonlinearity interval. -/
noncomputable def rodierSharpRandomNonlinearityIntervalProbability (n : ℕ) : ℝ :=
  (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
    {g | rodierRandomNonlinearityLowerThreshold n <
        (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) ∧
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) <
        rodierRandomNonlinearityUpperThreshold n}

private theorem sum_rodierRandomNonlinearityProbabilities_sub_one_le_sharpInterval
    (n : ℕ) :
    rodierRandomNonlinearityLowerProbability n +
        rodierRandomNonlinearityUpperProbability n - 1 ≤
      rodierSharpRandomNonlinearityIntervalProbability n := by
  let μ := (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure
  let lower : Set (FABL.BooleanFunction n) :=
    {g | rodierRandomNonlinearityLowerThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ)}
  let upper : Set (FABL.BooleanFunction n) :=
    {g | (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) <
      rodierRandomNonlinearityUpperThreshold n}
  have hunion : μ.real (lower ∪ upper) ≤ 1 := measureReal_le_one
  have hadd : μ.real (lower ∪ upper) + μ.real (lower ∩ upper) =
      μ.real lower + μ.real upper :=
    measureReal_union_add_inter (Set.toFinite upper).measurableSet
  unfold rodierRandomNonlinearityLowerProbability
    rodierRandomNonlinearityUpperProbability rodierSharpRandomNonlinearityIntervalProbability
  change μ.real lower + μ.real upper - 1 ≤ μ.real (lower ∩ upper)
  linarith

/-- The proportion of Boolean functions in Rodier's simultaneous sharp
two-sided nonlinearity interval tends to one. -/
theorem tendsto_rodierSharpRandomNonlinearityIntervalProbability :
    Filter.Tendsto rodierSharpRandomNonlinearityIntervalProbability Filter.atTop (nhds 1) := by
  have hupper : Filter.Tendsto rodierRandomNonlinearityUpperProbability
      Filter.atTop (nhds 1) :=
    tendsto_rodierRandomNonlinearityUpperProbability_of_fourierLower
      tendsto_rodierRandomFourierLowerProbability
  have hlower := tendsto_rodierRandomNonlinearityLowerProbability
  have hmodel : Filter.Tendsto
      (fun n ↦ rodierRandomNonlinearityLowerProbability n +
        rodierRandomNonlinearityUpperProbability n - 1)
      Filter.atTop (nhds 1) := by
    simpa using (hlower.add hupper).sub_const 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hmodel tendsto_const_nhds
  · exact Filter.Eventually.of_forall
      sum_rodierRandomNonlinearityProbabilities_sub_one_le_sharpInterval
  · exact Filter.Eventually.of_forall fun n ↦ by
      unfold rodierSharpRandomNonlinearityIntervalProbability
      exact measureReal_le_one

end CryptBoolean
