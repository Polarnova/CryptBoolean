/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.RandomNonlinearityAsymptotics
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.Probability.Moments.Variance

/-!
# Rodier's lower spectral-amplitude tail

Exact two-character moment identities used in Rodier's second-moment argument.
-/

open Finset MeasureTheory
open scoped BigOperators BooleanCube ENNReal FourierTransform Topology

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

local instance rodierLowerTailSignMeasurableSpace : MeasurableSpace FABL.Sign := ⊤

local instance rodierLowerTailSignMeasurableSingletonClass :
    MeasurableSingletonClass FABL.Sign where
  measurableSet_singleton _ := by simp

/-- Rodier's lower spectral-amplitude threshold in FABL's normalized Fourier
scale. -/
noncomputable def rodierRandomFourierLowerThreshold (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (Real.sqrt (2 * Real.log 2) -
      5 * Real.log (n : ℝ) / (n : ℝ)) *
    (2 : ℝ) ^ (-(n : ℝ) / 2)

/-- The upper endpoint of Rodier's random-nonlinearity interval. -/
noncomputable def rodierRandomNonlinearityUpperThreshold (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / 2 -
    (2 : ℝ) ^ n * rodierRandomFourierLowerThreshold n / 2

/-- Rodier's upper nonlinearity endpoint in Carlet's displayed normalization. -/
theorem rodierRandomNonlinearityUpperThreshold_eq_displayed (n : ℕ) :
    rodierRandomNonlinearityUpperThreshold n =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) * Real.sqrt (n : ℝ) *
          (Real.sqrt (2 * Real.log 2) -
            5 * Real.log (n : ℝ) / (n : ℝ)) := by
  have hfirst :
      (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast]
    simpa using
      (Real.rpow_sub (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
        (n : ℝ) 1).symm
  have hscale :
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 2) / 2 =
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
    rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg_one,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [rodierRandomNonlinearityUpperThreshold,
    rodierRandomFourierLowerThreshold, hfirst]
  rw [show
    (2 : ℝ) ^ n *
          (Real.sqrt (n : ℝ) *
            (Real.sqrt (2 * Real.log 2) -
              5 * Real.log (n : ℝ) / (n : ℝ)) *
            (2 : ℝ) ^ (-(n : ℝ) / 2)) /
        2 =
      ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 2) / 2) *
        Real.sqrt (n : ℝ) *
          (Real.sqrt (2 * Real.log 2) -
            5 * Real.log (n : ℝ) / (n : ℝ)) by ring,
    hscale]

/-- Relation (35) converts a strict lower bound for the normalized spectral
maximum into the matching upper bound for nonlinearity. -/
theorem nonlinearity_lt_rodierRandomNonlinearityUpperThreshold
    (g : FABL.BooleanFunction n)
    (h : rodierRandomFourierLowerThreshold n <
      FABL.fourierInfinityNorm g.toReal) :
    (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) <
      rodierRandomNonlinearityUpperThreshold n := by
  rw [nonlinearity_encoding_eq_fourierInfinityNorm,
    rodierRandomNonlinearityUpperThreshold]
  have hmul := mul_lt_mul_of_pos_left h
    (show 0 < (2 : ℝ) ^ n / 2 by positivity)
  have hmul' :
      (2 : ℝ) ^ n * rodierRandomFourierLowerThreshold n / 2 <
        (2 : ℝ) ^ n * FABL.fourierInfinityNorm g.toReal / 2 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact sub_lt_sub_left hmul' ((2 : ℝ) ^ n / 2)

/-- The uniform probability of Rodier's lower spectral-amplitude event. -/
noncomputable def rodierRandomFourierLowerProbability (n : ℕ) : ℝ :=
  (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
    {g | rodierRandomFourierLowerThreshold n <
      FABL.fourierInfinityNorm g.toReal}

/-- The uniform probability that nonlinearity lies below Rodier's displayed
upper endpoint. -/
noncomputable def rodierRandomNonlinearityUpperProbability (n : ℕ) : ℝ :=
  (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
    {g | (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) <
      rodierRandomNonlinearityUpperThreshold n}

/-- Relation (35) transports the lower spectral-amplitude event into the
upper nonlinearity event. -/
theorem rodierRandomFourierLowerProbability_le_nonlinearityUpperProbability
    (n : ℕ) :
    rodierRandomFourierLowerProbability n ≤
      rodierRandomNonlinearityUpperProbability n := by
  unfold rodierRandomFourierLowerProbability
    rodierRandomNonlinearityUpperProbability
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro g hg
  exact nonlinearity_lt_rodierRandomNonlinearityUpperThreshold g hg

/-- The missing analytic lower-tail limit is sufficient for Rodier's upper
nonlinearity endpoint. -/
theorem tendsto_rodierRandomNonlinearityUpperProbability_of_fourierLower
    (h : Filter.Tendsto rodierRandomFourierLowerProbability
      Filter.atTop (nhds 1)) :
    Filter.Tendsto rodierRandomNonlinearityUpperProbability
      Filter.atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
  · exact rodierRandomFourierLowerProbability_le_nonlinearityUpperProbability
  · intro n
    unfold rodierRandomNonlinearityUpperProbability
    exact measureReal_le_one


/-- The right transition in Rodier's cutoff. -/
noncomputable def rodierRightCutoff (M Δ x : ℝ) : ℝ :=
  Real.smoothTransition ((x - M) / Δ)

/-- Rodier's smooth cutoff `u_{M,Δ}`. -/
noncomputable def rodierCutoff (M Δ x : ℝ) : ℝ :=
  rodierRightCutoff M Δ x + rodierRightCutoff M Δ (-x)

theorem rodierCutoff_nonneg (M Δ : ℝ) (_hM : 0 < M) (_hΔ : 0 < Δ)
    (x : ℝ) :
    0 ≤ rodierCutoff M Δ x := by
  exact add_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

theorem rodierCutoff_le_one (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ)
    (x : ℝ) :
    rodierCutoff M Δ x ≤ 1 := by
  rcases le_or_gt x M with hx | hx
  · have hz : rodierRightCutoff M Δ x = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hΔ.le
    rw [rodierCutoff, hz, zero_add]
    exact Real.smoothTransition.le_one _
  · have hz : rodierRightCutoff M Δ (-x) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact hΔ.le
    rw [rodierCutoff, hz, add_zero]
    exact Real.smoothTransition.le_one _

theorem rodierCutoff_eq_zero_of_abs_le
    {M Δ x : ℝ} (_hM : 0 < M) (hΔ : 0 < Δ) (hx : |x| ≤ M) :
    rodierCutoff M Δ x = 0 := by
  have hx₁ : x ≤ M := (abs_le.mp hx).2
  have hx₂ : -x ≤ M := by linarith [(abs_le.mp hx).1]
  unfold rodierCutoff rodierRightCutoff
  rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx₁) hΔ.le),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx₂) hΔ.le),
    add_zero]

theorem rodierCutoff_eq_one_of_add_le_abs
    {M Δ x : ℝ} (hM : 0 < M) (hΔ : 0 < Δ) (hx : M + Δ ≤ |x|) :
    rodierCutoff M Δ x = 1 := by
  rcases le_total 0 x with hx0 | hx0
  · have hpos : M + Δ ≤ x := by simpa [abs_of_nonneg hx0] using hx
    have hone : rodierRightCutoff M Δ x = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [one_le_div hΔ]
      linarith
    have hzero : rodierRightCutoff M Δ (-x) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact hΔ.le
    rw [rodierCutoff, hone, hzero, add_zero]
  · have hneg : M + Δ ≤ -x := by simpa [abs_of_nonpos hx0] using hx
    have hone : rodierRightCutoff M Δ (-x) = 1 := by
      apply Real.smoothTransition.one_of_one_le
      rw [one_le_div hΔ]
      linarith
    have hzero : rodierRightCutoff M Δ x = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact hΔ.le
    rw [rodierCutoff, hone, hzero, zero_add]

private theorem rodierRightCutoff_contDiff {m : ℕ∞} (M Δ : ℝ) :
    ContDiff ℝ m (rodierRightCutoff M Δ) := by
  unfold rodierRightCutoff
  fun_prop

theorem rodierCutoff_contDiff
    (M Δ : ℝ) (_hM : 0 < M) (_hΔ : 0 < Δ) :
    ContDiff ℝ (⊤ : ℕ∞) (rodierCutoff M Δ) := by
  exact (rodierRightCutoff_contDiff M Δ).add
    ((rodierRightCutoff_contDiff M Δ).comp (by fun_prop))

/-- The `p`th derivative of Rodier's cutoff has the exact `Δ⁻ᵖ` scaling. -/
theorem iteratedDeriv_rodierCutoff (p : ℕ) (M Δ x : ℝ) :
    iteratedDeriv p (rodierCutoff M Δ) x =
      Δ⁻¹ ^ p *
        (iteratedDeriv p Real.smoothTransition ((x - M) / Δ) +
          (-1 : ℝ) ^ p *
            iteratedDeriv p Real.smoothTransition ((-x - M) / Δ)) := by
  have hright (y : ℝ) :
      iteratedDeriv p (rodierRightCutoff M Δ) y =
        Δ⁻¹ ^ p *
          iteratedDeriv p Real.smoothTransition ((y - M) / Δ) := by
    unfold rodierRightCutoff
    rw [show (fun z : ℝ => Real.smoothTransition ((z - M) / Δ)) =
        fun z => (fun w => Real.smoothTransition (Δ⁻¹ * w)) (z - M) by
      funext z
      simp [div_eq_mul_inv, mul_comm]]
    rw [congrFun (iteratedDeriv_comp_sub_const p
      (fun w => Real.smoothTransition (Δ⁻¹ * w)) M) y]
    rw [congrFun (iteratedDeriv_comp_const_mul
      (Real.smoothTransition.contDiff : ContDiff ℝ p Real.smoothTransition)
      Δ⁻¹) (y - M)]
    simp [div_eq_mul_inv, mul_comm]
  change iteratedDeriv p
      (rodierRightCutoff M Δ + fun z => rodierRightCutoff M Δ (-z)) x = _
  rw [iteratedDeriv_add (n := p) (f := rodierRightCutoff M Δ)
    (g := fun z => rodierRightCutoff M Δ (-z))
    (rodierRightCutoff_contDiff (m := p) M Δ).contDiffAt
    ((rodierRightCutoff_contDiff (m := p) M Δ).comp (by fun_prop)).contDiffAt]
  rw [hright, iteratedDeriv_comp_neg, hright]
  ring

private theorem smoothTransition_iteratedDeriv_hasCompactSupport
    {p : ℕ} (hp : 0 < p) :
    HasCompactSupport (iteratedDeriv p Real.smoothTransition) := by
  refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  have hx' : x < 0 ∨ 1 < x := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    exact hx
  rcases hx' with hxneg | hxpos
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hxneg] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.iteratedDeriv_eq p]
    simp
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => 1) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.iteratedDeriv_eq p]
    simp [iteratedDeriv_const, hp.ne']

private theorem exists_smoothTransition_iteratedDeriv_bound
    {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, |iteratedDeriv p Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (fun x => |iteratedDeriv p Real.smoothTransition x|) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ p Real.smoothTransition)
      |>.continuous_iteratedDeriv' p |>.abs
  have hcompact :
      HasCompactSupport (fun x => |iteratedDeriv p Real.smoothTransition x|) :=
    (smoothTransition_iteratedDeriv_hasCompactSupport hp).abs
  obtain ⟨x₀, hx₀⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcompact
  exact ⟨|iteratedDeriv p Real.smoothTransition x₀|, abs_nonneg _, hx₀⟩

/-- Uniform `Δ⁻ᵖ` control of the positive-order derivatives used in Rodier's
Fourier estimates. -/
theorem exists_iteratedDeriv_rodierCutoff_bound
    {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M Δ x : ℝ}, 0 < Δ →
      |iteratedDeriv p (rodierCutoff M Δ) x| ≤ C * Δ⁻¹ ^ p := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothTransition_iteratedDeriv_bound hp
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro M Δ x hΔ
  rw [iteratedDeriv_rodierCutoff, abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ Δ⁻¹ ^ p)]
  calc
    Δ⁻¹ ^ p *
        |iteratedDeriv p Real.smoothTransition ((x - M) / Δ) +
          (-1 : ℝ) ^ p *
            iteratedDeriv p Real.smoothTransition ((-x - M) / Δ)|
        ≤ Δ⁻¹ ^ p * (C + C) := by
          gcongr
          calc
            _ ≤ |iteratedDeriv p Real.smoothTransition ((x - M) / Δ)| +
                |(-1 : ℝ) ^ p *
                  iteratedDeriv p Real.smoothTransition ((-x - M) / Δ)| :=
              abs_add_le _ _
            _ ≤ C + C := by
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
              exact add_le_add (hbound ((x - M) / Δ))
                (hbound ((-x - M) / Δ))
    _ = (2 * C) * Δ⁻¹ ^ p := by ring

private theorem rodier_shift_scale_integral
    (g : ℝ → ℝ) {M Δ : ℝ} (hΔ : 0 < Δ) :
    (∫ x : ℝ, g ((x - M) / Δ)) = Δ * ∫ y : ℝ, g y := by
  calc
    (∫ x : ℝ, g ((x - M) / Δ)) =
        ∫ x : ℝ, (fun z => g (z / Δ)) (x + (-M)) := by
      congr with x
    _ = ∫ x : ℝ, g (x / Δ) := by
      exact integral_add_right_eq_self (fun z : ℝ => g (z / Δ)) (-M)
    _ = |Δ| • ∫ y : ℝ, g y := Measure.integral_comp_div g Δ
    _ = Δ * ∫ y : ℝ, g y := by rw [abs_of_pos hΔ]; rfl

private theorem rodier_neg_shift_scale_integral
    (g : ℝ → ℝ) {M Δ : ℝ} (hΔ : 0 < Δ) :
    (∫ x : ℝ, g ((-x - M) / Δ)) = Δ * ∫ y : ℝ, g y := by
  calc
    (∫ x : ℝ, g ((-x - M) / Δ)) =
        ∫ x : ℝ, (fun z => g ((z - M) / Δ)) (-x) := by rfl
    _ = ∫ x : ℝ, g ((x - M) / Δ) := by
      exact integral_neg_eq_self (fun z : ℝ => g ((z - M) / Δ)) volume
    _ = Δ * ∫ y : ℝ, g y := rodier_shift_scale_integral g hΔ

/-- The `L¹` norm of the `p`th positive-order cutoff derivative scales as
`Δ^(1-p)`. -/
theorem exists_integral_abs_iteratedDeriv_rodierCutoff_bound
    {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M Δ : ℝ}, 0 < Δ →
      (∫ x : ℝ, |iteratedDeriv p (rodierCutoff M Δ) x|) ≤
        C * Δ⁻¹ ^ p * Δ := by
  let g : ℝ → ℝ := fun y => |iteratedDeriv p Real.smoothTransition y|
  have hgcont : Continuous g :=
    (Real.smoothTransition.contDiff : ContDiff ℝ p Real.smoothTransition)
      |>.continuous_iteratedDeriv' p |>.abs
  have hgsupp : HasCompactSupport g :=
    (smoothTransition_iteratedDeriv_hasCompactSupport hp).abs
  have hg : Integrable g := hgcont.integrable_of_hasCompactSupport hgsupp
  let C : ℝ := 2 * ∫ y : ℝ, g y
  refine ⟨C, mul_nonneg (by norm_num) (integral_nonneg fun _ => abs_nonneg _), ?_⟩
  intro M Δ hΔ
  have h₁ : Integrable (fun x : ℝ => g ((x - M) / Δ)) := by
    simpa only [sub_eq_add_neg] using
      (hg.comp_div hΔ.ne').comp_add_right (-M)
  have h₂ : Integrable (fun x : ℝ => g ((-x - M) / Δ)) := by
    convert h₁.comp_neg using 1
  have hrhs : Integrable (fun x : ℝ =>
      Δ⁻¹ ^ p * (g ((x - M) / Δ) + g ((-x - M) / Δ))) :=
    (h₁.add h₂).const_mul _
  have hpoint (x : ℝ) :
      |iteratedDeriv p (rodierCutoff M Δ) x| ≤
        Δ⁻¹ ^ p * (g ((x - M) / Δ) + g ((-x - M) / Δ)) := by
    rw [iteratedDeriv_rodierCutoff, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ Δ⁻¹ ^ p)]
    gcongr
    calc
      _ ≤ |iteratedDeriv p Real.smoothTransition ((x - M) / Δ)| +
          |(-1 : ℝ) ^ p *
            iteratedDeriv p Real.smoothTransition ((-x - M) / Δ)| :=
        abs_add_le _ _
      _ = g ((x - M) / Δ) + g ((-x - M) / Δ) := by
        simp [g]
  calc
    _ ≤ ∫ x : ℝ,
        Δ⁻¹ ^ p * (g ((x - M) / Δ) + g ((-x - M) / Δ)) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hrhs (Filter.Eventually.of_forall hpoint)
    _ = Δ⁻¹ ^ p *
        ((∫ x : ℝ, g ((x - M) / Δ)) +
          ∫ x : ℝ, g ((-x - M) / Δ)) := by
      rw [integral_const_mul, integral_add h₁ h₂]
    _ = C * Δ⁻¹ ^ p * Δ := by
      rw [rodier_shift_scale_integral g hΔ,
        rodier_neg_shift_scale_integral g hΔ]
      ring

theorem rodierCutoff_sub_one_contDiff
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ rodierCutoff M Δ x - 1) :=
  (rodierCutoff_contDiff M Δ hM hΔ).sub contDiff_const

theorem rodierCutoff_sub_one_hasCompactSupport
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    HasCompactSupport (fun x ↦ rodierCutoff M Δ x - 1) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (M + Δ)) ?_
  intro x hx
  have hx' : M + Δ ≤ |x| := by
    have : M + Δ < |x| := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    exact this.le
  rw [rodierCutoff_eq_one_of_add_le_abs hM hΔ hx']
  simp

/-- The compactly supported part `u_{M,Δ} - 1`, bundled as a complex-valued
Schwartz function. -/
noncomputable def rodierCutoffRemainderSchwartz
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : SchwartzMap ℝ ℂ :=
  ((rodierCutoff_sub_one_hasCompactSupport M Δ hM hΔ).comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp
      (rodierCutoff_sub_one_contDiff M Δ hM hΔ))

@[simp]
theorem rodierCutoffRemainderSchwartz_apply
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (x : ℝ) :
    rodierCutoffRemainderSchwartz M Δ hM hΔ x =
      ((rodierCutoff M Δ x - 1 : ℝ) : ℂ) :=
  rfl

private theorem iteratedDeriv_rodierCutoffRemainderSchwartz
    {p : ℕ} (hp : 0 < p) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (x : ℝ) :
    iteratedDeriv p
        (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ) x =
      Complex.ofReal (iteratedDeriv p (rodierCutoff M Δ) x) := by
  rw [show (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ) =
      fun y => (rodierCutoff M Δ y - 1 : ℝ) • (1 : ℂ) by
    funext y
    rw [rodierCutoffRemainderSchwartz_apply]
    simp]
  have horder : ((p : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hf : ContDiffAt ℝ p (fun y => rodierCutoff M Δ y - 1) x :=
    (((rodierCutoff_contDiff M Δ hM hΔ).sub contDiff_const).of_le
      horder).contDiffAt
  rw [iteratedDeriv_smul_const hf]
  have hsub :
      iteratedDeriv p (fun y => rodierCutoff M Δ y - 1) x =
        iteratedDeriv p (rodierCutoff M Δ) x := by
    have hu : ContDiffAt ℝ p (rodierCutoff M Δ) x :=
      ((rodierCutoff_contDiff M Δ hM hΔ).of_le horder).contDiffAt
    change iteratedDeriv p (rodierCutoff M Δ - fun _ => 1) x = _
    rw [iteratedDeriv_sub hu contDiffAt_const]
    rw [iteratedDeriv_const, if_neg hp.ne']
    simp
  rw [hsub]
  simp

private theorem schwartz_iteratedDeriv_integrable
    (f : SchwartzMap ℝ ℂ) (p : ℕ) :
    Integrable (iteratedDeriv p (f : ℝ → ℂ)) := by
  have hfd : ContDiff ℝ p (f : ℝ → ℂ) := f.smooth p
  have hcont : Continuous (iteratedDeriv p (f : ℝ → ℂ)) :=
    hfd.continuous_iteratedDeriv' p
  have hsch : Integrable (fun x : ℝ => ‖x‖ ^ (0 : ℕ) *
      ‖iteratedFDeriv ℝ p (f : ℝ → ℂ) x‖) := by
    simpa using f.integrable_pow_mul_iteratedFDeriv volume 0 p
  have hfderiv : Integrable (fun x : ℝ =>
      ‖iteratedFDeriv ℝ p (f : ℝ → ℂ) x‖) := by
    simpa using hsch
  have hnorm : Integrable (fun x : ℝ =>
      ‖iteratedDeriv p (f : ℝ → ℂ) x‖) := by
    convert hfderiv using 1
    funext x
    exact (norm_iteratedFDeriv_eq_norm_iteratedDeriv
      (𝕜 := ℝ) (F := ℂ) (n := p) (f := (f : ℝ → ℂ)) (x := x)).symm
  exact (integrable_norm_iff hcont.aestronglyMeasurable).mp hnorm

/-- The unit-frequency Fourier density of `u_{M,Δ} - 1`, using Mathlib's
`exp (-2π i x ξ)` convention. -/
noncomputable def rodierCutoffUnitFourierDensity
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : SchwartzMap ℝ ℂ :=
  𝓕 (rodierCutoffRemainderSchwartz M Δ hM hΔ)

theorem rodierCutoffRemainder_fourierInv_unitDensity
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    𝓕⁻ (rodierCutoffUnitFourierDensity M Δ hM hΔ) =
      rodierCutoffRemainderSchwartz M Δ hM hΔ := by
  exact FourierPair.fourierInv_fourier_eq _

private theorem fourier_iteratedDeriv_rodierCutoffRemainder
    {p : ℕ} (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    𝓕 (iteratedDeriv p
      (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)) =
      fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) ^ p •
        rodierCutoffUnitFourierDensity M Δ hM hΔ ξ := by
  exact Real.fourier_iteratedDeriv (N := ⊤) (n := p)
    ((rodierCutoffRemainderSchwartz M Δ hM hΔ).smooth ⊤)
    (fun q _ => schwartz_iteratedDeriv_integrable _ q) le_top

/-- Rodier's angular-frequency density
`v(t) = (2π)⁻¹ 𝓕(u_{M,Δ} - 1)(t / (2π))`. -/
noncomputable def rodierCutoffFourierDensity
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (t : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    rodierCutoffUnitFourierDensity M Δ hM hΔ (t / (2 * Real.pi))

theorem rodierCutoffFourierDensity_integrable
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    Integrable (rodierCutoffFourierDensity M Δ hM hΔ) := by
  unfold rodierCutoffFourierDensity
  exact ((rodierCutoffUnitFourierDensity M Δ hM hΔ).integrable.comp_div
    (by positivity : 2 * Real.pi ≠ 0)).const_mul
      (((2 * Real.pi : ℝ) : ℂ)⁻¹)

private theorem integral_abs_rodierCutoff_sub_one_le
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (∫ x : ℝ, |rodierCutoff M Δ x - 1|) ≤ 2 * (M + Δ) := by
  let R : ℝ := M + Δ
  have hR : 0 < R := add_pos hM hΔ
  let g : ℝ → ℝ := Set.indicator (Set.Icc (-R) R) (fun _ => 1)
  have hg : Integrable g :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hpoint (x : ℝ) : |rodierCutoff M Δ x - 1| ≤ g x := by
    by_cases hx : x ∈ Set.Icc (-R) R
    · rw [show g x = 1 by simp [g, hx]]
      have hu0 := rodierCutoff_nonneg M Δ hM hΔ x
      have hu1 := rodierCutoff_le_one M Δ hM hΔ x
      rw [abs_of_nonpos (sub_nonpos.mpr hu1)]
      linarith
    · rw [show g x = 0 by simp [g, hx]]
      have hout : R ≤ |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (lt_of_lt_of_le hx (neg_nonpos.mpr hR.le))]
          linarith
        · exact le_trans hx.le (le_abs_self x)
      rw [rodierCutoff_eq_one_of_add_le_abs hM hΔ hout]
      simp
  calc
    _ ≤ ∫ x : ℝ, g x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hg (Filter.Eventually.of_forall hpoint)
    _ = 2 * R := by
      change (∫ x : ℝ,
        Set.indicator (Set.Icc (-R) R) (1 : ℝ → ℝ) x) = 2 * R
      rw [integral_indicator_one measurableSet_Icc,
        Real.volume_real_Icc_of_le (by linarith)]
      ring
    _ = 2 * (M + Δ) := rfl

private theorem norm_rodierCutoffFourierDensity_le
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (t : ℝ) :
    ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ ≤
      Real.pi⁻¹ * (M + Δ) := by
  let f : ℝ → ℂ := rodierCutoffRemainderSchwartz M Δ hM hΔ
  have hfourier :
      ‖rodierCutoffUnitFourierDensity M Δ hM hΔ (t / (2 * Real.pi))‖ ≤
        ∫ x : ℝ, ‖f x‖ := by
    rw [show rodierCutoffUnitFourierDensity M Δ hM hΔ
        (t / (2 * Real.pi)) = 𝓕 f (t / (2 * Real.pi)) from rfl,
      Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards [] with x
    simp
  have hintegral :
      (∫ x : ℝ, ‖f x‖) = ∫ x : ℝ, |rodierCutoff M Δ x - 1| := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [show f x = ((rodierCutoff M Δ x - 1 : ℝ) : ℂ) from rfl]
    exact Complex.norm_real _
  calc
    ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ =
        (2 * Real.pi)⁻¹ *
          ‖rodierCutoffUnitFourierDensity M Δ hM hΔ
            (t / (2 * Real.pi))‖ := by
      simp only [rodierCutoffFourierDensity, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    _ ≤ (2 * Real.pi)⁻¹ * ∫ x : ℝ, ‖f x‖ := by
      exact mul_le_mul_of_nonneg_left hfourier (by positivity)
    _ = (2 * Real.pi)⁻¹ * ∫ x : ℝ, |rodierCutoff M Δ x - 1| := by
      rw [hintegral]
    _ ≤ (2 * Real.pi)⁻¹ * (2 * (M + Δ)) := by
      exact mul_le_mul_of_nonneg_left
        (integral_abs_rodierCutoff_sub_one_le M Δ hM hΔ) (by positivity)
    _ = Real.pi⁻¹ * (M + Δ) := by field_simp

/-- Fourier integration by parts converts the cutoff's `L¹` derivative bound
into angular-frequency decay. -/
theorem exists_rodierCutoffFourierDensity_decay_bound
    {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (t : ℝ),
      |t| ^ p * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ ≤
        C * Δ⁻¹ ^ p * Δ := by
  obtain ⟨C, hC, hL1⟩ :=
    exists_integral_abs_iteratedDeriv_rodierCutoff_bound hp
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by
    dsimp [a]
    positivity
  refine ⟨a⁻¹ * C, mul_nonneg (inv_nonneg.mpr ha.le) hC, ?_⟩
  intro M Δ hM hΔ t
  let f : ℝ → ℂ :=
    iteratedDeriv p
      (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)
  have hfourier := congrFun
    (fourier_iteratedDeriv_rodierCutoffRemainder
      (p := p) M Δ hM hΔ) (t / a)
  have hfourierNorm :
      ‖𝓕 f (t / a)‖ ≤ ∫ x : ℝ, ‖f x‖ := by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards [] with x
    simp
  have hintegral :
      (∫ x : ℝ, ‖f x‖) =
        ∫ x : ℝ, |iteratedDeriv p (rodierCutoff M Δ) x| := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [show f x = Complex.ofReal
        (iteratedDeriv p (rodierCutoff M Δ) x) from
      iteratedDeriv_rodierCutoffRemainderSchwartz hp M Δ hM hΔ x]
    exact Complex.norm_real _
  calc
    |t| ^ p * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ =
        a⁻¹ * ‖𝓕 f (t / a)‖ := by
      rw [hfourier]
      simp only [rodierCutoffFourierDensity, a, norm_mul, norm_inv,
        Complex.norm_real, norm_smul, norm_pow, Complex.norm_I,
        Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos, abs_div, abs_of_pos ha]
      norm_num
      dsimp [a]
      field_simp
    _ ≤ a⁻¹ * ∫ x : ℝ, ‖f x‖ := by gcongr
    _ = a⁻¹ * ∫ x : ℝ,
        |iteratedDeriv p (rodierCutoff M Δ) x| := by rw [hintegral]
    _ ≤ a⁻¹ * (C * Δ⁻¹ ^ p * Δ) := by
      gcongr
      exact hL1 hΔ
    _ = (a⁻¹ * C) * Δ⁻¹ ^ p * Δ := by ring

private theorem exists_rodierCutoffFourierDensity_scaled_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (_hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M → ∀ t : ℝ,
        |t| ^ k * ‖rodierCutoffFourierDensity M Δ _hM hΔ t‖ ≤
          C * M * Δ⁻¹ ^ k := by
  rcases k with _ | k
  · refine ⟨2 * Real.pi⁻¹, mul_nonneg (by norm_num) (by positivity), ?_⟩
    intro M Δ hM hΔ hΔM t
    simp only [pow_zero, one_mul]
    calc
      ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ ≤
          Real.pi⁻¹ * (M + Δ) :=
        norm_rodierCutoffFourierDensity_le M Δ hM hΔ t
      _ ≤ Real.pi⁻¹ * (2 * M) := by
        gcongr
        linarith
      _ = (2 * Real.pi⁻¹) * M * Δ⁻¹ ^ 0 := by ring
  · obtain ⟨C, hC, hdecay⟩ :=
      exists_rodierCutoffFourierDensity_decay_bound (Nat.succ_pos k)
    refine ⟨C, hC, ?_⟩
    intro M Δ hM hΔ hΔM t
    calc
      |t| ^ (k + 1) * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ ≤
          C * Δ⁻¹ ^ (k + 1) * Δ := hdecay M Δ hM hΔ t
      _ ≤ C * M * Δ⁻¹ ^ (k + 1) := by
        have hscale : 0 ≤ C * Δ⁻¹ ^ (k + 1) :=
          mul_nonneg hC (by positivity)
        nlinarith

private theorem exists_rodierCutoffFourierDensity_moment_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ =>
          |t| ^ k * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ k *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * M * Δ⁻¹ ^ (k + 1) := by
  obtain ⟨A, hA, hbase⟩ :=
    exists_rodierCutoffFourierDensity_scaled_bound k
  obtain ⟨B, hB, hdecay⟩ :=
    exists_rodierCutoffFourierDensity_decay_bound
      (show 0 < k + 2 by omega)
  refine ⟨(A + B) * Real.pi,
    mul_nonneg (add_nonneg hA hB) Real.pi_pos.le, ?_⟩
  intro M Δ hM hΔ hΔM
  let w : ℝ → ℝ := fun t =>
    |t| ^ k * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖
  let K : ℝ → ℝ := fun t => (1 + (Δ * t) ^ 2)⁻¹
  let S : ℝ := (A + B) * M * Δ⁻¹ ^ k
  have hbase' (t : ℝ) : w t ≤ A * M * Δ⁻¹ ^ k :=
    hbase M Δ hM hΔ hΔM t
  have hscaled (t : ℝ) : (Δ * t) ^ 2 * w t ≤ B * M * Δ⁻¹ ^ k := by
    calc
      (Δ * t) ^ 2 * w t =
          Δ ^ 2 * (|t| ^ (k + 2) *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
        simp only [w, mul_pow]
        rw [pow_add]
        rw [sq_abs]
        ring
      _ ≤ Δ ^ 2 * (B * Δ⁻¹ ^ (k + 2) * Δ) := by
        exact mul_le_mul_of_nonneg_left (hdecay M Δ hM hΔ t) (sq_nonneg Δ)
      _ = B * Δ * Δ⁻¹ ^ k := by
        rw [pow_add]
        field_simp
      _ ≤ B * M * Δ⁻¹ ^ k := by
        have hscale : 0 ≤ B * Δ⁻¹ ^ k := mul_nonneg hB (by positivity)
        nlinarith
  have hpoint (t : ℝ) : w t ≤ S * K t := by
    have hden : 0 < 1 + (Δ * t) ^ 2 := by positivity
    have hsum : (1 + (Δ * t) ^ 2) * w t ≤ S := by
      dsimp [S]
      nlinarith [hbase' t, hscaled t]
    calc
      w t = ((1 + (Δ * t) ^ 2) * w t) * (1 + (Δ * t) ^ 2)⁻¹ := by
        field_simp
      _ ≤ S * (1 + (Δ * t) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hden.le)
      _ = S * K t := rfl
  have hK : Integrable K := by
    have h := integrable_inv_one_add_sq.comp_div (inv_ne_zero hΔ.ne')
    convert h using 1
    funext t
    dsimp [K]
    congr 2
    field_simp
  have hKint : (∫ t : ℝ, K t) = Δ⁻¹ * Real.pi := by
    have h := Measure.integral_comp_div
      (fun x : ℝ => (1 + x ^ 2)⁻¹) Δ⁻¹
    rw [abs_of_pos (inv_pos.mpr hΔ)] at h
    simpa [K, div_eq_mul_inv, hΔ.ne', mul_comm] using h
  have henv : Integrable (fun t => S * K t) := hK.const_mul S
  have hwcont : Continuous w := by
    dsimp [w, rodierCutoffFourierDensity]
    fun_prop
  have hw : Integrable w := by
    apply MeasureTheory.Integrable.mono' henv hwcont.aestronglyMeasurable
    filter_upwards [] with t
    have hwt : 0 ≤ w t := mul_nonneg (pow_nonneg (abs_nonneg t) k)
      (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hwt]
    exact hpoint t
  refine ⟨hw, ?_⟩
  calc
    (∫ t : ℝ, w t) ≤ ∫ t : ℝ, S * K t :=
      integral_mono hw henv hpoint
    _ = S * (Δ⁻¹ * Real.pi) := by rw [integral_const_mul, hKint]
    _ = ((A + B) * Real.pi) * M * Δ⁻¹ ^ (k + 1) := by
      dsimp [S]
      rw [pow_succ]
      ring

private theorem exists_rodierCutoffFourierDensity_positiveMoment_bound
    {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ =>
          |t| ^ k * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ k *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * Δ⁻¹ ^ k := by
  obtain ⟨A, hA, hbase⟩ :=
    exists_rodierCutoffFourierDensity_decay_bound hk
  obtain ⟨B, hB, hdecay⟩ :=
    exists_rodierCutoffFourierDensity_decay_bound
      (show 0 < k + 2 by omega)
  refine ⟨(A + B) * Real.pi,
    mul_nonneg (add_nonneg hA hB) Real.pi_pos.le, ?_⟩
  intro M Δ hM hΔ
  let w : ℝ → ℝ := fun t =>
    |t| ^ k * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖
  let K : ℝ → ℝ := fun t => (1 + (Δ * t) ^ 2)⁻¹
  let S : ℝ := (A + B) * Δ⁻¹ ^ k * Δ
  have hbase' (t : ℝ) : w t ≤ A * Δ⁻¹ ^ k * Δ :=
    hbase M Δ hM hΔ t
  have hscaled (t : ℝ) :
      (Δ * t) ^ 2 * w t ≤ B * Δ⁻¹ ^ k * Δ := by
    calc
      (Δ * t) ^ 2 * w t =
          Δ ^ 2 * (|t| ^ (k + 2) *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
        simp only [w, mul_pow]
        rw [pow_add, sq_abs]
        ring
      _ ≤ Δ ^ 2 * (B * Δ⁻¹ ^ (k + 2) * Δ) := by
        exact mul_le_mul_of_nonneg_left (hdecay M Δ hM hΔ t) (sq_nonneg Δ)
      _ = B * Δ⁻¹ ^ k * Δ := by
        rw [show k + 2 = k + 2 by rfl, pow_add]
        field_simp
  have hpoint (t : ℝ) : w t ≤ S * K t := by
    have hden : 0 < 1 + (Δ * t) ^ 2 := by positivity
    have hsum : (1 + (Δ * t) ^ 2) * w t ≤ S := by
      dsimp [S]
      nlinarith [hbase' t, hscaled t]
    calc
      w t = ((1 + (Δ * t) ^ 2) * w t) * (1 + (Δ * t) ^ 2)⁻¹ := by
        field_simp
      _ ≤ S * (1 + (Δ * t) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hden.le)
      _ = S * K t := rfl
  have hK : Integrable K := by
    have h := integrable_inv_one_add_sq.comp_div (inv_ne_zero hΔ.ne')
    convert h using 1
    funext t
    dsimp [K]
    congr 2
    field_simp
  have hKint : (∫ t : ℝ, K t) = Δ⁻¹ * Real.pi := by
    have h := Measure.integral_comp_div
      (fun x : ℝ => (1 + x ^ 2)⁻¹) Δ⁻¹
    rw [abs_of_pos (inv_pos.mpr hΔ)] at h
    simpa [K, div_eq_mul_inv, hΔ.ne', mul_comm] using h
  have henv : Integrable (fun t => S * K t) := hK.const_mul S
  have hwcont : Continuous w := by
    dsimp [w, rodierCutoffFourierDensity]
    fun_prop
  have hw : Integrable w := by
    apply MeasureTheory.Integrable.mono' henv hwcont.aestronglyMeasurable
    filter_upwards [] with t
    have hwt : 0 ≤ w t := mul_nonneg (pow_nonneg (abs_nonneg t) k)
      (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hwt]
    exact hpoint t
  refine ⟨hw, ?_⟩
  calc
    (∫ t : ℝ, w t) ≤ ∫ t : ℝ, S * K t :=
      integral_mono hw henv hpoint
    _ = S * (Δ⁻¹ * Real.pi) := by rw [integral_const_mul, hKint]
    _ = ((A + B) * Real.pi) * Δ⁻¹ ^ k := by
      dsimp [S]
      field_simp

/-- Rodier's cutoff density has total mass `O(M / Δ)` when `0 < Δ ≤ M`. -/
theorem exists_rodierCutoffFourierDensity_totalMass_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ =>
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
          C * M * Δ⁻¹ := by
  simpa using exists_rodierCutoffFourierDensity_moment_bound 0

/-- The fourth absolute moment of Rodier's cutoff density is
`O(M / Δ⁵)`. -/
theorem exists_rodierCutoffFourierDensity_fourthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ =>
          |t| ^ 4 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 4 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * M * Δ⁻¹ ^ 5 := by
  simpa using exists_rodierCutoffFourierDensity_moment_bound 4

/-- The sixth absolute moment of Rodier's cutoff density is
`O(M / Δ⁷)`. -/
theorem exists_rodierCutoffFourierDensity_sixthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ =>
          |t| ^ 6 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 6 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * M * Δ⁻¹ ^ 7 := by
  simpa using exists_rodierCutoffFourierDensity_moment_bound 6

/-- The eighth absolute moment of Rodier's cutoff density is
`O(M / Δ⁹)`. -/
theorem exists_rodierCutoffFourierDensity_eighthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ =>
          |t| ^ 8 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 8 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * M * Δ⁻¹ ^ 9 := by
  simpa using exists_rodierCutoffFourierDensity_moment_bound 8

/-- The sharp second absolute-moment estimate in Rodier Proposition 4.1 is
`O(Δ⁻²)`, uniformly in the cutoff center. -/
theorem exists_rodierCutoffFourierDensity_secondMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ =>
          |t| ^ 2 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 2 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * Δ⁻¹ ^ 2 := by
  simpa using exists_rodierCutoffFourierDensity_positiveMoment_bound
    (by norm_num : 0 < 2)

/-- The sharp fourth absolute-moment estimate in Rodier Proposition 4.1 is
`O(Δ⁻⁴)`, uniformly in the cutoff center. -/
theorem exists_rodierCutoffFourierDensity_fourthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ =>
          |t| ^ 4 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 4 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * Δ⁻¹ ^ 4 := by
  simpa using exists_rodierCutoffFourierDensity_positiveMoment_bound
    (by norm_num : 0 < 4)

/-- The sharp sixth absolute-moment estimate in Rodier Proposition 4.1 is
`O(Δ⁻⁶)`, uniformly in the cutoff center. -/
theorem exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ =>
          |t| ^ 6 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 6 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * Δ⁻¹ ^ 6 := by
  simpa using exists_rodierCutoffFourierDensity_positiveMoment_bound
    (by norm_num : 0 < 6)

/-- The sharp eighth absolute-moment estimate in Rodier Proposition 4.1 is
`O(Δ⁻⁸)`, uniformly in the cutoff center. -/
theorem exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ =>
          |t| ^ 8 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ∧
        (∫ t : ℝ, |t| ^ 8 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) ≤
            C * Δ⁻¹ ^ 8 := by
  simpa using exists_rodierCutoffFourierDensity_positiveMoment_bound
    (by norm_num : 0 < 8)

/-- Rodier's Fourier--Stieltjes complex measure
`U = δ₀ + v(t) dt`. -/
noncomputable def rodierCutoffFourierMeasure
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ComplexMeasure ℝ :=
  VectorMeasure.dirac 0 1 +
    volume.withDensityᵥ (rodierCutoffFourierDensity M Δ hM hΔ)

theorem rodierCutoffFourierMeasure_apply
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    rodierCutoffFourierMeasure M Δ hM hΔ s =
      VectorMeasure.dirac 0 1 s +
        ∫ t in s, rodierCutoffFourierDensity M Δ hM hΔ t := by
  unfold rodierCutoffFourierMeasure
  rw [add_apply, withDensityᵥ_apply
    (rodierCutoffFourierDensity_integrable M Δ hM hΔ) hs]

/-- The variation of Rodier's measure is dominated by its Dirac mass plus the
absolute density. -/
theorem rodierCutoffFourierMeasure_variation_le
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (rodierCutoffFourierMeasure M Δ hM hΔ).variation ≤
      Measure.dirac 0 + volume.withDensity
        (fun t => ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ₑ) := by
  unfold rodierCutoffFourierMeasure
  calc
    (VectorMeasure.dirac (M := ℂ) 0 1 +
        volume.withDensityᵥ (rodierCutoffFourierDensity M Δ hM hΔ)).variation ≤
      (VectorMeasure.dirac (M := ℂ) 0 1).variation +
        (volume.withDensityᵥ
          (rodierCutoffFourierDensity M Δ hM hΔ)).variation :=
      VectorMeasure.variation_add_le
    _ = _ := by
      rw [VectorMeasure.variation_dirac,
        Measure.variation_withDensityᵥ
          (rodierCutoffFourierDensity_integrable M Δ hM hΔ)]
      simp

private theorem rodierCutoffFourierMeasure_variation_real_univ_le
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (rodierCutoffFourierMeasure M Δ hM hΔ).variation.real Set.univ ≤
      1 + ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  have hv : Integrable v := rodierCutoffFourierDensity_integrable M Δ hM hΔ
  let ν : Measure ℝ := Measure.dirac 0 +
    volume.withDensity (fun t => ‖v t‖ₑ)
  have hle : (rodierCutoffFourierMeasure M Δ hM hΔ).variation Set.univ ≤
      ν Set.univ := rodierCutoffFourierMeasure_variation_le M Δ hM hΔ Set.univ
  have hν : ν Set.univ = ENNReal.ofReal
      (1 + ∫ t : ℝ, ‖v t‖) := by
    rw [show ν Set.univ = Measure.dirac (0 : ℝ) Set.univ +
        (volume.withDensity fun t => ‖v t‖ₑ) Set.univ by
      simp only [ν, Measure.add_apply],
      withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ,
      Measure.dirac_apply_of_mem (Set.mem_univ _)]
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hv]
    rw [ENNReal.ofReal_add (by positivity : 0 ≤ (1 : ℝ))
      (integral_nonneg fun _ => norm_nonneg _)]
    simp
  have hνtop : ν Set.univ ≠ ∞ := by
    rw [hν]
    exact ENNReal.ofReal_ne_top
  calc
    _ ≤ (ν Set.univ).toReal := ENNReal.toReal_mono hνtop hle
    _ = 1 + ∫ t : ℝ, ‖v t‖ := by
      rw [hν, ENNReal.toReal_ofReal]
      positivity
    _ = _ := rfl

/-- Rodier's Fourier--Stieltjes measure has total variation `O(M / Δ)` when
`0 < Δ ≤ M`. -/
theorem exists_rodierCutoffFourierMeasure_variation_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        (rodierCutoffFourierMeasure M Δ hM hΔ).variation.real Set.univ ≤
          C * M * Δ⁻¹ := by
  obtain ⟨C, hC, hmass⟩ :=
    exists_rodierCutoffFourierDensity_totalMass_bound
  refine ⟨1 + C, add_nonneg zero_le_one hC, ?_⟩
  intro M Δ hM hΔ hΔM
  have hratio : 1 ≤ M * Δ⁻¹ := by
    rw [le_mul_inv_iff₀ hΔ]
    simpa using hΔM
  calc
    _ ≤ 1 + ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ :=
      rodierCutoffFourierMeasure_variation_real_univ_le M Δ hM hΔ
    _ ≤ 1 + C * M * Δ⁻¹ := by
      gcongr
      exact (hmass M Δ hM hΔ hΔM).2
    _ ≤ (1 + C) * M * Δ⁻¹ := by
      nlinarith [mul_nonneg hC (le_trans zero_le_one hratio)]

private theorem rodierCutoffFourierMeasure_variation_moment_le_density
    {k : ℕ} (hk : 0 < k)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ)
    (hweight : Integrable (fun t : ℝ =>
      |t| ^ k * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)) :
    Integrable (fun t : ℝ => |t| ^ k)
        (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
      (∫ t : ℝ, |t| ^ k ∂
        (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
        ∫ t : ℝ, |t| ^ k *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let ρ : ℝ → ℝ≥0∞ := fun t => ‖v t‖ₑ
  let ν : Measure ℝ := Measure.dirac 0 + volume.withDensity ρ
  have hρ : Measurable ρ := by
    apply Continuous.measurable
    apply Continuous.enorm
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  have hρtop : ∀ᵐ t : ℝ ∂volume, ρ t < ∞ := by
    filter_upwards [] with t
    simp [ρ]
  have hdens : Integrable (fun t : ℝ => |t| ^ k) (volume.withDensity ρ) := by
    rw [integrable_withDensity_iff_integrable_smul' hρ hρtop]
    simpa [ρ, v, mul_comm] using hweight
  have hdirac : Integrable (fun t : ℝ => |t| ^ k) (Measure.dirac 0) :=
    integrable_dirac (by simp)
  have hν : Integrable (fun t : ℝ => |t| ^ k) ν :=
    integrable_add_measure.mpr ⟨hdirac, hdens⟩
  have hle : (rodierCutoffFourierMeasure M Δ hM hΔ).variation ≤ ν :=
    rodierCutoffFourierMeasure_variation_le M Δ hM hΔ
  refine ⟨hν.mono_measure hle, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, |t| ^ k ∂ν :=
      integral_mono_measure hle
        (Filter.Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _)
        hν
    _ = (∫ t : ℝ, |t| ^ k ∂Measure.dirac 0) +
        ∫ t : ℝ, |t| ^ k ∂volume.withDensity ρ := by
      exact integral_add_measure hdirac hdens
    _ = ∫ t : ℝ, |t| ^ k * ‖v t‖ := by
      rw [integral_dirac,
        integral_withDensity_eq_integral_toReal_smul hρ hρtop]
      simp [ρ, v, hk.ne', mul_comm]
    _ = _ := rfl

/-- The fourth absolute moment of the variation of Rodier's measure is
`O(M / Δ⁵)`. -/
theorem exists_rodierCutoffFourierMeasure_fourthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ => |t| ^ 4)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 4 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * M * Δ⁻¹ ^ 5 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ hΔM
  have hdensity := hmoment M Δ hM hΔ hΔM
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 4) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

/-- The sixth absolute moment of the variation of Rodier's measure is
`O(M / Δ⁷)`. -/
theorem exists_rodierCutoffFourierMeasure_sixthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ => |t| ^ 6)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 6 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * M * Δ⁻¹ ^ 7 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ hΔM
  have hdensity := hmoment M Δ hM hΔ hΔM
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 6) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

/-- The eighth absolute moment of the variation of Rodier's measure is
`O(M / Δ⁹)`. -/
theorem exists_rodierCutoffFourierMeasure_eighthMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ), Δ ≤ M →
        Integrable (fun t : ℝ => |t| ^ 8)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 8 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * M * Δ⁻¹ ^ 9 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ hΔM
  have hdensity := hmoment M Δ hM hΔ hΔM
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 8) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

/-- The fourth absolute moment of the variation satisfies Rodier's sharp
`O(Δ⁻⁴)` estimate. -/
theorem exists_rodierCutoffFourierMeasure_fourthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ => |t| ^ 4)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 4 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * Δ⁻¹ ^ 4 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_sharp_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ
  have hdensity := hmoment M Δ hM hΔ
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 4) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

/-- The sixth absolute moment of the variation satisfies Rodier's sharp
`O(Δ⁻⁶)` estimate. -/
theorem exists_rodierCutoffFourierMeasure_sixthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ => |t| ^ 6)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 6 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * Δ⁻¹ ^ 6 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ
  have hdensity := hmoment M Δ hM hΔ
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 6) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

/-- The eighth absolute moment of the variation satisfies Rodier's sharp
`O(Δ⁻⁸)` estimate. -/
theorem exists_rodierCutoffFourierMeasure_eighthMoment_sharp_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        Integrable (fun t : ℝ => |t| ^ 8)
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation ∧
        (∫ t : ℝ, |t| ^ 8 ∂
          (rodierCutoffFourierMeasure M Δ hM hΔ).variation) ≤
            C * Δ⁻¹ ^ 8 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound
  refine ⟨C, hC, ?_⟩
  intro M Δ hM hΔ
  have hdensity := hmoment M Δ hM hΔ
  have hvariation :=
    rodierCutoffFourierMeasure_variation_moment_le_density
      (by norm_num : 0 < 8) M Δ hM hΔ hdensity.1
  exact ⟨hvariation.1, hvariation.2.trans hdensity.2⟩

theorem rodierCutoff_eq_one_add_fourierInv_unitDensity
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (x : ℝ) :
    ((rodierCutoff M Δ x : ℝ) : ℂ) =
      1 + 𝓕⁻ (rodierCutoffUnitFourierDensity M Δ hM hΔ) x := by
  rw [rodierCutoffRemainder_fourierInv_unitDensity]
  simp

private theorem rodierCutoff_fourierInv_unitDensity_eq_angularIntegral
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (x : ℝ) :
    𝓕⁻ (rodierCutoffUnitFourierDensity M Δ hM hΔ) x =
      ∫ t : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        rodierCutoffFourierDensity M Δ hM hΔ t := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale := Measure.integral_comp_div
    (fun y : ℝ => Complex.exp (((a * y * x : ℝ) : ℂ) * Complex.I) *
      ((a : ℂ)⁻¹ * rodierCutoffUnitFourierDensity M Δ hM hΔ y)) a
  rw [abs_of_pos ha] at hscale
  calc
    _ = a • ∫ y : ℝ,
        Complex.exp (((a * y * x : ℝ) : ℂ) * Complex.I) *
          ((a : ℂ)⁻¹ * rodierCutoffUnitFourierDensity M Δ hM hΔ y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show inner ℝ y x = y * x by simp [mul_comm]]
      simp only [smul_eq_mul, Complex.real_smul]
      dsimp [a]
      push_cast
      field_simp
    _ = ∫ t : ℝ,
        Complex.exp (((a * (t / a) * x : ℝ) : ℂ) * Complex.I) *
          ((a : ℂ)⁻¹ *
            rodierCutoffUnitFourierDensity M Δ hM hΔ (t / a)) := hscale.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [rodierCutoffFourierDensity, a]
      congr 2
      push_cast
      field_simp

/-- Fourier inversion in Rodier's angular-frequency convention. Equivalently,
the cutoff is represented by the complex measure `δ₀ + v(t) dt`. -/
theorem rodierCutoff_fourierDensity_inversion
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (x : ℝ) :
    ((rodierCutoff M Δ x : ℝ) : ℂ) =
      1 + ∫ t : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        rodierCutoffFourierDensity M Δ hM hΔ t := by
  rw [rodierCutoff_eq_one_add_fourierInv_unitDensity M Δ hM hΔ x,
    rodierCutoff_fourierInv_unitDensity_eq_angularIntegral M Δ hM hΔ x]

private theorem expect_pi_prod_complex
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (g : ι → α → ℂ) :
    Finset.expect Finset.univ (fun f : ι → α ↦ ∏ i, g i (f i)) =
      ∏ i, Finset.expect Finset.univ (fun a : α ↦ g i a) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum, Fintype.card_pi]
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib]
  norm_cast

private theorem expect_sign_cexp_eq_cos (a : ℝ) :
    Finset.expect Finset.univ (fun s : FABL.Sign ↦
      Complex.exp (Complex.I * (FABL.signValue s * a : ℝ))) =
      (Real.cos a : ℂ) := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [FABL.Sign, FABL.signValue]
  rw [mul_comm Complex.I (a : ℂ)]
  calc
    (Complex.exp ((a : ℂ) * Complex.I) +
        Complex.exp (-((a : ℂ) * Complex.I))) / 2 =
        (2 * Complex.cos (a : ℂ)) / 2 := by
      rw [Complex.two_cos]
      ring_nf
    _ = Complex.cos (a : ℂ) := by ring

/-- The linear combination of two Walsh characters occurring in Rodier's
bivariate characteristic-function calculation. -/
noncomputable def rodierPairPhase
    (S T : Finset (Fin n)) (t r : ℝ) (x : {−1,1}^[n]) : ℝ :=
  t * FABL.monomial S x + r * FABL.monomial T x

private theorem abs_rodierPairPhase_le
    (S T : Finset (Fin n)) (t r : ℝ) (x : {−1,1}^[n]) :
    |rodierPairPhase S T t r x| ≤ |t| + |r| := by
  have hS : |FABL.monomial S x| = 1 := by
    rcases sq_eq_one_iff.mp (FABL.monomial_sq S x) with h | h <;> simp [h]
  have hT : |FABL.monomial T x| = 1 := by
    rcases sq_eq_one_iff.mp (FABL.monomial_sq T x) with h | h <;> simp [h]
  rw [rodierPairPhase]
  calc
    |t * FABL.monomial S x + r * FABL.monomial T x| ≤
        |t * FABL.monomial S x| + |r * FABL.monomial T x| := abs_add_le _ _
    _ = |t| + |r| := by simp [abs_mul, hS, hT]

/-- The joint characteristic function of two raw Walsh coefficients. -/
noncomputable def rodierPairCharacteristic
    (S T : Finset (Fin n)) (t r : ℝ) : ℂ :=
  Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
    Complex.exp
      (Complex.I *
        (∑ x : {−1,1}^[n],
          FABL.signValue (f x) * rodierPairPhase S T t r x : ℝ)))

/-- The exact independent-coordinate product underlying Rodier Lemma 6.4. -/
theorem rodierPairCharacteristic_eq_prod_cos
    (S T : Finset (Fin n)) (t r : ℝ) :
    rodierPairCharacteristic S T t r =
      ∏ x : {−1,1}^[n], (Real.cos (rodierPairPhase S T t r x) : ℂ) := by
  rw [rodierPairCharacteristic]
  have hexp (f : FABL.BooleanFunction n) :
      Complex.exp
          (Complex.I *
            (∑ x : {−1,1}^[n],
              FABL.signValue (f x) * rodierPairPhase S T t r x : ℝ)) =
        ∏ x : {−1,1}^[n],
          Complex.exp
            (Complex.I *
              (FABL.signValue (f x) * rodierPairPhase S T t r x : ℝ)) := by
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hexp]
  let g : {−1,1}^[n] → FABL.Sign → ℂ := fun x s ↦
    Complex.exp
      (Complex.I *
        (FABL.signValue s * rodierPairPhase S T t r x : ℝ))
  change Finset.expect Finset.univ
      (fun f : FABL.BooleanFunction n ↦ ∏ x, g x (f x)) = _
  rw [expect_pi_prod_complex g]
  apply Finset.prod_congr rfl
  intro x _
  exact expect_sign_cexp_eq_cos (rodierPairPhase S T t r x)

/-- The raw Walsh coefficient indexed by the sign character `S`. -/
noncomputable def rodierRawWalshCoefficient
    (S : Finset (Fin n)) (f : FABL.BooleanFunction n) : ℝ :=
  ∑ x : {−1,1}^[n], FABL.signValue (f x) * FABL.monomial S x

/-- The characteristic function of one raw Walsh coefficient. -/
noncomputable def rodierSingleCharacteristic
    (S : Finset (Fin n)) (t : ℝ) : ℂ :=
  Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
    Complex.exp
      (((t * rodierRawWalshCoefficient S f : ℝ) : ℂ) * Complex.I))

theorem rodierSingleCharacteristic_eq_pair
    (S T : Finset (Fin n)) (t : ℝ) :
    rodierSingleCharacteristic S t = rodierPairCharacteristic S T t 0 := by
  unfold rodierSingleCharacteristic rodierPairCharacteristic
    rodierRawWalshCoefficient rodierPairPhase
  congr 1
  funext f
  apply congrArg Complex.exp
  have hsum :
      t * ∑ x : {−1,1}^[n], FABL.signValue (f x) * FABL.monomial S x =
        ∑ x : {−1,1}^[n],
          FABL.signValue (f x) *
            (t * FABL.monomial S x + 0 * FABL.monomial T x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  push_cast
  ring

/-- Every raw Walsh coefficient has characteristic function
`cos(t)^(2^n)`. -/
theorem rodierSingleCharacteristic_eq_cos_pow
    (S : Finset (Fin n)) (t : ℝ) :
    rodierSingleCharacteristic S t = (Real.cos t : ℂ) ^ (2 ^ n) := by
  rw [rodierSingleCharacteristic_eq_pair S S t,
    rodierPairCharacteristic_eq_prod_cos]
  calc
    ∏ x : {−1,1}^[n], (Real.cos (rodierPairPhase S S t 0 x) : ℂ) =
        ∏ _x : {−1,1}^[n], (Real.cos t : ℂ) := by
      apply Finset.prod_congr rfl
      intro x _
      unfold rodierPairPhase
      rcases sq_eq_one_iff.mp (FABL.monomial_sq S x) with h | h <;>
        simp [h]
    _ = (Real.cos t : ℂ) ^ (2 ^ n) := by
      simp [Fintype.card_pi, FABL.Sign]

/-- The uniform expectation of Rodier's smooth cutoff at one raw Walsh
coefficient. -/
noncomputable def rodierSingleCutoffExpectation
    (S : Finset (Fin n)) (M Δ : ℝ) : ℂ :=
  Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
    (rodierCutoff M Δ (rodierRawWalshCoefficient S f) : ℂ))

/-- Fourier inversion and finite averaging express the one-coefficient cutoff
expectation through its exact characteristic function. -/
theorem rodierSingleCutoffExpectation_eq_characteristicIntegral
    (S : Finset (Fin n)) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    rodierSingleCutoffExpectation S M Δ =
      1 + ∫ t : ℝ, rodierSingleCharacteristic S t *
        rodierCutoffFourierDensity M Δ hM hΔ t := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  have hv : Integrable v := rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hint (f : FABL.BooleanFunction n) :
      Integrable (fun t : ℝ =>
        Complex.exp
          (((t * rodierRawWalshCoefficient S f : ℝ) : ℂ) * Complex.I) * v t) := by
    apply hv.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards [] with t
      simp [Complex.norm_exp]
  rw [rodierSingleCutoffExpectation, Fintype.expect_eq_sum_div_card]
  simp_rw [rodierCutoff_fourierDensity_inversion M Δ hM hΔ]
  simp_rw [rodierSingleCharacteristic, Fintype.expect_eq_sum_div_card]
  have hright :
      (∫ t : ℝ,
        (∑ f : FABL.BooleanFunction n,
            Complex.exp
              (((t * rodierRawWalshCoefficient S f : ℝ) : ℂ) * Complex.I)) /
            (Fintype.card (FABL.BooleanFunction n) : ℂ) *
          rodierCutoffFourierDensity M Δ hM hΔ t) =
        (∑ f : FABL.BooleanFunction n,
          ∫ t : ℝ,
            Complex.exp
              (((t * rodierRawWalshCoefficient S f : ℝ) : ℂ) * Complex.I) *
              rodierCutoffFourierDensity M Δ hM hΔ t) /
          (Fintype.card (FABL.BooleanFunction n) : ℂ) := by
    calc
      _ = ∫ t : ℝ,
          (∑ f : FABL.BooleanFunction n,
            Complex.exp
              (((t * rodierRawWalshCoefficient S f : ℝ) : ℂ) * Complex.I) *
              rodierCutoffFourierDensity M Δ hM hΔ t) /
            (Fintype.card (FABL.BooleanFunction n) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [← Finset.sum_mul]
          ring
      _ = _ := by
        rw [integral_div,
          MeasureTheory.integral_finsetSum Finset.univ (fun f _ ↦ hint f)]
  rw [hright]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  apply integral_congr_ae
  filter_upwards [] with t
  congr 2
  ring

/-- Distinct Walsh characters have zero raw correlation on the sign cube. -/
theorem sum_monomial_mul_eq_zero_of_ne
    {S T : Finset (Fin n)} (hST : S ≠ T) :
    ∑ x : {−1,1}^[n], FABL.monomial S x * FABL.monomial T x = 0 := by
  have h := FABL.expect_monomial_mul S T
  rw [if_neg hST, Fintype.expect_eq_sum_div_card] at h
  have hcard : (Fintype.card ({−1,1}^[n]) : ℝ) ≠ 0 := by
    positivity
  exact (div_eq_zero_iff).mp h |>.resolve_right hcard

/-- The exact quadratic character sum in Rodier Lemma 6.4. -/
theorem sum_rodierPairPhase_sq
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ) :
    ∑ x : {−1,1}^[n], rodierPairPhase S T t r x ^ 2 =
      (2 : ℝ) ^ n * (t ^ 2 + r ^ 2) := by
  have hcross := sum_monomial_mul_eq_zero_of_ne hST
  calc
    ∑ x : {−1,1}^[n], rodierPairPhase S T t r x ^ 2 =
        ∑ x : {−1,1}^[n],
          (t ^ 2 + r ^ 2 +
            2 * t * r * (FABL.monomial S x * FABL.monomial T x)) := by
      apply Finset.sum_congr rfl
      intro x _
      have hS := FABL.monomial_sq S x
      have hT := FABL.monomial_sq T x
      rw [rodierPairPhase]
      ring_nf
      rw [hS, hT]
      ring
    _ = (2 : ℝ) ^ n * (t ^ 2 + r ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
      simp
      ring

/-- The exact quartic character sum in Rodier Lemma 6.4. -/
theorem sum_rodierPairPhase_fourth
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ) :
    ∑ x : {−1,1}^[n], rodierPairPhase S T t r x ^ 4 =
      (2 : ℝ) ^ n *
        (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) := by
  have hcross := sum_monomial_mul_eq_zero_of_ne hST
  calc
    ∑ x : {−1,1}^[n], rodierPairPhase S T t r x ^ 4 =
        ∑ x : {−1,1}^[n],
          (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4 +
            (4 * t ^ 3 * r + 4 * t * r ^ 3) *
              (FABL.monomial S x * FABL.monomial T x)) := by
      apply Finset.sum_congr rfl
      intro x _
      have hS := FABL.monomial_sq S x
      have hT := FABL.monomial_sq T x
      have hS3 : FABL.monomial S x ^ 3 = FABL.monomial S x := by
        calc
          FABL.monomial S x ^ 3 = FABL.monomial S x ^ 2 * FABL.monomial S x := by
            ring
          _ = FABL.monomial S x := by rw [hS]; ring
      have hT3 : FABL.monomial T x ^ 3 = FABL.monomial T x := by
        calc
          FABL.monomial T x ^ 3 = FABL.monomial T x ^ 2 * FABL.monomial T x := by
            ring
          _ = FABL.monomial T x := by rw [hT]; ring
      have hS4 : FABL.monomial S x ^ 4 = 1 := by
        calc
          FABL.monomial S x ^ 4 = (FABL.monomial S x ^ 2) ^ 2 := by ring
          _ = 1 := by rw [hS]; norm_num
      have hT4 : FABL.monomial T x ^ 4 = 1 := by
        calc
          FABL.monomial T x ^ 4 = (FABL.monomial T x ^ 2) ^ 2 := by ring
          _ = 1 := by rw [hT]; norm_num
      rw [rodierPairPhase]
      ring_nf
      rw [hS, hT, hS3, hT3, hS4, hT4]
      ring
    _ = (2 : ℝ) ^ n *
        (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
      simp
      ring

private theorem abs_cos_sub_quartic_le
    {t : ℝ} (ht : |t| ≤ 1) :
    |Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24)| ≤
      |t| ^ 6 * (7 / 4320) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  calc
    ‖((Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24) : ℝ) : ℂ)‖ =
        ‖Complex.cos (t : ℂ) -
          (1 - (t : ℂ) ^ 2 / 2 + (t : ℂ) ^ 4 / 24)‖ := by
      simp
    _ =
        ‖(Complex.exp (-(t : ℂ) * Complex.I) -
              ∑ m ∈ Finset.range 6,
                (-(t : ℂ) * Complex.I) ^ m / m.factorial) / 2 +
          (Complex.exp ((t : ℂ) * Complex.I) -
              ∑ m ∈ Finset.range 6,
                ((t : ℂ) * Complex.I) ^ m / m.factorial) / 2‖ := by
      simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
      grind [Complex.I_sq, two_ne_zero]
    _ ≤
        ‖Complex.exp (-(t : ℂ) * Complex.I) -
              ∑ m ∈ Finset.range 6,
                (-(t : ℂ) * Complex.I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp ((t : ℂ) * Complex.I) -
              ∑ m ∈ Finset.range 6,
                ((t : ℂ) * Complex.I) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤
        ‖-(t : ℂ) * Complex.I‖ ^ 6 *
              (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 +
          ‖(t : ℂ) * Complex.I‖ ^ 6 *
              (Nat.succ 6 * (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound (by simpa) (by simp),
        Complex.exp_bound (by simpa) (by simp)]
    _ = |t| ^ 6 * (7 / 4320) := by norm_num

/-- Rodier Relation (10), with an explicit uniform quadratic remainder on the
nonnegative half-line. -/
theorem abs_exp_neg_sub_exp_neg_sub_linear_le_sq_div_two
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b) - (b - a) * Real.exp (-b)| ≤
      (a - b) ^ 2 / 2 := by
  by_cases hab : a = b
  · subst a
    simp
  have hcont : ContDiff ℝ 2 (fun s : ℝ ↦ Real.exp (-s)) := by fun_prop
  obtain ⟨c, hc, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun s : ℝ ↦ Real.exp (-s)) (x := a) (x₀ := b) (n := 1)
      (Ne.symm hab) hcont.contDiffOn
  have hderiv :
      derivWithin (fun s : ℝ ↦ Real.exp (-s)) (Set.uIcc b a) b =
        -Real.exp (-b) := by
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_exp (-b)).comp b
          (hasDerivAt_neg b)).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_uIcc (Ne.symm hab)) b Set.left_mem_uIcc)
  have hiteratedDeriv :
      iteratedDeriv 2 (fun s : ℝ ↦ Real.exp (-s)) c =
        Real.exp (-c) := by
    convert congrFun (iteratedDeriv_exp_const_mul 2 (-1)) c using 1 <;> norm_num
  have hremainder :
      Real.exp (-a) -
          (Real.exp (-b) + (a - b) * (-Real.exp (-b))) =
        Real.exp (-c) * (a - b) ^ 2 / 2 := by
    simpa [taylorWithinEval_succ, hderiv, hiteratedDeriv] using hrem
  have hcNonneg : 0 ≤ c := by
    grind [Set.uIoo]
  calc
    |Real.exp (-a) - Real.exp (-b) - (b - a) * Real.exp (-b)| =
        |Real.exp (-c) * (a - b) ^ 2 / 2| := by
      congr 1
      rw [← hremainder]
      ring
    _ = Real.exp (-c) * (a - b) ^ 2 / 2 := by
      rw [abs_of_nonneg]
      positivity
    _ ≤ 1 * (a - b) ^ 2 / 2 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by linarith)
    _ = (a - b) ^ 2 / 2 := by ring

/-- Uniform sixth-order remainder for the logarithm of cosine on Rodier's
cutoff interval. -/
theorem abs_log_cos_add_sq_div_two_add_pow_four_div_twelve_le
    (t : ℝ) (ht : |t| ≤ 1) :
    |Real.log (Real.cos t) + t ^ 2 / 2 + t ^ 4 / 12| ≤ |t| ^ 6 := by
  let x : ℝ := 1 - Real.cos t
  let q : ℝ := Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24)
  have htSq : t ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg t) ht
  have hcosHalf : (1 / 2 : ℝ) ≤ Real.cos t := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hxNonneg : 0 ≤ x := by
    dsimp [x]
    linarith [Real.cos_le_one t]
  have hxHalf : x ≤ 1 / 2 := by
    dsimp [x]
    linarith
  have hxAbsLt : |x| < 1 := by
    rw [abs_of_nonneg hxNonneg]
    linarith
  have hxLe : x ≤ |t| ^ 2 / 2 := by
    dsimp [x]
    rw [sq_abs]
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hlogTaylor :
      |x + x ^ 2 / 2 + Real.log (1 - x)| ≤
        |x| ^ 3 / (1 - |x|) := by
    have h := Real.abs_log_sub_add_sum_range_le (x := x) hxAbsLt 2
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hlog :
      |Real.log (Real.cos t) + x + x ^ 2 / 2| ≤ |t| ^ 6 / 4 := by
    calc
      |Real.log (Real.cos t) + x + x ^ 2 / 2| =
          |x + x ^ 2 / 2 + Real.log (1 - x)| := by
        congr 1
        dsimp [x]
        ring_nf
      _ ≤ |x| ^ 3 / (1 - |x|) := hlogTaylor
      _ = x ^ 3 / (1 - x) := by rw [abs_of_nonneg hxNonneg]
      _ ≤ (|t| ^ 2 / 2) ^ 3 / (1 / 2) := by
        gcongr
        linarith
      _ = |t| ^ 6 / 4 := by ring
  have hq : |q| ≤ |t| ^ 6 / 100 := by
    apply (abs_cos_sub_quartic_le ht).trans
    nlinarith [pow_nonneg (abs_nonneg t) 6]
  have htAbsSq : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  have htPowSixLePowFour : |t| ^ 6 ≤ |t| ^ 4 := by
    calc
      |t| ^ 6 = |t| ^ 4 * |t| ^ 2 := by ring
      _ ≤ |t| ^ 4 * 1 := by
        gcongr
      _ = |t| ^ 4 := by ring
  have hdifference : |t ^ 2 / 2 - x| ≤ |t| ^ 4 / 10 := by
    calc
      |t ^ 2 / 2 - x| = |t ^ 4 / 24 + q| := by
        congr 1
        dsimp [x, q]
        ring
      _ ≤ |t ^ 4 / 24| + |q| := abs_add_le _ _
      _ ≤ |t| ^ 4 / 24 + |t| ^ 6 / 100 := by
        gcongr
        simp [abs_div, abs_pow]
      _ ≤ |t| ^ 4 / 10 := by
        nlinarith [pow_nonneg (abs_nonneg t) 4]
  have hsum : |t ^ 2 / 2 + x| ≤ |t| ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    calc
      t ^ 2 / 2 + x ≤ t ^ 2 / 2 + |t| ^ 2 / 2 := by gcongr
      _ = |t| ^ 2 := by rw [sq_abs]; ring
  have hproduct :
      |(t ^ 2 / 2 - x) * (t ^ 2 / 2 + x) / 2| ≤ |t| ^ 6 / 20 := by
    rw [abs_div, abs_mul]
    norm_num
    calc
      |t ^ 2 / 2 - x| * |t ^ 2 / 2 + x| / 2 ≤
          (|t| ^ 4 / 10) * |t| ^ 2 / 2 := by gcongr
      _ = |t| ^ 6 / 20 := by ring
  have hpolynomial :
      |-x - x ^ 2 / 2 + t ^ 2 / 2 + t ^ 4 / 12| ≤ |t| ^ 6 / 4 := by
    calc
      |-x - x ^ 2 / 2 + t ^ 2 / 2 + t ^ 4 / 12| =
          |q + (t ^ 2 / 2 - x) * (t ^ 2 / 2 + x) / 2| := by
        congr 1
        dsimp [x, q]
        ring
      _ ≤ |q| + |(t ^ 2 / 2 - x) * (t ^ 2 / 2 + x) / 2| :=
        abs_add_le _ _
      _ ≤ |t| ^ 6 / 100 + |t| ^ 6 / 20 := add_le_add hq hproduct
      _ ≤ |t| ^ 6 / 4 := by
        nlinarith [pow_nonneg (abs_nonneg t) 6]
  calc
    |Real.log (Real.cos t) + t ^ 2 / 2 + t ^ 4 / 12| =
        |(Real.log (Real.cos t) + x + x ^ 2 / 2) +
          (-x - x ^ 2 / 2 + t ^ 2 / 2 + t ^ 4 / 12)| := by ring_nf
    _ ≤ |Real.log (Real.cos t) + x + x ^ 2 / 2| +
        |-x - x ^ 2 / 2 + t ^ 2 / 2 + t ^ 4 / 12| := abs_add_le _ _
    _ ≤ |t| ^ 6 / 4 + |t| ^ 6 / 4 := add_le_add hlog hpolynomial
    _ ≤ |t| ^ 6 := by
      nlinarith [pow_nonneg (abs_nonneg t) 6]

/-- The summed logarithmic remainder in Rodier's two-character expansion is
uniformly sixth order on the cutoff square. -/
theorem abs_sum_log_cos_rodierPairPhase_add_moments_le
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ)
    (htr : |t| + |r| ≤ 1) :
    |∑ x : {−1,1}^[n], Real.log (Real.cos (rodierPairPhase S T t r x)) +
          (2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2 +
          (2 : ℝ) ^ n * (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12| ≤
      (2 : ℝ) ^ n * (|t| + |r|) ^ 6 := by
  have hsum :
      |∑ x : {−1,1}^[n],
          (Real.log (Real.cos (rodierPairPhase S T t r x)) +
            rodierPairPhase S T t r x ^ 2 / 2 +
            rodierPairPhase S T t r x ^ 4 / 12)| ≤
        (2 : ℝ) ^ n * (|t| + |r|) ^ 6 := by
    calc
      |∑ x : {−1,1}^[n],
          (Real.log (Real.cos (rodierPairPhase S T t r x)) +
            rodierPairPhase S T t r x ^ 2 / 2 +
            rodierPairPhase S T t r x ^ 4 / 12)| ≤
          ∑ x : {−1,1}^[n],
            |Real.log (Real.cos (rodierPairPhase S T t r x)) +
              rodierPairPhase S T t r x ^ 2 / 2 +
              rodierPairPhase S T t r x ^ 4 / 12| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : {−1,1}^[n], |rodierPairPhase S T t r x| ^ 6 := by
        gcongr with x
        exact abs_log_cos_add_sq_div_two_add_pow_four_div_twelve_le _
          ((abs_rodierPairPhase_le S T t r x).trans htr)
      _ ≤ ∑ _x : {−1,1}^[n], (|t| + |r|) ^ 6 := by
        gcongr with x
        exact abs_rodierPairPhase_le S T t r x
      _ = (2 : ℝ) ^ n * (|t| + |r|) ^ 6 := by
        simp [Fintype.card_pi, FABL.Sign, nsmul_eq_mul]
  rw [← sum_rodierPairPhase_sq hST t r,
    ← sum_rodierPairPhase_fourth hST t r,
    Finset.sum_div, Finset.sum_div,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact hsum

/-- On the cutoff square, the exact cosine product is the exponential of its
real logarithmic sum. -/
theorem rodierPairCharacteristic_eq_exp_sum_log_cos
    (S T : Finset (Fin n)) (t r : ℝ) (htr : |t| + |r| ≤ 1) :
    rodierPairCharacteristic S T t r =
      (Real.exp
        (∑ x : {−1,1}^[n],
          Real.log (Real.cos (rodierPairPhase S T t r x))) : ℂ) := by
  rw [rodierPairCharacteristic_eq_prod_cos]
  norm_cast
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro x _
  exact (Real.exp_log
    (Real.cos_pos_of_le_one
      ((abs_rodierPairPhase_le S T t r x).trans htr))).symm

/-- Explicit additive-error form of Rodier Lemma 6.4 after exponentiating the
quadratic and quartic logarithmic expansion. -/
theorem abs_exp_sum_log_cos_rodierPairPhase_sub_quarticGaussian_le
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ)
    (htr : |t| + |r| ≤ 1) :
    |Real.exp
          (∑ x : {−1,1}^[n],
            Real.log (Real.cos (rodierPairPhase S T t r x))) -
        (Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) -
          ((2 : ℝ) ^ n *
              (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) *
            Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)))| ≤
      (2 : ℝ) ^ n * (|t| + |r|) ^ 6 +
        ((2 : ℝ) ^ n * (|t| + |r|) ^ 6) ^ 2 / 2 +
        ((2 : ℝ) ^ n *
            (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) ^ 2 / 2 := by
  let L : ℝ :=
    ∑ x : {−1,1}^[n], Real.log (Real.cos (rodierPairPhase S T t r x))
  let A : ℝ := (2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2
  let Q : ℝ :=
    (2 : ℝ) ^ n * (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12
  let E : ℝ := (2 : ℝ) ^ n * (|t| + |r|) ^ 6
  have hLNonpos : L ≤ 0 := by
    dsimp [L]
    apply Finset.sum_nonpos
    intro x _
    apply Real.log_nonpos
    · exact (Real.cos_pos_of_le_one
        ((abs_rodierPairPhase_le S T t r x).trans htr)).le
    · exact Real.cos_le_one _
  have hANonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hQNonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hENonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hdelta : |(A + Q) - (-L)| ≤ E := by
    calc
      |(A + Q) - (-L)| = |L + A + Q| := by ring_nf
      _ ≤ E := by
        simpa [L, A, Q, E] using
          abs_sum_log_cos_rodierPairPhase_add_moments_le hST t r htr
  have hdeltaSq : ((A + Q) - (-L)) ^ 2 ≤ E ^ 2 := by
    calc
      ((A + Q) - (-L)) ^ 2 = |(A + Q) - (-L)| ^ 2 := by rw [sq_abs]
      _ ≤ E ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdelta 2
  have hfirstTaylor :=
    abs_exp_neg_sub_exp_neg_sub_linear_le_sq_div_two
      (-L) (A + Q) (neg_nonneg.mpr hLNonpos) (add_nonneg hANonneg hQNonneg)
  have hfirst :
      |Real.exp L -
          (Real.exp (-(A + Q)) +
            ((A + Q) - (-L)) * Real.exp (-(A + Q)))| ≤
        E ^ 2 / 2 := by
    calc
      |Real.exp L -
          (Real.exp (-(A + Q)) +
            ((A + Q) - (-L)) * Real.exp (-(A + Q)))| =
          |Real.exp (-(-L)) - Real.exp (-(A + Q)) -
            ((A + Q) - (-L)) * Real.exp (-(A + Q))| := by ring_nf
      _ ≤ ((-L) - (A + Q)) ^ 2 / 2 := hfirstTaylor
      _ ≤ E ^ 2 / 2 := by
        nlinarith [hdeltaSq]
  have hexpBLeOne : Real.exp (-(A + Q)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hlinear :
      |((A + Q) - (-L)) * Real.exp (-(A + Q))| ≤ E := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |(A + Q) - (-L)| * Real.exp (-(A + Q)) ≤ E * 1 := by
        gcongr
      _ = E := by ring
  have htoQuartic :
      |Real.exp L - Real.exp (-(A + Q))| ≤ E ^ 2 / 2 + E := by
    calc
      |Real.exp L - Real.exp (-(A + Q))| =
          |(Real.exp L -
              (Real.exp (-(A + Q)) +
                ((A + Q) - (-L)) * Real.exp (-(A + Q)))) +
            ((A + Q) - (-L)) * Real.exp (-(A + Q))| := by ring_nf
      _ ≤
          |Real.exp L -
              (Real.exp (-(A + Q)) +
                ((A + Q) - (-L)) * Real.exp (-(A + Q)))| +
            |((A + Q) - (-L)) * Real.exp (-(A + Q))| := abs_add_le _ _
      _ ≤ E ^ 2 / 2 + E := add_le_add hfirst hlinear
  have hsecondTaylor :=
    abs_exp_neg_sub_exp_neg_sub_linear_le_sq_div_two
      (A + Q) A (add_nonneg hANonneg hQNonneg) hANonneg
  have hquartic :
      |Real.exp (-(A + Q)) -
          (Real.exp (-A) - Q * Real.exp (-A))| ≤ Q ^ 2 / 2 := by
    calc
      |Real.exp (-(A + Q)) -
          (Real.exp (-A) - Q * Real.exp (-A))| =
          |Real.exp (-(A + Q)) - Real.exp (-A) -
            (A - (A + Q)) * Real.exp (-A)| := by ring_nf
      _ ≤ ((A + Q) - A) ^ 2 / 2 := hsecondTaylor
      _ = Q ^ 2 / 2 := by ring
  calc
    |Real.exp
          (∑ x : {−1,1}^[n],
            Real.log (Real.cos (rodierPairPhase S T t r x))) -
        (Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) -
          ((2 : ℝ) ^ n *
              (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) *
            Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)))| =
        |Real.exp L - (Real.exp (-A) - Q * Real.exp (-A))| := by
      rfl
    _ ≤ |Real.exp L - Real.exp (-(A + Q))| +
        |Real.exp (-(A + Q)) -
          (Real.exp (-A) - Q * Real.exp (-A))| := by
      exact (abs_sub_le _ _ _)
    _ ≤ (E ^ 2 / 2 + E) + Q ^ 2 / 2 := add_le_add htoQuartic hquartic
    _ = E + E ^ 2 / 2 + Q ^ 2 / 2 := by ring
    _ =
        (2 : ℝ) ^ n * (|t| + |r|) ^ 6 +
          ((2 : ℝ) ^ n * (|t| + |r|) ^ 6) ^ 2 / 2 +
          ((2 : ℝ) ^ n *
              (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) ^ 2 / 2 := by
      rfl

/-- Rodier Lemma 6.4 with explicit sixth- and eighth-order additive errors for
the exact joint characteristic function. -/
theorem norm_rodierPairCharacteristic_sub_quarticGaussian_le
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ)
    (htr : |t| + |r| ≤ 1) :
    ‖rodierPairCharacteristic S T t r -
        ((Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) -
          ((2 : ℝ) ^ n *
              (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) *
            Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) : ℝ) : ℂ)‖ ≤
      (2 : ℝ) ^ n * (|t| + |r|) ^ 6 +
        ((2 : ℝ) ^ n * (|t| + |r|) ^ 6) ^ 2 / 2 +
        ((2 : ℝ) ^ n *
            (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) ^ 2 / 2 := by
  rw [rodierPairCharacteristic_eq_exp_sum_log_cos S T t r htr,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_sum_log_cos_rodierPairPhase_sub_quarticGaussian_le hST t r htr

private theorem rodier_finset_ne_compl
    {a : Type*} [Fintype a] [DecidableEq a] [Nonempty a]
    (s : Finset a) : s ≠ sᶜ := by
  intro h
  let i : a := Classical.choice (inferInstance : Nonempty a)
  by_cases hi : i ∈ s
  · have hic : i ∈ sᶜ := by rw [← h]; exact hi
    exact (Finset.mem_compl.mp hic) hi
  · have hic : i ∈ sᶜ := Finset.mem_compl.mpr hi
    have his : i ∈ s := by rw [h]; exact hic
    exact hi his

/-- The one-variable specialization of Rodier's quartic characteristic
expansion on the unit interval. -/
theorem norm_rodierSingleCharacteristic_sub_quarticGaussian_le
    (hn : 0 < n) (S : Finset (Fin n)) (t : ℝ) (ht : |t| ≤ 1) :
    ‖rodierSingleCharacteristic S t -
        ((Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) -
          ((2 : ℝ) ^ n * t ^ 4 / 12) *
            Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      (2 : ℝ) ^ n * |t| ^ 6 + ((2 : ℝ) ^ n) ^ 2 * |t| ^ 8 := by
  let T : Finset (Fin n) := Sᶜ
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hST : S ≠ T := rodier_finset_ne_compl S
  have h := norm_rodierPairCharacteristic_sub_quarticGaussian_le
    hST t 0 (by simpa using ht)
  rw [← rodierSingleCharacteristic_eq_pair S T t] at h
  norm_num at h
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have ht12le8 : |t| ^ 12 ≤ |t| ^ 8 := by
    calc
      |t| ^ 12 = |t| ^ 8 * |t| ^ 4 := by ring
      _ ≤ |t| ^ 8 * 1 := by
        gcongr
        exact pow_le_one₀ ht0 ht
      _ = |t| ^ 8 := by ring
  have hpow :
      (((2 : ℝ) ^ n * |t| ^ 6) ^ 2 / 2) ≤
        (((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) / 2 := by
    calc
      _ = (((2 : ℝ) ^ n) ^ 2 * |t| ^ 12) / 2 := by ring
      _ ≤ (((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) / 2 := by gcongr
  have hquartic :
      (((2 : ℝ) ^ n * t ^ 4 / 12) ^ 2 / 2) ≤
        (((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) / 288 := by
    rw [show t ^ 4 = |t| ^ 4 by
      calc
        t ^ 4 = |t ^ 4| := (abs_of_nonneg (by positivity)).symm
        _ = |t| ^ 4 := abs_pow t 4]
    ring_nf
    exact le_rfl
  calc
    _ ≤ (2 : ℝ) ^ n * |t| ^ 6 +
        ((2 : ℝ) ^ n * |t| ^ 6) ^ 2 / 2 +
        ((2 : ℝ) ^ n * t ^ 4 / 12) ^ 2 / 2 := by
      convert h using 1
      all_goals norm_num
    _ ≤ (2 : ℝ) ^ n * |t| ^ 6 +
        (((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) / 2 +
        (((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) / 288 := by gcongr
    _ ≤ (2 : ℝ) ^ n * |t| ^ 6 +
        ((2 : ℝ) ^ n) ^ 2 * |t| ^ 8 := by
      nlinarith [mul_nonneg (sq_nonneg ((2 : ℝ) ^ n))
        (pow_nonneg ht0 8)]

/-- A global one-variable remainder bound. Outside Rodier's unit interval,
the sixth and eighth moments absorb the bounded characteristic function. -/
theorem norm_rodierSingleCharacteristic_sub_quarticGaussian_global_le
    (hn : 0 < n) (S : Finset (Fin n)) (t : ℝ) :
    ‖rodierSingleCharacteristic S t -
        ((Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) -
          ((2 : ℝ) ^ n * t ^ 4 / 12) *
            Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      3 * ((2 : ℝ) ^ n * |t| ^ 6 +
        ((2 : ℝ) ^ n) ^ 2 * |t| ^ 8) := by
  by_cases ht : |t| ≤ 1
  · exact (norm_rodierSingleCharacteristic_sub_quarticGaussian_le hn S t ht).trans (by
      have hnonneg : 0 ≤ (2 : ℝ) ^ n * |t| ^ 6 +
          ((2 : ℝ) ^ n) ^ 2 * |t| ^ 8 := by positivity
      nlinarith)
  · have ht1 : 1 ≤ |t| := (lt_of_not_ge ht).le
    let q : ℝ := (2 : ℝ) ^ n
    let A : ℝ := q * t ^ 2 / 2
    let Q : ℝ := q * t ^ 4 / 12
    let G : ℝ := Real.exp (-A)
    have hq : 1 ≤ q := by
      dsimp [q]
      exact one_le_pow₀ (by norm_num)
    have hA : 0 ≤ A := by dsimp [A, q]; positivity
    have hQ : 0 ≤ Q := by dsimp [Q, q]; positivity
    have hG0 : 0 ≤ G := (Real.exp_pos _).le
    have hG1 : G ≤ 1 := by
      dsimp [G]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA)
    have hchar : ‖rodierSingleCharacteristic S t‖ ≤ 1 := by
      rw [rodierSingleCharacteristic_eq_cos_pow, norm_pow,
        Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
    have happ : ‖((G - Q * G : ℝ) : ℂ)‖ ≤ 1 + Q := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |G - Q * G| ≤ |G| + |Q * G| := abs_sub _ _
        _ = G + Q * G := by rw [abs_of_nonneg hG0, abs_mul,
          abs_of_nonneg hQ, abs_of_nonneg hG0]
        _ ≤ 1 + Q := by nlinarith [mul_le_mul_of_nonneg_left hG1 hQ]
    have hqpow : 1 ≤ q ^ 2 * |t| ^ 8 := by
      have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
      have ht8 : 1 ≤ |t| ^ 8 := one_le_pow₀ ht1
      nlinarith [mul_le_mul hq2 ht8 zero_le_one
        (by positivity : 0 ≤ q ^ 2)]
    have hQbound : Q ≤ q * |t| ^ 6 := by
      have ht46 : |t| ^ 4 ≤ |t| ^ 6 := by
        have ht2 : 1 ≤ |t| ^ 2 := one_le_pow₀ ht1
        calc
          |t| ^ 4 = |t| ^ 4 * 1 := by ring
          _ ≤ |t| ^ 4 * |t| ^ 2 :=
            mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = |t| ^ 6 := by ring
      dsimp [Q]
      have hq0 : 0 ≤ q := le_trans zero_le_one hq
      calc
        q * t ^ 4 / 12 = q * |t| ^ 4 / 12 := by
          congr 2
          calc
            t ^ 4 = |t ^ 4| := (abs_of_nonneg (by positivity)).symm
            _ = |t| ^ 4 := abs_pow t 4
        _ ≤ q * |t| ^ 4 := by
          have : 0 ≤ q * |t| ^ 4 := by positivity
          nlinarith
        _ ≤ q * |t| ^ 6 := mul_le_mul_of_nonneg_left ht46 hq0
    calc
      _ ≤ ‖rodierSingleCharacteristic S t‖ +
          ‖((G - Q * G : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + Q) := add_le_add hchar happ
      _ ≤ 3 * (q * |t| ^ 6 + q ^ 2 * |t| ^ 8) := by
        have hq6 : 0 ≤ q * |t| ^ 6 := by positivity
        nlinarith
      _ = _ := by rfl

/-- The Gaussian main term integrated against Rodier's Fourier--Stieltjes
measure `U = δ₀ + v(t)dt`. -/
noncomputable def rodierCutoffGaussianIntegral
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℂ :=
  1 + ∫ t : ℝ, (Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℂ) *
    rodierCutoffFourierDensity M Δ hM hΔ t

/-- The `p`th Gaussian-weighted moment of the density part of Rodier's
Fourier--Stieltjes measure. For positive `p`, the omitted Dirac contribution
vanishes. -/
noncomputable def rodierGaussianWeightedDensityMoment (n p : ℕ)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℂ :=
  ∫ t : ℝ, ((t ^ p * Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℝ) : ℂ) *
    rodierCutoffFourierDensity M Δ hM hΔ t

/-- The quartic Gaussian correction leaves only the sixth- and eighth-order
remainders in the one-coefficient cutoff expectation. -/
theorem norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
    (hn : 0 < n) (S : Finset (Fin n))
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖rodierSingleCutoffExpectation S M Δ -
        (rodierCutoffGaussianIntegral n M Δ hM hΔ -
          ((2 : ℝ) ^ n / 12 : ℝ) *
            rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ)‖ ≤
      (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, |t| ^ 6 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, |t| ^ 8 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t => (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_bound
  have h₄ := (hm₄ M Δ hM hΔ hΔM).1
  have h₆ := (hm₆ M Δ hM hΔ hΔM).1
  have h₈ := (hm₈ M Δ hM hΔ hΔM).1
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hcharCont : Continuous (rodierSingleCharacteristic S) := by
    rw [show rodierSingleCharacteristic S =
        fun t : ℝ => (Real.cos t : ℂ) ^ (2 ^ n) by
      funext t
      exact rodierSingleCharacteristic_eq_cos_pow S t]
    fun_prop
  have hcharNorm (t : ℝ) : ‖rodierSingleCharacteristic S t‖ ≤ 1 := by
    rw [rodierSingleCharacteristic_eq_cos_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  have hcharInt : Integrable (fun t => rodierSingleCharacteristic S t * v t) := by
    apply hv.bdd_mul (c := 1) hcharCont.aestronglyMeasurable
    exact Filter.Eventually.of_forall hcharNorm
  have hgCont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgNorm (t : ℝ) : ‖g t‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ q * t ^ 2 / 2 := by dsimp [q]; positivity
    linarith
  have hgInt : Integrable (fun t => g t * v t) := by
    apply hv.bdd_mul (c := 1) hgCont.aestronglyMeasurable
    exact Filter.Eventually.of_forall hgNorm
  have h4gInt : Integrable (fun t : ℝ =>
      (((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t)) := by
    apply h₄.mono'
    · fun_prop
    · filter_upwards [] with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ t ^ 4),
        abs_of_pos (Real.exp_pos _)]
      have heg : Real.exp (-(q * t ^ 2 / 2)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ q * t ^ 2 / 2 := by dsimp [q]; positivity
        linarith
      rw [show t ^ 4 = |t| ^ 4 by
        calc
          t ^ 4 = |t ^ 4| := (abs_of_nonneg (by positivity)).symm
          _ = |t| ^ 4 := abs_pow t 4]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) heg) (norm_nonneg _)
  have happInt : Integrable (fun t : ℝ =>
      (g t - ((q / 12 : ℝ) : ℂ) *
        ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) * v t) := by
    refine (hgInt.sub (h4gInt.const_mul ((q / 12 : ℝ) : ℂ))).congr ?_
    filter_upwards [] with t
    simp only [Pi.sub_apply, sub_mul, mul_assoc]
  have hpoint (t : ℝ) :
      ‖(rodierSingleCharacteristic S t -
          (g t - ((q / 12 : ℝ) : ℂ) *
            ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ))) * v t‖ ≤
        (3 * q * |t| ^ 6 + 3 * q ^ 2 * |t| ^ 8) * ‖v t‖ := by
    have hrem :=
      norm_rodierSingleCharacteristic_sub_quarticGaussian_global_le hn S t
    have happ :
        g t - ((q / 12 : ℝ) : ℂ) *
            ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) =
          (((Real.exp (-(q * t ^ 2 / 2)) -
            (q * t ^ 4 / 12) * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) := by
      dsimp [g]
      push_cast
      ring
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [happ]
    calc
      _ ≤ 3 * (q * |t| ^ 6 + q ^ 2 * |t| ^ 8) := by
        simpa [q] using hrem
      _ = _ := by ring
  have h₆' : Integrable (fun t : ℝ =>
      (3 * q) * (|t| ^ 6 * ‖v t‖)) := h₆.const_mul _
  have h₈' : Integrable (fun t : ℝ =>
      (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖)) := h₈.const_mul _
  have henv : Integrable (fun t : ℝ =>
      (3 * q * |t| ^ 6 + 3 * q ^ 2 * |t| ^ 8) * ‖v t‖) := by
    refine (h₆'.add h₈').congr ?_
    filter_upwards [] with t
    simp only [Pi.add_apply]
    ring
  have happIntegral :
      (∫ t : ℝ, (g t - ((q / 12 : ℝ) : ℂ) *
          ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) * v t) =
        (∫ t : ℝ, g t * v t) - ((q / 12 : ℝ) : ℂ) *
          ∫ t : ℝ,
            (((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t) := by
    rw [show (fun t : ℝ => (g t - ((q / 12 : ℝ) : ℂ) *
          ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) * v t) =
        fun t => g t * v t - ((q / 12 : ℝ) : ℂ) *
          (((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t) by
      funext t
      rw [sub_mul]
      rw [mul_assoc],
      integral_sub hgInt (h4gInt.const_mul _), integral_const_mul]
  rw [rodierSingleCutoffExpectation_eq_characteristicIntegral S M Δ hM hΔ,
    rodierCutoffGaussianIntegral, rodierGaussianWeightedDensityMoment]
  change ‖(1 + ∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
      ((1 + ∫ t : ℝ, g t * v t) -
        ((q / 12 : ℝ) : ℂ) * ∫ t : ℝ,
          (((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t))‖ ≤ _
  rw [show (1 + ∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
        ((1 + ∫ t : ℝ, g t * v t) -
          ((q / 12 : ℝ) : ℂ) * ∫ t : ℝ,
            (((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t)) =
      (∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
        ∫ t : ℝ, (g t - ((q / 12 : ℝ) : ℂ) *
          ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) * v t by
      rw [happIntegral]
      ring,
    ← integral_sub hcharInt happInt]
  rw [show (fun t : ℝ => rodierSingleCharacteristic S t * v t -
      (g t - ((q / 12 : ℝ) : ℂ) *
        ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ)) * v t) =
      fun t => (rodierSingleCharacteristic S t -
        (g t - ((q / 12 : ℝ) : ℂ) *
          ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ))) * v t by
    funext t
    ring]
  calc
    _ ≤ ∫ t : ℝ, ‖(rodierSingleCharacteristic S t -
        (g t - ((q / 12 : ℝ) : ℂ) *
          ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ))) * v t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ,
        (3 * q * |t| ^ 6 + 3 * q ^ 2 * |t| ^ 8) * ‖v t‖ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) henv
        (Filter.Eventually.of_forall hpoint)
    _ = (3 * q) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
        (3 * q ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) := by
      rw [show (fun t : ℝ =>
          (3 * q * |t| ^ 6 + 3 * q ^ 2 * |t| ^ 8) * ‖v t‖) =
        fun t => (3 * q) * (|t| ^ 6 * ‖v t‖) +
          (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖) by
        funext t
        ring,
        integral_add h₆' h₈', integral_const_mul, integral_const_mul]
    _ = _ := by rfl

/-- Rodier equation (12): the one-coefficient cutoff expectation differs from
its Gaussian `U`-integral by the fourth, sixth, and eighth absolute moments of
the Fourier density. -/
theorem norm_rodierSingleCutoffExpectation_sub_gaussianIntegral_le
    (hn : 0 < n) (S : Finset (Fin n))
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖rodierSingleCutoffExpectation S M Δ -
        rodierCutoffGaussianIntegral n M Δ hM hΔ‖ ≤
      ((2 : ℝ) ^ n / 12) *
          (∫ t : ℝ, |t| ^ 4 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, |t| ^ 6 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, |t| ^ 8 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t =>
    (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_bound
  have h₄ := (hm₄ M Δ hM hΔ hΔM).1
  have h₆ := (hm₆ M Δ hM hΔ hΔM).1
  have h₈ := (hm₈ M Δ hM hΔ hΔM).1
  have hv : Integrable v := rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hcharCont : Continuous (rodierSingleCharacteristic S) := by
    rw [show rodierSingleCharacteristic S =
        fun t : ℝ => (Real.cos t : ℂ) ^ (2 ^ n) by
      funext t
      exact rodierSingleCharacteristic_eq_cos_pow S t]
    fun_prop
  have hcharNorm (t : ℝ) : ‖rodierSingleCharacteristic S t‖ ≤ 1 := by
    rw [rodierSingleCharacteristic_eq_cos_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  have hcharInt : Integrable (fun t => rodierSingleCharacteristic S t * v t) := by
    apply hv.bdd_mul (c := 1) hcharCont.aestronglyMeasurable
    exact Filter.Eventually.of_forall hcharNorm
  have hgCont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgNorm (t : ℝ) : ‖g t‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have hnonneg : 0 ≤ q * t ^ 2 / 2 := by
      dsimp [q]
      positivity
    linarith
  have hgInt : Integrable (fun t => g t * v t) := by
    apply hv.bdd_mul (c := 1) hgCont.aestronglyMeasurable
    exact Filter.Eventually.of_forall hgNorm
  have hpoint (t : ℝ) :
      ‖(rodierSingleCharacteristic S t - g t) * v t‖ ≤
        (q / 12 * |t| ^ 4 + 3 * q * |t| ^ 6 +
          3 * q ^ 2 * |t| ^ 8) * ‖v t‖ := by
    let G : ℝ := Real.exp (-(q * t ^ 2 / 2))
    let Q : ℝ := q * t ^ 4 / 12
    have hG0 : 0 ≤ G := (Real.exp_pos _).le
    have hG1 : G ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hnonneg : 0 ≤ q * t ^ 2 / 2 := by
        dsimp [q]
        positivity
      linarith
    have hQ0 : 0 ≤ Q := by dsimp [Q, q]; positivity
    have hrem :=
      norm_rodierSingleCharacteristic_sub_quarticGaussian_global_le hn S t
    have hquartic : ‖((Q * G : ℝ) : ℂ)‖ ≤ q / 12 * |t| ^ 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hQ0, abs_of_nonneg hG0]
      have hQeq : Q = q / 12 * |t| ^ 4 := by
        dsimp [Q]
        rw [show t ^ 4 = |t| ^ 4 by
          calc
            t ^ 4 = |t ^ 4| := (abs_of_nonneg (by positivity)).symm
            _ = |t| ^ 4 := abs_pow t 4]
        ring
      rw [hQeq]
      exact mul_le_of_le_one_right (by positivity) hG1
    have hdiff :
        ‖rodierSingleCharacteristic S t - g t‖ ≤
          q / 12 * |t| ^ 4 + 3 * q * |t| ^ 6 +
            3 * q ^ 2 * |t| ^ 8 := by
      calc
        _ = ‖(rodierSingleCharacteristic S t -
              ((G - Q * G : ℝ) : ℂ)) - ((Q * G : ℝ) : ℂ)‖ := by
            apply congrArg norm
            dsimp [g, G]
            push_cast
            ring
        _ ≤ ‖rodierSingleCharacteristic S t -
              ((G - Q * G : ℝ) : ℂ)‖ + ‖((Q * G : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ 3 * (q * |t| ^ 6 + q ^ 2 * |t| ^ 8) +
              q / 12 * |t| ^ 4 := by
            have hrem' :
                ‖rodierSingleCharacteristic S t -
                    ((G - Q * G : ℝ) : ℂ)‖ ≤
                  3 * (q * |t| ^ 6 + q ^ 2 * |t| ^ 8) := by
              simpa [q, G, Q] using hrem
            exact add_le_add hrem' hquartic
        _ = _ := by ring
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
  have h₄' : Integrable (fun t : ℝ => q / 12 * (|t| ^ 4 * ‖v t‖)) :=
    h₄.const_mul _
  have h₆' : Integrable (fun t : ℝ => (3 * q) * (|t| ^ 6 * ‖v t‖)) :=
    h₆.const_mul _
  have h₈' : Integrable (fun t : ℝ => (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖)) :=
    h₈.const_mul _
  have henv : Integrable (fun t : ℝ =>
      (q / 12 * |t| ^ 4 + 3 * q * |t| ^ 6 +
        3 * q ^ 2 * |t| ^ 8) * ‖v t‖) := by
    refine ((h₄'.add h₆').add h₈').congr ?_
    filter_upwards [] with t
    simp only [Pi.add_apply]
    ring
  rw [rodierSingleCutoffExpectation_eq_characteristicIntegral,
    rodierCutoffGaussianIntegral]
  change ‖(1 + ∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
      (1 + ∫ t : ℝ, g t * v t)‖ ≤ _
  rw [show (1 + ∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
      (1 + ∫ t : ℝ, g t * v t) =
      (∫ t : ℝ, rodierSingleCharacteristic S t * v t) -
        ∫ t : ℝ, g t * v t by ring,
    ← integral_sub hcharInt hgInt]
  rw [show (fun t : ℝ => rodierSingleCharacteristic S t * v t - g t * v t) =
      fun t => (rodierSingleCharacteristic S t - g t) * v t by
    funext t
    ring]
  calc
    _ ≤ ∫ t : ℝ, ‖(rodierSingleCharacteristic S t - g t) * v t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ,
        (q / 12 * |t| ^ 4 + 3 * q * |t| ^ 6 +
          3 * q ^ 2 * |t| ^ 8) * ‖v t‖ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        henv (Filter.Eventually.of_forall hpoint)
    _ = q / 12 * (∫ t : ℝ, |t| ^ 4 * ‖v t‖) +
        (3 * q) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
        (3 * q ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) := by
      rw [show (fun t : ℝ =>
          (q / 12 * |t| ^ 4 + 3 * q * |t| ^ 6 +
            3 * q ^ 2 * |t| ^ 8) * ‖v t‖) =
        fun t => q / 12 * (|t| ^ 4 * ‖v t‖) +
            (3 * q) * (|t| ^ 6 * ‖v t‖) +
            (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖) by
        funext t
        ring]
      calc
        _ = (∫ t : ℝ, q / 12 * (|t| ^ 4 * ‖v t‖) +
              (3 * q) * (|t| ^ 6 * ‖v t‖)) +
            ∫ t : ℝ, (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖) :=
          integral_add (h₄'.add h₆') h₈'
        _ = ((∫ t : ℝ, q / 12 * (|t| ^ 4 * ‖v t‖)) +
              ∫ t : ℝ, (3 * q) * (|t| ^ 6 * ‖v t‖)) +
            ∫ t : ℝ, (3 * q ^ 2) * (|t| ^ 8 * ‖v t‖) := by
          rw [integral_add h₄' h₆']
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by rfl

private theorem rodier_even_pow_four (x : ℝ) : x ^ 4 = |x| ^ 4 := by
  calc
    x ^ 4 = |x ^ 4| := (abs_of_nonneg (by positivity)).symm
    _ = |x| ^ 4 := abs_pow x 4

private theorem rodier_even_pow_two (x : ℝ) : x ^ 2 = |x| ^ 2 := by
  rw [sq_abs]

private theorem rodierPairQuartic_le_abs_add_pow_four
    (t r : ℝ) :
    t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4 ≤ (|t| + |r|) ^ 4 := by
  rw [rodier_even_pow_four t, rodier_even_pow_four r,
    rodier_even_pow_two t, rodier_even_pow_two r]
  have ht := abs_nonneg t
  have hr := abs_nonneg r
  nlinarith [mul_nonneg (mul_nonneg ht hr)
    (add_nonneg (sq_nonneg |t|) (sq_nonneg |r|))]

/-- Global off-diagonal form of Rodier Lemma 6.4. The sixth- and eighth-order
moments absorb the complement of the local Fourier square. -/
theorem norm_rodierPairCharacteristic_sub_quarticGaussian_global_le
    {S T : Finset (Fin n)} (hST : S ≠ T) (t r : ℝ) :
    ‖rodierPairCharacteristic S T t r -
        ((Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) -
          ((2 : ℝ) ^ n *
              (t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4) / 12) *
            Real.exp (-((2 : ℝ) ^ n * (t ^ 2 + r ^ 2) / 2)) : ℝ) : ℂ)‖ ≤
      3 * ((2 : ℝ) ^ n * (|t| + |r|) ^ 6 +
        ((2 : ℝ) ^ n) ^ 2 * (|t| + |r|) ^ 8) := by
  let q : ℝ := (2 : ℝ) ^ n
  let a : ℝ := |t| + |r|
  let P : ℝ := t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4
  have hq : 1 ≤ q := by
    dsimp [q]
    exact one_le_pow₀ (by norm_num)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hP : P ≤ a ^ 4 := by
    simpa [P, a] using rodierPairQuartic_le_abs_add_pow_four t r
  by_cases ha : a ≤ 1
  · have h := norm_rodierPairCharacteristic_sub_quarticGaussian_le
      hST t r (by simpa [a] using ha)
    have ha12le8 : a ^ 12 ≤ a ^ 8 := by
      calc
        a ^ 12 = a ^ 8 * a ^ 4 := by ring
        _ ≤ a ^ 8 * 1 := by
          gcongr
          exact pow_le_one₀ ha0 ha
        _ = a ^ 8 := by ring
    have hpow : (q * a ^ 6) ^ 2 / 2 ≤ q ^ 2 * a ^ 8 / 2 := by
      calc
        _ = q ^ 2 * a ^ 12 / 2 := by ring
        _ ≤ q ^ 2 * a ^ 8 / 2 := by gcongr
    have hQ : q * P / 12 ≤ q * a ^ 4 / 12 := by
      gcongr
    have hQ0 : 0 ≤ q * P / 12 := by positivity
    have hQa0 : 0 ≤ q * a ^ 4 / 12 := by positivity
    have hquartic : (q * P / 12) ^ 2 / 2 ≤ q ^ 2 * a ^ 8 / 288 := by
      have hsq := (sq_le_sq₀ hQ0 hQa0).mpr hQ
      calc
        _ ≤ (q * a ^ 4 / 12) ^ 2 / 2 := by
          exact div_le_div_of_nonneg_right hsq (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ q * a ^ 6 + (q * a ^ 6) ^ 2 / 2 +
          (q * P / 12) ^ 2 / 2 := by
        simpa [q, a, P] using h
      _ ≤ q * a ^ 6 + q ^ 2 * a ^ 8 / 2 + q ^ 2 * a ^ 8 / 288 := by
        gcongr
      _ ≤ 3 * (q * a ^ 6 + q ^ 2 * a ^ 8) := by
        have hq6 : 0 ≤ q * a ^ 6 := by positivity
        have hq8 : 0 ≤ q ^ 2 * a ^ 8 := by positivity
        nlinarith
      _ = _ := by rfl
  · have ha1 : 1 ≤ a := (lt_of_not_ge ha).le
    let A : ℝ := q * (t ^ 2 + r ^ 2) / 2
    let Q : ℝ := q * P / 12
    let G : ℝ := Real.exp (-A)
    have hA : 0 ≤ A := by dsimp [A, q]; positivity
    have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
    have hG0 : 0 ≤ G := (Real.exp_pos _).le
    have hG1 : G ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA)
    have hchar : ‖rodierPairCharacteristic S T t r‖ ≤ 1 := by
      rw [rodierPairCharacteristic_eq_prod_cos, norm_prod]
      apply Finset.prod_le_one
      · intro x _
        exact norm_nonneg _
      · intro x _
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
    have happ : ‖((G - Q * G : ℝ) : ℂ)‖ ≤ 1 + Q := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |G - Q * G| ≤ |G| + |Q * G| := abs_sub _ _
        _ = G + Q * G := by rw [abs_of_nonneg hG0, abs_mul,
          abs_of_nonneg hQ0, abs_of_nonneg hG0]
        _ ≤ 1 + Q := by nlinarith [mul_le_mul_of_nonneg_left hG1 hQ0]
    have hqpow : 1 ≤ q ^ 2 * a ^ 8 := by
      have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
      have ha8 : 1 ≤ a ^ 8 := one_le_pow₀ ha1
      nlinarith [mul_le_mul hq2 ha8 zero_le_one
        (by positivity : 0 ≤ q ^ 2)]
    have hQbound : Q ≤ q * a ^ 6 := by
      have ha46 : a ^ 4 ≤ a ^ 6 := by
        have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha1
        calc
          a ^ 4 = a ^ 4 * 1 := by ring
          _ ≤ a ^ 4 * a ^ 2 := mul_le_mul_of_nonneg_left ha2 (by positivity)
          _ = a ^ 6 := by ring
      dsimp [Q]
      calc
        q * P / 12 ≤ q * a ^ 4 / 12 := by
          gcongr
        _ ≤ q * a ^ 4 := by
          have : 0 ≤ q * a ^ 4 := by positivity
          nlinarith
        _ ≤ q * a ^ 6 :=
          mul_le_mul_of_nonneg_left ha46 (le_trans zero_le_one hq)
    calc
      _ ≤ ‖rodierPairCharacteristic S T t r‖ +
          ‖((G - Q * G : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + Q) := add_le_add hchar happ
      _ ≤ 3 * (q * a ^ 6 + q ^ 2 * a ^ 8) := by
        have hq6 : 0 ≤ q * a ^ 6 := by positivity
        nlinarith
      _ = _ := by rfl

/-- The pair characteristic function written directly in terms of the two raw
Walsh coefficients. -/
theorem rodierPairCharacteristic_eq_rawWalsh
    (S T : Finset (Fin n)) (t r : ℝ) :
    rodierPairCharacteristic S T t r =
      Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
        Complex.exp
          (((t * rodierRawWalshCoefficient S f +
            r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) := by
  unfold rodierPairCharacteristic rodierRawWalshCoefficient rodierPairPhase
  congr 1
  funext f
  apply congrArg Complex.exp
  have hsum :
      t * ∑ x : {−1,1}^[n], FABL.signValue (f x) * FABL.monomial S x +
          r * ∑ x : {−1,1}^[n], FABL.signValue (f x) * FABL.monomial T x =
        ∑ x : {−1,1}^[n], FABL.signValue (f x) *
          (t * FABL.monomial S x + r * FABL.monomial T x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [← hsum]
  push_cast
  ring

/-- The joint cutoff expectation at two raw Walsh coefficients. -/
noncomputable def rodierPairCutoffExpectation
    (S T : Finset (Fin n)) (M Δ : ℝ) : ℂ :=
  Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
    (rodierCutoff M Δ (rodierRawWalshCoefficient S f) : ℂ) *
      (rodierCutoff M Δ (rodierRawWalshCoefficient T f) : ℂ))

/-- The full `(δ₀ + v dt) ⊗ (δ₀ + v dt)` Fourier representation of
the joint cutoff expectation. -/
noncomputable def rodierPairFourierIntegral
    (S T : Finset (Fin n)) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℂ :=
  1 +
    (∫ t : ℝ, rodierSingleCharacteristic S t *
      rodierCutoffFourierDensity M Δ hM hΔ t) +
    (∫ r : ℝ, rodierSingleCharacteristic T r *
      rodierCutoffFourierDensity M Δ hM hΔ r) +
    (∫ t : ℝ, ∫ r : ℝ, rodierPairCharacteristic S T t r *
      rodierCutoffFourierDensity M Δ hM hΔ t *
      rodierCutoffFourierDensity M Δ hM hΔ r)

/-- Two applications of Fourier inversion identify the joint cutoff
expectation with the full pair Fourier integral. -/
theorem rodierPairCutoffExpectation_eq_fourierIntegral
    (S T : Finset (Fin n)) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    rodierPairCutoffExpectation S T M Δ =
      rodierPairFourierIntegral S T M Δ hM hΔ := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let e : FABL.BooleanFunction n → Finset (Fin n) → ℝ → ℂ :=
    fun f A t ↦ Complex.exp
      (((t * rodierRawWalshCoefficient A f : ℝ) : ℂ) * Complex.I)
  have hv : Integrable v := rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have heNorm (f : FABL.BooleanFunction n) (A : Finset (Fin n)) (t : ℝ) :
      ‖e f A t‖ = 1 := by
    simp [e, Complex.norm_exp]
  have hei (f : FABL.BooleanFunction n) (A : Finset (Fin n)) :
      Integrable (fun t ↦ e f A t * v t) := by
    apply hv.bdd_mul (c := 1)
    · dsimp [e]
      fun_prop
    · filter_upwards [] with t
      rw [heNorm]
  have hpairPoint (f : FABL.BooleanFunction n) (t r : ℝ) :
      Complex.exp
          ((((t * rodierRawWalshCoefficient S f +
            r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
          v t * v r =
        (e f S t * v t) * (e f T r * v r) := by
    have hexp :
        Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) =
          e f S t * e f T r := by
      dsimp [e]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  have hri (f : FABL.BooleanFunction n) (t : ℝ) :
      Integrable (fun r : ℝ ↦
        Complex.exp
          ((((t * rodierRawWalshCoefficient S f +
            r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
          v t * v r) := by
    rw [show (fun r : ℝ ↦
        Complex.exp
          ((((t * rodierRawWalshCoefficient S f +
            r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
          v t * v r) =
        fun r ↦ (e f S t * v t) * (e f T r * v r) by
      funext r
      exact hpairPoint f t r]
    exact (hei f T).const_mul _
  have hinner (f : FABL.BooleanFunction n) (t : ℝ) :
      (∫ r : ℝ,
        Complex.exp
          ((((t * rodierRawWalshCoefficient S f +
            r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
          v t * v r) =
        e f S t * v t * (∫ r : ℝ, e f T r * v r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    exact hpairPoint f t r
  have hdoubleIntegrable (f : FABL.BooleanFunction n) :
      Integrable (fun t : ℝ ↦
        ∫ r : ℝ,
          Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
            v t * v r) := by
    rw [show (fun t : ℝ ↦
        ∫ r : ℝ,
          Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
            v t * v r) =
        fun t ↦ e f S t * v t * (∫ r : ℝ, e f T r * v r) by
      funext t
      exact hinner f t]
    exact (hei f S).mul_const _
  have hproduct (f : FABL.BooleanFunction n) :
      (∫ t : ℝ, e f S t * v t) * (∫ r : ℝ, e f T r * v r) =
        ∫ t : ℝ, ∫ r : ℝ,
          Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
            v t * v r := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with t
    exact (hinner f t).symm
  let N : ℂ := Fintype.card (FABL.BooleanFunction n)
  have hmarg (A : Finset (Fin n)) :
      (∫ t : ℝ, (∑ f : FABL.BooleanFunction n, e f A t) / N * v t) =
        (∫ t : ℝ, ∑ f : FABL.BooleanFunction n, e f A t * v t) / N := by
    calc
      _ = ∫ t : ℝ,
          (∑ f : FABL.BooleanFunction n, e f A t * v t) / N := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [← Finset.sum_mul]
        ring
      _ = _ := integral_div N _
  have hcross :
      (∫ t : ℝ, ∫ r : ℝ,
        ((∑ f : FABL.BooleanFunction n,
          Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I))) / N) *
          v t * v r) =
        (∫ t : ℝ, ∑ f : FABL.BooleanFunction n, ∫ r : ℝ,
          Complex.exp
            ((((t * rodierRawWalshCoefficient S f +
              r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
            v t * v r) / N := by
    calc
      _ = ∫ t : ℝ,
          (∑ f : FABL.BooleanFunction n, ∫ r : ℝ,
            Complex.exp
              ((((t * rodierRawWalshCoefficient S f +
                r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
              v t * v r) / N := by
        apply integral_congr_ae
        filter_upwards [] with t
        calc
          _ = ∫ r : ℝ,
              (∑ f : FABL.BooleanFunction n,
                Complex.exp
                  ((((t * rodierRawWalshCoefficient S f +
                    r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
                  v t * v r) / N := by
            apply integral_congr_ae
            filter_upwards [] with r
            rw [← Finset.sum_mul]
            rw [← Finset.sum_mul]
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = (∫ r : ℝ,
              ∑ f : FABL.BooleanFunction n,
                Complex.exp
                  ((((t * rodierRawWalshCoefficient S f +
                    r * rodierRawWalshCoefficient T f : ℝ) : ℂ) * Complex.I)) *
                  v t * v r) / N := integral_div N _
          _ = _ := by
            rw [MeasureTheory.integral_finsetSum Finset.univ
              (fun f _ ↦ hri f t)]
      _ = _ := integral_div N _
  rw [rodierPairCutoffExpectation, Fintype.expect_eq_sum_div_card]
  simp_rw [rodierCutoff_fourierDensity_inversion M Δ hM hΔ]
  change (∑ f : FABL.BooleanFunction n,
      (1 + ∫ t : ℝ, e f S t * v t) *
        (1 + ∫ r : ℝ, e f T r * v r)) /
      (Fintype.card (FABL.BooleanFunction n) : ℂ) = _
  simp_rw [mul_add, add_mul, hproduct]
  simp only [one_mul, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun f _ ↦ hei f S),
    ← MeasureTheory.integral_finsetSum Finset.univ
      (fun f _ ↦ hei f T),
    ← MeasureTheory.integral_finsetSum Finset.univ
      (fun f _ ↦ hdoubleIntegrable f)]
  rw [rodierPairFourierIntegral]
  simp_rw [rodierSingleCharacteristic, Fintype.expect_eq_sum_div_card,
    rodierPairCharacteristic_eq_rawWalsh, Fintype.expect_eq_sum_div_card]
  rw [hmarg S, hmarg T, hcross]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  field_simp
  ring_nf
  simp only [mul_comm Complex.I]

private theorem rodierDoubleDensityAbsAddMoment_integrable_and_le
    (k : ℕ) (v : ℝ → ℂ) (hv : Continuous v)
    (h0 : Integrable (fun t : ℝ => ‖v t‖))
    (hk : Integrable (fun t : ℝ => |t| ^ k * ‖v t‖)) :
    Integrable (fun z : ℝ × ℝ =>
        (|z.1| + |z.2|) ^ k * ‖v z.1‖ * ‖v z.2‖)
        (volume.prod volume) ∧
      Integrable (fun t : ℝ => ∫ r : ℝ,
        (|t| + |r|) ^ k * ‖v t‖ * ‖v r‖) ∧
      (∫ t : ℝ, ∫ r : ℝ,
          (|t| + |r|) ^ k * ‖v t‖ * ‖v r‖) ≤
        (2 : ℝ) ^ (k - 1) *
          (2 * (∫ t : ℝ, |t| ^ k * ‖v t‖) *
            ∫ t : ℝ, ‖v t‖) := by
  let C : ℝ := (2 : ℝ) ^ (k - 1)
  let F : ℝ × ℝ → ℝ := fun z =>
    (|z.1| + |z.2|) ^ k * ‖v z.1‖ * ‖v z.2‖
  let E : ℝ × ℝ → ℝ := fun z => C *
    ((|z.1| ^ k * ‖v z.1‖) * ‖v z.2‖ +
      ‖v z.1‖ * (|z.2| ^ k * ‖v z.2‖))
  have hprod₁ : Integrable (fun z : ℝ × ℝ =>
      (|z.1| ^ k * ‖v z.1‖) * ‖v z.2‖) (volume.prod volume) :=
    hk.mul_prod h0
  have hprod₂ : Integrable (fun z : ℝ × ℝ =>
      ‖v z.1‖ * (|z.2| ^ k * ‖v z.2‖)) (volume.prod volume) :=
    h0.mul_prod hk
  have hE : Integrable E (volume.prod volume) := by
    exact (hprod₁.add hprod₂).const_mul C
  have hpoint (z : ℝ × ℝ) : F z ≤ E z := by
    have hadd := add_pow_le (abs_nonneg z.1) (abs_nonneg z.2) k
    dsimp [F, E, C]
    calc
      _ ≤ (2 : ℝ) ^ (k - 1) * (|z.1| ^ k + |z.2| ^ k) *
          ‖v z.1‖ * ‖v z.2‖ := by gcongr
      _ = _ := by ring
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF : Integrable F (volume.prod volume) := by
    apply Integrable.mono' hE hFcont.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    exact hpoint z
  have hprodInt₁ :
      (∫ z : ℝ × ℝ,
          (|z.1| ^ k * ‖v z.1‖) * ‖v z.2‖ ∂volume.prod volume) =
        (∫ t : ℝ, |t| ^ k * ‖v t‖) * (∫ t : ℝ, ‖v t‖) := by
    simpa using (integral_prod_mul (μ := volume) (ν := volume)
      (fun t : ℝ => |t| ^ k * ‖v t‖) (fun t : ℝ => ‖v t‖))
  have hprodInt₂ :
      (∫ z : ℝ × ℝ,
          ‖v z.1‖ * (|z.2| ^ k * ‖v z.2‖) ∂volume.prod volume) =
        (∫ t : ℝ, ‖v t‖) * (∫ t : ℝ, |t| ^ k * ‖v t‖) := by
    simpa using (integral_prod_mul (μ := volume) (ν := volume)
      (fun t : ℝ => ‖v t‖) (fun t : ℝ => |t| ^ k * ‖v t‖))
  refine ⟨hF, hF.integral_prod_left, ?_⟩
  calc
    (∫ t : ℝ, ∫ r : ℝ,
        (|t| + |r|) ^ k * ‖v t‖ * ‖v r‖) =
        ∫ z : ℝ × ℝ, F z ∂volume.prod volume := by
      rw [integral_prod F hF]
    _ ≤ ∫ z : ℝ × ℝ, E z ∂volume.prod volume :=
      integral_mono hF hE hpoint
    _ = C *
        ((∫ t : ℝ, |t| ^ k * ‖v t‖) * (∫ t : ℝ, ‖v t‖) +
          (∫ t : ℝ, ‖v t‖) * (∫ t : ℝ, |t| ^ k * ‖v t‖)) := by
      rw [show E = fun z : ℝ × ℝ => C *
          (((|z.1| ^ k * ‖v z.1‖) * ‖v z.2‖) +
            (‖v z.1‖ * (|z.2| ^ k * ‖v z.2‖))) by rfl,
        integral_const_mul, integral_add hprod₁ hprod₂,
        hprodInt₁, hprodInt₂]
    _ = (2 : ℝ) ^ (k - 1) *
        (2 * (∫ t : ℝ, |t| ^ k * ‖v t‖) *
          ∫ t : ℝ, ‖v t‖) := by
      dsimp [C]
      ring

/-- The off-diagonal pair Fourier integral differs from the square of its
Gaussian main term by the fourth, sixth, and eighth double density moments. -/
theorem norm_rodierPairCharacteristicIntegral_sub_gaussianSquare_le
    {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖(∫ t : ℝ, ∫ r : ℝ,
          rodierPairCharacteristic S T t r *
            rodierCutoffFourierDensity M Δ hM hΔ t *
            rodierCutoffFourierDensity M Δ hM hΔ r) -
        (∫ t : ℝ,
          (Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℂ) *
            rodierCutoffFourierDensity M Δ hM hΔ t) ^ 2‖ ≤
      ((2 : ℝ) ^ n / 12) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 4 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) +
        (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t => (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hvcont : Continuous v := by
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_bound
  have h₄ := (hm₄ M Δ hM hΔ hΔM).1
  have h₆ := (hm₆ M Δ hM hΔ hΔM).1
  have h₈ := (hm₈ M Δ hM hΔ hΔM).1
  have h0 : Integrable (fun t : ℝ => ‖v t‖) := hv.norm
  have hD₄ := rodierDoubleDensityAbsAddMoment_integrable_and_le 4 v hvcont h0 h₄
  have hD₆ := rodierDoubleDensityAbsAddMoment_integrable_and_le 6 v hvcont h0 h₆
  have hD₈ := rodierDoubleDensityAbsAddMoment_integrable_and_le 8 v hvcont h0 h₈
  have hpairCont : Continuous (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2) := by
    rw [show (fun z : ℝ × ℝ => rodierPairCharacteristic S T z.1 z.2) =
        fun z => ∏ x : {−1,1}^[n],
          (Real.cos (rodierPairPhase S T z.1 z.2 x) : ℂ) by
      funext z
      exact rodierPairCharacteristic_eq_prod_cos S T z.1 z.2]
    unfold rodierPairPhase
    fun_prop
  have hpairNorm (t r : ℝ) : ‖rodierPairCharacteristic S T t r‖ ≤ 1 := by
    rw [rodierPairCharacteristic_eq_prod_cos, norm_prod]
    apply Finset.prod_le_one
    · intro x _
      exact norm_nonneg _
    · intro x _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hgCont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgNorm (t : ℝ) : ‖g t‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ q * t ^ 2 / 2 := by dsimp [q]; positivity
    linarith
  have hvprod : Integrable (fun z : ℝ × ℝ => v z.1 * v z.2)
      (volume.prod volume) := hv.mul_prod hv
  have hpairProd : Integrable (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2)
      (volume.prod volume) := by
    have h := hvprod.bdd_mul (c := 1) hpairCont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hpairNorm z.1 z.2)
    simpa only [mul_assoc] using h
  have hgaussProd : Integrable (fun z : ℝ × ℝ =>
      g z.1 * g z.2 * v z.1 * v z.2) (volume.prod volume) := by
    have hbound : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,
        ‖g z.1 * g z.2‖ ≤ 1 := by
      filter_upwards [] with z
      rw [norm_mul]
      exact mul_le_one₀ (hgNorm z.1) (norm_nonneg _) (hgNorm z.2)
    have h := hvprod.bdd_mul (c := 1)
      ((hgCont.comp continuous_fst).mul
        (hgCont.comp continuous_snd)).aestronglyMeasurable hbound
    refine h.congr ?_
    filter_upwards [] with z
    dsimp
    ring
  have hgaussMul (t r : ℝ) :
      ((Real.exp (-(q * (t ^ 2 + r ^ 2) / 2)) : ℝ) : ℂ) =
        g t * g r := by
    dsimp [g]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  have hpointDiff (t r : ℝ) :
      ‖rodierPairCharacteristic S T t r - g t * g r‖ ≤
        q / 12 * (|t| + |r|) ^ 4 +
          3 * q * (|t| + |r|) ^ 6 +
          3 * q ^ 2 * (|t| + |r|) ^ 8 := by
    let P : ℝ := t ^ 4 + 6 * t ^ 2 * r ^ 2 + r ^ 4
    let G : ℝ := Real.exp (-(q * (t ^ 2 + r ^ 2) / 2))
    let Q : ℝ := q * P / 12
    have hG0 : 0 ≤ G := (Real.exp_pos _).le
    have hG1 : G ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ q * (t ^ 2 + r ^ 2) / 2 := by dsimp [q]; positivity
      linarith
    have hQ0 : 0 ≤ Q := by
      dsimp [Q, P, q]
      positivity
    have hP : P ≤ (|t| + |r|) ^ 4 := by
      exact rodierPairQuartic_le_abs_add_pow_four t r
    have hquartic : ‖((Q * G : ℝ) : ℂ)‖ ≤
        q / 12 * (|t| + |r|) ^ 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hQ0, abs_of_nonneg hG0]
      have hq0 : 0 ≤ q := by dsimp [q]; positivity
      calc
        Q * G ≤ Q := mul_le_of_le_one_right hQ0 hG1
        _ ≤ q / 12 * (|t| + |r|) ^ 4 := by
          dsimp [Q]
          nlinarith [mul_le_mul_of_nonneg_left hP hq0]
    have hrem :=
      norm_rodierPairCharacteristic_sub_quarticGaussian_global_le
        hST t r
    calc
      _ = ‖(rodierPairCharacteristic S T t r -
            (((G - Q * G : ℝ) : ℂ))) - (((Q * G : ℝ) : ℂ))‖ := by
          apply congrArg norm
          rw [← hgaussMul]
          dsimp [G]
          push_cast
          ring
      _ ≤ ‖rodierPairCharacteristic S T t r -
            (((G - Q * G : ℝ) : ℂ))‖ + ‖(((Q * G : ℝ) : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ 3 * (q * (|t| + |r|) ^ 6 +
            q ^ 2 * (|t| + |r|) ^ 8) +
          q / 12 * (|t| + |r|) ^ 4 := by
        have hrem' :
            ‖rodierPairCharacteristic S T t r -
                (((G - Q * G : ℝ) : ℂ))‖ ≤
              3 * (q * (|t| + |r|) ^ 6 +
                q ^ 2 * (|t| + |r|) ^ 8) := by
          simpa [q, G, Q, P] using hrem
        exact add_le_add hrem' hquartic
      _ = _ := by ring
  let E : ℝ × ℝ → ℝ := fun z =>
    (q / 12 * (|z.1| + |z.2|) ^ 4 +
      3 * q * (|z.1| + |z.2|) ^ 6 +
      3 * q ^ 2 * (|z.1| + |z.2|) ^ 8) * ‖v z.1‖ * ‖v z.2‖
  have hE : Integrable E (volume.prod volume) := by
    have h₄' := hD₄.1.const_mul (q / 12)
    have h₆' := hD₆.1.const_mul (3 * q)
    have h₈' := hD₈.1.const_mul (3 * q ^ 2)
    refine ((h₄'.add h₆').add h₈').congr ?_
    filter_upwards [] with z
    dsimp [E]
    ring
  have hpoint (z : ℝ × ℝ) :
      ‖rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 -
          g z.1 * g z.2 * v z.1 * v z.2‖ ≤ E z := by
    rw [show rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 -
        g z.1 * g z.2 * v z.1 * v z.2 =
      (rodierPairCharacteristic S T z.1 z.2 - g z.1 * g z.2) *
        v z.1 * v z.2 by ring,
      norm_mul, norm_mul]
    dsimp [E]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpointDiff z.1 z.2) (norm_nonneg _))
      (norm_nonneg _)
  have hgaussSquare :
      (∫ t : ℝ, ∫ r : ℝ, g t * g r * v t * v r) =
        (∫ t : ℝ, g t * v t) ^ 2 := by
    calc
      _ = ∫ z : ℝ × ℝ,
          (g z.1 * v z.1) * (g z.2 * v z.2) ∂volume.prod volume := by
        rw [← integral_prod (fun z : ℝ × ℝ =>
          g z.1 * g z.2 * v z.1 * v z.2) hgaussProd]
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = (∫ t : ℝ, g t * v t) * (∫ t : ℝ, g t * v t) := by
        simpa using (integral_prod_mul (μ := volume) (ν := volume)
          (fun t : ℝ => g t * v t) (fun t : ℝ => g t * v t))
      _ = _ := by ring
  change ‖(∫ t : ℝ, ∫ r : ℝ,
      rodierPairCharacteristic S T t r * v t * v r) -
      (∫ t : ℝ, g t * v t) ^ 2‖ ≤ _
  rw [← hgaussSquare,
    ← integral_prod (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2) hpairProd,
    ← integral_prod (fun z : ℝ × ℝ =>
      g z.1 * g z.2 * v z.1 * v z.2) hgaussProd,
    ← integral_sub hpairProd hgaussProd]
  calc
    _ ≤ ∫ z : ℝ × ℝ,
        ‖rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 -
          g z.1 * g z.2 * v z.1 * v z.2‖ ∂volume.prod volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, E z ∂volume.prod volume :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hE
        (Filter.Eventually.of_forall hpoint)
    _ = q / 12 *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 4 * ‖v t‖ * ‖v r‖) +
        (3 * q) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 * ‖v t‖ * ‖v r‖) +
        (3 * q ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 * ‖v t‖ * ‖v r‖) := by
      let F₄ : ℝ × ℝ → ℝ := fun z =>
        (|z.1| + |z.2|) ^ 4 * ‖v z.1‖ * ‖v z.2‖
      let F₆ : ℝ × ℝ → ℝ := fun z =>
        (|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖
      let F₈ : ℝ × ℝ → ℝ := fun z =>
        (|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖
      have hF₄ : Integrable F₄ (volume.prod volume) := hD₄.1
      have hF₆ : Integrable F₆ (volume.prod volume) := hD₆.1
      have hF₈ : Integrable F₈ (volume.prod volume) := hD₈.1
      calc
        _ = ∫ z : ℝ × ℝ,
            q / 12 * F₄ z + (3 * q) * F₆ z + (3 * q ^ 2) * F₈ z
              ∂volume.prod volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp [E, F₄, F₆, F₈]
          ring
        _ = (∫ z : ℝ × ℝ, q / 12 * F₄ z ∂volume.prod volume) +
              (∫ z : ℝ × ℝ, (3 * q) * F₆ z ∂volume.prod volume) +
              ∫ z : ℝ × ℝ, (3 * q ^ 2) * F₈ z ∂volume.prod volume := by
          calc
            _ = (∫ z : ℝ × ℝ,
                  q / 12 * F₄ z + (3 * q) * F₆ z ∂volume.prod volume) +
                ∫ z : ℝ × ℝ, (3 * q ^ 2) * F₈ z ∂volume.prod volume :=
              integral_add ((hF₄.const_mul _).add (hF₆.const_mul _))
                (hF₈.const_mul _)
            _ = _ := by
              rw [integral_add (hF₄.const_mul _) (hF₆.const_mul _)]
        _ = q / 12 * (∫ z : ℝ × ℝ, F₄ z ∂volume.prod volume) +
              (3 * q) * (∫ z : ℝ × ℝ, F₆ z ∂volume.prod volume) +
              (3 * q ^ 2) * (∫ z : ℝ × ℝ, F₈ z ∂volume.prod volume) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
        _ = _ := by
          rw [integral_prod F₄ hF₄, integral_prod F₆ hF₆,
            integral_prod F₈ hF₈]
    _ = _ := by rfl

/-- The off-diagonal pair Fourier integral with its quartic Gaussian correction retained.
Only the sixth- and eighth-order double density moments enter the remainder. -/
theorem norm_rodierPairCharacteristicIntegral_sub_quarticGaussian_le
    {n : ℕ} {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    ‖(∫ t : ℝ, ∫ r : ℝ,
          rodierPairCharacteristic S T t r *
            rodierCutoffFourierDensity M Δ hM hΔ t *
            rodierCutoffFourierDensity M Δ hM hΔ r) -
        ((∫ t : ℝ,
          (Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℂ) *
            rodierCutoffFourierDensity M Δ hM hΔ t) ^ 2 -
          (((2 : ℝ) ^ n / 12 : ℝ) : ℂ) *
            (2 * rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ *
                (∫ t : ℝ,
                  (Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℂ) *
                    rodierCutoffFourierDensity M Δ hM hΔ t) +
              6 * (rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ) ^ 2))‖ ≤
      (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t => (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  let F₀ : ℝ → ℂ := fun t => g t * v t
  let F₂ : ℝ → ℂ := fun t =>
    ((t ^ 2 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t
  let F₄ : ℝ → ℂ := fun t =>
    ((t ^ 4 * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t
  let A₂ : ℂ := ∫ t : ℝ, F₂ t
  let A₄ : ℂ := ∫ t : ℝ, F₄ t
  let J : ℂ := ∫ t : ℝ, F₀ t
  let H : ℝ × ℝ → ℂ := fun z =>
    (((Real.exp (-(q * (z.1 ^ 2 + z.2 ^ 2) / 2)) -
      (q * (z.1 ^ 4 + 6 * z.1 ^ 2 * z.2 ^ 2 + z.2 ^ 4) / 12) *
        Real.exp (-(q * (z.1 ^ 2 + z.2 ^ 2) / 2)) : ℝ) : ℂ)) *
      v z.1 * v z.2
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  obtain ⟨C₂, hC₂, hm₂⟩ :=
    exists_rodierCutoffFourierDensity_secondMoment_sharp_bound
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_sharp_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound
  have h₂ := (hm₂ M Δ hM hΔ).1
  have h₄ := (hm₄ M Δ hM hΔ).1
  have h₆ := (hm₆ M Δ hM hΔ).1
  have h₈ := (hm₈ M Δ hM hΔ).1
  have hgNorm (t : ℝ) : ‖g t‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ q * t ^ 2 / 2 := by dsimp [q]; positivity
    linarith
  have hF₀ : Integrable F₀ := by
    apply hv.bdd_mul (c := 1)
    · dsimp [g]
      fun_prop
    · exact Filter.Eventually.of_forall hgNorm
  have hweighted (p : ℕ)
      (hp : Integrable (fun t : ℝ => |t| ^ p * ‖v t‖)) :
      Integrable (fun t : ℝ =>
        ((t ^ p * Real.exp (-(q * t ^ 2 / 2)) : ℝ) : ℂ) * v t) := by
    apply hp.mono'
    · fun_prop
    · filter_upwards [] with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_pow, abs_of_pos (Real.exp_pos _)]
      have heg : Real.exp (-(q * t ^ 2 / 2)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ q * t ^ 2 / 2 := by dsimp [q]; positivity
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (by positivity) heg) (norm_nonneg _)
  have hF₂ : Integrable F₂ := hweighted 2 h₂
  have hF₄ : Integrable F₄ := hweighted 4 h₄
  have hprod₀₀ : Integrable (fun z : ℝ × ℝ => F₀ z.1 * F₀ z.2)
      (volume.prod volume) := hF₀.mul_prod hF₀
  have hprod₄₀ : Integrable (fun z : ℝ × ℝ => F₄ z.1 * F₀ z.2)
      (volume.prod volume) := hF₄.mul_prod hF₀
  have hprod₂₂ : Integrable (fun z : ℝ × ℝ => F₂ z.1 * F₂ z.2)
      (volume.prod volume) := hF₂.mul_prod hF₂
  have hprod₀₄ : Integrable (fun z : ℝ × ℝ => F₀ z.1 * F₄ z.2)
      (volume.prod volume) := hF₀.mul_prod hF₄
  let E : ℝ × ℝ → ℂ := fun z =>
    F₀ z.1 * F₀ z.2 - ((q / 12 : ℝ) : ℂ) *
      (F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) + F₀ z.1 * F₄ z.2)
  have hE : Integrable E (volume.prod volume) := by
    exact hprod₀₀.sub (((hprod₄₀.add (hprod₂₂.const_mul 6)).add hprod₀₄).const_mul _)
  have hHEq (z : ℝ × ℝ) : H z = E z := by
    dsimp [H, E, F₀, F₂, F₄, g]
    push_cast
    rw [show Complex.exp (-(q * (z.1 ^ 2 + z.2 ^ 2) / 2)) =
        Complex.exp (-(q * z.1 ^ 2 / 2)) *
          Complex.exp (-(q * z.2 ^ 2 / 2)) by
      rw [← Complex.exp_add]
      congr 1
      ring]
    ring
  have hH : Integrable H (volume.prod volume) :=
    hE.congr (Filter.Eventually.of_forall fun z => (hHEq z).symm)
  have hpairCont : Continuous (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2) := by
    rw [show (fun z : ℝ × ℝ => rodierPairCharacteristic S T z.1 z.2) =
        fun z => ∏ x : {−1,1}^[n],
          (Real.cos (rodierPairPhase S T z.1 z.2 x) : ℂ) by
      funext z
      exact rodierPairCharacteristic_eq_prod_cos S T z.1 z.2]
    unfold rodierPairPhase
    fun_prop
  have hpairNorm (t r : ℝ) : ‖rodierPairCharacteristic S T t r‖ ≤ 1 := by
    rw [rodierPairCharacteristic_eq_prod_cos, norm_prod]
    apply Finset.prod_le_one
    · intro x _
      exact norm_nonneg _
    · intro x _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hvprod : Integrable (fun z : ℝ × ℝ => v z.1 * v z.2)
      (volume.prod volume) := hv.mul_prod hv
  have hpairProd : Integrable (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2)
      (volume.prod volume) := by
    have h := hvprod.bdd_mul (c := 1) hpairCont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hpairNorm z.1 z.2)
    simpa only [mul_assoc] using h
  have hvcont : Continuous v := by
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  have hD₆ : Integrable (fun z : ℝ × ℝ =>
      (|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖)
      (volume.prod volume) := by
    let C : ℝ := (2 : ℝ) ^ 5
    let B : ℝ × ℝ → ℝ := fun z => C *
      ((|z.1| ^ 6 * ‖v z.1‖) * ‖v z.2‖ +
        ‖v z.1‖ * (|z.2| ^ 6 * ‖v z.2‖))
    have hB : Integrable B (volume.prod volume) :=
      ((h₆.mul_prod hv.norm).add (hv.norm.mul_prod h₆)).const_mul C
    apply hB.mono'
    · have hcont : Continuous (fun z : ℝ × ℝ =>
          (|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖) := by
        fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖)]
      have hadd := add_pow_le (abs_nonneg z.1) (abs_nonneg z.2) 6
      dsimp [B, C]
      calc
        _ ≤ (2 : ℝ) ^ 5 * (|z.1| ^ 6 + |z.2| ^ 6) *
            ‖v z.1‖ * ‖v z.2‖ := by gcongr
        _ = _ := by ring
  have hD₈ : Integrable (fun z : ℝ × ℝ =>
      (|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖)
      (volume.prod volume) := by
    let C : ℝ := (2 : ℝ) ^ 7
    let B : ℝ × ℝ → ℝ := fun z => C *
      ((|z.1| ^ 8 * ‖v z.1‖) * ‖v z.2‖ +
        ‖v z.1‖ * (|z.2| ^ 8 * ‖v z.2‖))
    have hB : Integrable B (volume.prod volume) :=
      ((h₈.mul_prod hv.norm).add (hv.norm.mul_prod h₈)).const_mul C
    apply hB.mono'
    · have hcont : Continuous (fun z : ℝ × ℝ =>
          (|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖) := by
        fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖)]
      have hadd := add_pow_le (abs_nonneg z.1) (abs_nonneg z.2) 8
      dsimp [B, C]
      calc
        _ ≤ (2 : ℝ) ^ 7 * (|z.1| ^ 8 + |z.2| ^ 8) *
            ‖v z.1‖ * ‖v z.2‖ := by gcongr
        _ = _ := by ring
  let R : ℝ × ℝ → ℝ := fun z =>
    (3 * q * (|z.1| + |z.2|) ^ 6 +
      3 * q ^ 2 * (|z.1| + |z.2|) ^ 8) * ‖v z.1‖ * ‖v z.2‖
  have hR : Integrable R (volume.prod volume) := by
    refine ((hD₆.const_mul (3 * q)).add
      (hD₈.const_mul (3 * q ^ 2))).congr ?_
    filter_upwards [] with z
    dsimp [R]
    ring
  have hpoint (z : ℝ × ℝ) :
      ‖rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 - H z‖ ≤ R z := by
    have hrem :=
      norm_rodierPairCharacteristic_sub_quarticGaussian_global_le
        hST z.1 z.2
    rw [show rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 - H z =
        (rodierPairCharacteristic S T z.1 z.2 -
          (((Real.exp (-(q * (z.1 ^ 2 + z.2 ^ 2) / 2)) -
            (q * (z.1 ^ 4 + 6 * z.1 ^ 2 * z.2 ^ 2 + z.2 ^ 4) / 12) *
              Real.exp (-(q * (z.1 ^ 2 + z.2 ^ 2) / 2)) : ℝ) : ℂ))) *
          v z.1 * v z.2 by dsimp [H]; ring,
      norm_mul, norm_mul]
    dsimp [R]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ 3 * ((2 : ℝ) ^ n * (|z.1| + |z.2|) ^ 6 +
          ((2 : ℝ) ^ n) ^ 2 * (|z.1| + |z.2|) ^ 8) := hrem
      _ = _ := by dsimp [q]; ring
  have hEIntegral :
      (∫ z : ℝ × ℝ, E z ∂volume.prod volume) =
        J ^ 2 - (((q / 12 : ℝ) : ℂ) *
          (2 * A₄ * J + 6 * A₂ ^ 2)) := by
    have h00 : (∫ z : ℝ × ℝ, F₀ z.1 * F₀ z.2 ∂volume.prod volume) = J ^ 2 := by
      simpa [J, pow_two] using (integral_prod_mul (μ := volume) (ν := volume) F₀ F₀)
    have h40 : (∫ z : ℝ × ℝ, F₄ z.1 * F₀ z.2 ∂volume.prod volume) = A₄ * J := by
      simpa [A₄, J] using (integral_prod_mul (μ := volume) (ν := volume) F₄ F₀)
    have h22 : (∫ z : ℝ × ℝ, F₂ z.1 * F₂ z.2 ∂volume.prod volume) = A₂ ^ 2 := by
      simpa [A₂, pow_two] using (integral_prod_mul (μ := volume) (ν := volume) F₂ F₂)
    have h04 : (∫ z : ℝ × ℝ, F₀ z.1 * F₄ z.2 ∂volume.prod volume) = J * A₄ := by
      simpa [A₄, J] using (integral_prod_mul (μ := volume) (ν := volume) F₀ F₄)
    have hsum : Integrable (fun z : ℝ × ℝ =>
        F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) + F₀ z.1 * F₄ z.2)
        (volume.prod volume) :=
      (hprod₄₀.add (hprod₂₂.const_mul 6)).add hprod₀₄
    have hsumIntegral :
        (∫ z : ℝ × ℝ,
            F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) +
              F₀ z.1 * F₄ z.2 ∂volume.prod volume) =
          ((∫ z : ℝ × ℝ, F₄ z.1 * F₀ z.2 ∂volume.prod volume) +
            ∫ z : ℝ × ℝ, 6 * (F₂ z.1 * F₂ z.2) ∂volume.prod volume) +
            ∫ z : ℝ × ℝ, F₀ z.1 * F₄ z.2 ∂volume.prod volume := by
      calc
        _ = (∫ z : ℝ × ℝ,
              F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2)
                ∂volume.prod volume) +
              ∫ z : ℝ × ℝ, F₀ z.1 * F₄ z.2 ∂volume.prod volume := by
            simpa only [Pi.add_apply] using
              integral_add (hprod₄₀.add (hprod₂₂.const_mul 6)) hprod₀₄
        _ = _ := by
          rw [show (∫ z : ℝ × ℝ,
              F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2)
                ∂volume.prod volume) =
              (∫ z : ℝ × ℝ, F₄ z.1 * F₀ z.2 ∂volume.prod volume) +
                ∫ z : ℝ × ℝ, 6 * (F₂ z.1 * F₂ z.2) ∂volume.prod volume by
            simpa only [Pi.add_apply] using
              integral_add hprod₄₀ (hprod₂₂.const_mul 6)]
    change (∫ z : ℝ × ℝ,
        F₀ z.1 * F₀ z.2 - ((q / 12 : ℝ) : ℂ) *
          (F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) +
            F₀ z.1 * F₄ z.2) ∂volume.prod volume) = _
    calc
      _ = (∫ z : ℝ × ℝ, F₀ z.1 * F₀ z.2 ∂volume.prod volume) -
          ∫ z : ℝ × ℝ, ((q / 12 : ℝ) : ℂ) *
            (F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) +
              F₀ z.1 * F₄ z.2) ∂volume.prod volume :=
        integral_sub hprod₀₀ (hsum.const_mul _)
      _ = (∫ z : ℝ × ℝ, F₀ z.1 * F₀ z.2 ∂volume.prod volume) -
          ((q / 12 : ℝ) : ℂ) *
            ∫ z : ℝ × ℝ,
              F₄ z.1 * F₀ z.2 + 6 * (F₂ z.1 * F₂ z.2) +
                F₀ z.1 * F₄ z.2 ∂volume.prod volume := by
        rw [integral_const_mul]
      _ = (∫ z : ℝ × ℝ, F₀ z.1 * F₀ z.2 ∂volume.prod volume) -
          ((q / 12 : ℝ) : ℂ) *
            (((∫ z : ℝ × ℝ, F₄ z.1 * F₀ z.2 ∂volume.prod volume) +
              ∫ z : ℝ × ℝ, 6 * (F₂ z.1 * F₂ z.2) ∂volume.prod volume) +
              ∫ z : ℝ × ℝ, F₀ z.1 * F₄ z.2 ∂volume.prod volume) := by
        rw [hsumIntegral]
      _ = _ := by
        rw [integral_const_mul, h00, h40, h22, h04]
        ring
  have hHIntegral :
      (∫ z : ℝ × ℝ, H z ∂volume.prod volume) =
        J ^ 2 - (((q / 12 : ℝ) : ℂ) *
          (2 * A₄ * J + 6 * A₂ ^ 2)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hHEq), hEIntegral]
  change ‖(∫ t : ℝ, ∫ r : ℝ,
      rodierPairCharacteristic S T t r * v t * v r) -
      (J ^ 2 - (((q / 12 : ℝ) : ℂ) *
        (2 * A₄ * J + 6 * A₂ ^ 2)))‖ ≤ _
  rw [← hHIntegral,
    ← integral_prod (fun z : ℝ × ℝ =>
      rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2) hpairProd,
    ← integral_sub hpairProd hH]
  calc
    _ ≤ ∫ z : ℝ × ℝ,
        ‖rodierPairCharacteristic S T z.1 z.2 * v z.1 * v z.2 - H z‖
          ∂volume.prod volume := norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, R z ∂volume.prod volume :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) hR
        (Filter.Eventually.of_forall hpoint)
    _ = (3 * q) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 * ‖v t‖ * ‖v r‖) +
        (3 * q ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 * ‖v t‖ * ‖v r‖) := by
      rw [show R = fun z : ℝ × ℝ =>
          (3 * q) * ((|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖) +
          (3 * q ^ 2) * ((|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖) by
        funext z
        dsimp [R]
        ring]
      calc
        _ = (∫ z : ℝ × ℝ,
              (3 * q) * ((|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖)
                ∂volume.prod volume) +
            ∫ z : ℝ × ℝ,
              (3 * q ^ 2) * ((|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖)
                ∂volume.prod volume :=
          integral_add (hD₆.const_mul _) (hD₈.const_mul _)
        _ = (3 * q) * (∫ z : ℝ × ℝ,
              (|z.1| + |z.2|) ^ 6 * ‖v z.1‖ * ‖v z.2‖ ∂volume.prod volume) +
            (3 * q ^ 2) * (∫ z : ℝ × ℝ,
              (|z.1| + |z.2|) ^ 8 * ‖v z.1‖ * ‖v z.2‖ ∂volume.prod volume) := by
          rw [integral_const_mul, integral_const_mul]
        _ = _ := by
          rw [integral_prod _ hD₆, integral_prod _ hD₈]
    _ = _ := by rfl


/-- Rodier's off-diagonal cutoff estimate with the quartic Gaussian correction
retained. The remaining error uses only sixth- and eighth-order density moments. -/
theorem norm_rodierPairCutoffExpectation_sub_quarticGaussianIntegral_sq_le
    (hn : 0 < n) {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖rodierPairCutoffExpectation S T M Δ -
        ((rodierCutoffGaussianIntegral n M Δ hM hΔ) ^ 2 -
          (((2 : ℝ) ^ n / 12 : ℝ) : ℂ) *
            (2 * rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ *
                rodierCutoffGaussianIntegral n M Δ hM hΔ +
              6 * (rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ) ^ 2))‖ ≤
      2 * ((3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, |t| ^ 6 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, |t| ^ 8 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)) +
      (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖ *
              ‖rodierCutoffFourierDensity M Δ hM hΔ r‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t => (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  let G : ℂ := rodierCutoffGaussianIntegral n M Δ hM hΔ
  let J : ℂ := ∫ t : ℝ, g t * v t
  let A₂ : ℂ := rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ
  let A₄ : ℂ := rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ
  let K : ℂ := ∫ t : ℝ, ∫ r : ℝ,
    rodierPairCharacteristic S T t r * v t * v r
  let c : ℂ := (((2 : ℝ) ^ n / 12 : ℝ) : ℂ)
  have hS := norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
    hn S M Δ hM hΔ hΔM
  have hT := norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
    hn T M Δ hM hΔ hΔM
  have hK := norm_rodierPairCharacteristicIntegral_sub_quarticGaussian_le
    hST M Δ hM hΔ
  have hGJ : G = 1 + J := by
    rfl
  have hdecomp :
      rodierPairCutoffExpectation S T M Δ -
          (G ^ 2 - c * (2 * A₄ * G + 6 * A₂ ^ 2)) =
        (rodierSingleCutoffExpectation S M Δ - (G - c * A₄)) +
          (rodierSingleCutoffExpectation T M Δ - (G - c * A₄)) +
          (K - (J ^ 2 - c * (2 * A₄ * J + 6 * A₂ ^ 2))) := by
    rw [rodierPairCutoffExpectation_eq_fourierIntegral S T M Δ hM hΔ,
      rodierPairFourierIntegral,
      rodierSingleCutoffExpectation_eq_characteristicIntegral S M Δ hM hΔ,
      rodierSingleCutoffExpectation_eq_characteristicIntegral T M Δ hM hΔ]
    dsimp [G, J, K, A₂, A₄, c, g, v, q,
      rodierCutoffGaussianIntegral]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖(rodierSingleCutoffExpectation S M Δ - (G - c * A₄)) +
          (rodierSingleCutoffExpectation T M Δ - (G - c * A₄))‖ +
        ‖K - (J ^ 2 - c * (2 * A₄ * J + 6 * A₂ ^ 2))‖ :=
      norm_add_le _ _
    _ ≤ (‖rodierSingleCutoffExpectation S M Δ - (G - c * A₄)‖ +
          ‖rodierSingleCutoffExpectation T M Δ - (G - c * A₄)‖) +
        ‖K - (J ^ 2 - c * (2 * A₄ * J + 6 * A₂ ^ 2))‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤
        (((3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
            (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖)) +
          ((3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
            (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖))) +
        ((3 * (2 : ℝ) ^ n) *
            (∫ t : ℝ, ∫ r : ℝ,
              (|t| + |r|) ^ 6 * ‖v t‖ * ‖v r‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) *
            (∫ t : ℝ, ∫ r : ℝ,
              (|t| + |r|) ^ 8 * ‖v t‖ * ‖v r‖)) := by
      apply add_le_add
      · exact add_le_add (by simpa [G, A₄, c, v] using hS)
          (by simpa [G, A₄, c, v] using hT)
      · simpa [K, J, A₂, A₄, c, g, v, q] using hK
    _ = _ := by
      dsimp [v]
      ring

/-- The refined off-diagonal cutoff remainder factors through the sharp
sixth and eighth density moments and the total density mass. -/
theorem norm_rodierPairCutoffExpectation_sub_quarticGaussianIntegral_sq_le_moments
    (hn : 0 < n) {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖rodierPairCutoffExpectation S T M Δ -
        ((rodierCutoffGaussianIntegral n M Δ hM hΔ) ^ 2 -
          (((2 : ℝ) ^ n / 12 : ℝ) : ℂ) *
            (2 * rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ *
                rodierCutoffGaussianIntegral n M Δ hM hΔ +
              6 * (rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ) ^ 2))‖ ≤
      2 * ((3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, |t| ^ 6 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, |t| ^ 8 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)) +
      (3 * (2 : ℝ) ^ n) *
          (64 * (∫ t : ℝ, |t| ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (256 * (∫ t : ℝ, |t| ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hvcont : Continuous v := by
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_sharp_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_sharp_bound
  have h₆ := (hm₆ M Δ hM hΔ).1
  have h₈ := (hm₈ M Δ hM hΔ).1
  have h₀ : Integrable (fun t : ℝ => ‖v t‖) := hv.norm
  have hD₆ := rodierDoubleDensityAbsAddMoment_integrable_and_le 6 v hvcont h₀ h₆
  have hD₈ := rodierDoubleDensityAbsAddMoment_integrable_and_le 8 v hvcont h₀ h₈
  have hpair :=
    norm_rodierPairCutoffExpectation_sub_quarticGaussianIntegral_sq_le
      hn hST M Δ hM hΔ hΔM
  change _ ≤
      2 * ((3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖)) +
      (3 * (2 : ℝ) ^ n) *
          (64 * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) * ∫ t : ℝ, ‖v t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (256 * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)
  calc
    _ ≤ 2 * ((3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖)) +
        (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 * ‖v t‖ * ‖v r‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 * ‖v t‖ * ‖v r‖) := by
      simpa [v] using hpair
    _ ≤ 2 * ((3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖)) +
        (3 * (2 : ℝ) ^ n) *
          ((2 : ℝ) ^ (6 - 1) *
            (2 * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          ((2 : ℝ) ^ (8 - 1) *
            (2 * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) := by
      gcongr
      · exact hD₆.2.2
      · exact hD₈.2.2
    _ = _ := by
      norm_num
      ring


/-- The double moments in the off-diagonal pair estimate factor into the
corresponding one-variable density moment and total mass. -/
theorem norm_rodierPairCharacteristicIntegral_sub_gaussianSquare_le_moments
    {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖(∫ t : ℝ, ∫ r : ℝ,
          rodierPairCharacteristic S T t r *
            rodierCutoffFourierDensity M Δ hM hΔ t *
            rodierCutoffFourierDensity M Δ hM hΔ r) -
        (∫ t : ℝ,
          (Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℂ) *
            rodierCutoffFourierDensity M Δ hM hΔ t) ^ 2‖ ≤
      ((2 : ℝ) ^ n / 12) *
          (16 * (∫ t : ℝ, |t| ^ 4 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * (2 : ℝ) ^ n) *
          (64 * (∫ t : ℝ, |t| ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (256 * (∫ t : ℝ, |t| ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hvcont : Continuous v := by
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  obtain ⟨C₄, hC₄, hm₄⟩ :=
    exists_rodierCutoffFourierDensity_fourthMoment_bound
  obtain ⟨C₆, hC₆, hm₆⟩ :=
    exists_rodierCutoffFourierDensity_sixthMoment_bound
  obtain ⟨C₈, hC₈, hm₈⟩ :=
    exists_rodierCutoffFourierDensity_eighthMoment_bound
  have h₄ := (hm₄ M Δ hM hΔ hΔM).1
  have h₆ := (hm₆ M Δ hM hΔ hΔM).1
  have h₈ := (hm₈ M Δ hM hΔ hΔM).1
  have h0 : Integrable (fun t : ℝ => ‖v t‖) := hv.norm
  have hD₄ := rodierDoubleDensityAbsAddMoment_integrable_and_le 4 v hvcont h0 h₄
  have hD₆ := rodierDoubleDensityAbsAddMoment_integrable_and_le 6 v hvcont h0 h₆
  have hD₈ := rodierDoubleDensityAbsAddMoment_integrable_and_le 8 v hvcont h0 h₈
  have hcross := norm_rodierPairCharacteristicIntegral_sub_gaussianSquare_le
    hST M Δ hM hΔ hΔM
  change _ ≤ ((2 : ℝ) ^ n / 12) *
      (16 * (∫ t : ℝ, |t| ^ 4 * ‖v t‖) * ∫ t : ℝ, ‖v t‖) +
    (3 * (2 : ℝ) ^ n) *
      (64 * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) * ∫ t : ℝ, ‖v t‖) +
    (3 * ((2 : ℝ) ^ n) ^ 2) *
      (256 * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)
  calc
    _ ≤ ((2 : ℝ) ^ n / 12) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 4 * ‖v t‖ * ‖v r‖) +
        (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 6 * ‖v t‖ * ‖v r‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, ∫ r : ℝ,
            (|t| + |r|) ^ 8 * ‖v t‖ * ‖v r‖) := by
      simpa [v] using hcross
    _ ≤ ((2 : ℝ) ^ n / 12) *
          ((2 : ℝ) ^ (4 - 1) *
            (2 * (∫ t : ℝ, |t| ^ 4 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) +
        (3 * (2 : ℝ) ^ n) *
          ((2 : ℝ) ^ (6 - 1) *
            (2 * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          ((2 : ℝ) ^ (8 - 1) *
            (2 * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) := by
      gcongr
      · exact hD₄.2.2
      · exact hD₆.2.2
      · exact hD₈.2.2
    _ = _ := by
      norm_num
      ring

/-- Rodier Lemma 6.5 in cutoff-expectation form: for distinct Walsh
coefficients, the joint cutoff expectation is controlled by the square of the
Gaussian main term and the one- and two-variable density moments. -/
theorem norm_rodierPairCutoffExpectation_sub_gaussianIntegral_sq_le
    (hn : 0 < n) {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    ‖rodierPairCutoffExpectation S T M Δ -
        (rodierCutoffGaussianIntegral n M Δ hM hΔ) ^ 2‖ ≤
      2 * (((2 : ℝ) ^ n / 12) *
          (∫ t : ℝ, |t| ^ 4 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * (2 : ℝ) ^ n) *
          (∫ t : ℝ, |t| ^ 6 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (∫ t : ℝ, |t| ^ 8 *
            ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)) +
      ((2 : ℝ) ^ n / 12) *
          (16 * (∫ t : ℝ, |t| ^ 4 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * (2 : ℝ) ^ n) *
          (64 * (∫ t : ℝ, |t| ^ 6 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
        (3 * ((2 : ℝ) ^ n) ^ 2) *
          (256 * (∫ t : ℝ, |t| ^ 8 *
              ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
            ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) := by
  let q : ℝ := (2 : ℝ) ^ n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let g : ℝ → ℂ := fun t => (Real.exp (-(q * t ^ 2 / 2)) : ℂ)
  let G : ℂ := rodierCutoffGaussianIntegral n M Δ hM hΔ
  let J : ℂ := ∫ t : ℝ, g t * v t
  let K : ℂ := ∫ t : ℝ, ∫ r : ℝ,
    rodierPairCharacteristic S T t r * v t * v r
  have hS := norm_rodierSingleCutoffExpectation_sub_gaussianIntegral_le
    hn S M Δ hM hΔ hΔM
  have hT := norm_rodierSingleCutoffExpectation_sub_gaussianIntegral_le
    hn T M Δ hM hΔ hΔM
  have hK :=
    norm_rodierPairCharacteristicIntegral_sub_gaussianSquare_le_moments
      hST M Δ hM hΔ hΔM
  have hdecomp :
      rodierPairCutoffExpectation S T M Δ - G ^ 2 =
        (rodierSingleCutoffExpectation S M Δ - G) +
          (rodierSingleCutoffExpectation T M Δ - G) +
          (K - J ^ 2) := by
    rw [rodierPairCutoffExpectation_eq_fourierIntegral S T M Δ hM hΔ,
      rodierPairFourierIntegral,
      rodierSingleCutoffExpectation_eq_characteristicIntegral S M Δ hM hΔ,
      rodierSingleCutoffExpectation_eq_characteristicIntegral T M Δ hM hΔ]
    dsimp [G, J, K, g, v, q, rodierCutoffGaussianIntegral]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖(rodierSingleCutoffExpectation S M Δ - G) +
          (rodierSingleCutoffExpectation T M Δ - G)‖ + ‖K - J ^ 2‖ :=
      norm_add_le _ _
    _ ≤ (‖rodierSingleCutoffExpectation S M Δ - G‖ +
          ‖rodierSingleCutoffExpectation T M Δ - G‖) + ‖K - J ^ 2‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤
        ((((2 : ℝ) ^ n / 12) *
            (∫ t : ℝ, |t| ^ 4 * ‖v t‖) +
          (3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖)) +
        (((2 : ℝ) ^ n / 12) *
            (∫ t : ℝ, |t| ^ 4 * ‖v t‖) +
          (3 * (2 : ℝ) ^ n) * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) * (∫ t : ℝ, |t| ^ 8 * ‖v t‖))) +
        (((2 : ℝ) ^ n / 12) *
            (16 * (∫ t : ℝ, |t| ^ 4 * ‖v t‖) * ∫ t : ℝ, ‖v t‖) +
          (3 * (2 : ℝ) ^ n) *
            (64 * (∫ t : ℝ, |t| ^ 6 * ‖v t‖) * ∫ t : ℝ, ‖v t‖) +
          (3 * ((2 : ℝ) ^ n) ^ 2) *
            (256 * (∫ t : ℝ, |t| ^ 8 * ‖v t‖) * ∫ t : ℝ, ‖v t‖)) := by
      apply add_le_add
      · exact add_le_add (by simpa [G, v] using hS) (by simpa [G, v] using hT)
      · simpa [K, J, g, v, q] using hK
    _ = _ := by
      dsimp [v]
      ring

/-- Rodier's smoothed fraction of Walsh coefficients outside the cutoff window. -/
noncomputable def rodierCutoffFrequencyAverage
    (M Δ : ℝ) (f : FABL.BooleanFunction n) : ℝ :=
  Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
    rodierCutoff M Δ (rodierRawWalshCoefficient S f))

/-- The real finite expectation underlying the complex single-cutoff expectation. -/
theorem ofReal_expect_rodierCutoff_eq_singleCutoffExpectation
    (S : Finset (Fin n)) (M Δ : ℝ) :
    ((Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      rodierCutoff M Δ (rodierRawWalshCoefficient S f)) : ℝ) : ℂ) =
      rodierSingleCutoffExpectation S M Δ := by
  rw [rodierSingleCutoffExpectation, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  push_cast
  rfl

/-- The real finite expectation underlying the complex pair-cutoff expectation. -/
theorem ofReal_expect_rodierCutoff_mul_eq_pairCutoffExpectation
    (S T : Finset (Fin n)) (M Δ : ℝ) :
    ((Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      rodierCutoff M Δ (rodierRawWalshCoefficient S f) *
        rodierCutoff M Δ (rodierRawWalshCoefficient T f)) : ℝ) : ℂ) =
      rodierPairCutoffExpectation S T M Δ := by
  rw [rodierPairCutoffExpectation, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  push_cast
  rfl

/-- All Walsh coordinates have the same single-cutoff expectation. -/
theorem rodierSingleCutoffExpectation_eq_of_indices (S T : Finset (Fin n))
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    rodierSingleCutoffExpectation S M Δ =
      rodierSingleCutoffExpectation T M Δ := by
  rw [rodierSingleCutoffExpectation_eq_characteristicIntegral S M Δ hM hΔ,
    rodierSingleCutoffExpectation_eq_characteristicIntegral T M Δ hM hΔ]
  apply congrArg (fun z : ℂ => 1 + z)
  apply integral_congr_ae
  filter_upwards [] with t
  rw [rodierSingleCharacteristic_eq_cos_pow,
    rodierSingleCharacteristic_eq_cos_pow]

/-- The mean of the smoothed Walsh exceedance fraction is any one-coordinate mean. -/
theorem expect_rodierCutoffFrequencyAverage (S₀ : Finset (Fin n))
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      rodierCutoffFrequencyAverage M Δ f) =
      (rodierSingleCutoffExpectation S₀ M Δ).re := by
  rw [show Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      rodierCutoffFrequencyAverage M Δ f) =
      Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
        Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
          rodierCutoff M Δ (rodierRawWalshCoefficient S f))) by
    unfold rodierCutoffFrequencyAverage
    exact Finset.expect_comm Finset.univ Finset.univ _]
  calc
    _ = Finset.expect Finset.univ (fun _S : Finset (Fin n) ↦
          (rodierSingleCutoffExpectation S₀ M Δ).re) := by
      apply Finset.expect_congr rfl
      intro S _
      calc
        _ = (rodierSingleCutoffExpectation S M Δ).re := by
          have h := congrArg Complex.re
            (ofReal_expect_rodierCutoff_eq_singleCutoffExpectation S M Δ)
          simpa using h
        _ = _ := congrArg Complex.re
          (rodierSingleCutoffExpectation_eq_of_indices S S₀ M Δ hM hΔ)
    _ = _ := Fintype.expect_const _

/-- The exact finite second moment is the average of all pair-cutoff expectations. -/
theorem expect_sq_rodierCutoffFrequencyAverage (M Δ : ℝ) :
    Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      (rodierCutoffFrequencyAverage M Δ f) ^ 2) =
      Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
        Finset.expect Finset.univ (fun T : Finset (Fin n) ↦
          (rodierPairCutoffExpectation S T M Δ).re)) := by
  rw [show Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
      (rodierCutoffFrequencyAverage M Δ f) ^ 2) =
      Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
        Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
          Finset.expect Finset.univ (fun T : Finset (Fin n) ↦
            rodierCutoff M Δ (rodierRawWalshCoefficient S f) *
              rodierCutoff M Δ (rodierRawWalshCoefficient T f)))) by
    apply Finset.expect_congr rfl
    intro f _
    rw [pow_two]
    unfold rodierCutoffFrequencyAverage
    exact Finset.expect_mul_expect _ _ _ _]
  calc
    _ = Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
          Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
            Finset.expect Finset.univ (fun T : Finset (Fin n) ↦
              rodierCutoff M Δ (rodierRawWalshCoefficient S f) *
                rodierCutoff M Δ (rodierRawWalshCoefficient T f)))) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = Finset.expect Finset.univ (fun S : Finset (Fin n) ↦
          Finset.expect Finset.univ (fun T : Finset (Fin n) ↦
            Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
              rodierCutoff M Δ (rodierRawWalshCoefficient S f) *
                rodierCutoff M Δ (rodierRawWalshCoefficient T f)))) := by
      apply Finset.expect_congr rfl
      intro S _
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = _ := by
      apply Finset.expect_congr rfl
      intro S _
      apply Finset.expect_congr rfl
      intro T _
      have h := congrArg Complex.re
        (ofReal_expect_rodierCutoff_mul_eq_pairCutoffExpectation S T M Δ)
      simpa using h

/-- A uniform off-diagonal pair error gives the finite second-moment bound
used in Rodier's lower-tail argument. -/
theorem expect_sq_rodierCutoffFrequencyAverage_le (S₀ : Finset (Fin n))
    (M Δ ε : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hpair : ∀ S T : Finset (Fin n), S ≠ T →
      (rodierPairCutoffExpectation S T M Δ).re ≤
        (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 + ε) :
    Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
        (rodierCutoffFrequencyAverage M Δ f) ^ 2) ≤
      (rodierSingleCutoffExpectation S₀ M Δ).re / (2 : ℝ) ^ n +
        (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 + ε := by
  let e : ℝ := (rodierSingleCutoffExpectation S₀ M Δ).re
  let B : ℝ := e ^ 2 + ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdiag (S : Finset (Fin n)) :
      (rodierPairCutoffExpectation S S M Δ).re ≤ e := by
    have hp := congrArg Complex.re
      (ofReal_expect_rodierCutoff_mul_eq_pairCutoffExpectation S S M Δ)
    have hs := congrArg Complex.re
      (ofReal_expect_rodierCutoff_eq_singleCutoffExpectation S M Δ)
    have hse := congrArg Complex.re
      (rodierSingleCutoffExpectation_eq_of_indices S S₀ M Δ hM hΔ)
    have hpoint (f : FABL.BooleanFunction n) :
        rodierCutoff M Δ (rodierRawWalshCoefficient S f) ^ 2 ≤
          rodierCutoff M Δ (rodierRawWalshCoefficient S f) := by
      have h0 := rodierCutoff_nonneg M Δ hM hΔ
        (rodierRawWalshCoefficient S f)
      have h1 := rodierCutoff_le_one M Δ hM hΔ
        (rodierRawWalshCoefficient S f)
      nlinarith
    dsimp [e]
    rw [← hse]
    have hp' : (rodierPairCutoffExpectation S S M Δ).re =
        Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
          rodierCutoff M Δ (rodierRawWalshCoefficient S f) ^ 2) := by
      simpa [pow_two] using hp.symm
    have hs' : (rodierSingleCutoffExpectation S M Δ).re =
        Finset.expect Finset.univ (fun f : FABL.BooleanFunction n ↦
          rodierCutoff M Δ (rodierRawWalshCoefficient S f)) := by
      simpa using hs.symm
    rw [hp', hs', Fintype.expect_eq_sum_div_card,
      Fintype.expect_eq_sum_div_card]
    gcongr with f
    exact hpoint f
  have hinner (S : Finset (Fin n)) :
      Finset.expect Finset.univ (fun T : Finset (Fin n) ↦
          (rodierPairCutoffExpectation S T M Δ).re) ≤
        e / (2 : ℝ) ^ n + B := by
    rw [Fintype.expect_eq_sum_div_card]
    rw [show (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n by
      norm_num]
    calc
      (∑ T : Finset (Fin n), (rodierPairCutoffExpectation S T M Δ).re) /
          (2 : ℝ) ^ n ≤
        (∑ T : Finset (Fin n),
          ((if T = S then e else 0) + B)) / (2 : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro T _
        by_cases hTS : T = S
        · subst T
          simpa using (hdiag S).trans (le_add_of_nonneg_right hB)
        · simp only [if_neg hTS, zero_add]
          exact hpair S T (fun h => hTS h.symm)
      _ = e / (2 : ℝ) ^ n + B := by
        simp only [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [show (∑ T : Finset (Fin n), if T = S then e else 0) = e by simp]
        rw [show (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n by norm_num]
        field_simp
  rw [expect_sq_rodierCutoffFrequencyAverage]
  calc
    _ ≤ Finset.expect Finset.univ (fun _S : Finset (Fin n) ↦
          e / (2 : ℝ) ^ n + B) := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
      gcongr with S
      exact hinner S
    _ = e / (2 : ℝ) ^ n + B := Fintype.expect_const _
    _ = _ := by dsimp [e, B]; ring

/-- Chebyshev's inequality turns the finite second-moment estimate into a
bound for the probability that the smoothed exceedance fraction vanishes. -/
theorem measure_rodierCutoffFrequencyAverage_eq_zero_le (S₀ : Finset (Fin n))
    (M Δ ε : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (he : 0 < (rodierSingleCutoffExpectation S₀ M Δ).re)
    (hpair : ∀ S T : Finset (Fin n), S ≠ T →
      (rodierPairCutoffExpectation S T M Δ).re ≤
        (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 + ε) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | rodierCutoffFrequencyAverage M Δ f = 0} ≤
      ((rodierSingleCutoffExpectation S₀ M Δ).re / (2 : ℝ) ^ n + ε) /
        (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 := by
  let μ : Measure (FABL.BooleanFunction n) :=
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure
  let X : FABL.BooleanFunction n → ℝ := rodierCutoffFrequencyAverage M Δ
  let e : ℝ := (rodierSingleCutoffExpectation S₀ M Δ).re
  have hXbounds (f : FABL.BooleanFunction n) : X f ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [X, rodierCutoffFrequencyAverage]
    rw [Fintype.expect_eq_sum_div_card]
    have hcard : (0 : ℝ) < Fintype.card (Finset (Fin n)) := by positivity
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun S _ =>
          rodierCutoff_nonneg M Δ hM hΔ (rodierRawWalshCoefficient S f)) hcard.le
    · apply (div_le_one hcard).mpr
      calc
        (∑ S : Finset (Fin n),
            rodierCutoff M Δ (rodierRawWalshCoefficient S f)) ≤
            ∑ _S : Finset (Fin n), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro S _
          exact rodierCutoff_le_one M Δ hM hΔ
            (rodierRawWalshCoefficient S f)
        _ = Fintype.card (Finset (Fin n)) := by simp
  have hXmeas : AEStronglyMeasurable X μ :=
    (measurable_of_finite X).aestronglyMeasurable
  have hXlp : MemLp X 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall hXbounds) hXmeas 2
  have hmean : ∫ f, X f ∂μ = e := by
    dsimp [μ, X, e]
    rw [FABL.integral_uniformPMF_eq_expect,
      expect_rodierCutoffFrequencyAverage S₀ M Δ hM hΔ]
  have hsecond :
      (∫ f, (X ^ 2) f ∂μ) ≤ e / (2 : ℝ) ^ n + e ^ 2 + ε := by
    dsimp [μ]
    rw [FABL.integral_uniformPMF_eq_expect]
    simpa [X, e] using
      expect_sq_rodierCutoffFrequencyAverage_le S₀ M Δ ε hM hΔ hε hpair
  have hvar : ProbabilityTheory.variance X μ ≤ e / (2 : ℝ) ^ n + ε := by
    rw [ProbabilityTheory.variance_eq_sub hXlp, hmean]
    calc
      _ ≤ (e / (2 : ℝ) ^ n + e ^ 2 + ε) - e ^ 2 :=
        sub_le_sub_right hsecond _
      _ = _ := by ring
  have hdev := ProbabilityTheory.meas_ge_le_variance_div_sq hXlp
    (show 0 < e by exact he)
  rw [hmean] at hdev
  have hsubset : {f | X f = 0} ⊆ {f | e ≤ |X f - e|} := by
    intro f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [hf, zero_sub, abs_neg, abs_of_pos he]
  have hmono : μ.real {f | X f = 0} ≤ μ.real {f | e ≤ |X f - e|} :=
    measureReal_mono hsubset
  have hdevReal : μ.real {f | e ≤ |X f - e|} ≤
      ProbabilityTheory.variance X μ / e ^ 2 := by
    have htoReal := ENNReal.toReal_mono (by simp) hdev
    simpa [Measure.real, ENNReal.toReal_ofReal
      (div_nonneg (ProbabilityTheory.variance_nonneg X μ) (sq_nonneg e))]
      using htoReal
  change μ.real {f | X f = 0} ≤ (e / (2 : ℝ) ^ n + ε) / e ^ 2
  exact hmono.trans (hdevReal.trans (div_le_div_of_nonneg_right hvar (sq_nonneg e)))


end CryptBoolean
