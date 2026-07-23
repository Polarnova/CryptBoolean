/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.RodierLowerTail
public import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# The Gaussian main term in Rodier's lower-tail argument

Rodier's Fourier--Stieltjes main term as a Gaussian cutoff expectation and
its explicit interval lower bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform NNReal ProbabilityTheory Topology

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The centered Gaussian measure whose variance is the Boolean-cube size. -/
noncomputable def rodierGaussianMeasure (n : ℕ) : Measure ℝ :=
  gaussianReal 0 (2 ^ n)

/-- Rodier's Gaussian Fourier main term is the expectation of his cutoff
under the centered Gaussian of variance `2^n`. -/
theorem rodierCutoffGaussianIntegral_eq_gaussianExpectation
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    rodierCutoffGaussianIntegral n M Δ hM hΔ =
      ∫ x : ℝ, (rodierCutoff M Δ x : ℂ) ∂rodierGaussianMeasure n := by
  let q : ℝ := (2 : ℝ) ^ n
  let γ : Measure ℝ := rodierGaussianMeasure n
  let v : ℝ → ℂ := rodierCutoffFourierDensity M Δ hM hΔ
  let F : ℝ → ℝ → ℂ := fun x t =>
    Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) * v t
  letI : IsProbabilityMeasure γ := by
    dsimp [γ, rodierGaussianMeasure]
    infer_instance
  have hv : Integrable v :=
    rodierCutoffFourierDensity_integrable M Δ hM hΔ
  have hvcont : Continuous v := by
    dsimp [v, rodierCutoffFourierDensity]
    exact continuous_const.mul
      ((rodierCutoffUnitFourierDensity M Δ hM hΔ).continuous.comp (by fun_prop))
  have hprod : Integrable (Function.uncurry F) (γ.prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * ‖v z.2‖)
        (γ.prod volume) :=
      (integrable_const (μ := γ) (1 : ℝ)).mul_prod hv.norm
    apply hdom.mono
    · apply Continuous.aestronglyMeasurable
      dsimp [F]
      exact (Complex.continuous_exp.comp (by fun_prop)).mul
        (hvcont.comp continuous_snd)
    · filter_upwards [] with z
      change ‖Complex.exp ((((z.2 * z.1 : ℝ) : ℂ) * Complex.I)) * v z.2‖ ≤
        |(1 : ℝ) * ‖v z.2‖|
      rw [norm_mul, Complex.norm_exp]
      simp
  have hswap :
      (∫ x : ℝ, (∫ t : ℝ, F x t) ∂γ) =
        ∫ t : ℝ, ∫ x : ℝ, F x t ∂γ :=
    integral_integral_swap hprod
  have hchar (t : ℝ) :
      (∫ x : ℝ,
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) ∂γ) =
        (Real.exp (-(q * t ^ 2 / 2)) : ℂ) := by
    change charFun γ t = _
    rw [show γ = gaussianReal 0 (2 ^ n) from rfl,
      charFun_gaussianReal]
    push_cast
    congr 1
    simp only [mul_zero, zero_mul, zero_sub]
    dsimp [q]
    norm_cast
    push_cast
    ring
  have houter : Integrable (fun x : ℝ => ∫ t : ℝ, F x t) γ := by
    simpa using hprod.integral_prod_left
  rw [rodierCutoffGaussianIntegral]
  simp_rw [rodierCutoff_fourierDensity_inversion M Δ hM hΔ]
  change 1 + ∫ t : ℝ, (Real.exp (-(q * t ^ 2 / 2)) : ℂ) * v t =
    ∫ x : ℝ,
      (1 + ∫ t : ℝ, F x t) ∂γ
  rw [integral_add (μ := γ) (integrable_const 1) houter,
    integral_const]
  simp only [probReal_univ, one_smul]
  rw [hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  calc
    (Real.exp (-(q * t ^ 2 / 2)) : ℂ) * v t =
        (∫ x : ℝ,
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) ∂γ) * v t := by
      rw [hchar]
    _ = ∫ x : ℝ, F x t ∂γ := by
      rw [← integral_mul_const]

/-- The real part of Rodier's Gaussian main term is the ordinary Gaussian
density integral of the cutoff. -/
theorem rodierCutoffGaussianIntegral_re_eq_gaussianDensityIntegral
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (rodierCutoffGaussianIntegral n M Δ hM hΔ).re =
      ∫ x : ℝ,
        gaussianPDFReal 0 (2 ^ n) x * rodierCutoff M Δ x := by
  rw [rodierCutoffGaussianIntegral_eq_gaussianExpectation]
  unfold rodierGaussianMeasure
  rw [integral_gaussianReal_eq_integral_smul
    (by positivity : (2 ^ n : ℝ≥0) ≠ 0)]
  simp_rw [Complex.real_smul]
  simp only [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  simp

private theorem integrable_gaussianPDFReal_mul_rodierCutoff
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    Integrable (fun x : ℝ =>
      gaussianPDFReal 0 (2 ^ n) x * rodierCutoff M Δ x) := by
  apply (integrable_gaussianPDFReal 0 (2 ^ n)).mul_bdd
  · exact (rodierCutoff_contDiff M Δ hM hΔ).continuous.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (rodierCutoff_nonneg M Δ hM hΔ x)]
    exact rodierCutoff_le_one M Δ hM hΔ x

/-- The Fourier transform of the centered Gaussian density, in Mathlib's
unit-frequency convention. -/
theorem fourier_gaussianPDFReal_zero_powTwo
    (n : ℕ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (gaussianPDFReal 0 (2 ^ n) x : ℂ)) ξ =
      (Real.exp (-((2 : ℝ) ^ n * (2 * Real.pi * ξ) ^ 2 / 2)) : ℂ) := by
  let γ : Measure ℝ := gaussianReal 0 (2 ^ n)
  have hv : (2 ^ n : ℝ≥0) ≠ 0 := by positivity
  calc
    𝓕 (fun x : ℝ => (gaussianPDFReal 0 (2 ^ n) x : ℂ)) ξ =
        charFun γ (-2 * Real.pi * ξ) := by
      rw [Real.fourier_real_eq_integral_exp_smul, charFun_apply_real]
      unfold γ
      rw [integral_gaussianReal_eq_integral_smul hv]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul, Complex.real_smul]
      rw [mul_comm]
      congr 1
      push_cast
      ring
    _ = (Real.exp (-((2 : ℝ) ^ n * (2 * Real.pi * ξ) ^ 2 / 2)) : ℂ) := by
      dsimp [γ]
      rw [charFun_gaussianReal]
      push_cast
      congr 1
      ring

private theorem integrable_fourier_gaussianPDFReal_zero_powTwo
    (n : ℕ) :
    Integrable (𝓕 (fun x : ℝ =>
      (gaussianPDFReal 0 (2 ^ n) x : ℂ))) := by
  let q : ℝ := (2 : ℝ) ^ n
  let b : ℝ := q * (2 * Real.pi) ^ 2 / 2
  have hb : 0 < b := by
    dsimp [b, q]
    positivity
  have hg : Integrable (fun ξ : ℝ =>
      (Real.exp (-b * ξ ^ 2) : ℂ)) :=
    (integrable_exp_neg_mul_sq hb).ofReal
  apply hg.congr
  filter_upwards [] with ξ
  rw [fourier_gaussianPDFReal_zero_powTwo]
  congr 2
  dsimp [b, q]
  ring

private theorem fourier_fourier_gaussianPDFReal_zero_powTwo
    (n : ℕ) (x : ℝ) :
    𝓕 (𝓕 (fun y : ℝ =>
      (gaussianPDFReal 0 (2 ^ n) y : ℂ))) x =
        (gaussianPDFReal 0 (2 ^ n) (-x) : ℂ) := by
  let f : ℝ → ℂ := fun y => (gaussianPDFReal 0 (2 ^ n) y : ℂ)
  have hf : Integrable f := (integrable_gaussianPDFReal 0 (2 ^ n)).ofReal
  have hF : Integrable (𝓕 f) :=
    integrable_fourier_gaussianPDFReal_zero_powTwo n
  have hinv := hf.fourierInv_fourier_eq hF
    (show ContinuousAt f (-x) by
      dsimp [f, gaussianPDFReal]
      fun_prop)
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  simpa [f] using hinv

private theorem integrable_iteratedDeriv_rodierCutoffRemainder
    (p : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    Integrable (iteratedDeriv p
      (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)) := by
  let f := rodierCutoffRemainderSchwartz M Δ hM hΔ
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

private theorem iteratedDeriv_rodierCutoffRemainder_eq_ofReal
    {p : ℕ} (hp : 0 < p) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ)
    (x : ℝ) :
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

private theorem fourier_iteratedDeriv_rodierCutoffRemainder
    (p : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    𝓕 (iteratedDeriv p
      (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)) =
      fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) ^ p •
        rodierCutoffUnitFourierDensity M Δ hM hΔ ξ := by
  exact Real.fourier_iteratedDeriv (N := ⊤) (n := p)
    ((rodierCutoffRemainderSchwartz M Δ hM hΔ).smooth ⊤)
    (fun k _ =>
      integrable_iteratedDeriv_rodierCutoffRemainder k M Δ hM hΔ)
    le_top

private theorem integral_fourier_iteratedDeriv_mul_fourier_gaussianPDF
    {p : ℕ} (hp : 0 < p) (n : ℕ)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (∫ ξ : ℝ,
        𝓕 (iteratedDeriv p
          (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)) ξ *
        𝓕 (fun y : ℝ =>
          (gaussianPDFReal 0 (2 ^ n) y : ℂ)) ξ) =
      ∫ x : ℝ,
        ((iteratedDeriv p (rodierCutoff M Δ) x : ℝ) : ℂ) *
          (gaussianPDFReal 0 (2 ^ n) x : ℂ) := by
  let d : ℝ → ℂ := iteratedDeriv p
    (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)
  let g : ℝ → ℂ := fun y => (gaussianPDFReal 0 (2 ^ n) y : ℂ)
  have hd : Integrable d :=
    integrable_iteratedDeriv_rodierCutoffRemainder p M Δ hM hΔ
  have hg : Integrable (𝓕 g) :=
    integrable_fourier_gaussianPDFReal_zero_powTwo n
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hd hg
  have hswap' :
      (∫ ξ : ℝ, 𝓕 d ξ * 𝓕 g ξ) =
        ∫ x : ℝ, d x * 𝓕 (𝓕 g) x := by
    calc
      _ = ∫ ξ : ℝ,
          VectorFourier.fourierIntegral Real.fourierChar volume
              (innerₗ ℝ) d ξ • 𝓕 g ξ := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        change
          VectorFourier.fourierIntegral Real.fourierChar volume
              (innerₗ ℝ) d ξ * 𝓕 g ξ =
            VectorFourier.fourierIntegral Real.fourierChar volume
              (innerₗ ℝ) d ξ • 𝓕 g ξ
        simp only [smul_eq_mul]
      _ = ∫ x : ℝ, d x •
          VectorFourier.fourierIntegral Real.fourierChar volume
            (innerₗ ℝ).flip (𝓕 g) x := hswap
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [flip_innerₗ]
        change d x • 𝓕 (𝓕 g) x = d x * 𝓕 (𝓕 g) x
        simp only [smul_eq_mul]
  rw [show (fun x : ℝ => d x * 𝓕 (𝓕 g) x) =
      fun x => ((iteratedDeriv p (rodierCutoff M Δ) x : ℝ) : ℂ) *
        (gaussianPDFReal 0 (2 ^ n) x : ℂ) by
    funext x
    rw [show d x =
        Complex.ofReal (iteratedDeriv p (rodierCutoff M Δ) x) by
      exact iteratedDeriv_rodierCutoffRemainder_eq_ofReal hp M Δ hM hΔ x]
    rw [show 𝓕 (𝓕 g) x =
        (gaussianPDFReal 0 (2 ^ n) (-x) : ℂ) by
      exact fourier_fourier_gaussianPDFReal_zero_powTwo n x]
    rw [show gaussianPDFReal 0 (2 ^ n) (-x) =
        gaussianPDFReal 0 (2 ^ n) x by
      simp [gaussianPDFReal]]
  ] at hswap'
  simpa [d, g, smul_eq_mul] using hswap'

private theorem rodierGaussianWeightedDensityMoment_eq_unitFourierIntegral
    (n p : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    rodierGaussianWeightedDensityMoment n p M Δ hM hΔ =
      ∫ ξ : ℝ,
        (((((2 * Real.pi : ℝ) * ξ) ^ p *
          Real.exp (-((2 : ℝ) ^ n *
            ((2 * Real.pi : ℝ) * ξ) ^ 2 / 2)) : ℝ) : ℂ) *
          rodierCutoffUnitFourierDensity M Δ hM hΔ ξ) := by
  let a : ℝ := 2 * Real.pi
  let w : ℝ → ℂ := fun ξ =>
    ((((a * ξ) ^ p *
      Real.exp (-((2 : ℝ) ^ n * (a * ξ) ^ 2 / 2)) : ℝ) : ℂ) *
      ((a : ℂ)⁻¹ *
        rodierCutoffUnitFourierDensity M Δ hM hΔ ξ))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale := Measure.integral_comp_div w a
  rw [abs_of_pos ha] at hscale
  rw [rodierGaussianWeightedDensityMoment]
  calc
    (∫ t : ℝ,
        ((t ^ p * Real.exp (-((2 : ℝ) ^ n * t ^ 2 / 2)) : ℝ) : ℂ) *
          rodierCutoffFourierDensity M Δ hM hΔ t) =
        ∫ t : ℝ, w (t / a) := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [w, a, rodierCutoffFourierDensity]
      congr 3 <;> field_simp
    _ = a • ∫ ξ : ℝ, w ξ := hscale
    _ = ∫ ξ : ℝ,
        (((((2 * Real.pi : ℝ) * ξ) ^ p *
          Real.exp (-((2 : ℝ) ^ n *
            ((2 * Real.pi : ℝ) * ξ) ^ 2 / 2)) : ℝ) : ℂ) *
          rodierCutoffUnitFourierDensity M Δ hM hΔ ξ) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [w, a]
      push_cast
      field_simp

/-- Positive Gaussian-weighted density moments are Gaussian pairings with
the corresponding cutoff derivative. -/
theorem complex_I_pow_mul_rodierGaussianWeightedDensityMoment_eq
    {p : ℕ} (hp : 0 < p) (n : ℕ)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    Complex.I ^ p *
        rodierGaussianWeightedDensityMoment n p M Δ hM hΔ =
      ∫ x : ℝ,
        ((iteratedDeriv p (rodierCutoff M Δ) x : ℝ) : ℂ) *
          (gaussianPDFReal 0 (2 ^ n) x : ℂ) := by
  rw [rodierGaussianWeightedDensityMoment_eq_unitFourierIntegral]
  calc
    Complex.I ^ p *
        (∫ ξ : ℝ,
          (((((2 * Real.pi : ℝ) * ξ) ^ p *
            Real.exp (-((2 : ℝ) ^ n *
              ((2 * Real.pi : ℝ) * ξ) ^ 2 / 2)) : ℝ) : ℂ) *
            rodierCutoffUnitFourierDensity M Δ hM hΔ ξ)) =
        ∫ ξ : ℝ,
          𝓕 (iteratedDeriv p
            (rodierCutoffRemainderSchwartz M Δ hM hΔ : ℝ → ℂ)) ξ *
          𝓕 (fun y : ℝ =>
            (gaussianPDFReal 0 (2 ^ n) y : ℂ)) ξ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [congrFun (fourier_iteratedDeriv_rodierCutoffRemainder
        p M Δ hM hΔ) ξ]
      rw [fourier_gaussianPDFReal_zero_powTwo]
      simp only [smul_eq_mul]
      push_cast
      ring
    _ = _ :=
      integral_fourier_iteratedDeriv_mul_fourier_gaussianPDF
        hp n M Δ hM hΔ

private theorem iteratedDeriv_rodierCutoff_eq_zero_of_abs_lt
    {p : ℕ} {M Δ x : ℝ}
    (hM : 0 < M) (hΔ : 0 < Δ) (hx : |x| < M) :
    iteratedDeriv p (rodierCutoff M Δ) x = 0 := by
  have hnhds : {y : ℝ | |y| < M} ∈ 𝓝 x :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  have heq : rodierCutoff M Δ =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
    filter_upwards [hnhds] with y hy
    exact rodierCutoff_eq_zero_of_abs_le hM hΔ hy.le
  rw [heq.iteratedDeriv_eq p]
  simp

/-- A centered Gaussian with variance `2^n` has the elementary two-sided
Chernoff tail bound used in the signed-moment estimate. -/
theorem gaussianReal_zero_powTwo_measureReal_abs_ge_le
    (n : ℕ) (M : ℝ) (hM : 0 < M) :
    (gaussianReal 0 (2 ^ n)).real {x : ℝ | M ≤ |x|} ≤
      2 * Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
  let q : ℝ := (2 : ℝ) ^ n
  let γ : Measure ℝ := gaussianReal 0 (2 ^ n)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have htpos : 0 ≤ M / q := div_nonneg hM.le hq.le
  have htneg : -M / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hM.le) hq.le
  have hup₀ := measure_ge_le_exp_mul_mgf
    (μ := γ) (X := id) (t := M / q) M htpos
    (by
      dsimp [γ]
      exact integrable_exp_mul_gaussianReal (M / q))
  have hlo₀ := measure_le_le_exp_mul_mgf
    (μ := γ) (X := id) (t := -M / q) (-M) htneg
    (by
      dsimp [γ]
      exact integrable_exp_mul_gaussianReal (-M / q))
  have hmgfpos : mgf id γ (M / q) =
      Real.exp (q * (M / q) ^ 2 / 2) := by
    dsimp [γ]
    rw [congrFun mgf_id_gaussianReal (M / q)]
    simp only [zero_mul, zero_add]
    congr 1
  have hmgfneg : mgf id γ (-M / q) =
      Real.exp (q * (-M / q) ^ 2 / 2) := by
    dsimp [γ]
    rw [congrFun mgf_id_gaussianReal (-M / q)]
    simp only [zero_mul, zero_add]
    congr 1
  have hrhspos :
      Real.exp (-(M / q) * M) * mgf id γ (M / q) =
        Real.exp (-(M ^ 2) / (2 * q)) := by
    rw [hmgfpos, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hrhsneg :
      Real.exp (-(-M / q) * (-M)) * mgf id γ (-M / q) =
        Real.exp (-(M ^ 2) / (2 * q)) := by
    rw [hmgfneg, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hup : γ.real {x : ℝ | M ≤ x} ≤
      Real.exp (-(M ^ 2) / (2 * q)) := by
    rw [← hrhspos]
    simpa [id] using hup₀
  have hlo : γ.real {x : ℝ | x ≤ -M} ≤
      Real.exp (-(M ^ 2) / (2 * q)) := by
    rw [← hrhsneg]
    simpa [id] using hlo₀
  have hsubset : {x : ℝ | M ≤ |x|} ⊆
      {x : ℝ | M ≤ x} ∪ {x : ℝ | x ≤ -M} := by
    intro x hx
    change M ≤ |x| at hx
    change M ≤ x ∨ x ≤ -M
    rcases le_total 0 x with hx0 | hx0
    · exact Or.inl (by simpa [abs_of_nonneg hx0] using hx)
    · rw [abs_of_nonpos hx0] at hx
      exact Or.inr (by linarith)
  calc
    γ.real {x : ℝ | M ≤ |x|} ≤
        γ.real ({x : ℝ | M ≤ x} ∪ {x : ℝ | x ≤ -M}) :=
      measureReal_mono hsubset
    _ ≤ γ.real {x : ℝ | M ≤ x} + γ.real {x : ℝ | x ≤ -M} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(M ^ 2) / (2 * q)) +
        Real.exp (-(M ^ 2) / (2 * q)) := add_le_add hup hlo
    _ = 2 * Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
      dsimp [q]
      ring

/-- Rodier Proposition 4.1(7), in the slightly coarser Chernoff form sufficient
for the random-nonlinearity argument. The crucial Gaussian tail factor is
retained uniformly in the moment order. -/
theorem exists_rodierGaussianWeightedDensityMoment_exponential_bound
    {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        ‖rodierGaussianWeightedDensityMoment n p M Δ hM hΔ‖ ≤
          C * Δ⁻¹ ^ p *
            Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
  obtain ⟨C₀, hC₀, hderiv⟩ :=
    exists_iteratedDeriv_rodierCutoff_bound hp
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro n M Δ hM hΔ
  let γ : Measure ℝ := gaussianReal 0 (2 ^ n)
  let d : ℝ → ℝ := fun x => iteratedDeriv p (rodierCutoff M Δ) x
  let s : Set ℝ := {x | M ≤ |x|}
  let K : ℝ := C₀ * Δ⁻¹ ^ p
  have hv : (2 ^ n : ℝ≥0) ≠ 0 := by positivity
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgauss :
      (∫ x : ℝ, ((d x : ℝ) : ℂ) *
          (gaussianPDFReal 0 (2 ^ n) x : ℂ)) =
        ∫ x : ℝ, ((d x : ℝ) : ℂ) ∂γ := by
    dsimp [γ]
    rw [integral_gaussianReal_eq_integral_smul hv]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Complex.real_smul]
    ring
  have henv : Integrable (s.indicator (fun _ : ℝ => K)) γ :=
    (integrable_const K).indicator hs
  have hpoint (x : ℝ) : |d x| ≤ s.indicator (fun _ : ℝ => K) x := by
    by_cases hx : M ≤ |x|
    · have hxs : x ∈ s := by simpa [s] using hx
      rw [Set.indicator_of_mem hxs]
      dsimp [d, K]
      exact hderiv hΔ
    · have hxlt : |x| < M := lt_of_not_ge hx
      have hxns : x ∉ s := by simpa [s] using hx
      rw [Set.indicator_of_notMem hxns]
      dsimp [d]
      rw [iteratedDeriv_rodierCutoff_eq_zero_of_abs_lt hM hΔ hxlt]
      simp
  have hnormIntegral :
      ‖∫ x : ℝ, ((d x : ℝ) : ℂ) ∂γ‖ ≤
        K * γ.real s := by
    calc
      ‖∫ x : ℝ, ((d x : ℝ) : ℂ) ∂γ‖ ≤
          ∫ x : ℝ, ‖((d x : ℝ) : ℂ)‖ ∂γ :=
        norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, |d x| ∂γ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∫ x : ℝ, s.indicator (fun _ : ℝ => K) x ∂γ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          henv (Filter.Eventually.of_forall hpoint)
      _ = K * γ.real s := by
        rw [integral_indicator_const K hs, smul_eq_mul]
        ring
  have htail : γ.real s ≤
      2 * Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
    simpa [γ, s] using
      gaussianReal_zero_powTwo_measureReal_abs_ge_le n M hM
  calc
    ‖rodierGaussianWeightedDensityMoment n p M Δ hM hΔ‖ =
        ‖Complex.I ^ p *
          rodierGaussianWeightedDensityMoment n p M Δ hM hΔ‖ := by
      simp
    _ = ‖∫ x : ℝ, ((d x : ℝ) : ℂ) *
          (gaussianPDFReal 0 (2 ^ n) x : ℂ)‖ := by
      rw [complex_I_pow_mul_rodierGaussianWeightedDensityMoment_eq
        hp n M Δ hM hΔ]
    _ = ‖∫ x : ℝ, ((d x : ℝ) : ℂ) ∂γ‖ := by rw [hgauss]
    _ ≤ K * γ.real s := hnormIntegral
    _ ≤ K * (2 * Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n))) :=
      mul_le_mul_of_nonneg_left htail hK
    _ = (2 * C₀) * Δ⁻¹ ^ p *
        Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
      dsimp [K]
      ring

theorem exists_rodierGaussianWeightedDensityMoment_second_exponential_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        ‖rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ‖ ≤
          C * Δ⁻¹ ^ 2 *
            Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
  simpa using
    (exists_rodierGaussianWeightedDensityMoment_exponential_bound
      (by norm_num : 0 < 2))

theorem exists_rodierGaussianWeightedDensityMoment_fourth_exponential_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ),
        ‖rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ‖ ≤
          C * Δ⁻¹ ^ 4 *
            Real.exp (-(M ^ 2) / (2 * (2 : ℝ) ^ n)) := by
  simpa using
    (exists_rodierGaussianWeightedDensityMoment_exponential_bound
      (by norm_num : 0 < 4))

/-- A one-sided interval already gives an explicit positive lower bound for
Rodier's Gaussian main term. -/
theorem rodierCutoffGaussianIntegral_re_lower_bound_oneSide
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    (Real.sqrt (2 * Real.pi * (2 : ℝ) ^ n))⁻¹ *
          Real.exp (-((M + 2 * Δ) ^ 2) / (2 * (2 : ℝ) ^ n)) * Δ ≤
      (rodierCutoffGaussianIntegral n M Δ hM hΔ).re := by
  let q : ℝ := (2 : ℝ) ^ n
  let a : ℝ := M + Δ
  let b : ℝ := M + 2 * Δ
  let c : ℝ := (Real.sqrt (2 * Real.pi * q))⁻¹ *
    Real.exp (-(b ^ 2) / (2 * q))
  let f : ℝ → ℝ := fun x =>
    gaussianPDFReal 0 (2 ^ n) x * rodierCutoff M Δ x
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hf : Integrable f := by
    exact integrable_gaussianPDFReal_mul_rodierCutoff n M Δ hM hΔ
  have hfnn (x : ℝ) : 0 ≤ f x := by
    exact mul_nonneg (gaussianPDFReal_nonneg 0 (2 ^ n) x)
      (rodierCutoff_nonneg M Δ hM hΔ x)
  have hinterval (x : ℝ) (hx : x ∈ Set.Icc a b) : c ≤ f x := by
    have hax : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have hx0 : 0 ≤ x := ha.le.trans hax
    have hb0 : 0 ≤ b := hx0.trans hxb
    have hsquare : x ^ 2 ≤ b ^ 2 := by
      nlinarith
    have hexp : Real.exp (-(b ^ 2) / (2 * q)) ≤
        Real.exp (-(x ^ 2) / (2 * q)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * q)).2
      linarith
    have hpdf : c ≤ gaussianPDFReal 0 (2 ^ n) x := by
      have hscale : 0 ≤ (Real.sqrt (2 * Real.pi * q))⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hexp hscale
      simpa [c, b, q, gaussianPDFReal] using hmul
    have hcutoff : rodierCutoff M Δ x = 1 := by
      apply rodierCutoff_eq_one_of_add_le_abs hM hΔ
      rw [abs_of_nonneg hx0]
      exact hax
    dsimp [f]
    rw [hcutoff, mul_one]
    exact hpdf
  calc
    (Real.sqrt (2 * Real.pi * (2 : ℝ) ^ n))⁻¹ *
          Real.exp (-((M + 2 * Δ) ^ 2) / (2 * (2 : ℝ) ^ n)) * Δ =
        c * volume.real (Set.Icc a b) := by
      rw [Real.volume_real_Icc_of_le hab]
      dsimp [c, a, b, q]
      ring
    _ ≤ ∫ x in Set.Icc a b, f x := by
      exact setIntegral_ge_of_const_le_real measurableSet_Icc
        isCompact_Icc.measure_ne_top hinterval hf.integrableOn
    _ ≤ ∫ x, f x := by
      exact setIntegral_le_integral hf (Filter.Eventually.of_forall hfnn)
    _ = (rodierCutoffGaussianIntegral n M Δ hM hΔ).re := by
      exact (rodierCutoffGaussianIntegral_re_eq_gaussianDensityIntegral
        n M Δ hM hΔ).symm

/-- The cube cardinality in Rodier's asymptotic parameterization. -/
noncomputable def rodierAsymptoticQ (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n

/-- A transition width of order `sqrt(2^n / n)`, sufficient for the sharp
lower spectral tail. -/
noncomputable def rodierAsymptoticDelta (n : ℕ) : ℝ :=
  Real.sqrt (rodierAsymptoticQ n) / Real.sqrt (n : ℝ)

/-- The raw-Walsh form of Rodier's lower spectral threshold. -/
noncomputable def rodierAsymptoticM (n : ℕ) : ℝ :=
  Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) *
    (Real.sqrt (2 * Real.log 2) -
      5 * Real.log (n : ℝ) / (n : ℝ))

theorem rodierAsymptoticQ_pos (n : ℕ) :
    0 < rodierAsymptoticQ n := by
  unfold rodierAsymptoticQ
  positivity

theorem rodierAsymptoticDelta_pos {n : ℕ} (hn : 0 < n) :
    0 < rodierAsymptoticDelta n := by
  unfold rodierAsymptoticDelta
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (Real.sqrt_pos.2 (rodierAsymptoticQ_pos n))
    (Real.sqrt_pos.2 hnℝ)

/-- The raw cutoff center is exactly `2^n` times the normalized threshold
used in the final Fourier-infinity event. -/
theorem rodierAsymptoticM_eq_q_mul_threshold (n : ℕ) :
    rodierAsymptoticM n =
      rodierAsymptoticQ n * rodierRandomFourierLowerThreshold n := by
  rw [rodierAsymptoticM, rodierAsymptoticQ,
    rodierRandomFourierLowerThreshold, sqrt_two_pow_eq_rpow]
  have hscale :
      (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 2) =
        (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← hscale]
  ring

/-- The dimension-scale numerator appearing after normalizing Rodier's
Gaussian exponent. -/
noncomputable def rodierAsymptoticExponentNumerator (n : ℕ) : ℝ :=
  (n : ℝ) * Real.sqrt (2 * Real.log 2) -
    5 * Real.log (n : ℝ) + 2

theorem rodierAsymptoticM_add_two_delta_eq
    {n : ℕ} (hn : 0 < n) :
    rodierAsymptoticM n + 2 * rodierAsymptoticDelta n =
      Real.sqrt (rodierAsymptoticQ n) / Real.sqrt (n : ℝ) *
        rodierAsymptoticExponentNumerator n := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hsqrtne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnℝ)
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnℝ.le
  unfold rodierAsymptoticM rodierAsymptoticDelta
    rodierAsymptoticExponentNumerator
  field_simp [hnne, hsqrtne]
  rw [hsqrt]
  ring

theorem rodierAsymptotic_gaussianExponent_eq
    {n : ℕ} (hn : 0 < n) :
    (rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2 /
          (2 * rodierAsymptoticQ n) =
      rodierAsymptoticExponentNumerator n ^ 2 / (2 * (n : ℝ)) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hqne : rodierAsymptoticQ n ≠ 0 :=
    ne_of_gt (rodierAsymptoticQ_pos n)
  have hsqrtnne : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnℝ)
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnℝ.le
  have hsqrtq : Real.sqrt (rodierAsymptoticQ n) ^ 2 =
      rodierAsymptoticQ n :=
    Real.sq_sqrt (rodierAsymptoticQ_pos n).le
  rw [rodierAsymptoticM_add_two_delta_eq hn]
  field_simp [hnne, hqne, hsqrtnne]
  rw [hsqrtn, hsqrtq]
  ring

private theorem tendsto_rodierLogSqDivNat :
    Filter.Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def] using h.tendsto_div_nhds_zero

private theorem tendsto_rodierLogDivNat :
    Filter.Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def] using h.tendsto_div_nhds_zero

private theorem tendsto_rodierInvNat :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 0)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [Function.comp_def] using h.tendsto_div_nhds_zero

private theorem eventually_rodierExponentRemainder_le_one :
    ∀ᶠ n : ℕ in Filter.atTop,
      (25 * Real.log (n : ℝ) ^ 2 - 20 * Real.log (n : ℝ) + 4) /
          (2 * (n : ℝ)) ≤ 1 := by
  have hmajor : Filter.Tendsto
      (fun n : ℕ =>
        (25 / 2 : ℝ) * (Real.log (n : ℝ) ^ 2 / (n : ℝ)) +
          2 * ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_rodierLogSqDivNat.const_mul (25 / 2)).add
        (tendsto_rodierInvNat.const_mul 2)
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (25 / 2 : ℝ) * (Real.log (n : ℝ) ^ 2 / (n : ℝ)) +
          2 * ((1 : ℝ) / (n : ℝ)) < 1 :=
    hmajor.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with n hnsmall hn
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hremMajor :
      (25 * Real.log (n : ℝ) ^ 2 - 20 * Real.log (n : ℝ) + 4) /
          (2 * (n : ℝ)) ≤
        (25 / 2 : ℝ) * (Real.log (n : ℝ) ^ 2 / (n : ℝ)) +
          2 * ((1 : ℝ) / (n : ℝ)) := by
    calc
      _ ≤ (25 * Real.log (n : ℝ) ^ 2 + 4) / (2 * (n : ℝ)) := by
        apply (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * n)).2
        nlinarith
      _ = _ := by
        field_simp
        ring
  exact hremMajor.trans hnsmall.le

/-- At Rodier's threshold and transition scale, the normalized Gaussian
exponent loses at most five logarithmic powers and a fixed constant. -/
theorem eventually_rodierAsymptotic_gaussianExponent_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      (rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2 /
          (2 * rodierAsymptoticQ n) ≤
        (n : ℝ) * Real.log 2 - 5 * Real.log (n : ℝ) + 5 := by
  filter_upwards [eventually_rodierExponentRemainder_le_one,
    Filter.eventually_ge_atTop 1] with n hrem hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  let c : ℝ := Real.sqrt (2 * Real.log 2)
  have hc₁ : 1 ≤ c := by
    dsimp [c]
    rw [Real.one_le_sqrt]
    nlinarith [Real.log_two_gt_d9]
  have hc₂ : c ≤ 2 := by
    dsimp [c]
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.log_two_lt_d9]
  have hcsq : c ^ 2 = 2 * Real.log 2 := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  have hclog : Real.log (n : ℝ) ≤ c * Real.log (n : ℝ) :=
    by simpa using mul_le_mul_of_nonneg_right hc₁ hlog
  rw [rodierAsymptotic_gaussianExponent_eq hnpos]
  have hexpand :
      rodierAsymptoticExponentNumerator n ^ 2 / (2 * (n : ℝ)) =
        (n : ℝ) * Real.log 2 -
            5 * c * Real.log (n : ℝ) + 2 * c +
          (25 * Real.log (n : ℝ) ^ 2 -
              20 * Real.log (n : ℝ) + 4) / (2 * (n : ℝ)) := by
    unfold rodierAsymptoticExponentNumerator
    change
      ((n : ℝ) * c - 5 * Real.log (n : ℝ) + 2) ^ 2 /
          (2 * (n : ℝ)) = _
    calc
      _ = (((n : ℝ) ^ 2 * c ^ 2 -
              10 * (n : ℝ) * c * Real.log (n : ℝ) +
              4 * (n : ℝ) * c +
              25 * Real.log (n : ℝ) ^ 2 -
              20 * Real.log (n : ℝ) + 4) /
            (2 * (n : ℝ))) := by ring
      _ = _ := by
        rw [hcsq]
        field_simp [hnne]
        ring
  rw [hexpand]
  nlinarith

/-- Rodier's asymptotic cutoff parameters are eventually admissible. -/
theorem eventually_rodierAsymptotic_parameters :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < n ∧ 0 < rodierAsymptoticM n ∧
        0 < rodierAsymptoticDelta n ∧
          rodierAsymptoticDelta n ≤ rodierAsymptoticM n := by
  have hscaled : Filter.Tendsto
      (fun n : ℕ => 5 * (Real.log (n : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_rodierLogDivNat.const_mul 5
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      5 * (Real.log (n : ℝ) / (n : ℝ)) < (1 / 2 : ℝ) :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 2] with n hsmall hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (hn.trans' (by omega : 0 < 2))
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnℝTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnℝ
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnℝ.le
  have hsqrtqpos : 0 < Real.sqrt (rodierAsymptoticQ n) :=
    Real.sqrt_pos.2 (rodierAsymptoticQ_pos n)
  have hc : 1 ≤ Real.sqrt (2 * Real.log 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.log_two_gt_d9]
  let a : ℝ := Real.sqrt (2 * Real.log 2) -
    5 * Real.log (n : ℝ) / (n : ℝ)
  have hsmall' :
      5 * Real.log (n : ℝ) / (n : ℝ) < (1 / 2 : ℝ) := by
    calc
      _ = 5 * (Real.log (n : ℝ) / (n : ℝ)) := by ring
      _ < _ := hsmall
  have ha : (1 / 2 : ℝ) < a := by
    dsimp [a]
    nlinarith [hsmall']
  have hna : 1 ≤ (n : ℝ) * a := by
    nlinarith
  have hM : 0 < rodierAsymptoticM n := by
    unfold rodierAsymptoticM
    change 0 < Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) * a
    exact mul_pos (mul_pos hsqrtqpos hsqrtnpos) (by linarith [ha])
  have hΔ : 0 < rodierAsymptoticDelta n :=
    rodierAsymptoticDelta_pos hnpos
  have hΔM : rodierAsymptoticDelta n ≤ rodierAsymptoticM n := by
    rw [rodierAsymptoticDelta]
    apply (div_le_iff₀ hsqrtnpos).2
    calc
      Real.sqrt (rodierAsymptoticQ n) =
          Real.sqrt (rodierAsymptoticQ n) * 1 := by ring
      _ ≤ Real.sqrt (rodierAsymptoticQ n) * ((n : ℝ) * a) :=
        mul_le_mul_of_nonneg_left hna hsqrtqpos.le
      _ = rodierAsymptoticM n * Real.sqrt (n : ℝ) := by
        unfold rodierAsymptoticM
        change Real.sqrt (rodierAsymptoticQ n) * ((n : ℝ) * a) =
          Real.sqrt (rodierAsymptoticQ n) * Real.sqrt (n : ℝ) * a *
            Real.sqrt (n : ℝ)
        calc
          _ = Real.sqrt (rodierAsymptoticQ n) *
              (Real.sqrt (n : ℝ) ^ 2 * a) := by rw [hsqrtn]
          _ = _ := by ring
  exact ⟨hnpos, hM, hΔ, hΔM⟩

/-- The Gaussian factor at Rodier's cutoff center retains five powers of the
dimension beyond the cube-cardinality decay. -/
theorem eventually_rodierAsymptotic_exp_lower_bound :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-5) * (n : ℝ) ^ 5 / rodierAsymptoticQ n ≤
        Real.exp
          (-((rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2) /
            (2 * rodierAsymptoticQ n)) := by
  filter_upwards [eventually_rodierAsymptotic_gaussianExponent_le,
    Filter.eventually_ge_atTop 1] with n hexponent hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hidentity :
      Real.exp
          (-((n : ℝ) * Real.log 2 - 5 * Real.log (n : ℝ) + 5)) =
        Real.exp (-5) * (n : ℝ) ^ 5 / rodierAsymptoticQ n := by
    rw [rodierAsymptoticQ]
    calc
      _ = Real.exp (-5) * Real.exp (5 * Real.log (n : ℝ)) *
          Real.exp (-((n : ℝ) * Real.log 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-5) * (n : ℝ) ^ 5 * ((2 : ℝ) ^ n)⁻¹ := by
        rw [show 5 * Real.log (n : ℝ) =
              (5 : ℕ) * Real.log (n : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hnℝ,
          Real.exp_neg ((n : ℝ) * Real.log 2),
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = _ := by rw [div_eq_mul_inv]
  rw [← hidentity]
  apply Real.exp_le_exp.mpr
  simpa [neg_div] using neg_le_neg hexponent

/-- The Gaussian main term, multiplied by the number of Walsh characters,
eventually dominates a fixed positive multiple of `n⁵ / sqrt n`. -/
theorem eventually_rodierCutoffGaussianIntegral_scaled_lower_bound :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hM : 0 < rodierAsymptoticM n)
        (hΔ : 0 < rodierAsymptoticDelta n),
        Real.exp (-5) * (n : ℝ) ^ 5 /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) ≤
          rodierAsymptoticQ n *
            (rodierCutoffGaussianIntegral n
              (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).re := by
  filter_upwards [eventually_rodierAsymptotic_exp_lower_bound,
    Filter.eventually_ge_atTop 1] with n hexp hn
  intro hM hΔ
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hq : 0 < rodierAsymptoticQ n := rodierAsymptoticQ_pos n
  have hqne : rodierAsymptoticQ n ≠ 0 := ne_of_gt hq
  have hsqrtqne : Real.sqrt (rodierAsymptoticQ n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hsqrtnne : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnℝ)
  have hmain := rodierCutoffGaussianIntegral_re_lower_bound_oneSide n
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ
  have hpref : 0 ≤
      (Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ := by positivity
  have hΔnonneg : 0 ≤ rodierAsymptoticDelta n := hΔ.le
  have hreplace :
      (Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ *
            (Real.exp (-5) * (n : ℝ) ^ 5 / rodierAsymptoticQ n) *
          rodierAsymptoticDelta n ≤
        (Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ *
            Real.exp
              (-((rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2) /
                (2 * rodierAsymptoticQ n)) *
          rodierAsymptoticDelta n := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hpref) hΔnonneg
  have hmain' :
      (Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ *
            Real.exp
              (-((rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2) /
                (2 * rodierAsymptoticQ n)) *
          rodierAsymptoticDelta n ≤
        (rodierCutoffGaussianIntegral n
          (rodierAsymptoticM n) (rodierAsymptoticDelta n) hM hΔ).re := by
    simpa [rodierAsymptoticQ] using hmain
  calc
    Real.exp (-5) * (n : ℝ) ^ 5 /
          (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) =
        rodierAsymptoticQ n *
          ((Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ *
            (Real.exp (-5) * (n : ℝ) ^ 5 / rodierAsymptoticQ n) *
              rodierAsymptoticDelta n) := by
      rw [rodierAsymptoticDelta,
        show 2 * Real.pi * rodierAsymptoticQ n =
          (2 * Real.pi) * rodierAsymptoticQ n by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      field_simp [hqne, hsqrtqne, hsqrtnne]
    _ ≤ rodierAsymptoticQ n *
        ((Real.sqrt (2 * Real.pi * rodierAsymptoticQ n))⁻¹ *
            Real.exp
              (-((rodierAsymptoticM n + 2 * rodierAsymptoticDelta n) ^ 2) /
                (2 * rodierAsymptoticQ n)) *
          rodierAsymptoticDelta n) :=
      mul_le_mul_of_nonneg_left hreplace hq.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain' hq.le

theorem tendsto_rodierScaledGaussianLower_atTop :
    Filter.Tendsto
      (fun n : ℕ => Real.exp (-5) * (n : ℝ) ^ 5 /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)))
      Filter.atTop Filter.atTop := by
  let C : ℝ := Real.exp (-5) / Real.sqrt (2 * Real.pi)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hnTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hnFour : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 4)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [hnTop.eventually (Filter.eventually_ge_atTop b),
      Filter.eventually_ge_atTop 1] with n hnb hn
    have hnℝ : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact hnb.trans (by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - n)])
  have hpoly : Filter.Tendsto (fun n : ℕ => C * (n : ℝ) ^ 4)
      Filter.atTop Filter.atTop := hnFour.const_mul_atTop hC
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hpoly
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnℝ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsqrtLe : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hnℝ.trans' (by norm_num)
    · nlinarith
  dsimp [C]
  rw [show Real.exp (-5) * (n : ℝ) ^ 5 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ)) =
      (Real.exp (-5) / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ 5 /
        Real.sqrt (n : ℝ) by ring]
  rw [le_div_iff₀ hsqrtPos]
  have hconst : 0 ≤ Real.exp (-5) / Real.sqrt (2 * Real.pi) := by positivity
  calc
    (Real.exp (-5) / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ 4 *
        Real.sqrt (n : ℝ) ≤
      (Real.exp (-5) / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ 4 *
        (n : ℝ) := by gcongr
    _ = (Real.exp (-5) / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ 5 := by ring

end CryptBoolean
