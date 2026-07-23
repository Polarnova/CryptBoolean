/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.RodierGaussianMainTerm

/-!
# Rodier's sharp random-nonlinearity interval

Finite second-moment and no-hit bridges from the smoothed cutoff estimates to
Rodier's lower spectral-amplitude probability.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal Topology

namespace CryptBoolean

variable {n : ℕ}

local instance rodierSharpSignMeasurableSpace : MeasurableSpace FABL.Sign := ⊤

local instance rodierSharpSignMeasurableSingletonClass :
    MeasurableSingletonClass FABL.Sign where
  measurableSet_singleton _ := by simp

/-- A raw Walsh coefficient is `2^n` times FABL's normalized coefficient. -/
theorem rodierRawWalshCoefficient_eq_card_mul_fourierCoeff
    (S : Finset (Fin n)) (f : FABL.BooleanFunction n) :
    rodierRawWalshCoefficient S f =
      (2 : ℝ) ^ n * FABL.fourierCoeff f.toReal S := by
  rw [rodierRawWalshCoefficient, FABL.fourierCoeff,
    Fintype.expect_eq_sum_div_card]
  have hcard : (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, FABL.Sign]
  rw [hcard]
  simp only [FABL.BooleanFunction.toReal]
  field_simp

/-- If every normalized Fourier coefficient is at most `M / 2^n`, Rodier's
smoothed exceedance fraction vanishes. -/
theorem fourierInfinityNorm_le_rawCutoff_subset_average_eq_zero
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) :
    {f : FABL.BooleanFunction n |
        FABL.fourierInfinityNorm f.toReal ≤ M / (2 : ℝ) ^ n} ⊆
      {f | rodierCutoffFrequencyAverage M Δ f = 0} := by
  intro f hf
  change rodierCutoffFrequencyAverage M Δ f = 0
  rw [rodierCutoffFrequencyAverage, Fintype.expect_eq_sum_div_card]
  have hq : 0 < (2 : ℝ) ^ n := by positivity
  have hzero (S : Finset (Fin n)) :
      rodierCutoff M Δ (rodierRawWalshCoefficient S f) = 0 := by
    apply rodierCutoff_eq_zero_of_abs_le hM hΔ
    rw [rodierRawWalshCoefficient_eq_card_mul_fourierCoeff,
      abs_mul, abs_of_pos hq]
    calc
      (2 : ℝ) ^ n * |FABL.fourierCoeff f.toReal S| ≤
          (2 : ℝ) ^ n * FABL.fourierInfinityNorm f.toReal := by
        gcongr
        unfold FABL.fourierInfinityNorm
        exact Finset.le_sup' (fun T : Finset (Fin n) ↦
          |FABL.fourierCoeff f.toReal T|) (Finset.mem_univ S)
      _ ≤ (2 : ℝ) ^ n * (M / (2 : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hq.le
        simpa only [Set.mem_setOf_eq] using hf
      _ = M := by field_simp
  simp_rw [hzero]
  simp

/-- The one-coordinate remainder after retaining the quartic Gaussian
correction. -/
noncomputable def rodierSingleQuarticRemainder
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℝ :=
  (3 * (2 : ℝ) ^ n) *
      (∫ t : ℝ, |t| ^ 6 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
    (3 * ((2 : ℝ) ^ n) ^ 2) *
      (∫ t : ℝ, |t| ^ 8 * ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)

/-- The two-coordinate remainder after retaining the quartic Gaussian
correction. -/
noncomputable def rodierPairQuarticRemainder
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℝ :=
  2 * rodierSingleQuarticRemainder n M Δ hM hΔ +
    (3 * (2 : ℝ) ^ n) *
      (64 * (∫ t : ℝ, |t| ^ 6 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
        ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) +
    (3 * ((2 : ℝ) ^ n) ^ 2) *
      (256 * (∫ t : ℝ, |t| ^ 8 *
          ‖rodierCutoffFourierDensity M Δ hM hΔ t‖) *
        ∫ t : ℝ, ‖rodierCutoffFourierDensity M Δ hM hΔ t‖)

/-- A uniform off-diagonal error combining the pair remainder, the two
quartic cross terms, and the single-coordinate square error. -/
noncomputable def rodierOffDiagonalPairError
    (n : ℕ) (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) : ℝ :=
  let c : ℝ := (2 : ℝ) ^ n / 12
  let A₂ := rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ
  let A₄ := rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ
  let G := rodierCutoffGaussianIntegral n M Δ hM hΔ
  let R₁ := rodierSingleQuarticRemainder n M Δ hM hΔ
  rodierPairQuarticRemainder n M Δ hM hΔ +
    6 * c * ‖A₂‖ ^ 2 + c ^ 2 * ‖A₄‖ ^ 2 +
    R₁ * (2 * ‖G - (c : ℂ) * A₄‖ + R₁)

/-- The refined single- and pair-cutoff estimates give a uniform
off-diagonal pair bound. -/
theorem rodierPairCutoffExpectation_re_le_single_sq_add_offDiagonalPairError
    (hn : 0 < n) (S₀ : Finset (Fin n)) {S T : Finset (Fin n)} (hST : S ≠ T)
    (M Δ : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hΔM : Δ ≤ M) :
    (rodierPairCutoffExpectation S T M Δ).re ≤
      (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 +
        rodierOffDiagonalPairError n M Δ hM hΔ := by
  let q : ℝ := (2 : ℝ) ^ n
  let c : ℝ := q / 12
  let G : ℂ := rodierCutoffGaussianIntegral n M Δ hM hΔ
  let A₂ : ℂ := rodierGaussianWeightedDensityMoment n 2 M Δ hM hΔ
  let A₄ : ℂ := rodierGaussianWeightedDensityMoment n 4 M Δ hM hΔ
  let C : ℂ := G - (c : ℂ) * A₄
  let P : ℂ := rodierPairCutoffExpectation S T M Δ
  let E : ℂ := rodierSingleCutoffExpectation S₀ M Δ
  let R₁ : ℝ := rodierSingleQuarticRemainder n M Δ hM hΔ
  let R₂ : ℝ := rodierPairQuarticRemainder n M Δ hM hΔ
  let center : ℂ := G ^ 2 - (c : ℂ) *
    (2 * A₄ * G + 6 * A₂ ^ 2)
  have hc : 0 ≤ c := by dsimp [c, q]; positivity
  have hR₁ : 0 ≤ R₁ := by
    dsimp [R₁, rodierSingleQuarticRemainder]
    positivity
  have hpair :=
    norm_rodierPairCutoffExpectation_sub_quarticGaussianIntegral_sq_le_moments
      hn hST M Δ hM hΔ hΔM
  have hP : ‖P - center‖ ≤ R₂ := by
    simpa [P, center, R₂, rodierPairQuarticRemainder,
      rodierSingleQuarticRemainder, q, c, G, A₂, A₄] using hpair
  have hsingle :=
    norm_rodierSingleCutoffExpectation_sub_quarticGaussianIntegral_le
      hn S₀ M Δ hM hΔ hΔM
  have hE : ‖E - C‖ ≤ R₁ := by
    simpa [E, C, R₁, rodierSingleQuarticRemainder, q, c, G, A₄] using hsingle
  have hcenterEq : center - C ^ 2 =
      -(6 : ℂ) * (c : ℂ) * A₂ ^ 2 - (c : ℂ) ^ 2 * A₄ ^ 2 := by
    dsimp [center, C]
    ring
  have hcenter : ‖center - C ^ 2‖ ≤
      6 * c * ‖A₂‖ ^ 2 + c ^ 2 * ‖A₄‖ ^ 2 := by
    rw [hcenterEq]
    calc
      _ ≤ ‖-(6 : ℂ) * (c : ℂ) * A₂ ^ 2‖ +
          ‖(c : ℂ) ^ 2 * A₄ ^ 2‖ := norm_sub_le _ _
      _ = _ := by
        simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hc]
        norm_num
  have hEnorm : ‖E‖ ≤ ‖C‖ + R₁ := by
    calc
      ‖E‖ = ‖C + (E - C)‖ := by ring_nf
      _ ≤ ‖C‖ + ‖E - C‖ := norm_add_le _ _
      _ ≤ ‖C‖ + R₁ := add_le_add (le_refl _) hE
  have hsquare : ‖C ^ 2 - E ^ 2‖ ≤
      R₁ * (2 * ‖C‖ + R₁) := by
    rw [show C ^ 2 - E ^ 2 = (C - E) * (C + E) by ring, norm_mul]
    calc
      ‖C - E‖ * ‖C + E‖ ≤ R₁ * (‖C‖ + ‖E‖) := by
        gcongr
        · simpa [norm_sub_rev] using hE
        · exact norm_add_le _ _
      _ ≤ R₁ * (‖C‖ + (‖C‖ + R₁)) := by gcongr
      _ = _ := by ring
  have htotal : ‖P - E ^ 2‖ ≤
      R₂ + (6 * c * ‖A₂‖ ^ 2 + c ^ 2 * ‖A₄‖ ^ 2) +
        R₁ * (2 * ‖C‖ + R₁) := by
    calc
      ‖P - E ^ 2‖ =
          ‖(P - center) + ((center - C ^ 2) + (C ^ 2 - E ^ 2))‖ := by
        ring_nf
      _ ≤ ‖P - center‖ + ‖(center - C ^ 2) + (C ^ 2 - E ^ 2)‖ :=
        norm_add_le _ _
      _ ≤ ‖P - center‖ +
          (‖center - C ^ 2‖ + ‖C ^ 2 - E ^ 2‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ R₂ +
          ((6 * c * ‖A₂‖ ^ 2 + c ^ 2 * ‖A₄‖ ^ 2) +
            R₁ * (2 * ‖C‖ + R₁)) := by
        gcongr
      _ = _ := by ring
  have hEreal : ((E.re : ℝ) : ℂ) = E := by
    dsimp [E]
    rw [← ofReal_expect_rodierCutoff_eq_singleCutoffExpectation S₀ M Δ]
    simp
  have hre : P.re - E.re ^ 2 ≤ ‖P - E ^ 2‖ := by
    calc
      P.re - E.re ^ 2 = (P - E ^ 2).re := by
        rw [← hEreal]
        norm_cast
      _ ≤ |(P - E ^ 2).re| := le_abs_self _
      _ ≤ ‖P - E ^ 2‖ := Complex.abs_re_le_norm _
  change (rodierPairCutoffExpectation S T M Δ).re ≤
    (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 +
      rodierOffDiagonalPairError n M Δ hM hΔ
  rw [show rodierOffDiagonalPairError n M Δ hM hΔ =
      R₂ + 6 * c * ‖A₂‖ ^ 2 + c ^ 2 * ‖A₄‖ ^ 2 +
        R₁ * (2 * ‖C‖ + R₁) by
    dsimp [rodierOffDiagonalPairError, R₂, R₁, C, G, A₂, A₄, c, q]]
  linarith

/-- The Chebyshev failure ratio attached to a one-coordinate mean and a
uniform off-diagonal pair error. -/
noncomputable def rodierSecondMomentFailureBound
    (n : ℕ) (S₀ : Finset (Fin n)) (M Δ ε : ℝ) : ℝ :=
  ((rodierSingleCutoffExpectation S₀ M Δ).re / (2 : ℝ) ^ n + ε) /
    (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2

/-- The finite second-moment estimate bounds the lower spectral event. -/
theorem measure_fourierInfinityNorm_le_rawCutoff_le_secondMomentFailureBound
    (S₀ : Finset (Fin n))
    (M Δ ε : ℝ) (hM : 0 < M) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (he : 0 < (rodierSingleCutoffExpectation S₀ M Δ).re)
    (hpair : ∀ S T : Finset (Fin n), S ≠ T →
      (rodierPairCutoffExpectation S T M Δ).re ≤
        (rodierSingleCutoffExpectation S₀ M Δ).re ^ 2 + ε) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | FABL.fourierInfinityNorm f.toReal ≤ M / (2 : ℝ) ^ n} ≤
      rodierSecondMomentFailureBound n S₀ M Δ ε := by
  calc
    _ ≤ (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | rodierCutoffFrequencyAverage M Δ f = 0} :=
      measureReal_mono
        (fourierInfinityNorm_le_rawCutoff_subset_average_eq_zero M Δ hM hΔ)
    _ ≤ _ := by
      simpa [rodierSecondMomentFailureBound] using
        measure_rodierCutoffFrequencyAverage_eq_zero_le
          S₀ M Δ ε hM hΔ hε he hpair

/-- The second-moment failure ratio at Rodier's asymptotic cutoff scale. -/
noncomputable def rodierAsymptoticSecondMomentFailureBound
    (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  rodierSecondMomentFailureBound n ∅
    (rodierAsymptoticM n) (rodierAsymptoticDelta n) (ε n)

/-- The finite no-hit bound gives a lower bound for Rodier's spectral event. -/
theorem one_sub_rodierAsymptoticSecondMomentFailureBound_le_fourierLowerProbability
    {n : ℕ} (hn : 0 < n) (hM : 0 < rodierAsymptoticM n)
    (ε : ℕ → ℝ) (hε : 0 ≤ ε n)
    (he : 0 < (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
      (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re)
    (hpair : ∀ S T : Finset (Fin n), S ≠ T →
      (rodierPairCutoffExpectation S T
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ≤
      (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ^ 2 + ε n) :
    1 - rodierAsymptoticSecondMomentFailureBound ε n ≤
      rodierRandomFourierLowerProbability n := by
  let μ := (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure
  let bad : Set (FABL.BooleanFunction n) :=
    {f | FABL.fourierInfinityNorm f.toReal ≤ rodierRandomFourierLowerThreshold n}
  let good : Set (FABL.BooleanFunction n) :=
    {f | rodierRandomFourierLowerThreshold n < FABL.fourierInfinityNorm f.toReal}
  have hdiv : rodierAsymptoticM n / (2 : ℝ) ^ n =
      rodierRandomFourierLowerThreshold n := by
    rw [rodierAsymptoticM_eq_q_mul_threshold, rodierAsymptoticQ]
    field_simp
  have hbad : μ.real bad ≤ rodierAsymptoticSecondMomentFailureBound ε n := by
    dsimp only [μ, bad, rodierAsymptoticSecondMomentFailureBound]
    rw [← hdiv]
    exact measure_fourierInfinityNorm_le_rawCutoff_le_secondMomentFailureBound
      (∅ : Finset (Fin n))
      (rodierAsymptoticM n) (rodierAsymptoticDelta n) (ε n)
      hM (rodierAsymptoticDelta_pos hn) hε he hpair
  have hcompl : badᶜ ⊆ good := by
    intro f hf
    simpa [bad, good] using hf
  calc
    1 - rodierAsymptoticSecondMomentFailureBound ε n ≤ 1 - μ.real bad :=
      sub_le_sub_left hbad 1
    _ = μ.real badᶜ := by
      rw [measureReal_compl (Set.toFinite bad).measurableSet]
      simp
    _ ≤ μ.real good := measureReal_mono hcompl
    _ = rodierRandomFourierLowerProbability n := by
      rfl

/-- An asymptotically vanishing second-moment ratio closes Rodier's lower
spectral tail. -/
theorem tendsto_rodierRandomFourierLowerProbability_of_secondMoment
    (ε : ℕ → ℝ)
    (hM : ∀ᶠ n in Filter.atTop, 0 < rodierAsymptoticM n)
    (hε : ∀ᶠ n in Filter.atTop, 0 ≤ ε n)
    (he : ∀ᶠ n in Filter.atTop,
      0 < (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re)
    (hpair : ∀ᶠ n in Filter.atTop, ∀ S T : Finset (Fin n), S ≠ T →
      (rodierPairCutoffExpectation S T
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ≤
      (rodierSingleCutoffExpectation (∅ : Finset (Fin n))
        (rodierAsymptoticM n) (rodierAsymptoticDelta n)).re ^ 2 + ε n)
    (hbound : Filter.Tendsto (rodierAsymptoticSecondMomentFailureBound ε)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto rodierRandomFourierLowerProbability
      Filter.atTop (nhds 1) := by
  have hlower : Filter.Tendsto
      (fun n => 1 - rodierAsymptoticSecondMomentFailureBound ε n)
      Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using hbound.const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 1, hM, hε, he, hpair] with
      n hn hnM hnε hne hnpair
    exact
      one_sub_rodierAsymptoticSecondMomentFailureBound_le_fourierLowerProbability
        (Nat.zero_lt_of_lt hn) hnM ε hnε hne hnpair
  · exact Filter.Eventually.of_forall fun n => by
      unfold rodierRandomFourierLowerProbability
      exact measureReal_le_one

end CryptBoolean
