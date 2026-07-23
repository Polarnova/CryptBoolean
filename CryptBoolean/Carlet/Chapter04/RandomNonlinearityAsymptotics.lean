/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import FABL.Chapter05.RandomBooleanFourierMaximum
public import FABL.Chapter06.F₂Polynomials.Encoding
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Carlet Chapter 4 random nonlinearity asymptotics

The Olejár--Stanek asymptotic lower bound and the Hoeffding side of Rodier's
sharp random-function interval.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal Topology

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

local instance randomNonlinearitySignMeasurableSpace : MeasurableSpace FABL.Sign := ⊤

local instance randomNonlinearitySignMeasurableSingletonClass :
    MeasurableSingletonClass FABL.Sign where
  measurableSet_singleton _ := by simp

/-- The normalized Fourier threshold corresponding to Carlet's displayed
nonlinearity threshold. -/
noncomputable def carletRandomFourierThreshold (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ)) * (2 : ℝ) ^ (-(n : ℝ) / 2)

/-- Carlet's displayed lower threshold
`2^(n-1) - sqrt(n) * 2^((n-1)/2)`, in an algebraically convenient form. -/
noncomputable def carletRandomNonlinearityThreshold (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / 2 -
    (2 : ℝ) ^ n * carletRandomFourierThreshold n / 2

/-- The implementation threshold is exactly Carlet's typography
`2^(n-1) - sqrt(n) * 2^((n-1)/2)`. -/
theorem carletRandomNonlinearityThreshold_eq_displayed (n : ℕ) :
    carletRandomNonlinearityThreshold n =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        Real.sqrt (n : ℝ) * (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have hfirst :
      (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast]
    simpa using
      (Real.rpow_sub (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
        (n : ℝ) 1).symm
  have hsqrt :
      Real.sqrt (2 * (n : ℝ)) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (2 * (n : ℝ)) =
          Real.sqrt 2 * Real.sqrt (n : ℝ) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow]
  have hpow :
      (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ (-1 : ℝ) =
        (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hdelta :
      (2 : ℝ) ^ n * carletRandomFourierThreshold n / 2 =
        Real.sqrt (n : ℝ) * (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
    rw [carletRandomFourierThreshold, hsqrt, ← Real.rpow_natCast,
      div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      (2 : ℝ) ^ (n : ℝ) *
            ((2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) *
              (2 : ℝ) ^ (-(n : ℝ) / 2)) *
          (2 : ℝ) ^ (-1 : ℝ) =
          Real.sqrt (n : ℝ) *
            ((2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) *
              (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 : ℝ) ^ (-1 : ℝ)) := by
        ring
      _ = Real.sqrt (n : ℝ) *
          (2 : ℝ) ^ (((n : ℝ) - 1) / 2) := by
        rw [hpow]
  rw [carletRandomNonlinearityThreshold, hfirst, hdelta]

private def randomNonlinearityParitySign
    (S : Finset (Fin n)) (x : {−1,1}^[n]) : FABL.Sign :=
  ∏ i ∈ S, x i

private theorem signValue_randomNonlinearityParitySign
    (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    FABL.signValue (randomNonlinearityParitySign S x) = FABL.monomial S x := by
  simp [randomNonlinearityParitySign, FABL.monomial, FABL.signValue]

private theorem signValue_mul (a b : FABL.Sign) :
    FABL.signValue (a * b) = FABL.signValue a * FABL.signValue b := by
  simp [FABL.signValue]

private noncomputable def randomNonlinearityCoefficientSampleEquiv
    (n : ℕ) (S : Finset (Fin n)) :
    FABL.BooleanFunction n ≃
      (Fin (Fintype.card ({−1,1}^[n])) → FABL.Sign) :=
  (Equiv.arrowCongr
      (Fintype.equivFin ({−1,1}^[n])) (Equiv.refl FABL.Sign)).trans
    (Equiv.mulRight fun i ↦
      randomNonlinearityParitySign S
        ((Fintype.equivFin ({−1,1}^[n])).symm i))

private theorem finiteUniformEmpiricalMean_randomNonlinearityCoefficientSampleEquiv
    (S : Finset (Fin n)) (f : FABL.BooleanFunction n) :
    FABL.finiteUniformEmpiricalMean FABL.signValue
        (randomNonlinearityCoefficientSampleEquiv n S f) =
      FABL.fourierCoeff f.toReal S := by
  classical
  rw [FABL.fourierCoeff, Fintype.expect_eq_sum_div_card]
  unfold FABL.finiteUniformEmpiricalMean
  congr 1
  symm
  apply Fintype.sum_equiv (Fintype.equivFin ({−1,1}^[n]))
  intro x
  simp [randomNonlinearityCoefficientSampleEquiv, Equiv.arrowCongr,
    FABL.BooleanFunction.toReal, signValue_mul,
    signValue_randomNonlinearityParitySign]

private theorem expect_signValue_eq_zero :
    Finset.expect Finset.univ FABL.signValue = 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [FABL.Sign, FABL.signValue]

private theorem signValue_mem_Icc (s : FABL.Sign) :
    FABL.signValue s ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [FABL.signValue]

private theorem measure_fourierCoeff_ge_le
    (S : Finset (Fin n)) (ε : ℝ) (hε : 0 ≤ ε) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | ε ≤ |FABL.fourierCoeff f.toReal S|} ≤
      2 * Real.exp
        (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2) := by
  classical
  let m := Fintype.card ({−1,1}^[n])
  let e := randomNonlinearityCoefficientSampleEquiv n S
  let failure : Set (Fin m → FABL.Sign) :=
    {samples | ε ≤ |FABL.finiteUniformEmpiricalMean FABL.signValue samples|}
  have h :=
    FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le
      FABL.signValue signValue_mem_Icc (m := m) Fintype.card_pos ε hε
  rw [expect_signValue_eq_zero] at h
  simp only [sub_zero] at h
  change (FABL.uniformPMF (Fin m → FABL.Sign)).toMeasure.real failure ≤ _ at h
  have hmap :
      (FABL.uniformPMF (FABL.BooleanFunction n)).map e =
        FABL.uniformPMF (Fin m → FABL.Sign) :=
    FABL.map_uniformPMF_equiv e
  rw [← hmap] at h
  have hmeasure :
      ((FABL.uniformPMF (FABL.BooleanFunction n)).map e).toMeasure.real failure =
        (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real (e ⁻¹' failure) := by
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_map_apply e _ failure (measurable_of_finite e)
        (Set.toFinite failure).measurableSet)
  rw [hmeasure] at h
  simpa [m, e, failure,
    finiteUniformEmpiricalMean_randomNonlinearityCoefficientSampleEquiv] using h

theorem carletRandomFourierThreshold_nonneg (n : ℕ) :
    0 ≤ carletRandomFourierThreshold n := by
  unfold carletRandomFourierThreshold
  exact mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by norm_num) _)

theorem card_mul_carletRandomFourierThreshold_sq_div_two (n : ℕ) :
    (Fintype.card ({−1,1}^[n]) : ℝ) *
        carletRandomFourierThreshold n ^ 2 / 2 = (n : ℝ) := by
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, FABL.Sign]
  have hsqrt : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hrpow :
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
    calc
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 =
          (2 : ℝ) ^ ((-(n : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (x := (2 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 2) (-(n : ℝ) / 2) 2).symm
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        congr 1
        norm_num
      _ = ((2 : ℝ) ^ n)⁻¹ := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_neg (x := (2 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ))
  rw [hcard, carletRandomFourierThreshold, mul_pow, hsqrt, hrpow]
  field_simp

private theorem fourierMaximumBad_subset (n : ℕ) (ε : ℝ) :
    {f : FABL.BooleanFunction n | ε ≤ FABL.fourierInfinityNorm f.toReal} ⊆
      ⋃ S : Finset (Fin n),
        {f : FABL.BooleanFunction n |
          ε ≤ |FABL.fourierCoeff f.toReal S|} := by
  intro f hf
  change ε ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun S : Finset (Fin n) ↦ |FABL.fourierCoeff f.toReal S|) at hf
  rw [Finset.le_sup'_iff] at hf
  obtain ⟨S, _, hS⟩ := hf
  exact Set.mem_iUnion.2 ⟨S, hS⟩

private theorem measure_fourierInfinityNorm_ge_le
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | ε ≤ FABL.fourierInfinityNorm f.toReal} ≤
      (2 : ℝ) ^ n *
        (2 * Real.exp
          (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2)) := by
  have hcard :
      (Fintype.card (Finset (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_finset]
  calc
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | ε ≤ FABL.fourierInfinityNorm f.toReal} ≤
        (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
          (⋃ S : Finset (Fin n),
            {f : FABL.BooleanFunction n |
              ε ≤ |FABL.fourierCoeff f.toReal S|}) :=
      measureReal_mono (fourierMaximumBad_subset n ε)
    _ ≤ ∑ S : Finset (Fin n),
        (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
          {f : FABL.BooleanFunction n |
            ε ≤ |FABL.fourierCoeff f.toReal S|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _S : Finset (Fin n),
        2 * Real.exp
          (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro S _
      exact measure_fourierCoeff_ge_le S ε hε
    _ = (Fintype.card (Finset (Fin n)) : ℝ) *
        (2 * Real.exp
          (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2)) := by
      simp [nsmul_eq_mul]
    _ = (2 : ℝ) ^ n *
        (2 * Real.exp
          (-(Fintype.card ({−1,1}^[n]) : ℝ) * ε ^ 2 / 2)) := by
      rw [hcard]

/-- The finite Hoeffding--union-bound estimate at the exact threshold needed by
Carlet's asymptotic nonlinearity statement. -/
theorem measure_fourierInfinityNorm_ge_carletThreshold_le (n : ℕ) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | carletRandomFourierThreshold n ≤
          FABL.fourierInfinityNorm f.toReal} ≤
      (2 : ℝ) ^ n * (2 * Real.exp (-(n : ℝ))) := by
  have h := measure_fourierInfinityNorm_ge_le n
    (carletRandomFourierThreshold n)
    (carletRandomFourierThreshold_nonneg n)
  rw [show
      -(Fintype.card ({−1,1}^[n]) : ℝ) *
            carletRandomFourierThreshold n ^ 2 / 2 = -(n : ℝ) by
        rw [show
          -(Fintype.card ({−1,1}^[n]) : ℝ) *
                carletRandomFourierThreshold n ^ 2 / 2 =
              -((Fintype.card ({−1,1}^[n]) : ℝ) *
                carletRandomFourierThreshold n ^ 2 / 2) by ring,
          card_mul_carletRandomFourierThreshold_sq_div_two]] at h
  exact h

/-- Rodier's upper spectral-amplitude threshold, normalized as a FABL Fourier
coefficient. -/
noncomputable def rodierRandomFourierUpperThreshold (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (Real.sqrt (2 * Real.log 2) +
      4 * Real.log (n : ℝ) / (n : ℝ)) *
    (2 : ℝ) ^ (-(n : ℝ) / 2)

/-- The lower endpoint of Rodier's nonlinearity interval. -/
noncomputable def rodierRandomNonlinearityLowerThreshold (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / 2 -
    (2 : ℝ) ^ n * rodierRandomFourierUpperThreshold n / 2

/-- Rodier's lower nonlinearity endpoint in the displayed source
normalization. -/
theorem rodierRandomNonlinearityLowerThreshold_eq_displayed (n : ℕ) :
    rodierRandomNonlinearityLowerThreshold n =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) * Real.sqrt (n : ℝ) *
          (Real.sqrt (2 * Real.log 2) +
            4 * Real.log (n : ℝ) / (n : ℝ)) := by
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
  rw [rodierRandomNonlinearityLowerThreshold,
    rodierRandomFourierUpperThreshold, hfirst]
  rw [show
    (2 : ℝ) ^ n *
          (Real.sqrt (n : ℝ) *
            (Real.sqrt (2 * Real.log 2) +
              4 * Real.log (n : ℝ) / (n : ℝ)) *
            (2 : ℝ) ^ (-(n : ℝ) / 2)) /
        2 =
      ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ) / 2) / 2) *
        Real.sqrt (n : ℝ) *
          (Real.sqrt (2 * Real.log 2) +
            4 * Real.log (n : ℝ) / (n : ℝ)) by ring,
    hscale]

theorem rodierRandomFourierUpperThreshold_nonneg (n : ℕ) :
    0 ≤ rodierRandomFourierUpperThreshold n := by
  unfold rodierRandomFourierUpperThreshold
  positivity

theorem card_mul_rodierRandomFourierUpperThreshold_sq_div_two_ge
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 2 + Real.log (n : ℝ) ≤
      (Fintype.card ({−1,1}^[n]) : ℝ) *
        rodierRandomFourierUpperThreshold n ^ 2 / 2 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnone : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hc : 1 ≤ Real.sqrt (2 * Real.log 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.log_two_gt_d9]
  have hc' : 1 ≤ Real.sqrt (Real.log 2 * 2) := by
    simpa [mul_comm] using hc
  have hcard :
      (Fintype.card ({−1,1}^[n]) : ℝ) = (2 : ℝ) ^ n := by
    norm_num [Fintype.card_pi, FABL.Sign]
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnpos.le
  have hlogsqrt :
      Real.sqrt (Real.log 2 * 2) ^ 2 = Real.log 2 * 2 := by
    simpa [mul_comm] using
      (Real.sq_sqrt (show 0 ≤ 2 * Real.log 2 by positivity))
  have hrpow :
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
    calc
      ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 =
          (2 : ℝ) ^ ((-(n : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast (x := (2 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 2) (-(n : ℝ) / 2) 2).symm
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        congr 1
        norm_num
      _ = ((2 : ℝ) ^ n)⁻¹ := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_neg (x := (2 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ))
  rw [hcard, rodierRandomFourierUpperThreshold, mul_pow, mul_pow,
    hsqrt, hrpow]
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  field_simp
  have hcorr :
      0 ≤ 8 * Real.sqrt (Real.log 2 * 2) - 2 := by
    nlinarith
  have hmain :
      0 ≤ (n : ℝ) * Real.log (n : ℝ) *
          (8 * Real.sqrt (Real.log 2 * 2) - 2) +
        16 * Real.log (n : ℝ) ^ 2 :=
    add_nonneg
      (mul_nonneg (mul_nonneg hnpos.le hlog) hcorr)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hid :
      ((n : ℝ) * Real.sqrt (Real.log 2 * 2) +
          Real.log (n : ℝ) * 4) ^ 2 -
          (n : ℝ) * ((n : ℝ) * Real.log 2 + Real.log (n : ℝ)) * 2 =
        (n : ℝ) * Real.log (n : ℝ) *
            (8 * Real.sqrt (Real.log 2 * 2) - 2) +
          16 * Real.log (n : ℝ) ^ 2 := by
    calc
      _ = (n : ℝ) ^ 2 *
            (Real.sqrt (Real.log 2 * 2) ^ 2 - Real.log 2 * 2) +
          (n : ℝ) * Real.log (n : ℝ) *
            (8 * Real.sqrt (Real.log 2 * 2) - 2) +
          16 * Real.log (n : ℝ) ^ 2 := by ring
      _ = _ := by rw [hlogsqrt]; ring
  exact sub_nonneg.mp (by rw [hid]; exact hmain)

/-- A finite Hoeffding--union-bound estimate for the easy side of Rodier's
sharp interval. -/
theorem measure_fourierInfinityNorm_ge_rodierUpperThreshold_le
    {n : ℕ} (hn : 1 ≤ n) :
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | rodierRandomFourierUpperThreshold n ≤
          FABL.fourierInfinityNorm f.toReal} ≤
      2 * (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpow : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ n = Real.exp (Real.log 2) ^ n := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((n : ℝ) * Real.log 2) :=
        (Real.exp_nat_mul (Real.log 2) n).symm
  calc
    (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
        {f | rodierRandomFourierUpperThreshold n ≤
          FABL.fourierInfinityNorm f.toReal} ≤
        (2 : ℝ) ^ n *
          (2 * Real.exp
            (-(Fintype.card ({−1,1}^[n]) : ℝ) *
              rodierRandomFourierUpperThreshold n ^ 2 / 2)) :=
      measure_fourierInfinityNorm_ge_le n
        (rodierRandomFourierUpperThreshold n)
        (rodierRandomFourierUpperThreshold_nonneg n)
    _ ≤ (2 : ℝ) ^ n *
        (2 * Real.exp
          (-((n : ℝ) * Real.log 2 + Real.log (n : ℝ)))) := by
      gcongr
      rw [show
        -(Fintype.card ({−1,1}^[n]) : ℝ) *
              rodierRandomFourierUpperThreshold n ^ 2 / 2 =
            -((Fintype.card ({−1,1}^[n]) : ℝ) *
              rodierRandomFourierUpperThreshold n ^ 2 / 2) by ring]
      exact neg_le_neg <|
        card_mul_rodierRandomFourierUpperThreshold_sq_div_two_ge hn
    _ = 2 * (n : ℝ)⁻¹ := by
      rw [hpow]
      calc
        Real.exp ((n : ℝ) * Real.log 2) *
            (2 * Real.exp
              (-((n : ℝ) * Real.log 2 + Real.log (n : ℝ)))) =
            2 * Real.exp
              ((n : ℝ) * Real.log 2 -
                ((n : ℝ) * Real.log 2 + Real.log (n : ℝ))) := by
          rw [show
            (n : ℝ) * Real.log 2 -
                ((n : ℝ) * Real.log 2 + Real.log (n : ℝ)) =
              (n : ℝ) * Real.log 2 +
                -((n : ℝ) * Real.log 2 + Real.log (n : ℝ)) by ring,
            Real.exp_add]
          ring
        _ = 2 * (n : ℝ)⁻¹ := by
          rw [show
            (n : ℝ) * Real.log 2 -
                ((n : ℝ) * Real.log 2 + Real.log (n : ℝ)) =
              -Real.log (n : ℝ) by ring,
            Real.exp_neg, Real.exp_log hnpos]

/-- A summable-rate surrogate is unnecessary for convergence in probability;
this explicit bound already vanishes. -/
noncomputable def rodierRandomNonlinearityLowerFailureBound (n : ℕ) : ℝ :=
  2 * (n : ℝ)⁻¹

theorem tendsto_rodierRandomNonlinearityLowerFailureBound :
    Filter.Tendsto rodierRandomNonlinearityLowerFailureBound
      Filter.atTop (nhds 0) := by
  unfold rodierRandomNonlinearityLowerFailureBound
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

/-- The finite failure bound in geometric form. -/
noncomputable def carletRandomNonlinearityFailureBound (n : ℕ) : ℝ :=
  2 * (2 / Real.exp 1) ^ n

theorem fourier_union_bound_eq_failureBound (n : ℕ) :
    (2 : ℝ) ^ n * (2 * Real.exp (-(n : ℝ))) =
      carletRandomNonlinearityFailureBound n := by
  rw [carletRandomNonlinearityFailureBound]
  have hneg : (-(n : ℝ)) = (n : ℝ) * (-1) := by ring
  rw [hneg, Real.exp_nat_mul, Real.exp_neg, div_pow]
  ring

theorem tendsto_carletRandomNonlinearityFailureBound :
    Filter.Tendsto carletRandomNonlinearityFailureBound
      Filter.atTop (nhds 0) := by
  have hbase_nonneg : 0 ≤ (2 : ℝ) / Real.exp 1 := by positivity
  have hbase_lt : (2 : ℝ) / Real.exp 1 < 1 := by
    rw [div_lt_one (Real.exp_pos 1)]
    exact Real.exp_one_gt_two
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt
  unfold carletRandomNonlinearityFailureBound
  simpa using hpow.const_mul 2

private theorem binaryFunctionOnSignCube_realSignView_encoding
    (g : FABL.BooleanFunction n) :
    FABL.binaryFunctionOnSignCube
        (realSignView (FABL.booleanFunctionF₂Encoding g)) = g.toReal := by
  funext x
  unfold FABL.binaryFunctionOnSignCube realSignView
    FABL.realSignEncodedFunction FABL.signEncodedFunction
    FABL.booleanFunctionF₂Encoding FABL.BooleanFunction.toReal
  rw [(FABL.binaryCubeSignEquiv n).apply_symm_apply]
  change FABL.signValue
      (FABL.binarySignEquiv (FABL.binarySignEquiv.symm (g x))) =
    FABL.signValue (g x)
  rw [FABL.binarySignEquiv.apply_symm_apply]

/-- The vector- and subset-indexed Fourier infinity norms agree across the
canonical Boolean-function encoding. -/
theorem spectralInfinityNorm_encoding_eq_fourierInfinityNorm
    (g : FABL.BooleanFunction n) :
    FABL.spectralInfinityNorm
        (realSignView (FABL.booleanFunctionF₂Encoding g)) =
      FABL.fourierInfinityNorm g.toReal := by
  classical
  unfold FABL.spectralInfinityNorm FABL.fourierInfinityNorm
  have hview := binaryFunctionOnSignCube_realSignView_encoding g
  apply le_antisymm
  · apply Finset.sup'_le
    intro γ _
    rw [FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
      hview]
    exact Finset.le_sup'
      (fun S : Finset (Fin n) ↦ |FABL.fourierCoeff g.toReal S|)
      (Finset.mem_univ (FABL.f₂Support γ))
  · apply Finset.sup'_le
    intro S _
    let γ : FABL.F₂Cube n := (FABL.f₂CubeEquivFinset n).symm S
    have hsupport : FABL.f₂Support γ = S :=
      (FABL.f₂CubeEquivFinset n).apply_symm_apply S
    calc
      |FABL.fourierCoeff g.toReal S| =
          |FABL.vectorFourierCoeff
            (realSignView (FABL.booleanFunctionF₂Encoding g)) γ| := by
        rw [FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
          hview, hsupport]
      _ ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun δ : FABL.F₂Cube n ↦
            |FABL.vectorFourierCoeff
              (realSignView (FABL.booleanFunctionF₂Encoding g)) δ|) :=
        Finset.le_sup'
          (fun δ : FABL.F₂Cube n ↦
            |FABL.vectorFourierCoeff
              (realSignView (FABL.booleanFunctionF₂Encoding g)) δ|)
          (Finset.mem_univ γ)

/-- Relation (35), transported to the uniform sign-cube model used by FABL's
concentration theorem. -/
theorem nonlinearity_encoding_eq_fourierInfinityNorm
    (g : FABL.BooleanFunction n) :
    (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) =
      (2 : ℝ) ^ n / 2 -
        (2 : ℝ) ^ n * FABL.fourierInfinityNorm g.toReal / 2 := by
  rw [nonlinearity_cast_eq_relation_35,
    maxWalshMagnitude_cast_eq_spectralInfinityNorm,
    spectralInfinityNorm_encoding_eq_fourierInfinityNorm]

private theorem randomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt
    (g : FABL.BooleanFunction n) (ε : ℝ)
    (h : FABL.fourierInfinityNorm g.toReal < ε) :
    (2 : ℝ) ^ n / 2 - (2 : ℝ) ^ n * ε / 2 <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) := by
  rw [nonlinearity_encoding_eq_fourierInfinityNorm]
  have hmul := mul_lt_mul_of_pos_left h
    (show 0 < (2 : ℝ) ^ n / 2 by positivity)
  have hmul' :
      (2 : ℝ) ^ n * FABL.fourierInfinityNorm g.toReal / 2 <
        (2 : ℝ) ^ n * ε / 2 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact sub_lt_sub_left hmul' ((2 : ℝ) ^ n / 2)

theorem carletRandomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt
    (g : FABL.BooleanFunction n)
    (h : FABL.fourierInfinityNorm g.toReal <
      carletRandomFourierThreshold n) :
    carletRandomNonlinearityThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) := by
  rw [carletRandomNonlinearityThreshold]
  exact randomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt g
    (carletRandomFourierThreshold n) h

theorem rodierRandomNonlinearityLowerThreshold_lt_of_fourierInfinityNorm_lt
    (g : FABL.BooleanFunction n)
    (h : FABL.fourierInfinityNorm g.toReal <
      rodierRandomFourierUpperThreshold n) :
    rodierRandomNonlinearityLowerThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ) := by
  rw [rodierRandomNonlinearityLowerThreshold]
  exact randomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt g
    (rodierRandomFourierUpperThreshold n) h

private theorem one_sub_bound_le_measureReal_of_compl_subset
    {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (bad good : Set α) (bound : ℝ)
    (hbad : μ.real bad ≤ bound) (hcompl : badᶜ ⊆ good) :
    1 - bound ≤ μ.real good := by
  calc
    1 - bound ≤ 1 - μ.real bad := sub_le_sub_left hbad 1
    _ = μ.real badᶜ := by
      rw [measureReal_compl (Set.toFinite bad).measurableSet]
      simp
    _ ≤ μ.real good := measureReal_mono hcompl

/-- The uniform probability that an `n`-variable Boolean function exceeds
Carlet's random-function nonlinearity threshold. -/
noncomputable def carletRandomNonlinearityProbability (n : ℕ) : ℝ :=
  (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
    {g | carletRandomNonlinearityThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ)}

/-- The finite failure estimate underlying the almost-all theorem. -/
theorem one_sub_failureBound_le_carletRandomNonlinearityProbability (n : ℕ) :
    1 - carletRandomNonlinearityFailureBound n ≤
      carletRandomNonlinearityProbability n := by
  let μ := (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure
  let bad : Set (FABL.BooleanFunction n) :=
    {g | carletRandomFourierThreshold n ≤
      FABL.fourierInfinityNorm g.toReal}
  let good : Set (FABL.BooleanFunction n) :=
    {g | carletRandomNonlinearityThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ)}
  have hbad : μ.real bad ≤ carletRandomNonlinearityFailureBound n := by
    dsimp only [μ, bad]
    rw [← fourier_union_bound_eq_failureBound]
    exact measure_fourierInfinityNorm_ge_carletThreshold_le n
  have hcompl : badᶜ ⊆ good := by
    intro g hg
    apply carletRandomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt g
    simpa [bad] using hg
  change 1 - carletRandomNonlinearityFailureBound n ≤ μ.real good
  exact one_sub_bound_le_measureReal_of_compl_subset μ bad good
    (carletRandomNonlinearityFailureBound n) hbad hcompl

/-- The uniform probability that the nonlinearity exceeds Rodier's lower
endpoint. -/
noncomputable def rodierRandomNonlinearityLowerProbability (n : ℕ) : ℝ :=
  (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure.real
    {g | rodierRandomNonlinearityLowerThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ)}

/-- The finite failure estimate for the Hoeffding side of Rodier's interval. -/
theorem one_sub_rodierLowerFailureBound_le_probability
    {n : ℕ} (hn : 1 ≤ n) :
    1 - rodierRandomNonlinearityLowerFailureBound n ≤
      rodierRandomNonlinearityLowerProbability n := by
  let μ := (FABL.uniformPMF (FABL.BooleanFunction n)).toMeasure
  let bad : Set (FABL.BooleanFunction n) :=
    {g | rodierRandomFourierUpperThreshold n ≤
      FABL.fourierInfinityNorm g.toReal}
  let good : Set (FABL.BooleanFunction n) :=
    {g | rodierRandomNonlinearityLowerThreshold n <
      (nonlinearity (FABL.booleanFunctionF₂Encoding g) : ℝ)}
  have hbad :
      μ.real bad ≤ rodierRandomNonlinearityLowerFailureBound n := by
    dsimp only [μ, bad, rodierRandomNonlinearityLowerFailureBound]
    exact measure_fourierInfinityNorm_ge_rodierUpperThreshold_le hn
  have hcompl : badᶜ ⊆ good := by
    intro g hg
    apply
      rodierRandomNonlinearityLowerThreshold_lt_of_fourierInfinityNorm_lt g
    simpa [bad] using hg
  change
    1 - rodierRandomNonlinearityLowerFailureBound n ≤ μ.real good
  exact one_sub_bound_le_measureReal_of_compl_subset μ bad good
    (rodierRandomNonlinearityLowerFailureBound n) hbad hcompl

/-- The Hoeffding side of Rodier's sharp interval: with probability tending
to one, random nonlinearity exceeds the displayed lower endpoint. -/
theorem tendsto_rodierRandomNonlinearityLowerProbability :
    Filter.Tendsto rodierRandomNonlinearityLowerProbability
      Filter.atTop (nhds 1) := by
  have hlower :
      Filter.Tendsto
        (fun n ↦ 1 - rodierRandomNonlinearityLowerFailureBound n)
        Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using
      tendsto_rodierRandomNonlinearityLowerFailureBound.const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact one_sub_rodierLowerFailureBound_le_probability hn
  · filter_upwards with n
    unfold rodierRandomNonlinearityLowerProbability
    exact measureReal_le_one

/-- Olejár--Stanek/Carlet: the proportion of Boolean functions whose
nonlinearity exceeds the displayed threshold tends to one. -/
theorem tendsto_carletRandomNonlinearityProbability :
    Filter.Tendsto carletRandomNonlinearityProbability
      Filter.atTop (nhds 1) := by
  have hlower :
      Filter.Tendsto
        (fun n ↦ 1 - carletRandomNonlinearityFailureBound n)
        Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using
      tendsto_carletRandomNonlinearityFailureBound.const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · exact one_sub_failureBound_le_carletRandomNonlinearityProbability
  · intro n
    unfold carletRandomNonlinearityProbability
    exact measureReal_le_one

end CryptBoolean
