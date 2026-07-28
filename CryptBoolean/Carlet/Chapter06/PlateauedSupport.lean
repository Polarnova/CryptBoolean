/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Plateaued

/-!
# Walsh-support bound for plateaued functions

Carlet Section 6.8: the support-size nonlinearity bound and its equality case.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The maximum Walsh magnitude is the amplitude supplied by a plateaued spectrum. -/
theorem maxWalshMagnitude_eq_of_hasPlateauedWalshAmplitude
    (f : BooleanFunction n) (amplitude : ℕ)
    (hf : HasPlateauedWalshAmplitude f amplitude) :
    maxWalshMagnitude f = amplitude := by
  apply le_antisymm
  · unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro a _ha
    rcases hf.2 a with hzero | hmagnitude
    · simp [hzero]
    · exact hmagnitude.le
  · obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
    have hmagnitude : (walshTransform f a).natAbs = amplitude := by
      rcases hf.2 a with hzero | hmagnitude
      · exact (ha hzero).elim
      · exact hmagnitude
    rw [← hmagnitude]
    unfold maxWalshMagnitude
    exact Finset.le_sup' (fun u ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ a)

/-- Parseval restricted to the nonzero Walsh support. -/
theorem sum_walshTransform_sq_walshSupport
    (f : BooleanFunction n) :
    (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) =
      ((2 : ℝ) ^ n) ^ 2 := by
  rw [← sum_walshTransform_sq_eq_two_pow_sq f]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ha hnot
  have hzero : walshTransform f a = 0 := by
    simpa only [mem_walshSupport, not_ne_iff] using hnot
  simp [hzero]

/-- Walsh support size times squared maximum magnitude dominates the Parseval mass. -/
theorem two_pow_sq_le_card_walshSupport_mul_maxWalshMagnitude_sq
    (f : BooleanFunction n) :
    ((2 : ℝ) ^ n) ^ 2 ≤
      ((walshSupport f).card : ℝ) * (maxWalshMagnitude f : ℝ) ^ 2 := by
  rw [← sum_walshTransform_sq_walshSupport f]
  calc
    (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) ≤
        ∑ _a ∈ walshSupport f, (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      have habs := abs_walshTransform_le_maxWalshMagnitude f a
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
          (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
    _ = ((walshSupport f).card : ℝ) *
        (maxWalshMagnitude f : ℝ) ^ 2 := by simp

/-- Equality in the Walsh-support product bound characterizes plateaued functions. -/
theorem two_pow_sq_eq_card_walshSupport_mul_maxWalshMagnitude_sq_iff_plateaued
    (f : BooleanFunction n) :
    ((2 : ℝ) ^ n) ^ 2 =
        ((walshSupport f).card : ℝ) * (maxWalshMagnitude f : ℝ) ^ 2 ↔
      IsPlateaued f := by
  constructor
  · intro heq
    have hgap :
        (∑ a ∈ walshSupport f,
          ((maxWalshMagnitude f : ℝ) ^ 2 -
            (walshTransform f a : ℝ) ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        sum_walshTransform_sq_walshSupport, heq]
      ring
    have hnonneg (a : FABL.F₂Cube n) :
        0 ≤ (maxWalshMagnitude f : ℝ) ^ 2 -
          (walshTransform f a : ℝ) ^ 2 := by
      have habs := abs_walshTransform_le_maxWalshMagnitude f a
      have hsquare : (walshTransform f a : ℝ) ^ 2 ≤
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
            (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
      linarith
    have hmaxPositive : 0 < (maxWalshMagnitude f : ℝ) := by
      obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
      have huPositive : 0 < |(walshTransform f u : ℝ)| :=
        abs_pos.mpr (by exact_mod_cast hu)
      exact huPositive.trans_le (abs_walshTransform_le_maxWalshMagnitude f u)
    apply (isPlateaued_iff_hasPlateauedWalshSpectrum f).mpr
    refine ⟨(maxWalshMagnitude f : ℝ), hmaxPositive, ?_⟩
    intro a
    by_cases ha : a ∈ walshSupport f
    · right
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun u _hu ↦ hnonneg u)).mp hgap a ha
      have hsquare : (walshTransform f a : ℝ) ^ 2 =
          (maxWalshMagnitude f : ℝ) ^ 2 := by linarith
      exact (sq_eq_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (Nat.cast_nonneg (maxWalshMagnitude f))).mp (by
          simpa only [sq_abs] using hsquare)
    · left
      have hzero : walshTransform f a = 0 := by
        simpa only [mem_walshSupport, not_ne_iff] using ha
      simp [hzero]
  · intro hf
    obtain ⟨amplitude, hfAmplitude⟩ := hf
    have hcard :=
      card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul
        f amplitude hfAmplitude
    have hmax :=
      maxWalshMagnitude_eq_of_hasPlateauedWalshAmplitude
        f amplitude hfAmplitude
    rw [hmax]
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hcard
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
    calc
      ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ (2 * n) := by
        rw [show 2 * n = n * 2 by omega, pow_mul]
      _ = ((walshSupport f).card : ℝ) * (amplitude : ℝ) ^ 2 := hcast.symm

/-- Carlet's support-size upper bound on nonlinearity. -/
theorem nonlinearity_cast_le_walshSupport_bound
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ n / 2 *
        (1 - (Real.sqrt ((walshSupport f).card : ℝ))⁻¹) := by
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  have hcardPositive : (0 : ℝ) < ((walshSupport f).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨u, (mem_walshSupport f u).mpr hu⟩
  have hsqrtPositive : 0 < Real.sqrt ((walshSupport f).card : ℝ) :=
    Real.sqrt_pos.2 hcardPositive
  have hproduct :=
    two_pow_sq_le_card_walshSupport_mul_maxWalshMagnitude_sq f
  have hpeak :
      (2 : ℝ) ^ n / Real.sqrt ((walshSupport f).card : ℝ) ≤
        (maxWalshMagnitude f : ℝ) := by
    rw [div_le_iff₀ hsqrtPositive]
    have hsquare :
        ((2 : ℝ) ^ n) ^ 2 ≤
          ((maxWalshMagnitude f : ℝ) *
            Real.sqrt ((walshSupport f).card : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcardPositive.le]
      simpa [mul_comm] using hproduct
    exact (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ) ^ n)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))).mp hsquare
  rw [nonlinearity_cast_eq_relation_35]
  have hsqrtNe : Real.sqrt ((walshSupport f).card : ℝ) ≠ 0 :=
    hsqrtPositive.ne'
  calc
    (2 : ℝ) ^ n / 2 - (maxWalshMagnitude f : ℝ) / 2 ≤
        (2 : ℝ) ^ n / 2 -
          ((2 : ℝ) ^ n / Real.sqrt ((walshSupport f).card : ℝ)) / 2 := by
      linarith
    _ = (2 : ℝ) ^ n / 2 *
        (1 - (Real.sqrt ((walshSupport f).card : ℝ))⁻¹) := by
      rw [inv_eq_one_div]
      field_simp

/-- Equality in the Walsh-support nonlinearity bound holds exactly for plateaued functions. -/
theorem nonlinearity_cast_eq_walshSupport_bound_iff_plateaued
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ n / 2 *
          (1 - (Real.sqrt ((walshSupport f).card : ℝ))⁻¹) ↔
      IsPlateaued f := by
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  have hcardPositive : (0 : ℝ) < ((walshSupport f).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨u, (mem_walshSupport f u).mpr hu⟩
  have hsqrtPositive : 0 < Real.sqrt ((walshSupport f).card : ℝ) :=
    Real.sqrt_pos.2 hcardPositive
  have hsqrtNe : Real.sqrt ((walshSupport f).card : ℝ) ≠ 0 :=
    hsqrtPositive.ne'
  constructor
  · intro hnonlinearity
    rw [nonlinearity_cast_eq_relation_35] at hnonlinearity
    have hpeak :
        (maxWalshMagnitude f : ℝ) =
          (2 : ℝ) ^ n / Real.sqrt ((walshSupport f).card : ℝ) := by
      rw [inv_eq_one_div] at hnonlinearity
      field_simp [hsqrtNe] at hnonlinearity
      apply (eq_div_iff hsqrtNe).mpr
      ring_nf at hnonlinearity ⊢
      linarith
    apply
      (two_pow_sq_eq_card_walshSupport_mul_maxWalshMagnitude_sq_iff_plateaued
        f).mp
    rw [hpeak]
    field_simp [hsqrtNe]
    rw [Real.sq_sqrt hcardPositive.le]
  · intro hf
    have hproduct :=
      (two_pow_sq_eq_card_walshSupport_mul_maxWalshMagnitude_sq_iff_plateaued
        f).mpr hf
    have hsquare :
        ((maxWalshMagnitude f : ℝ) *
          Real.sqrt ((walshSupport f).card : ℝ)) ^ 2 =
          ((2 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcardPositive.le]
      simpa [mul_comm] using hproduct.symm
    have hmul :
        (maxWalshMagnitude f : ℝ) *
          Real.sqrt ((walshSupport f).card : ℝ) = (2 : ℝ) ^ n :=
      (sq_eq_sq₀
        (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
        (by positivity : 0 ≤ (2 : ℝ) ^ n)).mp hsquare
    have hpeak :
        (maxWalshMagnitude f : ℝ) =
          (2 : ℝ) ^ n / Real.sqrt ((walshSupport f).card : ℝ) :=
      (eq_div_iff hsqrtNe).mpr hmul
    rw [nonlinearity_cast_eq_relation_35, hpeak, inv_eq_one_div]
    field_simp [hsqrtNe]

end CryptBoolean
