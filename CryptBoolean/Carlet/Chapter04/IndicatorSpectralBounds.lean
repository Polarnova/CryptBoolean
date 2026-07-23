/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AutocorrelationIdentities
public import CryptBoolean.Carlet.Chapter04.LinearStructureSpectrum
public import CryptBoolean.Carlet.Chapter04.Nonlinearity
import Mathlib.Algebra.Order.Chebyshev

/-!
# Carlet Chapter 4 indicator and Walsh-support bounds

The fourth Walsh moment controls nonlinearity and the product of the sum-of-squares indicator
with Walsh-support size. Equality characterizes plateaued and bent functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A Boolean function is plateaued when all nonzero raw Walsh coefficients have one magnitude. -/
def HasPlateauedWalshSpectrum (f : BooleanFunction n) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a, |(walshTransform f a : ℝ)| = 0 ∨
    |(walshTransform f a : ℝ)| = c

/-- Every raw Walsh coefficient is bounded by Carlet's maximum Walsh magnitude. -/
theorem abs_walshTransform_le_maxWalshMagnitude
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    |(walshTransform f a : ℝ)| ≤ (maxWalshMagnitude f : ℝ) := by
  have hnat : (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
    unfold maxWalshMagnitude
    exact Finset.le_sup'
      (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ a)
  have hreal : ((walshTransform f a).natAbs : ℝ) ≤
      (maxWalshMagnitude f : ℝ) := by exact_mod_cast hnat
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal

private theorem exists_walshTransform_ne_zero (f : BooleanFunction n) :
    ∃ a, walshTransform f a ≠ 0 := by
  by_contra h
  push Not at h
  have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
  have hsum : (∑ a, (walshTransform f a : ℝ) ^ 2) = 0 := by
    simp [h]
  rw [hsum] at hparseval
  have hpos : 0 < ((2 : ℝ) ^ n) ^ 2 := by positivity
  linarith

private theorem maxWalshMagnitude_pos (f : BooleanFunction n) :
    0 < (maxWalshMagnitude f : ℝ) := by
  obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
  have hpos : 0 < |(walshTransform f a : ℝ)| := abs_pos.mpr (by exact_mod_cast ha)
  exact hpos.trans_le (abs_walshTransform_le_maxWalshMagnitude f a)

private theorem exists_abs_walshTransform_eq_maxWalshMagnitude
    (f : BooleanFunction n) :
    ∃ a, |(walshTransform f a : ℝ)| = (maxWalshMagnitude f : ℝ) := by
  unfold maxWalshMagnitude
  obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube n))) Finset.univ_nonempty
    (fun u ↦ (walshTransform f u).natAbs)
  refine ⟨a, ?_⟩
  rw [hmax, Nat.cast_natAbs, Int.cast_abs]

private theorem walshTransform_fourth_le_maxWalshMagnitude_fourth
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (walshTransform f a : ℝ) ^ 4 ≤ (maxWalshMagnitude f : ℝ) ^ 4 := by
  have habs := abs_walshTransform_le_maxWalshMagnitude f a
  have hsq : (walshTransform f a : ℝ) ^ 2 ≤
      (maxWalshMagnitude f : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
  nlinarith [sq_nonneg (walshTransform f a : ℝ),
    sq_nonneg (maxWalshMagnitude f : ℝ)]

/-- The fourth Walsh moment is bounded by the second moment times the squared peak magnitude. -/
theorem sum_walshTransform_fourth_le_sum_sq_mul_maxWalshMagnitude_sq
    (f : BooleanFunction n) :
    (∑ a, (walshTransform f a : ℝ) ^ 4) ≤
      (∑ a, (walshTransform f a : ℝ) ^ 2) *
        (maxWalshMagnitude f : ℝ) ^ 2 := by
  calc
    (∑ a, (walshTransform f a : ℝ) ^ 4) ≤
        ∑ a, (walshTransform f a : ℝ) ^ 2 *
          (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      have habs := abs_walshTransform_le_maxWalshMagnitude f a
      have hsq : (walshTransform f a : ℝ) ^ 2 ≤
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
            (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
      nlinarith [sq_nonneg (walshTransform f a : ℝ)]
    _ = (∑ a, (walshTransform f a : ℝ) ^ 2) *
        (maxWalshMagnitude f : ℝ) ^ 2 := by rw [Finset.sum_mul]

/-- The fourth Walsh moment is bounded by the cube cardinality times the fourth power of its
peak magnitude. -/
theorem sum_walshTransform_fourth_le_two_pow_mul_maxWalshMagnitude_fourth
    (f : BooleanFunction n) :
    (∑ a, (walshTransform f a : ℝ) ^ 4) ≤
      (2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 4 := by
  calc
    (∑ a, (walshTransform f a : ℝ) ^ 4) ≤
        ∑ _a : FABL.F₂Cube n, (maxWalshMagnitude f : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro a _ha
      exact walshTransform_fourth_le_maxWalshMagnitude_fourth f a
    _ = (2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 4 := by
      rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
      push_cast
      rfl

private theorem sumOfSquaresIndicator_pos (f : BooleanFunction n) :
    0 < sumOfSquaresIndicator f := by
  exact (by positivity : 0 < (2 : ℝ) ^ (2 * n)).trans_le
    (sumOfSquaresIndicator_lower_bound f)

/-- The squared peak Walsh magnitude is at least `V(f) / 2^n`. -/
theorem sumOfSquaresIndicator_div_two_pow_le_maxWalshMagnitude_sq
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f / (2 : ℝ) ^ n ≤
      (maxWalshMagnitude f : ℝ) ^ 2 := by
  have hmoment := sum_walshTransform_fourth_le_sum_sq_mul_maxWalshMagnitude_sq f
  rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator,
    sum_walshTransform_sq_eq_two_pow_sq] at hmoment
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hpow]
  apply le_of_mul_le_mul_left _ hpow
  calc
    (2 : ℝ) ^ n * sumOfSquaresIndicator f ≤
        ((2 : ℝ) ^ n) ^ 2 * (maxWalshMagnitude f : ℝ) ^ 2 := hmoment
    _ = (2 : ℝ) ^ n *
        ((maxWalshMagnitude f : ℝ) ^ 2 * (2 : ℝ) ^ n) := by ring

/-- The fourth power of the peak Walsh magnitude is at least `V(f)`. -/
theorem sumOfSquaresIndicator_le_maxWalshMagnitude_fourth
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f ≤ (maxWalshMagnitude f : ℝ) ^ 4 := by
  have hmoment := sum_walshTransform_fourth_le_two_pow_mul_maxWalshMagnitude_fourth f
  rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator] at hmoment
  exact le_of_mul_le_mul_left hmoment (by positivity : 0 < (2 : ℝ) ^ n)

/-- The peak Walsh magnitude dominates the square-root expression in Carlet's first indicator
bound. -/
theorem inv_sqrt_two_pow_mul_sqrt_sumOfSquaresIndicator_le_maxWalshMagnitude
    (f : BooleanFunction n) :
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * Real.sqrt (sumOfSquaresIndicator f) ≤
      (maxWalshMagnitude f : ℝ) := by
  have hV : 0 ≤ sumOfSquaresIndicator f := (sumOfSquaresIndicator_pos f).le
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  calc
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * Real.sqrt (sumOfSquaresIndicator f) =
        Real.sqrt (sumOfSquaresIndicator f / (2 : ℝ) ^ n) := by
      rw [Real.sqrt_div hV, div_eq_inv_mul]
    _ ≤ (maxWalshMagnitude f : ℝ) := by
      exact Real.sqrt_le_iff.mpr
        ⟨Nat.cast_nonneg (maxWalshMagnitude f),
          sumOfSquaresIndicator_div_two_pow_le_maxWalshMagnitude_sq f⟩

private theorem fourthRoot_eq_sqrt_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  norm_num

/-- The peak Walsh magnitude dominates the real fourth root of `V(f)`. -/
theorem rpow_one_fourth_sumOfSquaresIndicator_le_maxWalshMagnitude
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f ^ (1 / 4 : ℝ) ≤
      (maxWalshMagnitude f : ℝ) := by
  have hV : 0 ≤ sumOfSquaresIndicator f := (sumOfSquaresIndicator_pos f).le
  rw [fourthRoot_eq_sqrt_sqrt _ hV]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Nat.cast_nonneg (maxWalshMagnitude f), ?_⟩
  apply Real.sqrt_le_iff.mpr
  refine ⟨sq_nonneg (maxWalshMagnitude f : ℝ), ?_⟩
  convert sumOfSquaresIndicator_le_maxWalshMagnitude_fourth f using 1
  ring

/-- Carlet's first fourth-moment nonlinearity bound. -/
theorem nonlinearity_cast_le_sqrt_sumOfSquaresIndicator_bound
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ n / 2 -
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
          Real.sqrt (sumOfSquaresIndicator f) / 2 := by
  rw [nonlinearity_cast_eq_relation_35]
  linarith [inv_sqrt_two_pow_mul_sqrt_sumOfSquaresIndicator_le_maxWalshMagnitude f]

/-- Carlet's second fourth-moment nonlinearity bound. -/
theorem nonlinearity_cast_le_fourthRoot_sumOfSquaresIndicator_bound
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ n / 2 -
        sumOfSquaresIndicator f ^ (1 / 4 : ℝ) / 2 := by
  rw [nonlinearity_cast_eq_relation_35]
  linarith [rpow_one_fourth_sumOfSquaresIndicator_le_maxWalshMagnitude f]

private theorem hasPlateauedWalshSpectrum_iff_pointwise_fourth_eq
    (f : BooleanFunction n) :
    HasPlateauedWalshSpectrum f ↔
      ∀ a, (walshTransform f a : ℝ) ^ 4 =
        (walshTransform f a : ℝ) ^ 2 *
          (maxWalshMagnitude f : ℝ) ^ 2 := by
  constructor
  · rintro ⟨c, hc, hplateaued⟩
    obtain ⟨u, hu⟩ := exists_abs_walshTransform_eq_maxWalshMagnitude f
    have hu_pos : 0 < |(walshTransform f u : ℝ)| := by
      rw [hu]
      exact maxWalshMagnitude_pos f
    have hmax_eq_c : (maxWalshMagnitude f : ℝ) = c := by
      rcases hplateaued u with hzero | hc_u
      · linarith
      · linarith
    intro a
    rcases hplateaued a with hzero | hc_a
    · have hwa : (walshTransform f a : ℝ) = 0 := abs_eq_zero.mp hzero
      rw [hwa]
      norm_num
    · have habs : |(walshTransform f a : ℝ)| =
          (maxWalshMagnitude f : ℝ) := by rw [hc_a, hmax_eq_c]
      have hsq : (walshTransform f a : ℝ) ^ 2 =
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        calc
          (walshTransform f a : ℝ) ^ 2 = |(walshTransform f a : ℝ)| ^ 2 :=
            (sq_abs _).symm
          _ = (maxWalshMagnitude f : ℝ) ^ 2 :=
            congrArg (fun x : ℝ ↦ x ^ 2) habs
      nlinarith
  · intro hpointwise
    refine ⟨(maxWalshMagnitude f : ℝ), maxWalshMagnitude_pos f, ?_⟩
    intro a
    have hfactor : (walshTransform f a : ℝ) ^ 2 *
        ((walshTransform f a : ℝ) ^ 2 -
          (maxWalshMagnitude f : ℝ) ^ 2) = 0 := by
      nlinarith [hpointwise a]
    rcases mul_eq_zero.mp hfactor with hzero | heq
    · left
      rw [sq_eq_zero_iff.mp hzero, abs_zero]
    · right
      have hsq : (walshTransform f a : ℝ) ^ 2 =
          (maxWalshMagnitude f : ℝ) ^ 2 := sub_eq_zero.mp heq
      exact (sq_eq_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (by positivity : 0 ≤ (maxWalshMagnitude f : ℝ))).mp (by
          calc
            |(walshTransform f a : ℝ)| ^ 2 =
                (walshTransform f a : ℝ) ^ 2 := sq_abs _
            _ = (maxWalshMagnitude f : ℝ) ^ 2 := hsq)

/-- Equality in the first fourth-moment estimate is equivalent to plateauedness. -/
theorem sum_walshTransform_fourth_eq_sum_sq_mul_maxWalshMagnitude_sq_iff_plateaued
    (f : BooleanFunction n) :
    (∑ a, (walshTransform f a : ℝ) ^ 4) =
        (∑ a, (walshTransform f a : ℝ) ^ 2) *
          (maxWalshMagnitude f : ℝ) ^ 2 ↔
      HasPlateauedWalshSpectrum f := by
  rw [hasPlateauedWalshSpectrum_iff_pointwise_fourth_eq]
  constructor
  · intro hsum a
    have hnonneg (u : FABL.F₂Cube n) :
        0 ≤ (walshTransform f u : ℝ) ^ 2 *
            (maxWalshMagnitude f : ℝ) ^ 2 -
          (walshTransform f u : ℝ) ^ 4 := by
      have habs := abs_walshTransform_le_maxWalshMagnitude f u
      have hsq : (walshTransform f u : ℝ) ^ 2 ≤
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (walshTransform f u : ℝ))
            (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
      nlinarith [sq_nonneg (walshTransform f u : ℝ)]
    have hgap :
        (∑ u, ((walshTransform f u : ℝ) ^ 2 *
            (maxWalshMagnitude f : ℝ) ^ 2 -
          (walshTransform f u : ℝ) ^ 4)) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
      ring
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _hu ↦ hnonneg u)).mp hgap a (Finset.mem_univ a)
    linarith
  · intro hpointwise
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ha ↦ hpointwise a)

private theorem all_abs_walshTransform_eq_max_iff_flat
    (f : BooleanFunction n) :
    (∀ a, |(walshTransform f a : ℝ)| = (maxWalshMagnitude f : ℝ)) ↔
      HasFlatWalshSpectrum f := by
  constructor
  · intro hall
    have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
    have hsum : (∑ a, (walshTransform f a : ℝ) ^ 2) =
        ∑ _a : FABL.F₂Cube n, (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        (walshTransform f a : ℝ) ^ 2 = |(walshTransform f a : ℝ)| ^ 2 :=
          (sq_abs _).symm
        _ = (maxWalshMagnitude f : ℝ) ^ 2 :=
          congrArg (fun x : ℝ ↦ x ^ 2) (hall a)
    rw [hsum, Finset.sum_const, Finset.card_univ, card_f₂Cube,
      nsmul_eq_mul] at hparseval
    push_cast at hparseval
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hmax_sq : (maxWalshMagnitude f : ℝ) ^ 2 = (2 : ℝ) ^ n := by
      apply le_antisymm
      · apply le_of_mul_le_mul_left _ hpow
        nlinarith
      · apply le_of_mul_le_mul_left _ hpow
        nlinarith
    have hmax : (maxWalshMagnitude f : ℝ) = Real.sqrt ((2 : ℝ) ^ n) :=
      (sq_eq_sq₀ (Nat.cast_nonneg (maxWalshMagnitude f))
        (Real.sqrt_nonneg _)).mp (by rw [Real.sq_sqrt hpow.le]; exact hmax_sq)
    intro a
    rw [hall a, hmax]
  · intro hflat
    obtain ⟨u, hu⟩ := exists_abs_walshTransform_eq_maxWalshMagnitude f
    have hmax : (maxWalshMagnitude f : ℝ) = Real.sqrt ((2 : ℝ) ^ n) := by
      rw [← hu, hflat u]
    intro a
    rw [hflat a, hmax]

/-- Equality in the second fourth-moment estimate is equivalent to a flat Walsh spectrum. -/
theorem sum_walshTransform_fourth_eq_two_pow_mul_maxWalshMagnitude_fourth_iff_flat
    (f : BooleanFunction n) :
    (∑ a, (walshTransform f a : ℝ) ^ 4) =
        (2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 4 ↔
      HasFlatWalshSpectrum f := by
  rw [← all_abs_walshTransform_eq_max_iff_flat]
  constructor
  · intro hsum a
    have hgap :
        (∑ u : FABL.F₂Cube n,
          ((maxWalshMagnitude f : ℝ) ^ 4 -
            (walshTransform f u : ℝ) ^ 4)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        card_f₂Cube, nsmul_eq_mul]
      push_cast
      linarith
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _hu ↦ sub_nonneg.mpr
        (walshTransform_fourth_le_maxWalshMagnitude_fourth f u))).mp
      hgap a (Finset.mem_univ a)
    have hfourth : (walshTransform f a : ℝ) ^ 4 =
        (maxWalshMagnitude f : ℝ) ^ 4 := by linarith
    have habsFourth : |(walshTransform f a : ℝ)| ^ 4 =
        |(maxWalshMagnitude f : ℝ)| ^ 4 := by
      simpa only [abs_pow] using congrArg abs hfourth
    have habs := (pow_left_inj₀ (abs_nonneg (walshTransform f a : ℝ))
      (abs_nonneg (maxWalshMagnitude f : ℝ)) (by norm_num : (4 : ℕ) ≠ 0)).mp
      habsFourth
    simpa only [abs_of_nonneg (by positivity : 0 ≤ (maxWalshMagnitude f : ℝ))] using habs
  · intro hall
    calc
      (∑ a, (walshTransform f a : ℝ) ^ 4) =
          ∑ _a : FABL.F₂Cube n, (maxWalshMagnitude f : ℝ) ^ 4 := by
        apply Finset.sum_congr rfl
        intro a _ha
        calc
          (walshTransform f a : ℝ) ^ 4 = |(walshTransform f a : ℝ)| ^ 4 := by
            rw [← abs_pow, abs_of_nonneg (by positivity :
              0 ≤ (walshTransform f a : ℝ) ^ 4)]
          _ = (maxWalshMagnitude f : ℝ) ^ 4 := by rw [hall a]
      _ = (2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 4 := by
        rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
        push_cast
        rfl

private theorem inv_sqrt_two_pow_mul_sqrt_indicator_sq
    (f : BooleanFunction n) :
    ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
        Real.sqrt (sumOfSquaresIndicator f)) ^ 2 =
      sumOfSquaresIndicator f / (2 : ℝ) ^ n := by
  have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hV : 0 ≤ sumOfSquaresIndicator f := (sumOfSquaresIndicator_pos f).le
  rw [mul_pow, inv_pow, Real.sq_sqrt hpow, Real.sq_sqrt hV]
  field_simp

private theorem maxWalshMagnitude_eq_indicatorSqrt_iff_plateaued
    (f : BooleanFunction n) :
    (maxWalshMagnitude f : ℝ) =
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
          Real.sqrt (sumOfSquaresIndicator f) ↔
      HasPlateauedWalshSpectrum f := by
  rw [← sum_walshTransform_fourth_eq_sum_sq_mul_maxWalshMagnitude_sq_iff_plateaued]
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  constructor
  · intro hmax
    rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator,
      sum_walshTransform_sq_eq_two_pow_sq, hmax,
      inv_sqrt_two_pow_mul_sqrt_indicator_sq]
    field_simp
  · intro hmoment
    rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator,
      sum_walshTransform_sq_eq_two_pow_sq] at hmoment
    apply (sq_eq_sq₀ (Nat.cast_nonneg (maxWalshMagnitude f))
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))).mp
    rw [inv_sqrt_two_pow_mul_sqrt_indicator_sq]
    have hVeq : sumOfSquaresIndicator f =
        (2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply mul_left_cancel₀ hpow.ne'
      calc
        (2 : ℝ) ^ n * sumOfSquaresIndicator f =
            ((2 : ℝ) ^ n) ^ 2 * (maxWalshMagnitude f : ℝ) ^ 2 := hmoment
        _ = (2 : ℝ) ^ n *
            ((2 : ℝ) ^ n * (maxWalshMagnitude f : ℝ) ^ 2) := by ring
    rw [hVeq]
    field_simp

/-- Equality in Carlet's first indicator nonlinearity bound holds exactly for plateaued
functions. -/
theorem nonlinearity_cast_eq_sqrt_sumOfSquaresIndicator_bound_iff_plateaued
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ n / 2 -
          (Real.sqrt ((2 : ℝ) ^ n))⁻¹ *
            Real.sqrt (sumOfSquaresIndicator f) / 2 ↔
      HasPlateauedWalshSpectrum f := by
  rw [nonlinearity_cast_eq_relation_35,
    ← maxWalshMagnitude_eq_indicatorSqrt_iff_plateaued]
  constructor <;> intro h <;> linarith

private theorem fourthRoot_pow_four (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem maxWalshMagnitude_eq_indicatorFourthRoot_iff_bent
    (f : BooleanFunction n) :
    (maxWalshMagnitude f : ℝ) = sumOfSquaresIndicator f ^ (1 / 4 : ℝ) ↔
      IsBent f := by
  rw [← hasFlatWalshSpectrum_iff_isBent,
    ← sum_walshTransform_fourth_eq_two_pow_mul_maxWalshMagnitude_fourth_iff_flat]
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hV : 0 ≤ sumOfSquaresIndicator f := (sumOfSquaresIndicator_pos f).le
  constructor
  · intro hmax
    rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator, hmax,
      fourthRoot_pow_four _ hV]
  · intro hmoment
    rw [sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator] at hmoment
    have hfourth : (maxWalshMagnitude f : ℝ) ^ 4 = sumOfSquaresIndicator f := by
      apply le_antisymm
      · apply le_of_mul_le_mul_left _ hpow
        nlinarith
      · apply le_of_mul_le_mul_left _ hpow
        nlinarith
    apply (pow_left_inj₀ (Nat.cast_nonneg (maxWalshMagnitude f))
      (Real.rpow_nonneg hV _) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [fourthRoot_pow_four _ hV]
    exact hfourth

/-- Equality in Carlet's fourth-root nonlinearity bound holds exactly for bent functions. -/
theorem nonlinearity_cast_eq_fourthRoot_sumOfSquaresIndicator_bound_iff_bent
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ n / 2 -
          sumOfSquaresIndicator f ^ (1 / 4 : ℝ) / 2 ↔
      IsBent f := by
  rw [nonlinearity_cast_eq_relation_35,
    ← maxWalshMagnitude_eq_indicatorFourthRoot_iff_bent]
  constructor <;> intro h <;> linarith

private theorem sum_walshSupport_pow_eq_sum
    (f : BooleanFunction n) (k : ℕ) (hk : k ≠ 0) :
    (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ k) =
      ∑ a, (walshTransform f a : ℝ) ^ k := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ha hnot
  have hzero : walshTransform f a = 0 := by
    exact not_ne_iff.mp (by simpa only [mem_walshSupport] using hnot)
  simp [hzero, hk]

/-- Carlet's Walsh-support product bound `2^(3n) ≤ V(f) |supp(W_f)|`. -/
theorem two_pow_three_mul_n_le_sumOfSquaresIndicator_mul_card_walshSupport
    (f : BooleanFunction n) :
    (2 : ℝ) ^ (3 * n) ≤
      sumOfSquaresIndicator f * ((walshSupport f).card : ℝ) := by
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := walshSupport f) (f := fun a ↦ (walshTransform f a : ℝ) ^ 2)
  have hmoment :
      (((2 : ℝ) ^ n) ^ 2) ^ 2 ≤
        ((walshSupport f).card : ℝ) *
          ((2 : ℝ) ^ n * sumOfSquaresIndicator f) := by
    calc
      (((2 : ℝ) ^ n) ^ 2) ^ 2 =
          ((∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2)) ^ 2 := by
        rw [sum_walshSupport_pow_eq_sum f 2 (by norm_num),
          sum_walshTransform_sq_eq_two_pow_sq]
      _ ≤ ((walshSupport f).card : ℝ) *
          ∑ a ∈ walshSupport f, ((walshTransform f a : ℝ) ^ 2) ^ 2 := hcauchy
      _ = ((walshSupport f).card : ℝ) *
          ((2 : ℝ) ^ n * sumOfSquaresIndicator f) := by
        congr 1
        calc
          (∑ a ∈ walshSupport f, ((walshTransform f a : ℝ) ^ 2) ^ 2) =
              ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 4 := by
            apply Finset.sum_congr rfl
            intro a _ha
            ring
          _ = ∑ a, (walshTransform f a : ℝ) ^ 4 :=
            sum_walshSupport_pow_eq_sum f 4 (by norm_num)
          _ = (2 : ℝ) ^ n * sumOfSquaresIndicator f :=
            sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator f
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  apply le_of_mul_le_mul_left _ hpow
  calc
    (2 : ℝ) ^ n * (2 : ℝ) ^ (3 * n) = (2 : ℝ) ^ (4 * n) := by
      rw [← pow_add]
      congr 1
      omega
    _ = (((2 : ℝ) ^ n) ^ 2) ^ 2 := by
      rw [show 4 * n = n * 4 by omega, ← pow_mul]
      ring
    _ ≤ ((walshSupport f).card : ℝ) *
        ((2 : ℝ) ^ n * sumOfSquaresIndicator f) := hmoment
    _ = (2 : ℝ) ^ n *
        (sumOfSquaresIndicator f * ((walshSupport f).card : ℝ)) := by ring

private theorem sum_card_mul_sub_sum_sq
    {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    (∑ i ∈ s, (((s.card : ℝ) * y i) - ∑ j ∈ s, y j) ^ 2) =
      (s.card : ℝ) *
        ((s.card : ℝ) * ∑ i ∈ s, y i ^ 2 - (∑ i ∈ s, y i) ^ 2) := by
  classical
  let S : ℝ := ∑ i ∈ s, y i
  let K : ℝ := s.card
  calc
    (∑ i ∈ s, (((s.card : ℝ) * y i) - ∑ j ∈ s, y j) ^ 2) =
        ∑ i ∈ s, (K ^ 2 * y i ^ 2 - 2 * K * S * y i + S ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [K, S]
      ring
    _ = K ^ 2 * (∑ i ∈ s, y i ^ 2) -
          2 * K * S * (∑ i ∈ s, y i) + (s.card : ℝ) * S ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) *
        ((s.card : ℝ) * ∑ i ∈ s, y i ^ 2 - (∑ i ∈ s, y i) ^ 2) := by
      dsimp [K, S]
      ring

private theorem walshSupport_cauchy_equality_iff_plateaued
    (f : BooleanFunction n) :
    ((∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) ^ 2 =
        ((walshSupport f).card : ℝ) *
          ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 4) ↔
      HasPlateauedWalshSpectrum f := by
  classical
  constructor
  · intro heq
    obtain ⟨u, hu_nonzero⟩ := exists_walshTransform_ne_zero f
    have hu : u ∈ walshSupport f := (mem_walshSupport f u).2 hu_nonzero
    let y : FABL.F₂Cube n → ℝ := fun a ↦ (walshTransform f a : ℝ) ^ 2
    let S : ℝ := ∑ a ∈ walshSupport f, y a
    let K : ℝ := (walshSupport f).card
    have hcauchy : S ^ 2 = K * ∑ a ∈ walshSupport f, y a ^ 2 := by
      dsimp [S, K, y]
      calc
        (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) ^ 2 =
            ((walshSupport f).card : ℝ) *
              ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 4 := heq
        _ = ((walshSupport f).card : ℝ) *
            ∑ a ∈ walshSupport f, ((walshTransform f a : ℝ) ^ 2) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _ha
          ring
    have hdeviation :
        (∑ a ∈ walshSupport f, (K * y a - S) ^ 2) = 0 := by
      rw [show (∑ a ∈ walshSupport f, (K * y a - S) ^ 2) =
          K * (K * ∑ a ∈ walshSupport f, y a ^ 2 - S ^ 2) by
        simpa [K, S] using
          sum_card_mul_sub_sum_sq (walshSupport f) y]
      rw [hcauchy]
      ring
    have hconstant (a : FABL.F₂Cube n) (ha : a ∈ walshSupport f) :
        y a = y u := by
      have hzero (v : FABL.F₂Cube n) (hv : v ∈ walshSupport f) :
          (K * y v - S) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun w _hw ↦ sq_nonneg (K * y w - S))).mp hdeviation v hv
      have ha_eq : K * y a = S := by nlinarith [hzero a ha]
      have hu_eq : K * y u = S := by nlinarith [hzero u hu]
      have hK : 0 < K := by
        have hcard : 0 < (walshSupport f).card := Finset.card_pos.mpr ⟨u, hu⟩
        have hcardReal : (0 : ℝ) < ((walshSupport f).card : ℝ) := by
          exact_mod_cast hcard
        simpa [K] using hcardReal
      exact (mul_left_cancel₀ hK.ne' (ha_eq.trans hu_eq.symm))
    refine ⟨|(walshTransform f u : ℝ)|,
      abs_pos.mpr (by exact_mod_cast hu_nonzero), ?_⟩
    intro a
    by_cases ha : a ∈ walshSupport f
    · right
      apply (sq_eq_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (abs_nonneg (walshTransform f u : ℝ))).mp
      simpa only [sq_abs, y] using hconstant a ha
    · left
      have hzero : walshTransform f a = 0 :=
        not_ne_iff.mp (by simpa only [mem_walshSupport] using ha)
      simp [hzero]
  · rintro ⟨c, hc, hplateaued⟩
    have hvalue (a : FABL.F₂Cube n) (ha : a ∈ walshSupport f) :
        (walshTransform f a : ℝ) ^ 2 = c ^ 2 := by
      rcases hplateaued a with hzero | heq
      · have hne : walshTransform f a ≠ 0 := (mem_walshSupport f a).1 ha
        exact (hne (by exact_mod_cast (abs_eq_zero.mp hzero))).elim
      · calc
          (walshTransform f a : ℝ) ^ 2 = |(walshTransform f a : ℝ)| ^ 2 :=
            (sq_abs _).symm
          _ = c ^ 2 := congrArg (fun x : ℝ ↦ x ^ 2) heq
    calc
      (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) ^ 2 =
          (∑ _a ∈ walshSupport f, c ^ 2) ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl (fun a ha ↦ hvalue a ha)
      _ = ((walshSupport f).card : ℝ) *
          ∑ _a ∈ walshSupport f, c ^ 4 := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
      _ = ((walshSupport f).card : ℝ) *
          ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 4 := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [show (walshTransform f a : ℝ) ^ 4 = c ^ 4 by
          have := hvalue a ha
          nlinarith]

/-- Equality in the Walsh-support product bound holds exactly for plateaued functions. -/
theorem sumOfSquaresIndicator_mul_card_walshSupport_eq_two_pow_three_mul_n_iff_plateaued
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f * ((walshSupport f).card : ℝ) =
        (2 : ℝ) ^ (3 * n) ↔
      HasPlateauedWalshSpectrum f := by
  rw [← walshSupport_cauchy_equality_iff_plateaued]
  have hpow3 : (2 : ℝ) ^ (3 * n) = ((2 : ℝ) ^ n) ^ 3 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [sum_walshSupport_pow_eq_sum f 2 (by norm_num),
    sum_walshSupport_pow_eq_sum f 4 (by norm_num),
    sum_walshTransform_sq_eq_two_pow_sq,
    sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator, hpow3]
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  constructor <;> intro h
  · apply mul_left_cancel₀ hpow
    nlinarith
  · apply mul_left_cancel₀ hpow
    nlinarith

end CryptBoolean
