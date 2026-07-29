/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.PlateauedSupport
public import CryptBoolean.Carlet.Chapter07.WalshDivisibility

/-!
# The Sarkar--Maitra nonlinearity bound

Carlet's nonlinearity bound for resilient Boolean functions and its plateaued
equality case.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem two_pow_eq_two_mul_two_pow_sub_one
    (k : ℕ) (hk : 0 < k) :
    2 ^ k = 2 * 2 ^ (k - 1) := by
  calc
    2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
    _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
    _ = 2 * 2 ^ (k - 1) := Nat.mul_comm _ _

private theorem two_pow_add_two_eq_two_mul_two_pow_add_one
    (k : ℕ) :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  calc
    2 ^ (k + 2) = 2 ^ ((k + 1) + 1) := by congr 1
    _ = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
    _ = 2 * 2 ^ (k + 1) := Nat.mul_comm _ _

private theorem two_pow_m_add_two_le_maxWalshMagnitude_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    2 ^ (m + 2) ≤ maxWalshMagnitude f := by
  obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
  have hdivInt :=
    two_pow_m_add_two_dvd_walshTransform_of_isResilient f m hm hf a
  have hdivNat :
      2 ^ (m + 2) ∣ (walshTransform f a).natAbs := by
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdivInt
  have hlower : 2 ^ (m + 2) ≤ (walshTransform f a).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hdivNat
  have hupperReal := abs_walshTransform_le_maxWalshMagnitude f a
  have hupper :
      (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
    have hcast : ((walshTransform f a).natAbs : ℝ) ≤
        (maxWalshMagnitude f : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hupperReal
    exact_mod_cast hcast
  exact hlower.trans hupper

/-- Division-free Sarkar--Maitra bound: twice the nonlinearity plus the
smallest possible nonzero resilient Walsh magnitude is at most the cube size. -/
theorem two_mul_nonlinearity_add_two_pow_m_add_two_le_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    2 * nonlinearity f + 2 ^ (m + 2) ≤ 2 ^ n := by
  have hmax :=
    two_pow_m_add_two_le_maxWalshMagnitude_of_isResilient f m hm hf
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  omega

/-- Additive form of the Sarkar--Maitra bound, avoiding truncated subtraction. -/
theorem nonlinearity_add_two_pow_m_add_one_le_two_pow_sub_one_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    nonlinearity f + 2 ^ (m + 1) ≤ 2 ^ (n - 1) := by
  have hbound :=
    two_mul_nonlinearity_add_two_pow_m_add_two_le_of_isResilient
      f m hm hf
  have hdimension :
      2 ^ n = 2 * 2 ^ (n - 1) := by
    exact two_pow_eq_two_mul_two_pow_sub_one n (by omega)
  have hamplitude :
      2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    exact two_pow_add_two_eq_two_mul_two_pow_add_one m
  omega

/-- Sarkar--Maitra bound in Carlet's printed subtraction form. -/
theorem nonlinearity_le_two_pow_sub_two_pow_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    nonlinearity f ≤ 2 ^ (n - 1) - 2 ^ (m + 1) := by
  exact Nat.le_sub_of_add_le
    (nonlinearity_add_two_pow_m_add_one_le_two_pow_sub_one_of_isResilient
      f m hm hf)

theorem maxWalshMagnitude_eq_two_pow_m_add_two_of_nonlinearity_eq
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hnonlinearity :
      nonlinearity f = 2 ^ (n - 1) - 2 ^ (m + 1)) :
    maxWalshMagnitude f = 2 ^ (m + 2) := by
  have hpowerLe : 2 ^ (m + 1) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hadd :
      nonlinearity f + 2 ^ (m + 1) = 2 ^ (n - 1) := by
    calc
      nonlinearity f + 2 ^ (m + 1) =
          (2 ^ (n - 1) - 2 ^ (m + 1)) + 2 ^ (m + 1) := by
        rw [hnonlinearity]
      _ = 2 ^ (n - 1) := Nat.sub_add_cancel hpowerLe
  have hdimension :
      2 ^ n = 2 * 2 ^ (n - 1) := by
    exact two_pow_eq_two_mul_two_pow_sub_one n (by omega)
  have hamplitude :
      2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    exact two_pow_add_two_eq_two_mul_two_pow_add_one m
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  omega

/-- Equality in the Sarkar--Maitra bound is equivalent to plateauedness with
nonzero Walsh magnitude exactly `2^(m+2)`. -/
theorem nonlinearity_eq_sarkarMaitra_bound_iff_hasPlateauedWalshAmplitude
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    nonlinearity f = 2 ^ (n - 1) - 2 ^ (m + 1) ↔
      HasPlateauedWalshAmplitude f (2 ^ (m + 2)) := by
  constructor
  · intro hnonlinearity
    have hmax :=
      maxWalshMagnitude_eq_two_pow_m_add_two_of_nonlinearity_eq
        f m hm hnonlinearity
    have hdiv :=
      two_pow_m_add_two_dvd_walshTransform_of_isResilient f m hm hf
    refine ⟨by positivity, ?_⟩
    intro a
    by_cases ha : walshTransform f a = 0
    · exact Or.inl ha
    · right
      have hdivNat :
          2 ^ (m + 2) ∣ (walshTransform f a).natAbs := by
        apply Int.natCast_dvd.mp
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdiv a
      have hlower : 2 ^ (m + 2) ≤ (walshTransform f a).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hdivNat
      have hupperReal := abs_walshTransform_le_maxWalshMagnitude f a
      have hupper :
          (walshTransform f a).natAbs ≤ 2 ^ (m + 2) := by
        have hupperNat :
            (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
          have hcast : ((walshTransform f a).natAbs : ℝ) ≤
              (maxWalshMagnitude f : ℝ) := by
            simpa only [Nat.cast_natAbs, Int.cast_abs] using hupperReal
          exact_mod_cast hcast
        simpa [hmax] using hupperNat
      exact Nat.le_antisymm hupper hlower
  · intro hplateaued
    have hmax :=
      maxWalshMagnitude_eq_of_hasPlateauedWalshAmplitude
        f (2 ^ (m + 2)) hplateaued
    have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
    have hdimension :
        2 ^ n = 2 * 2 ^ (n - 1) := by
      exact two_pow_eq_two_mul_two_pow_sub_one n (by omega)
    have hamplitude :
        2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
      exact two_pow_add_two_eq_two_mul_two_pow_add_one m
    have hpowerLe : 2 ^ (m + 1) ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- At equality in the Sarkar--Maitra bound, every Walsh coefficient is zero
or one of the two signed values of magnitude `2^(m+2)`. -/
theorem walshTransform_eq_zero_or_eq_neg_two_pow_or_eq_two_pow_of_sarkarMaitra_equality
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f)
    (hnonlinearity :
      nonlinearity f = 2 ^ (n - 1) - 2 ^ (m + 1)) :
    ∀ a : FABL.F₂Cube n,
      walshTransform f a = 0 ∨
        walshTransform f a = -((2 : ℤ) ^ (m + 2)) ∨
          walshTransform f a = (2 : ℤ) ^ (m + 2) := by
  have hplateaued :=
    (nonlinearity_eq_sarkarMaitra_bound_iff_hasPlateauedWalshAmplitude
      f m hm hf).mp hnonlinearity
  intro a
  rcases hplateaued.2 a with hzero | hmagnitude
  · exact Or.inl hzero
  · rcases Int.natAbs_eq_iff.mp hmagnitude with hpositive | hnegative
    · exact Or.inr (Or.inr (by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpositive))
    · exact Or.inr (Or.inl (by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnegative))

/-- Equality in the Sarkar--Maitra bound implies Carlet plateauedness. -/
theorem isPlateaued_of_sarkarMaitra_equality
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f)
    (hnonlinearity :
      nonlinearity f = 2 ^ (n - 1) - 2 ^ (m + 1)) :
    IsPlateaued f := by
  exact ⟨2 ^ (m + 2),
    (nonlinearity_eq_sarkarMaitra_bound_iff_hasPlateauedWalshAmplitude
      f m hm hf).mp hnonlinearity⟩

end CryptBoolean
