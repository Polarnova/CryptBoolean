/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.IndicatorSpectralBounds
public import CryptBoolean.Carlet.Chapter06.Bentness
import Mathlib.Data.Nat.Factors

/-!
# Plateaued Boolean functions

Carlet Section 6.8: integral Walsh amplitudes and the full-support bent characterization.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A Boolean function has Walsh amplitude `amplitude` when every raw Walsh
coefficient is zero or has that positive integral magnitude. -/
def HasPlateauedWalshAmplitude
    (f : BooleanFunction n) (amplitude : ℕ) : Prop :=
  0 < amplitude ∧ ∀ a, walshTransform f a = 0 ∨
    (walshTransform f a).natAbs = amplitude

/-- A Boolean function is plateaued when it has some positive integral Walsh amplitude. -/
def IsPlateaued (f : BooleanFunction n) : Prop :=
  ∃ amplitude : ℕ, HasPlateauedWalshAmplitude f amplitude

/-- Carlet's integral-amplitude definition agrees with the existing real
flat-on-support predicate. -/
theorem isPlateaued_iff_hasPlateauedWalshSpectrum
    (f : BooleanFunction n) :
    IsPlateaued f ↔ HasPlateauedWalshSpectrum f := by
  constructor
  · rintro ⟨amplitude, hamplitude, hspec⟩
    refine ⟨(amplitude : ℝ), by exact_mod_cast hamplitude, ?_⟩
    intro a
    rcases hspec a with hzero | hmagnitude
    · left
      simp [hzero]
    · right
      have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmagnitude
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  · rintro ⟨c, hc, hspec⟩
    obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
    have huMagnitude : |(walshTransform f u : ℝ)| = c := by
      rcases hspec u with hzero | hmagnitude
      · exact (hu (by exact_mod_cast (abs_eq_zero.mp hzero))).elim
      · exact hmagnitude
    refine ⟨(walshTransform f u).natAbs, ?_, ?_⟩
    · exact Int.natAbs_pos.mpr hu
    · intro a
      rcases hspec a with hzero | hmagnitude
      · left
        exact_mod_cast abs_eq_zero.mp hzero
      · right
        apply Nat.cast_injective (R := ℝ)
        simpa only [Nat.cast_natAbs, Int.cast_abs, huMagnitude] using hmagnitude

/-- A bent function is exactly a plateaued function with full Walsh support. -/
theorem isBent_iff_isPlateaued_and_forall_walshTransform_ne_zero
    (f : BooleanFunction n) :
    IsBent f ↔ IsPlateaued f ∧ ∀ a, walshTransform f a ≠ 0 := by
  constructor
  · intro hf
    refine ⟨⟨2 ^ (n / 2), by positivity, fun a ↦ Or.inr ?_⟩, ?_⟩
    · exact natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a
    · intro a hzero
      have hmagnitude :=
        natAbs_walshTransform_eq_two_pow_half_of_isBent f hf a
      rw [hzero, Int.natAbs_zero] at hmagnitude
      have : 0 < 2 ^ (n / 2) := by positivity
      omega
  · rintro ⟨⟨amplitude, hamplitude, hspec⟩, hnonzero⟩
    have hmagnitude (a : FABL.F₂Cube n) :
        (walshTransform f a).natAbs = amplitude := by
      rcases hspec a with hzero | hmagnitude
      · exact (hnonzero a hzero).elim
      · exact hmagnitude
    have hsum :
        (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) =
          (2 : ℝ) ^ n * (amplitude : ℝ) ^ 2 := by
      calc
        (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) =
            ∑ _a : FABL.F₂Cube n, (amplitude : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _ha
          have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) (hmagnitude a)
          have habs : |(walshTransform f a : ℝ)| = (amplitude : ℝ) := by
            simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
          rw [← sq_abs, habs]
        _ = (2 : ℝ) ^ n * (amplitude : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
          norm_num
    have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
    rw [hsum] at hparseval
    have hamplitudeSquare : (amplitude : ℝ) ^ 2 = (2 : ℝ) ^ n := by
      apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0)
      calc
        (2 : ℝ) ^ n * (amplitude : ℝ) ^ 2 = ((2 : ℝ) ^ n) ^ 2 :=
          hparseval
        _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by ring
    apply (hasFlatWalshSpectrum_iff_isBent f).1
    intro a
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) (hmagnitude a)
    have habs : |(walshTransform f a : ℝ)| = (amplitude : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    rw [habs, ← Real.sqrt_sq
      (by positivity : (0 : ℝ) ≤ (amplitude : ℝ)), hamplitudeSquare]

/-- Parseval determines the product of Walsh-support size and squared plateaued amplitude. -/
theorem card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul
    (f : BooleanFunction n) (amplitude : ℕ)
    (hf : HasPlateauedWalshAmplitude f amplitude) :
    (walshSupport f).card * amplitude ^ 2 = 2 ^ (2 * n) := by
  have hsumSupport :
      (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) =
        ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ha hnot
    have hzero : walshTransform f a = 0 := by
      simpa only [mem_walshSupport, not_ne_iff] using hnot
    simp [hzero]
  have hsumAmplitude :
      (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) =
        ((walshSupport f).card : ℝ) * (amplitude : ℝ) ^ 2 := by
    calc
      (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) =
          ∑ _a ∈ walshSupport f, (amplitude : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hne : walshTransform f a ≠ 0 := (mem_walshSupport f a).mp ha
        have hmagnitude : (walshTransform f a).natAbs = amplitude := by
          rcases hf.2 a with hzero | hmagnitude
          · exact (hne hzero).elim
          · exact hmagnitude
        have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmagnitude
        have habs : |(walshTransform f a : ℝ)| = (amplitude : ℝ) := by
          simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
        rw [← sq_abs, habs]
      _ = ((walshSupport f).card : ℝ) * (amplitude : ℝ) ^ 2 := by
        simp
  have hreal :
      ((walshSupport f).card : ℝ) * (amplitude : ℝ) ^ 2 =
        ((2 : ℝ) ^ n) ^ 2 := by
    rw [← hsumAmplitude, ← hsumSupport]
    exact sum_walshTransform_sq_eq_two_pow_sq f
  have hnat :
      (walshSupport f).card * amplitude ^ 2 = (2 ^ n) ^ 2 := by
    exact_mod_cast hreal
  calc
    (walshSupport f).card * amplitude ^ 2 = (2 ^ n) ^ 2 := hnat
    _ = 2 ^ (2 * n) := by rw [show 2 * n = n * 2 by omega, pow_mul]

/-- The amplitude of a plateaued Boolean function is a power of two, and its
exponent is at least half the dimension. -/
theorem exists_plateauedAmplitudeExponent
    (f : BooleanFunction n) (amplitude : ℕ)
    (hf : HasPlateauedWalshAmplitude f amplitude) :
    ∃ r : ℕ, amplitude = 2 ^ r ∧ n ≤ 2 * r := by
  have hcard :=
    card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul f amplitude hf
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd amplitude with
    ⟨r, hr⟩ | ⟨p, hp, hpAmplitude, hpOdd⟩
  · refine ⟨r, hr, ?_⟩
    have hcardBound : (walshSupport f).card ≤ 2 ^ n := by
      calc
        (walshSupport f).card ≤
            (Finset.univ : Finset (FABL.F₂Cube n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = 2 ^ n := by simp
    have heq :
        (walshSupport f).card * 2 ^ (2 * r) = 2 ^ (2 * n) := by
      calc
        (walshSupport f).card * 2 ^ (2 * r) =
            (walshSupport f).card * (2 ^ r) ^ 2 := by
          rw [show 2 * r = r * 2 by omega, pow_mul]
        _ = (walshSupport f).card * amplitude ^ 2 := by rw [hr]
        _ = 2 ^ (2 * n) := hcard
    have hproduct :
        2 ^ (2 * n) ≤ 2 ^ n * 2 ^ (2 * r) := by
      rw [← heq]
      exact Nat.mul_le_mul_right (2 ^ (2 * r)) hcardBound
    have hpow : 2 ^ (2 * n) ≤ 2 ^ (n + 2 * r) := by
      simpa only [pow_add] using hproduct
    have hexponent : 2 * n ≤ n + 2 * r :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    omega
  · have hpAmplitudeSq : p ∣ amplitude ^ 2 :=
      dvd_trans hpAmplitude (dvd_pow_self amplitude (by omega))
    have hpPower : p ∣ 2 ^ (2 * n) := by
      rw [← hcard]
      exact dvd_mul_of_dvd_right hpAmplitudeSq _
    have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPower
    have hpEq : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpTwo
    rcases hpOdd with ⟨k, hk⟩
    omega

/-- Every Walsh coefficient of a plateaued Boolean function is divisible by
`2^⌈n/2⌉`; this is `2^(n/2)` in even dimension and `2^((n+1)/2)` in odd dimension. -/
theorem two_pow_add_one_div_two_dvd_walshTransform_of_hasPlateauedWalshAmplitude
    (f : BooleanFunction n) (amplitude : ℕ)
    (hf : HasPlateauedWalshAmplitude f amplitude)
    (a : FABL.F₂Cube n) :
    ((2 ^ ((n + 1) / 2) : ℕ) : ℤ) ∣ walshTransform f a := by
  obtain ⟨r, hr, hdimension⟩ :=
    exists_plateauedAmplitudeExponent f amplitude hf
  have hexponent : (n + 1) / 2 ≤ r := by omega
  have hpower : 2 ^ ((n + 1) / 2) ∣ 2 ^ r :=
    (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 2)).mpr hexponent
  rcases hf.2 a with hzero | hmagnitude
  · rw [hzero]
    exact dvd_zero _
  · apply Int.natCast_dvd.mpr
    rw [hmagnitude, hr]
    exact hpower

end CryptBoolean
