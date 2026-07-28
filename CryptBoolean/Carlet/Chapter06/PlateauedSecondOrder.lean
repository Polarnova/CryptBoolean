/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Plateaued
public import CryptBoolean.Carlet.Chapter06.SecondOrderCharacterization

/-!
# Second-order characterization of plateaued functions

Carlet Proposition 28 and Relation (55).
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A positive integer is the Walsh amplitude exactly when the raw Walsh
transform satisfies its corresponding cubic equation. -/
theorem hasPlateauedWalshAmplitude_iff_forall_walshTransform_cube_eq
    (f : BooleanFunction n) (amplitude : ℕ) :
    HasPlateauedWalshAmplitude f amplitude ↔
      0 < amplitude ∧ ∀ u : FABL.F₂Cube n,
        (walshTransform f u : ℝ) ^ 3 =
          (amplitude : ℝ) ^ 2 * (walshTransform f u : ℝ) := by
  constructor
  · rintro ⟨hamplitude, hspec⟩
    refine ⟨hamplitude, fun u ↦ ?_⟩
    rcases hspec u with hzero | hmagnitude
    · simp [hzero]
    · have habs : |(walshTransform f u : ℝ)| = (amplitude : ℝ) := by
        have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmagnitude
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
      have hsquare : (walshTransform f u : ℝ) ^ 2 = (amplitude : ℝ) ^ 2 := by
        rw [← sq_abs, habs]
      calc
        (walshTransform f u : ℝ) ^ 3 =
            (walshTransform f u : ℝ) ^ 2 * (walshTransform f u : ℝ) := by ring
        _ = (amplitude : ℝ) ^ 2 * (walshTransform f u : ℝ) := by rw [hsquare]
  · rintro ⟨hamplitude, hcubic⟩
    refine ⟨hamplitude, fun u ↦ ?_⟩
    by_cases hzero : walshTransform f u = 0
    · exact Or.inl hzero
    · right
      have hrealZero : (walshTransform f u : ℝ) ≠ 0 := by exact_mod_cast hzero
      have hsquare : (walshTransform f u : ℝ) ^ 2 = (amplitude : ℝ) ^ 2 := by
        apply mul_left_cancel₀ hrealZero
        calc
          (walshTransform f u : ℝ) * (walshTransform f u : ℝ) ^ 2 =
              (walshTransform f u : ℝ) ^ 3 := by ring
          _ = (amplitude : ℝ) ^ 2 * (walshTransform f u : ℝ) := hcubic u
          _ = (walshTransform f u : ℝ) * (amplitude : ℝ) ^ 2 := by ring
      have habs : |(walshTransform f u : ℝ)| = (amplitude : ℝ) := by
        have hnonneg : 0 ≤ (amplitude : ℝ) := by positivity
        rw [← sq_abs] at hsquare
        nlinarith [abs_nonneg (walshTransform f u : ℝ)]
      apply Nat.cast_injective (R := ℝ)
      simpa only [Nat.cast_natAbs, Int.cast_abs] using habs

/-- Carlet Proposition 28, Relation (55): a Boolean function is plateaued
exactly when all fixed-point double sums of second-derivative signs are the
same positive square. -/
theorem isPlateaued_iff_exists_forall_secondDerivativeDoubleSum_eq_sq
    (f : BooleanFunction n) :
    IsPlateaued f ↔
      ∃ amplitude : ℕ, 0 < amplitude ∧
        ∀ x : FABL.F₂Cube n,
          secondDerivativeDoubleSum f x = (amplitude : ℝ) ^ 2 := by
  constructor
  · rintro ⟨amplitude, hf⟩
    have hcubic :=
      (hasPlateauedWalshAmplitude_iff_forall_walshTransform_cube_eq
        f amplitude).1 hf
    refine ⟨amplitude, hcubic.1, fun x ↦ ?_⟩
    have hconvolution :
        rawTripleConvolution (realSignView f) =
          fun y ↦ (amplitude : ℝ) ^ 2 * realSignView f y := by
      apply eq_of_rawFourierTransform_eq
      funext u
      rw [rawFourierTransform_rawTripleConvolution,
        rawFourierTransform_const_mul_realSignView]
      have hwalsh : rawFourierTransform (realSignView f) u =
          (walshTransform f u : ℝ) := by
        simpa [rawFourierTransform] using
          (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm
      rw [hwalsh]
      exact hcubic.2 u
    rw [secondDerivativeDoubleSum_eq_mul_rawTripleConvolution, hconvolution]
    calc
      realSignView f x * ((amplitude : ℝ) ^ 2 * realSignView f x) =
          (amplitude : ℝ) ^ 2 *
            (realSignView f x * realSignView f x) := by ring
      _ = (amplitude : ℝ) ^ 2 := by rw [realSignView_mul_self, mul_one]
  · rintro ⟨amplitude, hamplitude, hsecond⟩
    refine ⟨amplitude,
      (hasPlateauedWalshAmplitude_iff_forall_walshTransform_cube_eq
        f amplitude).2 ⟨hamplitude, ?_⟩⟩
    have hconvolution :
        rawTripleConvolution (realSignView f) =
          fun x ↦ (amplitude : ℝ) ^ 2 * realSignView f x := by
      funext x
      have h := hsecond x
      rw [secondDerivativeDoubleSum_eq_mul_rawTripleConvolution] at h
      calc
        rawTripleConvolution (realSignView f) x =
            1 * rawTripleConvolution (realSignView f) x := by ring
        _ = (realSignView f x * realSignView f x) *
            rawTripleConvolution (realSignView f) x := by
          rw [realSignView_mul_self]
        _ = realSignView f x *
            (realSignView f x * rawTripleConvolution (realSignView f) x) := by ring
        _ = realSignView f x * (amplitude : ℝ) ^ 2 := by rw [h]
        _ = (amplitude : ℝ) ^ 2 * realSignView f x := by ring
    intro u
    have hu := congrArg (fun φ ↦ rawFourierTransform φ u) hconvolution
    rw [rawFourierTransform_rawTripleConvolution,
      rawFourierTransform_const_mul_realSignView] at hu
    have hwalsh : rawFourierTransform (realSignView f) u =
        (walshTransform f u : ℝ) := by
      simpa [rawFourierTransform] using
        (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm
    simpa only [hwalsh] using hu

end CryptBoolean
