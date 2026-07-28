/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AutocorrelationBounds
public import CryptBoolean.Carlet.Chapter04.AutocorrelationIdentities
public import CryptBoolean.Carlet.Chapter06.Bentness

/-!
# Carlet Chapter 6 second-order characterization

Carlet Proposition 24 and relation (52), in derivative, convolution, and Walsh forms.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The double sum of the signs of all second derivatives at a fixed point. -/
noncomputable def secondDerivativeDoubleSum
    (f : BooleanFunction n) (x : FABL.F₂Cube n) : ℝ :=
  ∑ a, ∑ e, realSignView (secondBooleanDerivative f a e) x

/-- The unnormalized threefold additive convolution of a real cube function. -/
noncomputable def rawTripleConvolution
    (φ : FABL.F₂Cube n → ℝ) : FABL.F₂Cube n → ℝ :=
  rawConvolution φ (rawConvolution φ φ)

/-- The fixed-point second-derivative sum is the sign view times its threefold
raw convolution. -/
theorem secondDerivativeDoubleSum_eq_mul_rawTripleConvolution
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    secondDerivativeDoubleSum f x =
      realSignView f x * rawTripleConvolution (realSignView f) x := by
  classical
  calc
    secondDerivativeDoubleSum f x =
        ∑ a, ∑ e, realSignView f x * realSignView f a *
          realSignView f e * realSignView f (x + a + e) := by
      rw [secondDerivativeDoubleSum]
      simp_rw [secondBooleanDerivative, realSignView_booleanDerivative]
      rw [← Equiv.sum_comp (Equiv.addRight x)]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← Equiv.sum_comp (Equiv.addRight x)]
      apply Finset.sum_congr rfl
      intro e _he
      have hx : x + x = 0 := ZModModule.add_self x
      rw [show (Equiv.addRight x) a = a + x by rfl,
        show (Equiv.addRight x) e = e + x by rfl]
      rw [show x + (a + x) = a by
        calc
          x + (a + x) = (x + x) + a := by ac_rfl
          _ = a := by rw [hx, zero_add]]
      rw [show x + (e + x) = e by
        calc
          x + (e + x) = (x + x) + e := by ac_rfl
          _ = e := by rw [hx, zero_add]]
      rw [show a + (e + x) = x + a + e by abel]
      ring
    _ = realSignView f x * rawTripleConvolution (realSignView f) x := by
      unfold rawTripleConvolution rawConvolution
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- The raw Fourier transform sends threefold raw convolution to a cube. -/
theorem rawFourierTransform_rawTripleConvolution
    (φ : FABL.F₂Cube n → ℝ) (u : FABL.F₂Cube n) :
    rawFourierTransform (rawTripleConvolution φ) u =
      rawFourierTransform φ u ^ 3 := by
  rw [rawTripleConvolution, rawFourierTransform_rawConvolution,
    rawFourierTransform_rawConvolution]
  ring

theorem rawFourierTransform_const_mul_realSignView
    (f : BooleanFunction n) (c : ℝ) (u : FABL.F₂Cube n) :
    rawFourierTransform
        (fun x ↦ c * realSignView f x) u =
      c * (walshTransform f u : ℝ) := by
  rw [rawFourierTransform]
  calc
    (∑ x, c * realSignView f x *
        FABL.vectorWalshCharacter u x) =
        c * ∑ x, realSignView f x *
          FABL.vectorWalshCharacter u x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = c * (walshTransform f u : ℝ) := by
      rw [walshTransform_cast_eq_sum_realSignView_mul_character]

theorem eq_of_rawFourierTransform_eq
    (φ ψ : FABL.F₂Cube n → ℝ)
    (h : rawFourierTransform φ = rawFourierTransform ψ) :
    φ = ψ := by
  funext x
  have hx := congrArg (fun θ ↦ rawFourierTransform θ x) h
  rw [rawFourierTransform_involution, rawFourierTransform_involution] at hx
  exact mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0) hx

private theorem walshTransform_cube_eq_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) (u : FABL.F₂Cube n) :
    (walshTransform f u : ℝ) ^ 3 =
      (2 : ℝ) ^ n * (walshTransform f u : ℝ) := by
  have hflat := (hasFlatWalshSpectrum_iff_isBent f).2 hf u
  have hsquare := congrArg (fun r : ℝ ↦ r ^ 2) hflat
  rw [sq_abs, Real.sq_sqrt (by positivity)] at hsquare
  calc
    (walshTransform f u : ℝ) ^ 3 =
        (walshTransform f u : ℝ) ^ 2 * (walshTransform f u : ℝ) := by ring
    _ = (2 : ℝ) ^ n * (walshTransform f u : ℝ) := by rw [hsquare]

private theorem rawTripleConvolution_realSignView_eq_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) :
    rawTripleConvolution (realSignView f) =
      fun x ↦ (2 : ℝ) ^ n * realSignView f x := by
  apply eq_of_rawFourierTransform_eq
  funext u
  rw [rawFourierTransform_rawTripleConvolution,
    rawFourierTransform_const_mul_realSignView]
  have hwalsh : rawFourierTransform (realSignView f) u =
      (walshTransform f u : ℝ) := by
    simpa [rawFourierTransform] using
      (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm
  rw [hwalsh]
  exact walshTransform_cube_eq_of_isBent f hf u

/-- Carlet Proposition 24: bentness is equivalent to the fixed-point double
sum of second-derivative signs being exactly `2^n` at every point. -/
theorem isBent_iff_forall_secondDerivativeDoubleSum_eq_two_pow
    (f : BooleanFunction n) :
    IsBent f ↔
      ∀ x : FABL.F₂Cube n,
        secondDerivativeDoubleSum f x = (2 : ℝ) ^ n := by
  constructor
  · intro hf x
    rw [secondDerivativeDoubleSum_eq_mul_rawTripleConvolution,
      rawTripleConvolution_realSignView_eq_of_isBent f hf]
    calc
      realSignView f x * ((2 : ℝ) ^ n * realSignView f x) =
          (2 : ℝ) ^ n * (realSignView f x * realSignView f x) := by ring
      _ = (2 : ℝ) ^ n := by rw [realSignView_mul_self, mul_one]
  · intro h
    apply (isBent_iff_forall_nonzero_derivative_isBalanced f).2
    apply (sumOfSquaresIndicator_eq_two_pow_iff f).1
    rw [sumOfSquaresIndicator_eq_sum_secondBooleanDerivative]
    calc
      (∑ a, ∑ e, ∑ x,
          realSignView (secondBooleanDerivative f a e) x) =
          ∑ a, ∑ x, ∑ e,
            realSignView (secondBooleanDerivative f a e) x := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact Finset.sum_comm
      _ = ∑ x, ∑ a, ∑ e,
          realSignView (secondBooleanDerivative f a e) x :=
        Finset.sum_comm
      _ = ∑ x, secondDerivativeDoubleSum f x := by
        rfl
      _ = ∑ _x : FABL.F₂Cube n, (2 : ℝ) ^ n := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact h x
      _ = (2 : ℝ) ^ (2 * n) := by
        rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
          nsmul_eq_mul]
        norm_num
        rw [← pow_add]
        congr 1
        omega

/-- At a fixed point, the second-derivative sum condition is equivalent to
the corresponding value of the threefold raw convolution. -/
theorem secondDerivativeDoubleSum_eq_two_pow_iff_rawTripleConvolution_eq
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    secondDerivativeDoubleSum f x = (2 : ℝ) ^ n ↔
      rawTripleConvolution (realSignView f) x =
        (2 : ℝ) ^ n * realSignView f x := by
  rw [secondDerivativeDoubleSum_eq_mul_rawTripleConvolution]
  constructor
  · intro h
    calc
      rawTripleConvolution (realSignView f) x =
          1 * rawTripleConvolution (realSignView f) x := by ring
      _ = (realSignView f x * realSignView f x) *
          rawTripleConvolution (realSignView f) x := by
        rw [realSignView_mul_self]
      _ = realSignView f x *
          (realSignView f x * rawTripleConvolution (realSignView f) x) := by ring
      _ = realSignView f x * (2 : ℝ) ^ n := by rw [h]
      _ = (2 : ℝ) ^ n * realSignView f x := by ring
  · intro h
    calc
      realSignView f x * rawTripleConvolution (realSignView f) x =
          realSignView f x * ((2 : ℝ) ^ n * realSignView f x) := by rw [h]
      _ = (2 : ℝ) ^ n * (realSignView f x * realSignView f x) := by ring
      _ = (2 : ℝ) ^ n := by rw [realSignView_mul_self, mul_one]

/-- Bentness is equivalent to the threefold raw convolution eigenvalue
identity for the sign view. -/
theorem isBent_iff_rawTripleConvolution_realSignView_eq
    (f : BooleanFunction n) :
    IsBent f ↔
      rawTripleConvolution (realSignView f) =
        fun x ↦ (2 : ℝ) ^ n * realSignView f x := by
  constructor
  · exact rawTripleConvolution_realSignView_eq_of_isBent f
  · intro h
    apply (isBent_iff_forall_secondDerivativeDoubleSum_eq_two_pow f).2
    intro x
    apply
      (secondDerivativeDoubleSum_eq_two_pow_iff_rawTripleConvolution_eq f x).2
    exact congrFun h x

/-- The frequency-domain form of Proposition 24: bentness is equivalent to
the cubic raw Walsh identity at every frequency. -/
theorem isBent_iff_forall_walshTransform_cube_eq
    (f : BooleanFunction n) :
    IsBent f ↔
      ∀ u : FABL.F₂Cube n,
        walshTransform f u ^ 3 =
          (2 ^ n : ℤ) * walshTransform f u := by
  constructor
  · intro hf u
    exact_mod_cast walshTransform_cube_eq_of_isBent f hf u
  · intro h
    apply (isBent_iff_rawTripleConvolution_realSignView_eq f).2
    apply eq_of_rawFourierTransform_eq
    funext u
    rw [rawFourierTransform_rawTripleConvolution,
      rawFourierTransform_const_mul_realSignView]
    have hwalsh : rawFourierTransform (realSignView f) u =
        (walshTransform f u : ℝ) := by
      simpa [rawFourierTransform] using
        (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm
    rw [hwalsh]
    exact_mod_cast h u

end CryptBoolean
