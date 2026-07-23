/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AutocorrelationIndicators
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
public import CryptBoolean.Carlet.Chapter04.LinearStructures

/-!
# Carlet Chapter 4 bounds for autocorrelation indicators

The zero direction supplies the universal lower bound for the sum-of-squares indicator. The
remaining autocorrelation coefficients control the absolute indicator, while the linear kernel
supplies a dimension-sensitive strengthening.
-/

open Finset
open scoped BigOperators BooleanCube NNReal

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The zero-direction autocorrelation is the cardinality of the Boolean cube. -/
@[simp] theorem autocorrelation_zero (f : BooleanFunction n) :
    autocorrelation f 0 = (2 : ℝ) ^ n := by
  unfold autocorrelation realSignView FABL.realSignEncodedFunction FABL.signEncodedFunction
  simp_rw [FABL.booleanDerivative, add_zero, ZModModule.add_self]
  rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
  rw [FABL.signValue_signEncode_eq_binarySign,
    (FABL.binarySign_eq_one_iff 0).2 rfl]
  norm_num

/-- Carlet's universal lower bound `V(f) ≥ 2^(2n)`. -/
theorem sumOfSquaresIndicator_lower_bound (f : BooleanFunction n) :
    (2 : ℝ) ^ (2 * n) ≤ sumOfSquaresIndicator f := by
  rw [sumOfSquaresIndicator]
  calc
    (2 : ℝ) ^ (2 * n) = autocorrelation f 0 ^ 2 := by
      rw [autocorrelation_zero, two_mul, pow_add, pow_two]
    _ ≤ ∑ e : FABL.F₂Cube n, autocorrelation f e ^ 2 :=
      Finset.single_le_sum (fun e _ ↦ sq_nonneg (autocorrelation f e))
        (Finset.mem_univ 0)

private theorem sumOfSquaresIndicator_eq_two_pow_iff_autocorrelation
    (f : BooleanFunction n) :
    sumOfSquaresIndicator f = (2 : ℝ) ^ (2 * n) ↔
      ∀ e : FABL.F₂Cube n, e ≠ 0 → autocorrelation f e = 0 := by
  classical
  constructor
  · intro h e he
    have hzeroSq : autocorrelation f 0 ^ 2 = (2 : ℝ) ^ (2 * n) := by
      rw [autocorrelation_zero, two_mul, pow_add, pow_two]
    have hrest : ∑ d ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
        autocorrelation f d ^ 2 = 0 := by
      have hdecomp := Finset.sum_erase_add
        (s := (Finset.univ : Finset (FABL.F₂Cube n)))
        (f := fun d ↦ autocorrelation f d ^ 2) (Finset.mem_univ 0)
      rw [sumOfSquaresIndicator] at h
      linarith
    have hsquare : autocorrelation f e ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun d _ ↦ sq_nonneg (autocorrelation f d))).mp hrest e (by simp [he])
    exact sq_eq_zero_iff.mp hsquare
  · intro h
    rw [sumOfSquaresIndicator]
    calc
      (∑ e : FABL.F₂Cube n, autocorrelation f e ^ 2) = autocorrelation f 0 ^ 2 := by
        apply Finset.sum_eq_single 0
        · intro e _ he
          rw [h e he, zero_pow (by decide)]
        · simp
      _ = (2 : ℝ) ^ (2 * n) := by
        rw [autocorrelation_zero, two_mul, pow_add, pow_two]

/-- Equality in the universal indicator bound holds exactly when every nonzero derivative is
balanced. -/
theorem sumOfSquaresIndicator_eq_two_pow_iff (f : BooleanFunction n) :
    sumOfSquaresIndicator f = (2 : ℝ) ^ (2 * n) ↔
      ∀ e : FABL.F₂Cube n, e ≠ 0 → IsBalanced (FABL.booleanDerivative f e) := by
  rw [sumOfSquaresIndicator_eq_two_pow_iff_autocorrelation]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro _he
  rw [isBalanced_iff_walshTransform_zero_eq_zero,
    autocorrelation_eq_walshTransform_booleanDerivative_zero]
  constructor <;> intro h <;> exact_mod_cast h

private theorem absoluteIndicator_nonneg (f : BooleanFunction n) :
    0 ≤ absoluteIndicator f := by
  exact NNReal.zero_le_coe

private theorem abs_autocorrelation_le_absoluteIndicator
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (he : e ≠ 0) :
    |autocorrelation f e| ≤ absoluteIndicator f := by
  classical
  unfold absoluteIndicator
  rw [← Real.coe_toNNReal |autocorrelation f e| (abs_nonneg _)]
  exact_mod_cast Finset.le_sup
    (f := fun d : FABL.F₂Cube n ↦ Real.toNNReal |autocorrelation f d|)
    (by simp [he] : e ∈ Finset.univ.erase (0 : FABL.F₂Cube n))

/-- The square of the absolute indicator dominates the mean squared nonzero autocorrelation. -/
theorem absoluteIndicator_sq_lower_bound
    (f : BooleanFunction n) (hn : 0 < n) :
    (sumOfSquaresIndicator f - (2 : ℝ) ^ (2 * n)) /
        ((2 : ℝ) ^ n - 1) ≤ absoluteIndicator f ^ 2 := by
  classical
  have hden : 0 < (2 : ℝ) ^ n - 1 := by
    have : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) hn.ne'
    linarith
  apply (div_le_iff₀ hden).2
  have hterm (e : FABL.F₂Cube n) (he : e ≠ 0) :
      autocorrelation f e ^ 2 ≤ absoluteIndicator f ^ 2 := by
    have habs := abs_autocorrelation_le_absoluteIndicator f e he
    have hindicator := absoluteIndicator_nonneg f
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (autocorrelation f e)) hindicator).mpr habs
    simpa only [sq_abs] using hsquare
  have hsum :
      (∑ e ∈ Finset.univ.erase (0 : FABL.F₂Cube n), autocorrelation f e ^ 2) ≤
        ∑ _e ∈ Finset.univ.erase (0 : FABL.F₂Cube n), absoluteIndicator f ^ 2 := by
    apply Finset.sum_le_sum
    intro e he
    exact hterm e (by simpa using he)
  have hdecomp :
      sumOfSquaresIndicator f - (2 : ℝ) ^ (2 * n) =
        ∑ e ∈ Finset.univ.erase (0 : FABL.F₂Cube n), autocorrelation f e ^ 2 := by
    have hsumErase := Finset.sum_erase_add
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      (f := fun e ↦ autocorrelation f e ^ 2) (Finset.mem_univ 0)
    have hzeroSq : autocorrelation f 0 ^ 2 = (2 : ℝ) ^ (2 * n) := by
      rw [autocorrelation_zero, two_mul, pow_add, pow_two]
    rw [sumOfSquaresIndicator]
    linarith
  rw [hdecomp]
  calc
    (∑ e ∈ Finset.univ.erase (0 : FABL.F₂Cube n), autocorrelation f e ^ 2) ≤
        ∑ _e ∈ Finset.univ.erase (0 : FABL.F₂Cube n), absoluteIndicator f ^ 2 := hsum
    _ = absoluteIndicator f ^ 2 * ((2 : ℝ) ^ n - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.cast_card_erase_of_mem (R := ℝ) (Finset.mem_univ 0),
        Finset.card_univ, card_f₂Cube]
      push_cast
      ring_nf

/-- In positive dimension, the absolute indicator is at least the square root of the mean squared
nonzero autocorrelation. -/
theorem absoluteIndicator_lower_bound
    (f : BooleanFunction n) (hn : 0 < n) :
    Real.sqrt ((sumOfSquaresIndicator f - (2 : ℝ) ^ (2 * n)) /
        ((2 : ℝ) ^ n - 1)) ≤ absoluteIndicator f := by
  exact Real.sqrt_le_iff.mpr
    ⟨absoluteIndicator_nonneg f, absoluteIndicator_sq_lower_bound f hn⟩

/-- A linear-structure direction contributes the full squared cube cardinality to the indicator. -/
theorem autocorrelation_sq_of_mem_linearKernel
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (he : e ∈ linearKernel f) :
    autocorrelation f e ^ 2 = (2 : ℝ) ^ (2 * n) := by
  obtain ⟨ε, hε⟩ := (mem_linearKernel f e).mp he
  unfold autocorrelation realSignView FABL.realSignEncodedFunction FABL.signEncodedFunction
  simp_rw [hε]
  rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul,
    two_mul, pow_add, pow_two]
  push_cast
  rcases FABL.signValue_eq_neg_one_or_one (FABL.signEncode ε) with hsign | hsign <;>
    rw [hsign] <;> ring

/-- A `k`-dimensional linear kernel strengthens Carlet's indicator bound to `2^(2n+k)`. -/
theorem sumOfSquaresIndicator_lower_bound_linearKernel (f : BooleanFunction n) :
    (2 : ℝ) ^ (2 * n + Module.finrank FABL.𝔽₂ (linearKernel f)) ≤
      sumOfSquaresIndicator f := by
  classical
  let kernelDirections :=
    Finset.univ.filter (fun e : FABL.F₂Cube n ↦ e ∈ linearKernel f)
  have hsubset :
      (∑ e ∈ kernelDirections, autocorrelation f e ^ 2) ≤
        ∑ e : FABL.F₂Cube n, autocorrelation f e ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ kernelDirections)
      (fun e _ _ ↦ sq_nonneg (autocorrelation f e))
  have hcard : kernelDirections.card =
      2 ^ Module.finrank FABL.𝔽₂ (linearKernel f) := by
    have hkernelCard : Fintype.card (linearKernel f) =
        2 ^ Module.finrank FABL.𝔽₂ (linearKernel f) := by
      rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := linearKernel f),
      Nat.card_zmod]
    simpa [kernelDirections, Fintype.card_subtype] using hkernelCard
  rw [sumOfSquaresIndicator]
  calc
    (2 : ℝ) ^ (2 * n + Module.finrank FABL.𝔽₂ (linearKernel f)) =
        ∑ e ∈ kernelDirections, autocorrelation f e ^ 2 := by
      rw [pow_add]
      calc
        (2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ Module.finrank FABL.𝔽₂ (linearKernel f) =
            (kernelDirections.card : ℝ) * (2 : ℝ) ^ (2 * n) := by
          rw [hcard]
          push_cast
          ring
        _ = ∑ e ∈ kernelDirections, autocorrelation f e ^ 2 := by
          rw [Finset.sum_congr rfl (fun e he ↦ autocorrelation_sq_of_mem_linearKernel
            f e (by simpa [kernelDirections] using he)), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ e : FABL.F₂Cube n, autocorrelation f e ^ 2 := hsubset

/-- Source-form specialization of the linear-kernel bound when its dimension is named `k`. -/
theorem sumOfSquaresIndicator_lower_bound_of_finrank_eq
    (f : BooleanFunction n) (k : ℕ)
    (hk : Module.finrank FABL.𝔽₂ (linearKernel f) = k) :
    (2 : ℝ) ^ (2 * n + k) ≤ sumOfSquaresIndicator f := by
  simpa [hk] using sumOfSquaresIndicator_lower_bound_linearKernel f

end CryptBoolean
