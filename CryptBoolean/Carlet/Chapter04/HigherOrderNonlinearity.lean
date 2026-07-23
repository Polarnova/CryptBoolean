/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import CryptBoolean.Carlet.Chapter02.Derivatives
public import CryptBoolean.Carlet.Chapter03.ReedMuller

/-!
# Carlet Chapter 4 higher-order nonlinearity

Distance to Reed--Muller codes and both recursive lower bounds in Carlet
Proposition 13.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The order-`r` nonlinearity is the minimum raw Hamming distance to `R(r,n)`. -/
noncomputable def higherOrderNonlinearity
    (r : ℕ) (f : BooleanFunction n) : ℕ :=
  letI : Fintype (reedMuller r n) := Fintype.ofFinite (reedMuller r n)
  (Finset.univ : Finset (reedMuller r n)).inf'
    Finset.univ_nonempty fun g ↦ hammingDistance f g.1

/-- Ordinary nonlinearity is first-order Reed--Muller distance. -/
theorem nonlinearity_eq_higherOrderNonlinearity_one
    (f : BooleanFunction n) :
    nonlinearity f = higherOrderNonlinearity 1 f := by
  classical
  letI : Fintype (reedMuller 1 n) := Fintype.ofFinite (reedMuller 1 n)
  unfold nonlinearity higherOrderNonlinearity
  apply le_antisymm
  · apply Finset.le_inf'
    intro g _hg
    obtain ⟨b, a, hga⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one g.1 g.2
    have hle := Finset.inf'_le
      (fun p : FABL.𝔽₂ × FABL.F₂Cube n ↦
        hammingDistance f (FABL.affineFunction p.1 p.2))
      (Finset.mem_univ (b, a))
    simpa [hga] using hle
  · apply Finset.le_inf'
    intro p _hp
    let g : reedMuller 1 n :=
      ⟨FABL.affineFunction p.1 p.2,
        affineFunction_mem_reedMuller_one p.1 p.2⟩
    have hle := Finset.inf'_le
      (fun g : reedMuller 1 n ↦ hammingDistance f g.1)
      (Finset.mem_univ g)
    exact hle

/-- Translating the input preserves Hamming weight. -/
theorem hammingWeight_translate
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    hammingWeight (fun x ↦ f (x + a)) = hammingWeight f := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  change
    (Finset.univ.filter fun x : FABL.F₂Cube n ↦ f (x + a) = 1).card =
      (Finset.univ.filter fun x : FABL.F₂Cube n ↦ f x = 1).card
  rw [Finset.card_filter, Finset.card_filter]
  change
    (∑ x, if f (x + a) = 1 then (1 : ℕ) else 0) =
      ∑ x, if f x = 1 then (1 : ℕ) else 0
  exact Equiv.sum_comp (Equiv.addRight a)
    (fun x ↦ if f x = 1 then (1 : ℕ) else 0)

/-- The weight of a directional derivative is at most twice the original weight. -/
theorem hammingWeight_booleanDerivative_le_two_mul
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    hammingWeight (FABL.booleanDerivative f a) ≤ 2 * hammingWeight f := by
  have htriangle := hammingDist_triangle_left f (fun x ↦ f (x + a)) 0
  rw [hammingDist_zero_left] at htriangle
  change hammingDistance f (fun x ↦ f (x + a)) ≤
    hammingWeight f + hammingWeight (fun x ↦ f (x + a)) at htriangle
  rw [hammingWeight_translate] at htriangle
  rw [hammingDistance_eq_hammingWeight_add] at htriangle
  have hderivative :
      f + (fun x ↦ f (x + a)) = FABL.booleanDerivative f a := rfl
  rw [hderivative] at htriangle
  simpa [two_mul] using htriangle

/-- Directional differentiation distributes over pointwise addition. -/
theorem booleanDerivative_add
    (f g : BooleanFunction n) (a : FABL.F₂Cube n) :
    FABL.booleanDerivative (f + g) a =
      FABL.booleanDerivative f a + FABL.booleanDerivative g a := by
  funext x
  simp only [FABL.booleanDerivative, Pi.add_apply]
  abel

/-- Distance to `R(r,n)` is bounded by the distance to each of its codewords. -/
theorem higherOrderNonlinearity_le_hammingDistance
    (r : ℕ) (f g : BooleanFunction n) (hg : g ∈ reedMuller r n) :
    higherOrderNonlinearity r f ≤ hammingDistance f g := by
  classical
  letI : Fintype (reedMuller r n) := Fintype.ofFinite (reedMuller r n)
  exact Finset.inf'_le
    (fun h : reedMuller r n ↦ hammingDistance f h.1)
    (Finset.mem_univ ⟨g, hg⟩)

/-- The finite Reed--Muller code contains a closest codeword. -/
theorem exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity
    (r : ℕ) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, g ∈ reedMuller r n ∧
      hammingDistance f g = higherOrderNonlinearity r f := by
  classical
  letI : Fintype (reedMuller r n) := Fintype.ofFinite (reedMuller r n)
  obtain ⟨g, _hg, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (reedMuller r n)))
    Finset.univ_nonempty (fun h ↦ hammingDistance f h.1)
  exact ⟨g.1, g.2, hmin.symm⟩

/-- Every derivative's order-`r-1` nonlinearity is at most twice the
order-`r` nonlinearity of the original function. -/
theorem derivative_higherOrderNonlinearity_le_two_mul
    (r : ℕ) (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) ≤
      2 * higherOrderNonlinearity r f := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  have hdegreeDerivative :
      FABL.functionAlgebraicDegree (FABL.booleanDerivative g a) ≤ r - 1 :=
    (FABL.functionAlgebraicDegree_booleanDerivative_le g a).trans
      (Nat.sub_le_sub_right hg 1)
  calc
    higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) ≤
        hammingDistance (FABL.booleanDerivative f a)
          (FABL.booleanDerivative g a) :=
      higherOrderNonlinearity_le_hammingDistance
        (r - 1) (FABL.booleanDerivative f a) (FABL.booleanDerivative g a)
        hdegreeDerivative
    _ = hammingWeight
        (FABL.booleanDerivative f a + FABL.booleanDerivative g a) :=
      hammingDistance_eq_hammingWeight_add _ _
    _ = hammingWeight (FABL.booleanDerivative (f + g) a) := by
      rw [booleanDerivative_add]
    _ ≤ 2 * hammingWeight (f + g) :=
      hammingWeight_booleanDerivative_le_two_mul (f + g) a
    _ = 2 * higherOrderNonlinearity r f := by
      rw [← hammingDistance_eq_hammingWeight_add, hfg]

/-- The largest lower-order nonlinearity among all directional derivatives. -/
noncomputable def maxDerivativeHigherOrderNonlinearity
    (r : ℕ) (f : BooleanFunction n) : ℕ :=
  (Finset.univ : Finset (FABL.F₂Cube n)).sup'
    Finset.univ_nonempty fun a ↦
      higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a)

/-- Division-free form of the first bound in Carlet Proposition 13. -/
theorem maxDerivativeHigherOrderNonlinearity_le_two_mul
    (r : ℕ) (f : BooleanFunction n) :
    maxDerivativeHigherOrderNonlinearity r f ≤
      2 * higherOrderNonlinearity r f := by
  classical
  rw [maxDerivativeHigherOrderNonlinearity]
  apply Finset.sup'_le
  intro a _ha
  exact derivative_higherOrderNonlinearity_le_two_mul r f a

/-- First recursive lower bound in Carlet Proposition 13. -/
theorem proposition_13_first_bound
    (r : ℕ) (f : BooleanFunction n) :
    (maxDerivativeHigherOrderNonlinearity r f : ℝ) / 2 ≤
      (higherOrderNonlinearity r f : ℝ) := by
  have hcast :
      (maxDerivativeHigherOrderNonlinearity r f : ℝ) ≤
        2 * (higherOrderNonlinearity r f : ℝ) := by
    exact_mod_cast maxDerivativeHigherOrderNonlinearity_le_two_mul r f
  linarith

/-- Increasing the Reed--Muller order can only decrease the distance to the code. -/
theorem higherOrderNonlinearity_antitone
    {r s : ℕ} (hrs : r ≤ s) (f : BooleanFunction n) :
    higherOrderNonlinearity s f ≤ higherOrderNonlinearity r f := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  exact (higherOrderNonlinearity_le_hammingDistance s f g
    (reedMuller_mono hrs hg)).trans_eq hfg

/-- For positive order, twice the distance to `R(r,n)` is at most the cube size. -/
theorem two_mul_higherOrderNonlinearity_le_two_pow
    (r : ℕ) (hr : 1 ≤ r) (f : BooleanFunction n) :
    2 * higherOrderNonlinearity r f ≤ 2 ^ n := by
  calc
    2 * higherOrderNonlinearity r f ≤
        2 * higherOrderNonlinearity 1 f :=
      Nat.mul_le_mul_left 2 (higherOrderNonlinearity_antitone hr f)
    _ = 2 * nonlinearity f := by
      rw [nonlinearity_eq_higherOrderNonlinearity_one]
    _ ≤ 2 ^ n := by
      have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
      omega

/-- Autocorrelation is the zero-frequency Walsh value of the derivative. -/
theorem autocorrelation_eq_walshTransform_booleanDerivative_zero
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    autocorrelation f a =
      (walshTransform (FABL.booleanDerivative f a) 0 : ℝ) := by
  rw [autocorrelation, walshTransform_cast_eq_sum_realSignView_mul_character]
  simp

/-- Autocorrelation is cube size minus twice the derivative weight. -/
theorem autocorrelation_eq_two_pow_sub_two_derivative_weight
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    autocorrelation f a =
      (2 ^ n : ℝ) - 2 * hammingWeight (FABL.booleanDerivative f a) := by
  rw [autocorrelation_eq_walshTransform_booleanDerivative_zero,
    walshTransform_zero_eq_two_pow_sub_two_weight]
  push_cast
  ring

/-- The derivative of an order-`r` approximant bounds autocorrelation by the
derivative's order-`r-1` nonlinearity. -/
theorem autocorrelation_le_two_pow_sub_two_higherOrderNonlinearity
    (r : ℕ) (f g : BooleanFunction n) (hg : g ∈ reedMuller r n)
    (a : FABL.F₂Cube n) :
    autocorrelation (f + g) a ≤
      (2 ^ n : ℝ) -
        2 * higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) := by
  have hdegreeDerivative :
      FABL.functionAlgebraicDegree (FABL.booleanDerivative g a) ≤ r - 1 :=
    (FABL.functionAlgebraicDegree_booleanDerivative_le g a).trans
      (Nat.sub_le_sub_right hg 1)
  have hnl := higherOrderNonlinearity_le_hammingDistance
    (r - 1) (FABL.booleanDerivative f a) (FABL.booleanDerivative g a)
    hdegreeDerivative
  have hweight :
      higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) ≤
        hammingWeight (FABL.booleanDerivative (f + g) a) := by
    calc
      higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) ≤
          hammingDistance (FABL.booleanDerivative f a)
            (FABL.booleanDerivative g a) := hnl
      _ = hammingWeight
          (FABL.booleanDerivative f a + FABL.booleanDerivative g a) :=
        hammingDistance_eq_hammingWeight_add _ _
      _ = hammingWeight (FABL.booleanDerivative (f + g) a) := by
        rw [booleanDerivative_add]
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight]
  have hweightReal :
      (higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a) : ℝ) ≤
        (hammingWeight (FABL.booleanDerivative (f + g) a) : ℝ) := by
    exact_mod_cast hweight
  linarith

/-- The sum of lower-order nonlinearities of all directional derivatives. -/
noncomputable def derivativeHigherOrderNonlinearitySum
    (r : ℕ) (f : BooleanFunction n) : ℕ :=
  ∑ a : FABL.F₂Cube n,
    higherOrderNonlinearity (r - 1) (FABL.booleanDerivative f a)

/-- Squared-correlation form underlying the second bound in Carlet Proposition 13. -/
theorem higherOrderNonlinearity_gap_sq_le
    (r : ℕ) (f : BooleanFunction n) :
    ((2 ^ n : ℝ) - 2 * higherOrderNonlinearity r f) ^ 2 ≤
      (2 ^ n : ℝ) ^ 2 -
        2 * derivativeHigherOrderNonlinearitySum r f := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  have hsum :
      (∑ a : FABL.F₂Cube n, autocorrelation (f + g) a) ≤
        ∑ a : FABL.F₂Cube n,
          ((2 ^ n : ℝ) -
            2 * higherOrderNonlinearity (r - 1)
              (FABL.booleanDerivative f a)) := by
    apply Finset.sum_le_sum
    intro a _ha
    exact autocorrelation_le_two_pow_sub_two_higherOrderNonlinearity
      r f g hg a
  have hwalsh :
      (walshTransform (f + g) 0 : ℝ) =
        (2 ^ n : ℝ) - 2 * higherOrderNonlinearity r f := by
    rw [walshTransform_zero_eq_two_pow_sub_two_weight]
    push_cast
    rw [← hammingDistance_eq_hammingWeight_add, hfg]
  calc
    ((2 ^ n : ℝ) - 2 * higherOrderNonlinearity r f) ^ 2 =
        (walshTransform (f + g) 0 : ℝ) ^ 2 := by rw [hwalsh]
    _ = ∑ a : FABL.F₂Cube n, autocorrelation (f + g) a := by
      rw [sum_autocorrelation_eq_walshTransform_zero_sq]
    _ ≤ ∑ a : FABL.F₂Cube n,
        ((2 ^ n : ℝ) -
          2 * higherOrderNonlinearity (r - 1)
            (FABL.booleanDerivative f a)) := hsum
    _ = (2 ^ n : ℝ) ^ 2 -
        2 * derivativeHigherOrderNonlinearitySum r f := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        card_f₂Cube, nsmul_eq_mul, ← Finset.mul_sum]
      rw [derivativeHigherOrderNonlinearitySum, Nat.cast_sum]
      push_cast
      ring

/-- Second recursive lower bound in Carlet Proposition 13. -/
theorem proposition_13_second_bound
    (r : ℕ) (hr : 1 ≤ r) (f : BooleanFunction n) :
    (2 ^ n : ℝ) / 2 -
        Real.sqrt ((2 ^ n : ℝ) ^ 2 -
          2 * derivativeHigherOrderNonlinearitySum r f) / 2 ≤
      (higherOrderNonlinearity r f : ℝ) := by
  have hgap :
      0 ≤ (2 ^ n : ℝ) - 2 * higherOrderNonlinearity r f := by
    have hcardReal :
        2 * (higherOrderNonlinearity r f : ℝ) ≤ (2 ^ n : ℝ) := by
      exact_mod_cast two_mul_higherOrderNonlinearity_le_two_pow r hr f
    linarith
  have hsq := higherOrderNonlinearity_gap_sq_le r f
  have hradicand :
      0 ≤ (2 ^ n : ℝ) ^ 2 -
        2 * derivativeHigherOrderNonlinearitySum r f :=
    (sq_nonneg ((2 ^ n : ℝ) -
      2 * higherOrderNonlinearity r f)).trans hsq
  have hsqrt :
      (2 ^ n : ℝ) - 2 * higherOrderNonlinearity r f ≤
        Real.sqrt ((2 ^ n : ℝ) ^ 2 -
          2 * derivativeHigherOrderNonlinearitySum r f) :=
    (Real.le_sqrt hgap hradicand).mpr hsq
  linarith

/-- Carlet Proposition 13 in the source's `2^(n-1)` and `2^(2n)` notation. -/
theorem proposition_13_second_bound_source_form
    (r : ℕ) (hr : 1 ≤ r) (hrn : r < n) (f : BooleanFunction n) :
    (2 : ℝ) ^ (n - 1) -
        Real.sqrt ((2 : ℝ) ^ (2 * n) -
          2 * derivativeHigherOrderNonlinearitySum r f) / 2 ≤
      (higherOrderNonlinearity r f : ℝ) := by
  have hn : n ≠ 0 := by omega
  have hhalf : (2 ^ n : ℝ) / 2 = (2 : ℝ) ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [pow_succ]
  have hsquare : (2 ^ n : ℝ) ^ 2 = (2 : ℝ) ^ (2 * n) := by
    calc
      (2 ^ n : ℝ) ^ 2 = (2 : ℝ) ^ (n * 2) := (pow_mul 2 n 2).symm
      _ = (2 : ℝ) ^ (2 * n) := by rw [Nat.mul_comm n 2]
  simpa [hhalf, hsquare] using proposition_13_second_bound r hr f

end CryptBoolean
