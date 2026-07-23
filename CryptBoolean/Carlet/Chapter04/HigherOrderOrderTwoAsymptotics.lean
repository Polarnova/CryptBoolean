/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwo
public import CryptBoolean.Carlet.Chapter04.HigherOrderTupleCounts
public import CryptBoolean.Carlet.Chapter04.IndicatorSpectralBounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# Asymptotic order-two moment estimates

Uniform denominator and ratio estimates that turn the low-weight dual-code
character bounds into Carlet--Mesnager's order-two covering-radius base.
-/

open Finset Filter
open scoped BigOperators BooleanCube Topology

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The support of a tuple's point-parity word is contained in the tuple's
image. -/
theorem hammingWeight_tuplePointParity_le
    {m : ℕ} (x : Fin m → FABL.F₂Cube n) :
    hammingWeight (tuplePointParity x) ≤ m := by
  rw [hammingWeight_eq_card_support]
  calc
    (support (tuplePointParity x)).card ≤
        (Finset.univ.image x).card := by
      apply Finset.card_le_card
      intro y hy
      by_contra hyimage
      have hne (i : Fin m) : x i ≠ y := by
        intro hxy
        apply hyimage
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hxy⟩
      have hzero : tuplePointParity x y = 0 := by
        simp [tuplePointParity, hne]
      have hyone := (mem_support (tuplePointParity x) y).mp hy
      rw [hzero] at hyone
      norm_num at hyone
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = m := by simp

private theorem tuplePointParity_fin_two_eq_zero_iff
    (x : Fin 2 → FABL.F₂Cube n) :
    tuplePointParity x = 0 ↔ x 0 = x 1 := by
  constructor
  · intro hzero
    by_contra hne
    have happ := congrFun hzero (x 0)
    have hfilter :
        (Finset.univ.filter fun i : Fin 2 ↦ x i = x 0) = {0} := by
      ext i
      fin_cases i <;> simp [Ne.symm hne]
    simp only [tuplePointParity, Finset.sum_boole, hfilter,
      Finset.card_singleton, Nat.cast_one, Pi.zero_apply] at happ
    norm_num at happ
  · intro heq
    funext y
    by_cases hy : x 0 = y
    · have hall (i : Fin 2) : x i = y := by
        fin_cases i <;> simpa [heq] using hy
      rw [tuplePointParity, Finset.sum_boole]
      have hfilter :
          (Finset.univ.filter fun i : Fin 2 ↦ x i = y) = Finset.univ :=
        Finset.filter_eq_self.mpr fun i _hi ↦ hall i
      rw [hfilter, Finset.card_univ, Fintype.card_fin]
      change (2 : FABL.𝔽₂) = 0
      exact ZMod.natCast_self 2
    · have hnone (i : Fin 2) : x i ≠ y := by
        fin_cases i <;> simpa [heq] using hy
      simp [tuplePointParity, hnone]

private def diagonalPointPair (y : FABL.F₂Cube n) :
    Fin 2 → FABL.F₂Cube n := fun _i ↦ y

private theorem diagonalPointPair_injective :
    Function.Injective (diagonalPointPair (n := n)) := by
  intro x y hxy
  exact congrFun hxy 0

private theorem tuplePointParityMultiplicity_one_zero (n : ℕ) :
    tuplePointParityMultiplicity 1 (0 : BooleanFunction n) = 2 ^ n := by
  classical
  rw [tuplePointParityMultiplicity, tuplePointParityFiber]
  have hfilter :
      (Finset.univ : Finset (Fin 2 → FABL.F₂Cube n)).filter
          (fun x ↦ tuplePointParity x = 0) =
        (Finset.univ : Finset (FABL.F₂Cube n)).image diagonalPointPair := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [tuplePointParity_fin_two_eq_zero_iff]
    constructor
    · intro hx
      refine ⟨x 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · exact hx
    · rintro ⟨y, rfl⟩
      rfl
  rw [hfilter, Finset.card_image_of_injective _ diagonalPointPair_injective,
    Finset.card_univ, card_f₂Cube]

/-- The point-parity multiplicity of the zero word for one pair is the cube
size. -/
theorem tuplePointParityMultiplicityByWeight_one_zero (n : ℕ) :
    tuplePointParityMultiplicityByWeight 1 n 0 = 2 ^ n := by
  calc
    tuplePointParityMultiplicityByWeight 1 n 0 =
        tuplePointParityMultiplicity 1 (0 : BooleanFunction n) := by
      simpa using
        (tuplePointParityMultiplicity_eq_byWeight
          1 (0 : BooleanFunction n)).symm
    _ = 2 ^ n := tuplePointParityMultiplicity_one_zero n

private theorem tuplePointParityMultiplicityByWeight_one_eq_zero_of_dual_ne_zero
    (h : BooleanFunction n) (hn : 3 ≤ n)
    (hdual : h ∈ reedMuller (n - 3) n) (hne : h ≠ 0) :
    tuplePointParityMultiplicityByWeight 1 n (hammingWeight h) = 0 := by
  rw [← tuplePointParityMultiplicity_eq_byWeight 1 h,
    tuplePointParityMultiplicity, tuplePointParityFiber]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _hx hparity
  have hupper := hammingWeight_tuplePointParity_le x
  rw [hparity] at hupper
  have hdegree : FABL.functionAlgebraicDegree h ≤ n - 3 := by
    simpa only [mem_reedMuller_iff] using hdual
  have hlower := two_pow_sub_le_hammingWeight_of_degree_le h hdegree hne
  have hexponent : n - (n - 3) = 3 := by omega
  rw [hexponent] at hlower
  norm_num at hlower
  omega

/-- The second correlation moment over `RM(2,n)` is the code cardinality
times the Boolean cube size. -/
theorem orderTwoCorrelationPowerSum_one_eq
    (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoCorrelationPowerSum 1 f =
      (Nat.card (reedMuller 2 n) : ℝ) * (2 : ℝ) ^ n := by
  rw [orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum 1 f hn]
  congr 1
  calc
    (∑ h ∈ orderTwoDualWords n,
        (tuplePointParityMultiplicityByWeight 1 n (hammingWeight h) : ℝ) *
          FABL.binarySign (booleanFunctionPairing n f h)) =
        (tuplePointParityMultiplicityByWeight 1 n
            (hammingWeight (0 : BooleanFunction n)) : ℝ) *
          FABL.binarySign
            (booleanFunctionPairing n f (0 : BooleanFunction n)) := by
      apply Finset.sum_eq_single 0
      · intro h hh hne
        have hdual : h ∈ reedMuller (n - 3) n := by
          simpa only [orderTwoDualWords, Finset.mem_filter, Finset.mem_univ,
            true_and] using hh
        rw [tuplePointParityMultiplicityByWeight_one_eq_zero_of_dual_ne_zero
          h hn hdual hne]
        simp
      · simp [orderTwoDualWords]
    _ = (2 : ℝ) ^ n := by
      simp [tuplePointParityMultiplicityByWeight_one_zero]

/-- Jensen's inequality and the exact second moment give the code-cardinality
scaled denominator required by the seventh/eighth moment comparison. -/
theorem reedMuller_card_mul_two_pow_seven_le_orderTwoCorrelationPowerSum_seven
    (f : BooleanFunction n) (hn : 3 ≤ n) :
    (Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7 ≤
      orderTwoCorrelationPowerSum 7 f := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  have hjensen :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (reedMuller 2 n)))
      (f := fun g : reedMuller 2 n ↦
        (orderTwoCorrelation f g.1) ^ 2)
      (fun g _hg ↦ sq_nonneg (orderTwoCorrelation f g.1)) 6
  have hmoments :
      (orderTwoCorrelationPowerSum 1 f) ^ 7 ≤
        (Nat.card (reedMuller 2 n) : ℝ) ^ 6 *
          orderTwoCorrelationPowerSum 7 f := by
    simpa only [orderTwoCorrelationPowerSum, mul_one, pow_mul,
      Nat.card_eq_fintype_card, Finset.card_univ] using hjensen
  rw [orderTwoCorrelationPowerSum_one_eq f hn] at hmoments
  have hcard : 0 < (Nat.card (reedMuller 2 n) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hfactor :
      ((Nat.card (reedMuller 2 n) : ℝ) * (2 : ℝ) ^ n) ^ 7 =
        (Nat.card (reedMuller 2 n) : ℝ) ^ 6 *
          ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) := by
    ring
  rw [hfactor] at hmoments
  exact le_of_mul_le_mul_left hmoments (pow_pos hcard 6)

/-- Parseval forces the squared largest raw Walsh coefficient to be at least
the Boolean cube size. -/
theorem two_pow_le_maxWalshMagnitude_sq (f : BooleanFunction n) :
    (2 : ℝ) ^ n ≤ (maxWalshMagnitude f : ℝ) ^ 2 := by
  have hsum :
      (∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2) ≤
        ∑ _a : FABL.F₂Cube n, (maxWalshMagnitude f : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _ha
    have habs := abs_walshTransform_le_maxWalshMagnitude f a
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
  rw [sum_walshTransform_sq_eq_two_pow_sq, Finset.sum_const,
    Finset.card_univ, card_f₂Cube, nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  nlinarith

/-- The affine subcode and Parseval give the uniform denominator estimate
`S_k(f) ≥ (2^n)^k`. -/
theorem two_pow_pow_le_orderTwoCorrelationPowerSum
    (k : ℕ) (f : BooleanFunction n) :
    ((2 : ℝ) ^ n) ^ k ≤ orderTwoCorrelationPowerSum k f := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  have hmaximum :
      ∃ a : FABL.F₂Cube n,
        |(walshTransform f a : ℝ)| = (maxWalshMagnitude f : ℝ) := by
    unfold maxWalshMagnitude
    obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube n))) Finset.univ_nonempty
      (fun u ↦ (walshTransform f u).natAbs)
    refine ⟨a, ?_⟩
    rw [hmax, Nat.cast_natAbs, Int.cast_abs]
  obtain ⟨a, ha⟩ := hmaximum
  let g : reedMuller 2 n :=
    ⟨FABL.affineFunction 0 a,
      reedMuller_mono (by omega : 1 ≤ 2)
        (affineFunction_mem_reedMuller_one 0 a)⟩
  have hcorrelation :
      orderTwoCorrelation f g.1 = walshTransform f a := by
    unfold orderTwoCorrelation walshTransform walshTerm
    push_cast
    apply Finset.sum_congr rfl
    intro x _hx
    simp [g, FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
  have htermLe :
      (orderTwoCorrelation f g.1) ^ (2 * k) ≤
        orderTwoCorrelationPowerSum k f := by
    rw [orderTwoCorrelationPowerSum]
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (reedMuller 2 n)))
      (f := fun h : reedMuller 2 n ↦
        (orderTwoCorrelation f h.1) ^ (2 * k))
      (fun h _hh ↦ by
        rw [show 2 * k = k * 2 by omega, pow_mul]
        exact sq_nonneg ((orderTwoCorrelation f h.1) ^ k))
      (Finset.mem_univ g)
    simpa using hsingle
  have hmaxSq := two_pow_le_maxWalshMagnitude_sq f
  have hpower :
      ((2 : ℝ) ^ n) ^ k ≤
        ((maxWalshMagnitude f : ℝ) ^ 2) ^ k :=
    pow_le_pow_left₀ (by positivity) hmaxSq k
  calc
    ((2 : ℝ) ^ n) ^ k ≤
        ((maxWalshMagnitude f : ℝ) ^ 2) ^ k := hpower
    _ = (maxWalshMagnitude f : ℝ) ^ (2 * k) := by
      rw [pow_mul]
    _ = |(walshTransform f a : ℝ)| ^ (2 * k) := by rw [ha]
    _ = (|(walshTransform f a : ℝ)| ^ 2) ^ k := by rw [pow_mul]
    _ = ((walshTransform f a : ℝ) ^ 2) ^ k := by rw [sq_abs]
    _ = (walshTransform f a : ℝ) ^ (2 * k) := by rw [pow_mul]
    _ = (orderTwoCorrelation f g.1) ^ (2 * k) := by rw [hcorrelation]
    _ ≤ orderTwoCorrelationPowerSum k f := htermLe

/-- An additive `K (2^n)^7` remainder in the eighth-versus-seventh moment
comparison becomes an additive constant in the quotient. -/
theorem orderTwoCorrelationPowerSum_eight_div_seven_ge
    (f : BooleanFunction n) (K : ℝ) (hK : 0 ≤ K)
    (hdifference :
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((2 : ℝ) ^ n) ^ 7 ≤
        orderTwoCorrelationPowerSum 8 f) :
    15 * (2 : ℝ) ^ n - K ≤
      orderTwoCorrelationPowerSum 8 f /
        orderTwoCorrelationPowerSum 7 f := by
  have hden := orderTwoCorrelationPowerSum_pos 7 f
  have hdenLower := two_pow_pow_le_orderTwoCorrelationPowerSum 7 f
  have hremainder :
      K * ((2 : ℝ) ^ n) ^ 7 ≤
        K * orderTwoCorrelationPowerSum 7 f :=
    mul_le_mul_of_nonneg_left hdenLower hK
  rw [le_div_iff₀ hden]
  nlinarith

/-- The code-cardinality-scaled remainder produced by dual-weight grouping
also becomes an additive constant in the seventh/eighth moment quotient. -/
theorem orderTwoCorrelationPowerSum_eight_div_seven_ge_of_card_scaled
    (f : BooleanFunction n) (K : ℝ) (hK : 0 ≤ K) (hn : 3 ≤ n)
    (hdifference :
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) ≤
        orderTwoCorrelationPowerSum 8 f) :
    15 * (2 : ℝ) ^ n - K ≤
      orderTwoCorrelationPowerSum 8 f /
        orderTwoCorrelationPowerSum 7 f := by
  have hden := orderTwoCorrelationPowerSum_pos 7 f
  have hdenLower :=
    reedMuller_card_mul_two_pow_seven_le_orderTwoCorrelationPowerSum_seven
      f hn
  have hremainder :
      K * ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) ≤
        K * orderTwoCorrelationPowerSum 7 f :=
    mul_le_mul_of_nonneg_left hdenLower hK
  rw [le_div_iff₀ hden]
  nlinarith

/-- Square roots of powers of the cube size are powers of `√2`. -/
theorem sqrt_two_pow_eq_sqrtTwo_pow (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The quotient estimate gives the sharp square-root term with an additive
`sqrt K` loss. -/
theorem sqrt_fifteen_mul_sqrtTwo_pow_sub_sqrt_le_momentRatio
    (f : BooleanFunction n) (K : ℝ) (hK : 0 ≤ K)
    (hratio :
      15 * (2 : ℝ) ^ n - K ≤
        orderTwoCorrelationPowerSum 8 f /
          orderTwoCorrelationPowerSum 7 f) :
    Real.sqrt 15 * (Real.sqrt 2) ^ n - Real.sqrt K ≤
      Real.sqrt
        (orderTwoCorrelationPowerSum 8 f /
          orderTwoCorrelationPowerSum 7 f) := by
  let R : ℝ :=
    orderTwoCorrelationPowerSum 8 f / orderTwoCorrelationPowerSum 7 f
  have hR : 0 ≤ R := by
    exact div_nonneg (orderTwoCorrelationPowerSum_nonneg 8 f)
      (orderTwoCorrelationPowerSum_nonneg 7 f)
  have hsum : 15 * (2 : ℝ) ^ n ≤ R + K := by
    dsimp only [R]
    linarith
  have hsqrtSum :
      Real.sqrt (15 * (2 : ℝ) ^ n) ≤
        Real.sqrt R + Real.sqrt K := by
    have hleftSq := Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 15 * (2 : ℝ) ^ n)
    have hRSq := Real.sq_sqrt hR
    have hKSq := Real.sq_sqrt hK
    have hleftNonneg := Real.sqrt_nonneg (15 * (2 : ℝ) ^ n)
    have hrightNonneg : 0 ≤ Real.sqrt R + Real.sqrt K := by positivity
    have hproduct : 0 ≤ Real.sqrt R * Real.sqrt K := mul_nonneg
      (Real.sqrt_nonneg R) (Real.sqrt_nonneg K)
    nlinarith
  have hfactor :
      Real.sqrt (15 * (2 : ℝ) ^ n) =
        Real.sqrt 15 * (Real.sqrt 2) ^ n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15),
      sqrt_two_pow_eq_sqrtTwo_pow]
  dsimp only [R] at hsqrtSum ⊢
  rw [hfactor] at hsqrtSum
  linarith

/-- A uniform eighth-versus-seventh moment comparison gives the sharp
order-two covering-radius estimate, with an explicit additive loss. -/
theorem maximumHigherOrderNonlinearity_two_cast_le_of_moment_difference
    (K : ℝ) (hK : 0 ≤ K)
    (hdifference : ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((2 : ℝ) ^ n) ^ 7 ≤
        orderTwoCorrelationPowerSum 8 f) :
    (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
      (2 : ℝ) ^ n / 2 -
        (Real.sqrt 15 / 2) * (Real.sqrt 2) ^ n +
        Real.sqrt K / 2 := by
  obtain ⟨f, hf⟩ := exists_higherOrderNonlinearity_eq_maximum 2 n
  have hratio := orderTwoCorrelationPowerSum_eight_div_seven_ge
    f K hK (hdifference f)
  have hlower :=
    sqrt_fifteen_mul_sqrtTwo_pow_sub_sqrt_le_momentRatio f K hK hratio
  have hupper := sqrt_orderTwoCorrelationPowerSum_ratio_le 7 f
  rw [maximumOrderTwoCorrelation_eq, hf] at hupper
  linarith

/-- A code-cardinality-scaled moment remainder gives the same sharp
order-two covering-radius estimate. -/
theorem maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference
    (K : ℝ) (hK : 0 ≤ K) (hn : 3 ≤ n)
    (hdifference : ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) ≤
        orderTwoCorrelationPowerSum 8 f) :
    (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
      (2 : ℝ) ^ n / 2 -
        (Real.sqrt 15 / 2) * (Real.sqrt 2) ^ n +
        Real.sqrt K / 2 := by
  obtain ⟨f, hf⟩ := exists_higherOrderNonlinearity_eq_maximum 2 n
  have hratio :=
    orderTwoCorrelationPowerSum_eight_div_seven_ge_of_card_scaled
      f K hK hn (hdifference f)
  have hlower :=
    sqrt_fifteen_mul_sqrtTwo_pow_sub_sqrt_le_momentRatio f K hK hratio
  have hupper := sqrt_orderTwoCorrelationPowerSum_ratio_le 7 f
  rw [maximumOrderTwoCorrelation_eq, hf] at hupper
  linarith

/-- Eventual uniform control of the moment remainder is exactly the
Carlet--Mesnager order-two `O(1)` base expected by the Plotkin propagation. -/
theorem eventually_maximumHigherOrderNonlinearity_two_cast_le_of_moment_difference
    (K : ℝ) (hK : 0 ≤ K)
    (hdifference : ∀ᶠ n in Filter.atTop, ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((2 : ℝ) ^ n) ^ 7 ≤
        orderTwoCorrelationPowerSum 8 f) :
    ∀ᶠ n in Filter.atTop,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          (Real.sqrt 15 / 2) * (Real.sqrt 2) ^ n +
          Real.sqrt K / 2 := by
  filter_upwards [hdifference] with n hn
  exact maximumHigherOrderNonlinearity_two_cast_le_of_moment_difference
    K hK hn

/-- Eventual code-cardinality-scaled moment control gives the sharp
order-two `O(1)` base. -/
theorem eventually_maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference
    (K : ℝ) (hK : 0 ≤ K)
    (hdifference : ∀ᶠ n in Filter.atTop, ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) ≤
        orderTwoCorrelationPowerSum 8 f) :
    ∀ᶠ n in Filter.atTop,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          (Real.sqrt 15 / 2) * (Real.sqrt 2) ^ n +
          Real.sqrt K / 2 := by
  filter_upwards [hdifference, Filter.eventually_ge_atTop 3] with n hn hthree
  exact
    maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference
      K hK hthree hn

/-- The complete abstract Carlet--Mesnager closure: a uniform seventh/eighth
moment remainder propagates the sharp order-two constant to every fixed
higher order. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_of_moment_difference
    (K : ℝ) (hK : 0 ≤ K)
    (hdifference : ∀ᶠ n in Filter.atTop, ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((2 : ℝ) ^ n) ^ 7 ≤
        orderTwoCorrelationPowerSum 8 f)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          ((Real.sqrt 15 / 2) *
              (1 + Real.sqrt 2) ^ (r - 2)) *
            (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) := by
  apply exists_maximumHigherOrderNonlinearity_cast_le_of_eventual_orderTwo
    (Real.sqrt 15 / 2) (by positivity) _ r hr
  refine ⟨Real.sqrt K / 2, ?_⟩
  exact eventually_maximumHigherOrderNonlinearity_two_cast_le_of_moment_difference
    K hK hdifference

/-- A code-cardinality-scaled seventh/eighth moment remainder propagates the
sharp Carlet--Mesnager coefficient to every fixed higher order. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_of_card_scaled_moment_difference
    (K : ℝ) (hK : 0 ≤ K)
    (hdifference : ∀ᶠ n in Filter.atTop, ∀ f : BooleanFunction n,
      15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          K * ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) ≤
        orderTwoCorrelationPowerSum 8 f)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          ((Real.sqrt 15 / 2) *
              (1 + Real.sqrt 2) ^ (r - 2)) *
            (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) := by
  apply exists_maximumHigherOrderNonlinearity_cast_le_of_eventual_orderTwo
    (Real.sqrt 15 / 2) (by positivity) _ r hr
  refine ⟨Real.sqrt K / 2, ?_⟩
  exact
    eventually_maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference
      K hK hdifference

end CryptBoolean
