/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoAsymptotics
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoLowWeightSpectrum
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightEight
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightFourteen
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.Basic
public import CryptBoolean.Carlet.Chapter04.HigherOrderTupleCountDifferences

/-!
# The seventh/eighth order-two moment difference

The low-weight dual-code grouping and uniform remainder estimate in the
Carlet--Mesnager order-two argument.
-/

open Finset Filter
open scoped BigOperators BooleanCube Topology

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The character sum over the words of a fixed weight in the order-two
dual Reed--Muller code. -/
noncomputable def orderTwoWeightCharacterSum
    (w : ℕ) (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ (orderTwoDualWords n).filter (fun h ↦ hammingWeight h = w),
    FABL.binarySign (booleanFunctionPairing n f h)

/-- A tuple-parity multiplicity vanishes when the prescribed word has more
support points than the tuple has entries. -/
theorem tuplePointParityMultiplicityByWeight_eq_zero_of_lt
    (k : ℕ) (h : BooleanFunction n)
    (hweight : 2 * k < hammingWeight h) :
    tuplePointParityMultiplicityByWeight k n (hammingWeight h) = 0 := by
  rw [← tuplePointParityMultiplicity_eq_byWeight k h,
    tuplePointParityMultiplicity, tuplePointParityFiber]
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro x _hx hparity
  have hupper := hammingWeight_tuplePointParity_le x
  rw [hparity] at hupper
  omega

/-- Above weight sixteen, the coefficient in the seventh/eighth moment
difference vanishes. -/
theorem tuplePointParityMomentDifference_eq_zero_of_sixteen_lt
    (h : BooleanFunction n) (hweight : 16 < hammingWeight h) :
    tuplePointParityMomentDifference n (hammingWeight h) = 0 := by
  rw [tuplePointParityMomentDifference,
    tuplePointParityMultiplicityByWeight_eq_zero_of_lt 8 h (by omega),
    tuplePointParityMultiplicityByWeight_eq_zero_of_lt 7 h (by omega)]
  ring

/-- The fixed-weight definition specializes definitionally to the canonical
weight-eight character sum. -/
theorem orderTwoWeightCharacterSum_eight
    (f : BooleanFunction n) :
    orderTwoWeightCharacterSum 8 f =
      orderTwoWeightEightCharacterSum f := by
  rfl

/-- The fixed-weight definition specializes definitionally to the canonical
weight-twelve character sum. -/
theorem orderTwoWeightCharacterSum_twelve
    (f : BooleanFunction n) :
    orderTwoWeightCharacterSum 12 f =
      orderTwoWeightTwelveCharacterSum f := by
  rfl

/-- The fixed-weight definition specializes definitionally to the canonical
weight-fourteen character sum. -/
theorem orderTwoWeightCharacterSum_fourteen
    (f : BooleanFunction n) :
    orderTwoWeightCharacterSum 14 f =
      orderTwoWeightFourteenCharacterSum f := by
  rfl

/-- The fixed-weight definition specializes definitionally to the canonical
weight-sixteen character sum. -/
theorem orderTwoWeightCharacterSum_sixteen
    (f : BooleanFunction n) :
    orderTwoWeightCharacterSum 16 f =
      orderTwoWeightSixteenCharacterSum f := by
  rfl

/-- The weight-zero character sum consists only of the zero word. -/
theorem orderTwoWeightCharacterSum_zero (f : BooleanFunction n) :
    orderTwoWeightCharacterSum 0 f = 1 := by
  classical
  have hfilter :
      (orderTwoDualWords n).filter (fun h ↦ hammingWeight h = 0) =
        {0} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hh
      exact hammingNorm_eq_zero.mp hh.2
    · rintro rfl
      simp [orderTwoDualWords]
  rw [orderTwoWeightCharacterSum, hfilter]
  simp

/-- The dual-code coefficient sum is supported only at weights
`0, 8, 12, 14, 16`. -/
theorem orderTwoMomentDifferenceCharacterSum_eq_lowWeights
    (f : BooleanFunction n) (hn : 7 ≤ n) :
    (∑ h ∈ orderTwoDualWords n,
        tuplePointParityMomentDifference n (hammingWeight h) *
          FABL.binarySign (booleanFunctionPairing n f h)) =
      tuplePointParityMomentDifference n 0 +
        tuplePointParityMomentDifference n 8 *
          orderTwoWeightEightCharacterSum f +
        tuplePointParityMomentDifference n 12 *
          orderTwoWeightTwelveCharacterSum f +
        tuplePointParityMomentDifference n 14 *
          orderTwoWeightFourteenCharacterSum f +
        tuplePointParityMomentDifference n 16 *
          orderTwoWeightSixteenCharacterSum f := by
  classical
  have hpointwise (h : BooleanFunction n) (hh : h ∈ orderTwoDualWords n) :
      tuplePointParityMomentDifference n (hammingWeight h) *
          FABL.binarySign (booleanFunctionPairing n f h) =
        (if hammingWeight h = 0 then
          tuplePointParityMomentDifference n 0 *
            FABL.binarySign (booleanFunctionPairing n f h) else 0) +
        (if hammingWeight h = 8 then
          tuplePointParityMomentDifference n 8 *
            FABL.binarySign (booleanFunctionPairing n f h) else 0) +
        (if hammingWeight h = 12 then
          tuplePointParityMomentDifference n 12 *
            FABL.binarySign (booleanFunctionPairing n f h) else 0) +
        (if hammingWeight h = 14 then
          tuplePointParityMomentDifference n 14 *
            FABL.binarySign (booleanFunctionPairing n f h) else 0) +
        (if hammingWeight h = 16 then
          tuplePointParityMomentDifference n 16 *
            FABL.binarySign (booleanFunctionPairing n f h) else 0) := by
    have hdual : h ∈ reedMuller (n - 3) n := by
      simpa only [orderTwoDualWords, Finset.mem_filter, Finset.mem_univ,
        true_and] using hh
    have hdegree : FABL.functionAlgebraicDegree h ≤ n - 3 := by
      simpa only [mem_reedMuller_iff] using hdual
    have heven : Even (hammingWeight h) :=
      even_hammingWeight_of_degree_lt_dimension h (by omega)
    by_cases hupper : hammingWeight h ≤ 16
    · rcases hasOrderTwoLowWeightSpectrum (n := n) (by omega)
          h hh heven hupper with hzero | height | htwelve | hfourteen | hsixteen
      · simp [hzero]
      · simp [height]
      · simp [htwelve]
      · simp [hfourteen]
      · simp [hsixteen]
    · have hlarge : 16 < hammingWeight h := by omega
      rw [tuplePointParityMomentDifference_eq_zero_of_sixteen_lt h hlarge]
      have hne0 : hammingWeight h ≠ 0 := by omega
      have hne8 : hammingWeight h ≠ 8 := by omega
      have hne12 : hammingWeight h ≠ 12 := by omega
      have hne14 : hammingWeight h ≠ 14 := by omega
      have hne16 : hammingWeight h ≠ 16 := by omega
      simp [hne0, hne8, hne12, hne14, hne16]
  calc
    (∑ h ∈ orderTwoDualWords n,
        tuplePointParityMomentDifference n (hammingWeight h) *
          FABL.binarySign (booleanFunctionPairing n f h)) =
        ∑ h ∈ orderTwoDualWords n,
          ((if hammingWeight h = 0 then
              tuplePointParityMomentDifference n 0 *
                FABL.binarySign (booleanFunctionPairing n f h) else 0) +
            (if hammingWeight h = 8 then
              tuplePointParityMomentDifference n 8 *
                FABL.binarySign (booleanFunctionPairing n f h) else 0) +
            (if hammingWeight h = 12 then
              tuplePointParityMomentDifference n 12 *
                FABL.binarySign (booleanFunctionPairing n f h) else 0) +
            (if hammingWeight h = 14 then
              tuplePointParityMomentDifference n 14 *
                FABL.binarySign (booleanFunctionPairing n f h) else 0) +
            (if hammingWeight h = 16 then
              tuplePointParityMomentDifference n 16 *
                FABL.binarySign (booleanFunctionPairing n f h) else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact hpointwise h hh
    _ = tuplePointParityMomentDifference n 0 *
          orderTwoWeightCharacterSum 0 f +
        tuplePointParityMomentDifference n 8 *
          orderTwoWeightCharacterSum 8 f +
        tuplePointParityMomentDifference n 12 *
          orderTwoWeightCharacterSum 12 f +
        tuplePointParityMomentDifference n 14 *
          orderTwoWeightCharacterSum 14 f +
        tuplePointParityMomentDifference n 16 *
          orderTwoWeightCharacterSum 16 f := by
      simp only [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_filter]
      simp only [orderTwoWeightCharacterSum, Finset.mul_sum]
    _ = _ := by
      rw [orderTwoWeightCharacterSum_zero,
        orderTwoWeightCharacterSum_eight,
        orderTwoWeightCharacterSum_twelve,
        orderTwoWeightCharacterSum_fourteen,
        orderTwoWeightCharacterSum_sixteen]
      ring

/-- The correlation-power difference is the common code cardinality times
the low-weight coefficient sum. -/
theorem orderTwoCorrelationPowerSum_difference_eq_lowWeights
    (f : BooleanFunction n) (hn : 7 ≤ n) :
    orderTwoCorrelationPowerSum 8 f -
        15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        (tuplePointParityMomentDifference n 0 +
          tuplePointParityMomentDifference n 8 *
            orderTwoWeightEightCharacterSum f +
          tuplePointParityMomentDifference n 12 *
            orderTwoWeightTwelveCharacterSum f +
          tuplePointParityMomentDifference n 14 *
            orderTwoWeightFourteenCharacterSum f +
          tuplePointParityMomentDifference n 16 *
            orderTwoWeightSixteenCharacterSum f) := by
  have hsevenFactor :
      15 * (2 : ℝ) ^ n *
          (∑ h ∈ orderTwoDualWords n,
            (tuplePointParityMultiplicityByWeight 7 n
                (hammingWeight h) : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h)) =
        ∑ h ∈ orderTwoDualWords n,
          15 * (2 : ℝ) ^ n *
            (tuplePointParityMultiplicityByWeight 7 n
              (hammingWeight h) : ℝ) *
            FABL.binarySign (booleanFunctionPairing n f h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _hh
    ring
  rw [orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum
      8 f (by omega),
    orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum
      7 f (by omega),
    ← orderTwoMomentDifferenceCharacterSum_eq_lowWeights f hn]
  unfold tuplePointParityMomentDifference
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [← hsevenFactor]
  ring

/-- A dimension-independent `q⁷` lower bound for the weight-sixteen character
sum gives a code-cardinality-scaled seventh/eighth moment remainder. -/
theorem orderTwoCorrelationPowerSum_difference_ge_of_weightSixteenCharacterSum
    (f : BooleanFunction n) (hn : 7 ≤ n)
    (hweightTwelve : HasWeightTwelveFlatPairClassification n)
    (hweightFourteen : HasWeightFourteenFlatPairClassification n)
    (B : ℝ) (hB : 0 ≤ B)
    (hweightSixteen :
      -B * ((2 : ℝ) ^ n) ^ 7 ≤ orderTwoWeightSixteenCharacterSum f) :
    orderTwoCorrelationPowerSum 8 f -
        15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f ≥
      -(133000020000000 + 21000000000000 * B) *
        ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) := by
  let q : ℝ := (2 : ℝ) ^ n
  let d0 := tuplePointParityMomentDifference n 0
  let d8 := tuplePointParityMomentDifference n 8
  let d12 := tuplePointParityMomentDifference n 12
  let d14 := tuplePointParityMomentDifference n 14
  let d16 := tuplePointParityMomentDifference n 16
  let m8 := orderTwoWeightEightCharacterSum f
  let m12 := orderTwoWeightTwelveCharacterSum f
  let m14 := orderTwoWeightFourteenCharacterSum f
  let m16 := orderTwoWeightSixteenCharacterSum f
  have hq : 2 ≤ q := by
    dsimp only [q]
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hpow
  have hd0 : -20000000 * q ^ 7 ≤ d0 := by
    simpa only [q, d0] using
      tuplePointParityMomentDifference_zero_ge n hn
  have hd8 := tuplePointParityMomentDifference_eight_bounds n hn
  have hd12 := tuplePointParityMomentDifference_twelve_bounds n hn
  have hd14 := tuplePointParityMomentDifference_fourteen_bounds n hn
  have hd16 := tuplePointParityMomentDifference_sixteen_bounds n hn
  have hm8Exact := orderTwoWeightEightCharacterSum_ge f (by omega)
  have hm8 : -q ^ 3 ≤ m8 := by
    have hproduct : q * (q - 1) * (q - 2) ≤ q ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr (by linarith : 1 ≤ q))]
    dsimp only [q, m8] at hm8Exact ⊢
    nlinarith
  have hm12 : -q ^ 5 ≤ m12 := by
    have h := orderTwoWeightTwelveCharacterSum_ge f hweightTwelve
    dsimp only [q, m12] at h ⊢
    have hq5 : 0 ≤ ((2 : ℝ) ^ n) ^ 5 := by positivity
    linarith
  have hm14 : -q ^ 6 ≤ m14 := by
    have h := orderTwoWeightFourteenCharacterSum_ge f hweightFourteen
    dsimp only [q, m14] at h ⊢
    have hq6 : 0 ≤ ((2 : ℝ) ^ n) ^ 6 := by positivity
    linarith
  have hm16 : -B * q ^ 7 ≤ m16 := by
    simpa only [q, m16] using hweightSixteen
  have hterm8 :
      -120000000000000 * q ^ 7 ≤ d8 * m8 := by
    have hmulLower := mul_le_mul_of_nonneg_left hm8 hd8.1
    have hmulUpper := mul_le_mul_of_nonneg_right hd8.2
      (pow_nonneg (by positivity : 0 ≤ q) 3)
    dsimp only [q, d8, m8] at hmulLower hmulUpper ⊢
    nlinarith
  have hterm12 :
      -3000000000000 * q ^ 7 ≤ d12 * m12 := by
    have hmulLower := mul_le_mul_of_nonneg_left hm12 hd12.1
    have hmulUpper := mul_le_mul_of_nonneg_right hd12.2
      (pow_nonneg (by positivity : 0 ≤ q) 5)
    dsimp only [q, d12, m12] at hmulLower hmulUpper ⊢
    nlinarith
  have hterm14 :
      -10000000000000 * q ^ 7 ≤ d14 * m14 := by
    have hmulLower := mul_le_mul_of_nonneg_left hm14 hd14.1
    have hmulUpper := mul_le_mul_of_nonneg_right hd14.2
      (pow_nonneg (by positivity : 0 ≤ q) 6)
    dsimp only [q, d14, m14] at hmulLower hmulUpper ⊢
    nlinarith
  have hterm16 :
      -(21000000000000 * B) * q ^ 7 ≤ d16 * m16 := by
    have hmulLower := mul_le_mul_of_nonneg_left hm16 hd16.1
    have hmulUpper := mul_le_mul_of_nonneg_right hd16.2
      (mul_nonneg hB
        (pow_nonneg (by positivity : 0 ≤ q) 7))
    dsimp only [q, d16, m16] at hmulLower hmulUpper ⊢
    nlinarith
  have hsum :
      -(133000020000000 + 21000000000000 * B) * q ^ 7 ≤
        d0 + d8 * m8 + d12 * m12 + d14 * m14 + d16 * m16 := by
    have hq7 : 0 ≤ q ^ 7 := pow_nonneg (by positivity) 7
    linarith
  rw [orderTwoCorrelationPowerSum_difference_eq_lowWeights f hn]
  have hcard : 0 ≤ (Nat.card (reedMuller 2 n) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hsum hcard
  dsimp only [q, d0, d8, d12, d14, d16, m8, m12, m14, m16] at this ⊢
  nlinarith

/-- Compatibility form using the earlier exceptional-family multiplicity
interface for the weight-sixteen character sum. -/
theorem orderTwoCorrelationPowerSum_difference_ge
    (f : BooleanFunction n) (hn : 7 ≤ n)
    (hweightTwelve : HasWeightTwelveFlatPairClassification n)
    (hweightFourteen : HasWeightFourteenFlatPairClassification n)
    (typeA typeB : Finset (BooleanFunction n))
    (hweightSixteen : HasWeightSixteenExceptionalMultiplicity typeA typeB)
    (hweightSixteenCounts :
      HasWeightSixteenExceptionalCountBounds typeA typeB) :
    orderTwoCorrelationPowerSum 8 f -
        15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f ≥
      -500000000000000 *
        ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) := by
  let q : ℝ := (2 : ℝ) ^ n
  have hq : 2 ≤ q := by
    dsimp only [q]
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hpow
  have hm16Raw := orderTwoWeightSixteenCharacterSum_ge f typeA typeB
    hweightSixteen hweightSixteenCounts
  have hq5le : q ^ 5 ≤ q ^ 7 := by
    calc
      q ^ 5 ≤ q ^ 5 * q ^ 2 :=
        le_mul_of_one_le_right (pow_nonneg (by positivity) 5)
          (one_le_pow₀ (by linarith : 1 ≤ q))
      _ = q ^ 7 := by ring
  have hq6le : q ^ 6 ≤ q ^ 7 := by
    calc
      q ^ 6 ≤ q ^ 6 * q :=
        le_mul_of_one_le_right (pow_nonneg (by positivity) 6)
          (by linarith : 1 ≤ q)
      _ = q ^ 7 := by ring
  have hq7 : 0 ≤ q ^ 7 := pow_nonneg (by positivity) 7
  have hm16 : -17 * ((2 : ℝ) ^ n) ^ 7 ≤
      orderTwoWeightSixteenCharacterSum f := by
    dsimp only [q] at hq5le hq6le hq7
    linarith
  have hgeneric :=
    orderTwoCorrelationPowerSum_difference_ge_of_weightSixteenCharacterSum
      f hn hweightTwelve hweightFourteen 17 (by norm_num) (by
        simpa only [neg_mul] using hm16)
  have hscale : 0 ≤
      (Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7 := by
    positivity
  nlinarith

end CryptBoolean
