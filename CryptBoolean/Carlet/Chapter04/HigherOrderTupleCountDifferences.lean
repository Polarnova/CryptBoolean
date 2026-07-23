/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderTupleCounts

/-!
# Consecutive tuple-count differences

Exact coefficients and dimension-free polynomial bounds for the seventh and
eighth moments in the Carlet--Mesnager argument.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The coefficient of a dual word of weight `w` in
`S₈(f) - 15 · 2ⁿ · S₇(f)` after the common Reed--Muller cardinality is
factored out. -/
noncomputable def tuplePointParityMomentDifference (n w : ℕ) : ℝ :=
  (tuplePointParityMultiplicityByWeight 8 n w : ℝ) -
    15 * (2 : ℝ) ^ n *
      (tuplePointParityMultiplicityByWeight 7 n w : ℝ)

private theorem two_pow_mul_eq_pow_two_pow (n k : ℕ) :
    (2 : ℝ) ^ (k * n) = ((2 : ℝ) ^ n) ^ k := by
  rw [mul_comm, ← pow_mul]

/-- Exact null-word coefficient in the seventh/eighth moment difference. -/
theorem tuplePointParityMomentDifference_zero
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMomentDifference n 0 =
      -9459450 * ((2 : ℝ) ^ n) ^ 7 +
        139999860 * ((2 : ℝ) ^ n) ^ 6 -
        877476600 * ((2 : ℝ) ^ n) ^ 5 +
        2931168240 * ((2 : ℝ) ^ n) ^ 4 -
        5409855360 * ((2 : ℝ) ^ n) ^ 3 +
        5129380608 * ((2 : ℝ) ^ n) ^ 2 -
        1903757312 * (2 : ℝ) ^ n := by
  have hsevenInt := tuplePointParityMultiplicityByWeight_seven_zero n hn
  have heightInt := tuplePointParityMultiplicityByWeight_eight_zero n hn
  have hseven :
      (tuplePointParityMultiplicityByWeight 7 n 0 : ℝ) =
        135135 * (2 : ℝ) ^ (7 * n) -
          1891890 * (2 : ℝ) ^ (6 * n) +
          11351340 * (2 : ℝ) ^ (5 * n) -
          36636600 * (2 : ℝ) ^ (4 * n) +
          65825760 * (2 : ℝ) ^ (3 * n) -
          61152000 * (2 : ℝ) ^ (2 * n) +
          22368256 * (2 : ℝ) ^ n := by
    exact_mod_cast hsevenInt
  have height :
      (tuplePointParityMultiplicityByWeight 8 n 0 : ℝ) =
        2027025 * (2 : ℝ) ^ (8 * n) -
          37837800 * (2 : ℝ) ^ (7 * n) +
          310269960 * (2 : ℝ) ^ (6 * n) -
          1427025600 * (2 : ℝ) ^ (5 * n) +
          3918554640 * (2 : ℝ) ^ (4 * n) -
          6327135360 * (2 : ℝ) ^ (3 * n) +
          5464904448 * (2 : ℝ) ^ (2 * n) -
          1903757312 * (2 : ℝ) ^ n := by
    exact_mod_cast heightInt
  unfold tuplePointParityMomentDifference
  rw [hseven, height]
  simp_rw [two_pow_mul_eq_pow_two_pow n]
  ring

/-- Exact weight-eight coefficient in the seventh/eighth moment difference. -/
theorem tuplePointParityMomentDifference_eight
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMomentDifference n 8 =
      27243216000 * ((2 : ℝ) ^ n) ^ 4 -
        889945056000 * ((2 : ℝ) ^ n) ^ 3 +
        10504984089600 * ((2 : ℝ) ^ n) ^ 2 -
        54385415884800 * (2 : ℝ) ^ n +
        105309161717760 := by
  have hsevenInt := tuplePointParityMultiplicityByWeight_seven_eight n hn
  have heightInt := tuplePointParityMultiplicityByWeight_eight_eight n hn
  have hseven :
      (tuplePointParityMultiplicityByWeight 7 n 8 : ℝ) =
        1816214400 * (2 : ℝ) ^ (3 * n) -
          32691859200 * (2 : ℝ) ^ (2 * n) +
          203416012800 * (2 : ℝ) ^ n - 435430195200 := by
    exact_mod_cast hsevenInt
  have height :
      (tuplePointParityMultiplicityByWeight 8 n 8 : ℝ) =
        54486432000 * (2 : ℝ) ^ (4 * n) -
          1380322944000 * (2 : ℝ) ^ (3 * n) +
          13556224281600 * (2 : ℝ) ^ (2 * n) -
          60916868812800 * (2 : ℝ) ^ n + 105309161717760 := by
    exact_mod_cast heightInt
  unfold tuplePointParityMomentDifference
  rw [hseven, height]
  simp_rw [two_pow_mul_eq_pow_two_pow n]
  ring

/-- Exact weight-twelve coefficient in the seventh/eighth moment
difference. -/
theorem tuplePointParityMomentDifference_twelve
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMomentDifference n 12 =
      1961511552000 * ((2 : ℝ) ^ n) ^ 2 -
        38358448128000 * (2 : ℝ) ^ n +
        186910256332800 := by
  have hsevenInt := tuplePointParityMultiplicityByWeight_seven_twelve n hn
  have heightInt := tuplePointParityMultiplicityByWeight_eight_twelve n hn
  have hseven :
      (tuplePointParityMultiplicityByWeight 7 n 12 : ℝ) =
        43589145600 * (2 : ℝ) ^ n - 348713164800 := by
    exact_mod_cast hsevenInt
  have height :
      (tuplePointParityMultiplicityByWeight 8 n 12 : ℝ) =
        2615348736000 * (2 : ℝ) ^ (2 * n) -
          43589145600000 * (2 : ℝ) ^ n + 186910256332800 := by
    exact_mod_cast heightInt
  unfold tuplePointParityMomentDifference
  rw [hseven, height]
  simp_rw [two_pow_mul_eq_pow_two_pow n]
  ring

/-- Exact weight-fourteen coefficient in the seventh/eighth moment
difference. -/
theorem tuplePointParityMomentDifference_fourteen
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMomentDifference n 14 =
      9153720576000 * (2 : ℝ) ^ n - 97639686144000 := by
  have hsevenInt := tuplePointParityMultiplicityByWeight_seven_fourteen n hn
  have heightInt := tuplePointParityMultiplicityByWeight_eight_fourteen n hn
  have hseven :
      (tuplePointParityMultiplicityByWeight 7 n 14 : ℝ) =
        87178291200 := by
    exact_mod_cast hsevenInt
  have height :
      (tuplePointParityMultiplicityByWeight 8 n 14 : ℝ) =
        10461394944000 * (2 : ℝ) ^ n - 97639686144000 := by
    exact_mod_cast heightInt
  unfold tuplePointParityMomentDifference
  rw [hseven, height]
  ring

/-- Exact weight-sixteen coefficient in the seventh/eighth moment
difference. -/
theorem tuplePointParityMomentDifference_sixteen
    (n : ℕ) (hn : 4 ≤ n) :
    tuplePointParityMomentDifference n 16 = 20922789888000 := by
  rw [tuplePointParityMomentDifference,
    tuplePointParityMultiplicityByWeight_seven_sixteen n hn]
  norm_num only [Nat.cast_zero, mul_zero, sub_zero]
  exact_mod_cast tuplePointParityMultiplicityByWeight_eight_sixteen n hn

/-- The null-word coefficient has magnitude `O((2^n)^7)` in the direction
needed for the lower moment bound. -/
theorem tuplePointParityMomentDifference_zero_ge
    (n : ℕ) (hn : 7 ≤ n) :
    tuplePointParityMomentDifference n 0 ≥
      -20000000 * ((2 : ℝ) ^ n) ^ 7 := by
  rw [tuplePointParityMomentDifference_zero n (by omega)]
  have hq : (128 : ℝ) ≤ (2 : ℝ) ^ n := by
    have hpowNat : (2 : ℕ) ^ 7 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hn
    norm_num at hpowNat
    exact_mod_cast hpowNat
  let t : ℝ := (2 : ℝ) ^ n - 128
  have ht : 0 ≤ t := by dsimp only [t]; linarith
  have hidentity :
      (-9459450 * ((2 : ℝ) ^ n) ^ 7 +
          139999860 * ((2 : ℝ) ^ n) ^ 6 -
          877476600 * ((2 : ℝ) ^ n) ^ 5 +
          2931168240 * ((2 : ℝ) ^ n) ^ 4 -
          5409855360 * ((2 : ℝ) ^ n) ^ 3 +
          5129380608 * ((2 : ℝ) ^ n) ^ 2 -
          1903757312 * (2 : ℝ) ^ n) +
        20000000 * ((2 : ℝ) ^ n) ^ 7 =
      10540550 * t ^ 7 + 9584332660 * t ^ 6 +
        3733266211080 * t ^ 5 + 807527454713840 * t ^ 4 +
        104760756411041920 * t ^ 3 +
        8151179294477968128 * t ^ 2 +
        352213550106363426816 * t +
        6520153728953236586496 := by
    dsimp only [t]
    ring
  have hnonneg :
      0 ≤ 10540550 * t ^ 7 + 9584332660 * t ^ 6 +
        3733266211080 * t ^ 5 + 807527454713840 * t ^ 4 +
        104760756411041920 * t ^ 3 +
        8151179294477968128 * t ^ 2 +
        352213550106363426816 * t +
        6520153728953236586496 := by positivity
  linarith

/-- The weight-eight coefficient is nonnegative and at most a fixed multiple
of `(2^n)^4`. -/
theorem tuplePointParityMomentDifference_eight_bounds
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ tuplePointParityMomentDifference n 8 ∧
      tuplePointParityMomentDifference n 8 ≤
        120000000000000 * ((2 : ℝ) ^ n) ^ 4 := by
  rw [tuplePointParityMomentDifference_eight n (by omega)]
  have hq : (128 : ℝ) ≤ (2 : ℝ) ^ n := by
    have hpowNat : (2 : ℕ) ^ 7 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hn
    norm_num at hpowNat
    exact_mod_cast hpowNat
  let t : ℝ := (2 : ℝ) ^ n - 128
  have ht : 0 ≤ t := by dsimp only [t]; linarith
  constructor
  · have hidentity :
        27243216000 * ((2 : ℝ) ^ n) ^ 4 -
            889945056000 * ((2 : ℝ) ^ n) ^ 3 +
            10504984089600 * ((2 : ℝ) ^ n) ^ 2 -
            54385415884800 * (2 : ℝ) ^ n +
            105309161717760 =
          27243216000 * t ^ 4 + 13058581536000 * t ^ 3 +
            2346883188249600 * t ^ 2 +
            187424970801868800 * t +
            5611952691038453760 := by
      dsimp only [t]
      ring
    rw [hidentity]
    positivity
  · have hidentity :
        120000000000000 * ((2 : ℝ) ^ n) ^ 4 -
          (27243216000 * ((2 : ℝ) ^ n) ^ 4 -
            889945056000 * ((2 : ℝ) ^ n) ^ 3 +
            10504984089600 * ((2 : ℝ) ^ n) ^ 2 -
            54385415884800 * (2 : ℝ) ^ n +
            105309161717760) =
          119972756784000 * t ^ 4 + 61426941418464000 * t ^ 3 +
            11794133116811750400 * t ^ 2 +
            1006445535029198131200 * t +
            32206642767308961546240 := by
      dsimp only [t]
      ring
    have hnonneg :
        0 ≤ 119972756784000 * t ^ 4 + 61426941418464000 * t ^ 3 +
          11794133116811750400 * t ^ 2 +
          1006445535029198131200 * t +
          32206642767308961546240 := by positivity
    linarith

/-- The weight-twelve coefficient is nonnegative and at most a fixed
multiple of `(2^n)^2`. -/
theorem tuplePointParityMomentDifference_twelve_bounds
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ tuplePointParityMomentDifference n 12 ∧
      tuplePointParityMomentDifference n 12 ≤
        3000000000000 * ((2 : ℝ) ^ n) ^ 2 := by
  rw [tuplePointParityMomentDifference_twelve n (by omega)]
  have hq : (128 : ℝ) ≤ (2 : ℝ) ^ n := by
    have hpowNat : (2 : ℕ) ^ 7 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hn
    norm_num at hpowNat
    exact_mod_cast hpowNat
  let t : ℝ := (2 : ℝ) ^ n - 128
  have ht : 0 ≤ t := by dsimp only [t]; linarith
  constructor
  · have hidentity :
        1961511552000 * ((2 : ℝ) ^ n) ^ 2 -
            38358448128000 * (2 : ℝ) ^ n + 186910256332800 =
          1961511552000 * t ^ 2 + 463788509184000 * t +
            27414434163916800 := by
      dsimp only [t]
      ring
    rw [hidentity]
    positivity
  · have hidentity :
        3000000000000 * ((2 : ℝ) ^ n) ^ 2 -
          (1961511552000 * ((2 : ℝ) ^ n) ^ 2 -
            38358448128000 * (2 : ℝ) ^ n + 186910256332800) =
          1038488448000 * t ^ 2 + 304211490816000 * t +
            21737565836083200 := by
      dsimp only [t]
      ring
    have hnonneg :
        0 ≤ 1038488448000 * t ^ 2 + 304211490816000 * t +
          21737565836083200 := by positivity
    linarith

/-- The weight-fourteen coefficient is nonnegative and at most a fixed
multiple of `2^n`. -/
theorem tuplePointParityMomentDifference_fourteen_bounds
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ tuplePointParityMomentDifference n 14 ∧
      tuplePointParityMomentDifference n 14 ≤
        10000000000000 * (2 : ℝ) ^ n := by
  rw [tuplePointParityMomentDifference_fourteen n (by omega)]
  have hq : (128 : ℝ) ≤ (2 : ℝ) ^ n := by
    have hpowNat : (2 : ℕ) ^ 7 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hn
    norm_num at hpowNat
    exact_mod_cast hpowNat
  constructor <;> nlinarith

/-- The weight-sixteen coefficient is positive and bounded by a fixed
constant. -/
theorem tuplePointParityMomentDifference_sixteen_bounds
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ tuplePointParityMomentDifference n 16 ∧
      tuplePointParityMomentDifference n 16 ≤ 21000000000000 := by
  rw [tuplePointParityMomentDifference_sixteen n (by omega)]
  norm_num

end CryptBoolean
