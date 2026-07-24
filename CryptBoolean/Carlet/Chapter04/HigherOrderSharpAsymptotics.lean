/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoMomentDifference
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoAsymptotics
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightTwelveClassification
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightFourteenClassification

/-!
# Sharp higher-order nonlinearity asymptotics

The final composition layer of the Carlet--Mesnager argument.  A uniform
`q⁷` lower bound for the weight-sixteen dual character sum combines with
the exact weight-twelve and weight-fourteen classifications, the
seventh/eighth moment comparison, and Plotkin propagation.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The dimension-free loss contributed by the three rank-seven orbits and
the rank-at-most-six residual cover. -/
def orderTwoWeightSixteenCharacterLoss : ℝ :=
  3 * 127 + 127 * 2 ^ 128

/-- The resulting uniform constant in the seventh/eighth moment difference. -/
def orderTwoMomentDifferenceLoss : ℝ :=
  133000020000000 +
    21000000000000 * orderTwoWeightSixteenCharacterLoss

/-- A uniform weight-sixteen character-sum estimate closes the sharp
Carlet--Mesnager upper bound in every fixed order. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_of_weightSixteenCharacterSum
    (hweightSixteen : ∀ {n : ℕ} (f : BooleanFunction n), 7 ≤ n →
      -orderTwoWeightSixteenCharacterLoss * ((2 : ℝ) ^ n) ^ 7 ≤
        orderTwoWeightSixteenCharacterSum f)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          ((Real.sqrt 15 / 2) *
              (1 + Real.sqrt 2) ^ (r - 2)) *
            (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) := by
  apply exists_maximumHigherOrderNonlinearity_cast_le_of_card_scaled_moment_difference
    orderTwoMomentDifferenceLoss (by
      unfold orderTwoMomentDifferenceLoss orderTwoWeightSixteenCharacterLoss
      positivity) _ r hr
  filter_upwards [Filter.eventually_ge_atTop 7] with n hn
  intro f
  have hdifference :=
    orderTwoCorrelationPowerSum_difference_ge_of_weightSixteenCharacterSum
      f hn (hasWeightTwelveFlatPairClassification n (by omega))
        (hasWeightFourteenFlatPairClassification n)
        orderTwoWeightSixteenCharacterLoss (by
          unfold orderTwoWeightSixteenCharacterLoss
          positivity)
        (hweightSixteen f hn)
  have hconverted := (le_sub_iff_add_le).mp hdifference
  calc
    15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f -
          orderTwoMomentDifferenceLoss *
            ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) =
        (-orderTwoMomentDifferenceLoss) *
            ((Nat.card (reedMuller 2 n) : ℝ) * ((2 : ℝ) ^ n) ^ 7) +
          15 * (2 : ℝ) ^ n * orderTwoCorrelationPowerSum 7 f := by ring
    _ ≤ orderTwoCorrelationPowerSum 8 f := by
      simpa only [orderTwoMomentDifferenceLoss] using hconverted

end CryptBoolean
