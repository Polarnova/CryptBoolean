/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenOrbitPairwiseDisjoint

/-!
# Weight-sixteen character bound from a rank-seven classifier
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A certificate-producing rank-seven classifier implies the full
weight-sixteen dual character lower bound. -/
theorem orderTwoWeightSixteenCharacterSum_ge_of_certificate
    (f : BooleanFunction n)
    (hn : 3 ≤ n)
    (hcertificate : ∀ h : BooleanFunction n,
      h ∈ orderTwoWeightSixteenDualWords n →
      HasSupportAffineSpanRankSeven h →
      RankSevenWeightSixteenPatternCertificate h) :
    orderTwoWeightSixteenCharacterSum f ≥
      -((3 * 127 + 127 * 2 ^ 128) * (2 ^ n : ℝ) ^ 7) :=
  orderTwoWeightSixteenCharacterSum_ge_of_orbitClassification f
    (hasRankSevenWeightSixteenOrbitClassification_of_certificate hcertificate)
    (hasRankAtMostSixWeightSixteenDeficientAffineMaskCover hn)

end CryptBoolean
