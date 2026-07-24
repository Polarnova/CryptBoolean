/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.OrbitAggregation
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.OrbitDisjointness

/-!
# Pairwise disjointness of the rank-seven weight-sixteen word orbits
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The three finite affine word orbits are pairwise disjoint. -/
theorem pairwiseDisjoint_rankSevenWeightSixteenPatternOrbitWords
    (n : ℕ) :
    Set.PairwiseDisjoint
      (↑(Finset.univ : Finset RankSevenWeightSixteenPatternClass))
      (rankSevenWeightSixteenPatternOrbitWords n) := by
  intro c _hc e _he hce
  change Disjoint (rankSevenWeightSixteenPatternOrbitWords n c)
    (rankSevenWeightSixteenPatternOrbitWords n e)
  rw [Finset.disjoint_left]
  intro h hhC hhE
  rcases (mem_rankSevenWeightSixteenPatternOrbitWords_iff c h).1 hhC with
    ⟨d, hd, hwordD⟩
  rcases (mem_rankSevenWeightSixteenPatternOrbitWords_iff e h).1 hhE with
    ⟨q, hq, hwordQ⟩
  apply hce
  exact rankSevenWeightSixteenPatternClass_unique
    ⟨d, hd, hwordD.symm⟩ ⟨q, hq, hwordQ.symm⟩

/-- A certificate-producing rank-seven classifier discharges the complete
orbit classification: soundness and pairwise disjointness are proved by the
library. -/
theorem hasRankSevenWeightSixteenOrbitClassification_of_certificate
    {n : ℕ}
    (hcertificate : ∀ h : BooleanFunction n,
      h ∈ orderTwoWeightSixteenDualWords n →
      HasSupportAffineSpanRankSeven h →
      RankSevenWeightSixteenPatternCertificate h) :
    HasRankSevenWeightSixteenOrbitClassification n :=
  hasRankSevenWeightSixteenOrbitClassification_of_certificate_and_disjointness
    hcertificate
    (pairwiseDisjoint_rankSevenWeightSixteenPatternOrbitWords n)

end CryptBoolean
