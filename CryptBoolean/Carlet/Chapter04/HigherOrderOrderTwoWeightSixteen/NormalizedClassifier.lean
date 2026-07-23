/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.NormalizedCandidates

/-!
# Kernel-checked normalized rank-seven pattern classification

The affine-basis normalization of a rank-seven weight-sixteen support is a
128-bit set containing zero and the seven standard basis points.  Self-duality
is exactly the evenness of its seven linear and twenty-one quadratic coordinate
moments.  This file packages the finite classifier that identifies every such
normalized set with an affine image of one of the three canonical patterns.
-/

@[expose] public section

namespace CryptBoolean

/-- Coordinate support masks on the low half of the seven-variable cube. -/
def normalizedCoordinateMaskLow : Fin 7 → BitVec 64
  | 0 => 0xAAAAAAAAAAAAAAAA#64
  | 1 => 0xCCCCCCCCCCCCCCCC#64
  | 2 => 0xF0F0F0F0F0F0F0F0#64
  | 3 => 0xFF00FF00FF00FF00#64
  | 4 => 0xFFFF0000FFFF0000#64
  | 5 => 0xFFFFFFFF00000000#64
  | 6 => 0#64

/-- Coordinate support masks on the high half of the seven-variable cube. -/
def normalizedCoordinateMaskHigh : Fin 7 → BitVec 64
  | 0 => 0xAAAAAAAAAAAAAAAA#64
  | 1 => 0xCCCCCCCCCCCCCCCC#64
  | 2 => 0xF0F0F0F0F0F0F0F0#64
  | 3 => 0xFF00FF00FF00FF00#64
  | 4 => 0xFFFF0000FFFF0000#64
  | 5 => 0xFFFFFFFF00000000#64
  | 6 => 0xFFFFFFFFFFFFFFFF#64

/-- Whether a 64-bit intersection has even cardinality. -/
def normalizedMaskEven (x : BitVec 64) : Bool :=
  !(x.cpop.getLsbD 0)

/-- The card-sixteen, affine-basis, and degree-at-most-two parity constraints
on a normalized pair of 64-bit support masks. -/
def IsNormalizedWeightSixteenMask (low high : BitVec 64) : Bool :=
  low.cpop + high.cpop == 16#64 &&
    low &&& 0x0000000100010117#64 == 0x0000000100010117#64 &&
    high &&& 1#64 == 1#64 &&
    (List.ofFn fun i : Fin 7 ↦
      normalizedMaskEven (low &&& normalizedCoordinateMaskLow i) ==
        normalizedMaskEven (high &&& normalizedCoordinateMaskHigh i)).all id &&
    (List.ofFn fun i : Fin 7 ↦
      (List.ofFn fun j : Fin 7 ↦
        if i < j then
          normalizedMaskEven
              (low &&& normalizedCoordinateMaskLow i &&&
                normalizedCoordinateMaskLow j) ==
            normalizedMaskEven
              (high &&& normalizedCoordinateMaskHigh i &&&
                normalizedCoordinateMaskHigh j)
        else true).all id).all id

/-- The `i`th systematic column packed into a 64-bit code. -/
def systematicWeightSixteenColumn
    (code : BitVec 64) (i : ℕ) : BitVec 8 :=
  code.extractLsb' (8 * i) 8

/-- A systematic column is odd and is not one of the eight unit columns already
occupied by the normalized affine basis. -/
def isSystematicWeightSixteenNonunitOddColumn (column : BitVec 8) : Bool :=
  column.cpop.getLsbD 0 && column &&& (column - 1) != 0

/-- Two systematic columns are orthogonal over the binary field. -/
def areSystematicWeightSixteenColumnsOrthogonal
    (left right : BitVec 8) : Bool :=
  !((left &&& right).cpop.getLsbD 0)

/-- The eight sorted columns form an orthonormal basis and avoid the eight
unit columns already occupied by the normalized affine basis. -/
def SystematicWeightSixteenConstraints (code : BitVec 64) : Bool :=
  isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 0) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 1) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 2) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 3) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 4) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 5) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 6) &&
    isSystematicWeightSixteenNonunitOddColumn
      (systematicWeightSixteenColumn code 7) &&
    (systematicWeightSixteenColumn code 0).ult
      (systematicWeightSixteenColumn code 1) &&
    (systematicWeightSixteenColumn code 1).ult
      (systematicWeightSixteenColumn code 2) &&
    (systematicWeightSixteenColumn code 2).ult
      (systematicWeightSixteenColumn code 3) &&
    (systematicWeightSixteenColumn code 3).ult
      (systematicWeightSixteenColumn code 4) &&
    (systematicWeightSixteenColumn code 4).ult
      (systematicWeightSixteenColumn code 5) &&
    (systematicWeightSixteenColumn code 5).ult
      (systematicWeightSixteenColumn code 6) &&
    (systematicWeightSixteenColumn code 6).ult
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 1) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 2) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 0)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 2) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 1)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 3) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 2)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 4) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 3)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 5) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 4)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 5)
      (systematicWeightSixteenColumn code 6) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 5)
      (systematicWeightSixteenColumn code 7) &&
    areSystematicWeightSixteenColumnsOrthogonal
      (systematicWeightSixteenColumn code 6)
      (systematicWeightSixteenColumn code 7)

/-- Boolean membership in the generated systematic-code family. -/
def isGeneratedSystematicWeightSixteenCode (code : BitVec 64) : Bool :=
  match normalizedWeightSixteenCandidateBucket (code.extractLsb' 0 16) with
  | some tree => tree.containsSystematicCode code
  | none => false

private theorem exists_candidate_of_tree_containsSystematicCode
    (tree : NormalizedWeightSixteenCandidateTree) (code : BitVec 64)
    (hcontains : tree.containsSystematicCode code = true) :
    ∃ candidate,
      tree.Member candidate ∧ candidate.systematicCode = code := by
  induction tree with
  | leaf candidate =>
      refine ⟨candidate, .leaf, ?_⟩
      simpa [NormalizedWeightSixteenCandidateTree.containsSystematicCode]
        using hcontains
  | node left right ihLeft ihRight =>
      have hcases :
          left.containsSystematicCode code = true ∨
            right.containsSystematicCode code = true := by
        simpa [NormalizedWeightSixteenCandidateTree.containsSystematicCode]
          using hcontains
      rcases hcases with hleft | hright
      · obtain ⟨candidate, hmember, hcode⟩ := ihLeft hleft
        exact ⟨candidate, .left hmember, hcode⟩
      · obtain ⟨candidate, hmember, hcode⟩ := ihRight hright
        exact ⟨candidate, .right hmember, hcode⟩

/-- A successful generated-code test carries an actual class and affine-map
certificate leaf, rather than only a Boolean membership result. -/
theorem exists_normalizedWeightSixteenCandidate_of_generated
    (code : BitVec 64)
    (hgenerated : isGeneratedSystematicWeightSixteenCode code = true) :
    ∃ tree candidate,
      normalizedWeightSixteenCandidateBucket (code.extractLsb' 0 16) =
          some tree ∧
        NormalizedWeightSixteenCandidateTree.Member candidate tree ∧
        candidate.systematicCode = code := by
  unfold isGeneratedSystematicWeightSixteenCode at hgenerated
  split at hgenerated
  next tree heq =>
    obtain ⟨candidate, hmember, hcode⟩ :=
      exists_candidate_of_tree_containsSystematicCode tree code hgenerated
    exact ⟨tree, candidate, heq, hmember, hcode⟩
  next heq => simp at hgenerated

end CryptBoolean
