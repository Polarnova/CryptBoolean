/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.SystematicEncoding

/-!
# Semantic soundness of generated normalized candidates

A generated leaf is sound when its decoded affine map sends the declared
canonical pattern onto the support reconstructed from its systematic code.
The tree predicate packages a proof for every leaf and transports it along
propositional tree membership.
-/

@[expose] public section

namespace CryptBoolean

/-- Semantic soundness of one generated normalized candidate. -/
def NormalizedWeightSixteenCandidate.IsSound
    (candidate : NormalizedWeightSixteenCandidate) : Prop :=
  rankSevenWeightSixteenPatternImage candidate.patternClass
      (normalizedCandidateAffineMapData candidate) =
    systematicWeightSixteenSupportOfCode candidate.systematicCode

/-- The little-endian numerical index of a seven-variable point. -/
def normalizedSevenPointIndex (x : FABL.F₂Cube 7) : ℕ :=
  Nat.ofBits fun i ↦ decide (x i = 1)

/-- An explicit enumeration of the sixteen indices in each canonical pattern. -/
def rankSevenWeightSixteenPatternPointIndex :
    RankSevenWeightSixteenPatternClass → Fin 16 → ℕ
  | .twoE8 =>
      ![0, 1, 2, 3, 4, 5, 6, 7,
        64, 72, 80, 88, 96, 104, 112, 120]
  | .d16Plus =>
      ![0, 1, 2, 4, 8, 16, 32, 64,
        127, 126, 125, 123, 119, 111, 95, 63]
  | .f16 =>
      ![0, 1, 2, 4, 8, 16, 32, 64,
        126, 87, 55, 17, 31, 5, 3, 105]

/-- The `i`th point of a canonical sixteen-point pattern. -/
def rankSevenWeightSixteenPatternPoint
    (c : RankSevenWeightSixteenPatternClass) (i : Fin 16) :
    FABL.F₂Cube 7 :=
  f₂CubeOfNat 7 (rankSevenWeightSixteenPatternPointIndex c i)

/-- The explicit sixteen-point enumeration has exactly the canonical range. -/
theorem image_rankSevenWeightSixteenPatternPoint
    (c : RankSevenWeightSixteenPatternClass) :
    Finset.univ.image (rankSevenWeightSixteenPatternPoint c) =
      rankSevenWeightSixteenPattern c := by
  cases c <;> decide

/-- The normalized origin and seven coordinate points as an eight-point family. -/
def systematicWeightSixteenFixedPoint : Fin 8 → FABL.F₂Cube 7 :=
  Fin.cases 0 fun i ↦ Pi.single i (1 : FABL.𝔽₂)

/-- The explicit eight-point family enumerates the fixed systematic support. -/
theorem image_systematicWeightSixteenFixedPoint :
    Finset.univ.image systematicWeightSixteenFixedPoint =
      systematicWeightSixteenFixedPoints := by
  decide

/-- Whether the generated low/high masks contain a seven-variable point. -/
def NormalizedWeightSixteenCandidate.maskContains
    (candidate : NormalizedWeightSixteenCandidate)
    (x : FABL.F₂Cube 7) : Bool :=
  let index := normalizedSevenPointIndex x
  if index < 64 then candidate.maskLow.getLsbD index
  else candidate.maskHigh.getLsbD (index - 64)

/-- The set-bit indices of a sixty-four-bit mask. -/
def bitVecSixtyFourSupport (mask : BitVec 64) : Finset (Fin 64) :=
  Finset.univ.filter fun i ↦ mask.getLsbD i = true

/-- The low-half cube point represented by one mask index. -/
def normalizedLowMaskPoint (i : Fin 64) : FABL.F₂Cube 7 :=
  f₂CubeOfNat 7 i

/-- The high-half cube point represented by one mask index. -/
def normalizedHighMaskPoint (i : Fin 64) : FABL.F₂Cube 7 :=
  f₂CubeOfNat 7 (64 + i)

/-- The point set represented by the generated low/high masks, split into two
disjoint sixty-four-point halves. -/
def NormalizedWeightSixteenCandidate.maskSupport
    (candidate : NormalizedWeightSixteenCandidate) :
    Finset (FABL.F₂Cube 7) :=
  (bitVecSixtyFourSupport candidate.maskLow).image normalizedLowMaskPoint ∪
    (bitVecSixtyFourSupport candidate.maskHigh).image normalizedHighMaskPoint

private theorem bitVec_cpopNatRec_eq_sum_range
    {w : ℕ} (mask : BitVec w) (n : ℕ) :
    mask.cpopNatRec n 0 =
      ∑ i ∈ Finset.range n, (mask.getLsbD i).toNat := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq,
        ih, Finset.sum_range_succ]
      simp

/-- The cardinality of a bitvector's set-bit support is its population count. -/
theorem card_bitVecSixtyFourSupport (mask : BitVec 64) :
    (bitVecSixtyFourSupport mask).card = mask.cpop.toNat := by
  calc
    (bitVecSixtyFourSupport mask).card =
        ∑ i : Fin 64, if mask.getLsbD i = true then 1 else 0 := by
      symm
      simpa [bitVecSixtyFourSupport] using
        (Finset.sum_boole (R := ℕ)
          (fun i : Fin 64 ↦ mask.getLsbD i = true) Finset.univ)
    _ = ∑ i ∈ Finset.range 64, (mask.getLsbD i).toNat := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi64 : i < 64 := Finset.mem_range.mp hi
      simp only [hi64, dite_true]
      cases mask.getLsbD i <;> simp
    _ = mask.cpopNatRec 64 0 :=
      (bitVec_cpopNatRec_eq_sum_range mask 64).symm
    _ = mask.cpop.toNat := (BitVec.toNat_cpop mask).symm

theorem normalizedLowMaskPoint_injective :
    Function.Injective normalizedLowMaskPoint := by
  decide

theorem normalizedHighMaskPoint_injective :
    Function.Injective normalizedHighMaskPoint := by
  decide

theorem normalizedLowMaskPoint_ne_highMaskPoint
    (i j : Fin 64) :
    normalizedLowMaskPoint i ≠ normalizedHighMaskPoint j := by
  revert i j
  decide

/-- The cardinality of the represented mask support is the sum of the two
population counts. -/
theorem NormalizedWeightSixteenCandidate.card_maskSupport
    (candidate : NormalizedWeightSixteenCandidate) :
    candidate.maskSupport.card =
      candidate.maskLow.cpop.toNat + candidate.maskHigh.cpop.toNat := by
  rw [NormalizedWeightSixteenCandidate.maskSupport,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ normalizedLowMaskPoint_injective,
      Finset.card_image_of_injective _ normalizedHighMaskPoint_injective,
      card_bitVecSixtyFourSupport, card_bitVecSixtyFourSupport]
  · rw [Finset.disjoint_left]
    intro x hxLow hxHigh
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hxLow
    obtain ⟨j, _hj, heq⟩ := Finset.mem_image.mp hxHigh
    exact normalizedLowMaskPoint_ne_highMaskPoint i j heq.symm

theorem normalizedSevenPointIndex_lt (x : FABL.F₂Cube 7) :
    normalizedSevenPointIndex x < 128 := by
  revert x
  set_option maxRecDepth 100000 in decide

theorem f₂CubeOfNat_normalizedSevenPointIndex (x : FABL.F₂Cube 7) :
    f₂CubeOfNat 7 (normalizedSevenPointIndex x) = x := by
  revert x
  set_option maxRecDepth 100000 in decide

/-- A positive mask bit puts its corresponding point into the represented
support. -/
theorem NormalizedWeightSixteenCandidate.mem_maskSupport_of_maskContains
    {candidate : NormalizedWeightSixteenCandidate}
    {x : FABL.F₂Cube 7}
    (hcontains : candidate.maskContains x = true) :
    x ∈ candidate.maskSupport := by
  let index := normalizedSevenPointIndex x
  have hbound : index < 128 := normalizedSevenPointIndex_lt x
  change (if index < 64 then candidate.maskLow.getLsbD index
    else candidate.maskHigh.getLsbD (index - 64)) = true at hcontains
  by_cases hlow : index < 64
  · rw [if_pos hlow] at hcontains
    rw [NormalizedWeightSixteenCandidate.maskSupport, Finset.mem_union]
    left
    refine Finset.mem_image.mpr ⟨⟨index, hlow⟩, ?_, ?_⟩
    · simp [bitVecSixtyFourSupport, hcontains]
    · change f₂CubeOfNat 7 index = x
      exact f₂CubeOfNat_normalizedSevenPointIndex x
  · rw [if_neg hlow] at hcontains
    have hhigh : index - 64 < 64 := by omega
    rw [NormalizedWeightSixteenCandidate.maskSupport, Finset.mem_union]
    right
    refine Finset.mem_image.mpr ⟨⟨index - 64, hhigh⟩, ?_, ?_⟩
    · simp [bitVecSixtyFourSupport, hcontains]
    · change f₂CubeOfNat 7 (64 + (index - 64)) = x
      rw [Nat.add_sub_of_le (by omega : 64 ≤ index)]
      exact f₂CubeOfNat_normalizedSevenPointIndex x

/-- The generated pair of masks has Hamming weight sixteen. -/
def NormalizedWeightSixteenCandidate.HasMaskWeightSixteen
    (candidate : NormalizedWeightSixteenCandidate) : Prop :=
  candidate.maskLow.cpop + candidate.maskHigh.cpop = 16#64

/-- The pure bitvector weight certificate gives the represented support's
cardinality without evaluating a 128-point filter at every generated leaf. -/
theorem NormalizedWeightSixteenCandidate.HasMaskWeightSixteen.maskSupport_card
    {candidate : NormalizedWeightSixteenCandidate}
    (hweight : candidate.HasMaskWeightSixteen) :
    candidate.maskSupport.card = 16 := by
  rw [candidate.card_maskSupport]
  have hlow := BitVec.toNat_cpop_le candidate.maskLow
  have hhigh := BitVec.toNat_cpop_le candidate.maskHigh
  have hsumlt :
      candidate.maskLow.cpop.toNat + candidate.maskHigh.cpop.toNat <
        2 ^ 64 := by
    norm_num at ⊢
    omega
  change candidate.maskLow.cpop + candidate.maskHigh.cpop = 16#64 at hweight
  have htoNat := congrArg BitVec.toNat hweight
  change (candidate.maskLow.cpop.toNat +
    candidate.maskHigh.cpop.toNat) % 2 ^ 64 = 16 at htoNat
  rw [Nat.mod_eq_of_lt hsumlt] at htoNat
  exact htoNat

/-- A compact certificate checks only fixed finite point families: the mask
weight, sixteen distinct mapped pattern points, and the two eight-point
systematic families. -/
def NormalizedWeightSixteenCandidate.IsCompactMaskSound
    (candidate : NormalizedWeightSixteenCandidate) : Prop :=
  candidate.HasMaskWeightSixteen ∧
    Function.Injective (fun i : Fin 16 ↦
      sevenVariableAffinePoint (normalizedCandidateAffineMapData candidate)
        (rankSevenWeightSixteenPatternPoint candidate.patternClass i)) ∧
    (∀ i : Fin 16,
      candidate.maskContains
        (sevenVariableAffinePoint (normalizedCandidateAffineMapData candidate)
          (rankSevenWeightSixteenPatternPoint candidate.patternClass i)) = true) ∧
    (∀ i : Fin 8,
      candidate.maskContains (systematicWeightSixteenFixedPoint i) = true) ∧
    (∀ i : Fin 8,
      candidate.maskContains
        (systematicWeightSixteenColumnPoint
          (systematicWeightSixteenColumn candidate.systematicCode i)) = true)

instance NormalizedWeightSixteenCandidate.instDecidableIsCompactMaskSound
    (candidate : NormalizedWeightSixteenCandidate) :
    Decidable candidate.IsCompactMaskSound := by
  unfold NormalizedWeightSixteenCandidate.IsCompactMaskSound
    NormalizedWeightSixteenCandidate.HasMaskWeightSixteen
  infer_instance

/-- A compact certificate gives sixteen distinct points in the canonical
pattern image. -/
theorem NormalizedWeightSixteenCandidate.IsCompactMaskSound.patternImage_card
    {candidate : NormalizedWeightSixteenCandidate}
    (hsound : candidate.IsCompactMaskSound) :
    (rankSevenWeightSixteenPatternImage candidate.patternClass
      (normalizedCandidateAffineMapData candidate)).card = 16 := by
  rw [rankSevenWeightSixteenPatternImage,
    ← image_rankSevenWeightSixteenPatternPoint, Finset.image_image]
  have hinjective : Function.Injective
      (sevenVariableAffinePoint (normalizedCandidateAffineMapData candidate) ∘
        rankSevenWeightSixteenPatternPoint candidate.patternClass) := by
    intro i j hij
    exact hsound.2.1 hij
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective
      (Finset.univ : Finset (Fin 16)) hinjective

/-- Every canonical image point selected by a compact certificate belongs to
the generated mask. -/
theorem NormalizedWeightSixteenCandidate.IsCompactMaskSound.patternImage_subset
    {candidate : NormalizedWeightSixteenCandidate}
    (hsound : candidate.IsCompactMaskSound) :
    rankSevenWeightSixteenPatternImage candidate.patternClass
        (normalizedCandidateAffineMapData candidate) ⊆
      candidate.maskSupport := by
  rw [rankSevenWeightSixteenPatternImage,
    ← image_rankSevenWeightSixteenPatternPoint]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
  exact NormalizedWeightSixteenCandidate.mem_maskSupport_of_maskContains
    (hsound.2.2.1 i)

/-- Every fixed or decoded systematic point selected by a compact certificate
belongs to the generated mask. -/
theorem NormalizedWeightSixteenCandidate.IsCompactMaskSound.systematicSupport_subset
    {candidate : NormalizedWeightSixteenCandidate}
    (hsound : candidate.IsCompactMaskSound) :
    systematicWeightSixteenSupportOfCode candidate.systematicCode ⊆
      candidate.maskSupport := by
  intro x hx
  rw [systematicWeightSixteenSupportOfCode, Finset.mem_union] at hx
  obtain hx | hx := hx
  · rw [← image_systematicWeightSixteenFixedPoint] at hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    exact NormalizedWeightSixteenCandidate.mem_maskSupport_of_maskContains
      (hsound.2.2.2.1 i)
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    exact NormalizedWeightSixteenCandidate.mem_maskSupport_of_maskContains
      (hsound.2.2.2.2 i)

/-- An affine image containing the normalized origin and seven coordinate
points has an invertible seven-dimensional linear part. -/
theorem linearIndependent_of_systematicFixedPoints_subset_patternImage
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData 7)
    (hfixed : systematicWeightSixteenFixedPoints ⊆
      rankSevenWeightSixteenPatternImage c d) :
    LinearIndependent FABL.𝔽₂ d.2 := by
  classical
  have hzero : (0 : FABL.F₂Cube 7) ∈
      rankSevenWeightSixteenPatternImage c d := by
    apply hfixed
    simp [systematicWeightSixteenFixedPoints]
  obtain ⟨x0, _hx0Pattern, hx0⟩ := Finset.mem_image.mp hzero
  have hsingle (i : Fin 7) : Pi.single i (1 : FABL.𝔽₂) ∈
      rankSevenWeightSixteenPatternImage c d := by
    apply hfixed
    simp [systematicWeightSixteenFixedPoints]
  choose x hxPattern hx using fun i ↦ Finset.mem_image.mp (hsingle i)
  let L : FABL.F₂Cube 7 →ₗ[FABL.𝔽₂] FABL.F₂Cube 7 :=
    Fintype.linearCombination FABL.𝔽₂ d.2
  change d.1 + L x0 = 0 at hx0
  have hLbasis (i : Fin 7) :
      L (x i + x0) = Pi.single i (1 : FABL.𝔽₂) := by
    have hxi := hx i
    change d.1 + L (x i) = Pi.single i (1 : FABL.𝔽₂) at hxi
    rw [map_add]
    calc
      L (x i) + L x0 =
          (d.1 + d.1) + (L (x i) + L x0) := by
            rw [ZModModule.add_self, zero_add]
      _ = (d.1 + L (x i)) + (d.1 + L x0) := by abel
      _ = Pi.single i (1 : FABL.𝔽₂) := by rw [hxi, hx0, add_zero]
  have hsurjective : Function.Surjective L := by
    intro y
    refine ⟨∑ i : Fin 7, y i • (x i + x0), ?_⟩
    rw [map_sum]
    simp_rw [map_smul, hLbasis]
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  exact LinearMap.injective_iff_surjective.mpr hsurjective

/-- A valid compact mask certificate implies semantic candidate soundness once
the two generic mask cardinality bridges are supplied. -/
theorem NormalizedWeightSixteenCandidate.IsCompactMaskSound.isSound
    {candidate : NormalizedWeightSixteenCandidate}
    (hsound : candidate.IsCompactMaskSound)
    (hsystematicCard :
      (systematicWeightSixteenSupportOfCode
        candidate.systematicCode).card = 16) :
    candidate.IsSound := by
  have hmaskCard := hsound.1.maskSupport_card
  have himageEq :
      rankSevenWeightSixteenPatternImage candidate.patternClass
          (normalizedCandidateAffineMapData candidate) =
        candidate.maskSupport := by
    apply Finset.eq_of_subset_of_card_le hsound.patternImage_subset
    rw [hmaskCard, hsound.patternImage_card]
  have hsystematicEq :
      systematicWeightSixteenSupportOfCode candidate.systematicCode =
        candidate.maskSupport := by
    apply Finset.eq_of_subset_of_card_le hsound.systematicSupport_subset
    rw [hmaskCard, hsystematicCard]
  exact himageEq.trans hsystematicEq.symm

namespace NormalizedWeightSixteenCandidateTree

/-- A predicate holds for every candidate leaf of a generated tree. -/
def All (P : NormalizedWeightSixteenCandidate → Prop) :
    NormalizedWeightSixteenCandidateTree → Prop
  | .leaf candidate => P candidate
  | .node left right => left.All P ∧ right.All P

/-- A pointwise implication transports a tree-wide invariant. -/
theorem All.imp
    {P Q : NormalizedWeightSixteenCandidate → Prop}
    (hPQ : ∀ candidate, P candidate → Q candidate) :
    (tree : NormalizedWeightSixteenCandidateTree) →
      tree.All P → tree.All Q
  | .leaf candidate, hall => hPQ candidate hall
  | .node left right, hall =>
      ⟨All.imp hPQ left hall.1, All.imp hPQ right hall.2⟩

instance instDecidableAll
    (P : NormalizedWeightSixteenCandidate → Prop) [DecidablePred P] :
    (tree : NormalizedWeightSixteenCandidateTree) → Decidable (tree.All P)
  | .leaf candidate => (inferInstance : DecidablePred P) candidate
  | .node left right =>
      @instDecidableAnd (left.All P) (right.All P)
        (instDecidableAll P left) (instDecidableAll P right)

/-- A tree-wide invariant holds at every propositionally selected leaf. -/
theorem All.of_member
    {P : NormalizedWeightSixteenCandidate → Prop}
    {candidate : NormalizedWeightSixteenCandidate}
    {tree : NormalizedWeightSixteenCandidateTree}
    (hall : tree.All P) (hmember : tree.Member candidate) :
    P candidate := by
  induction hmember with
  | leaf => simpa [All] using hall
  | left hmember ih =>
      exact ih hall.1
  | right hmember ih =>
      exact ih hall.2

end NormalizedWeightSixteenCandidateTree

/-- Every systematic orthonormal-column code has a generated candidate with a
valid compact mask certificate. -/
def HasNormalizedWeightSixteenCompactCandidateSoundness : Prop :=
  ∀ {code : BitVec 64},
    SystematicWeightSixteenConstraints code = true →
      ∃ candidate : NormalizedWeightSixteenCandidate,
        candidate.systematicCode = code ∧ candidate.IsCompactMaskSound

/-- Declare a kernel-reduced compact-mask certificate for one generated
candidate tree while keeping each certificate as an independent declaration. -/
macro "compact_mask_soundness " theoremName:ident " for " tree:term : command =>
  `(command|
    set_option Elab.async true in
    set_option linter.style.maxHeartbeats false in
    set_option maxRecDepth 100000 in
    set_option maxHeartbeats 20000000 in
    /-- Every candidate leaf in the selected generated tree has a valid compact mask. -/
    theorem $theoremName :
        NormalizedWeightSixteenCandidateTree.All
          NormalizedWeightSixteenCandidate.IsCompactMaskSound $tree := by
      exact of_decide_eq_true rfl)

end CryptBoolean
