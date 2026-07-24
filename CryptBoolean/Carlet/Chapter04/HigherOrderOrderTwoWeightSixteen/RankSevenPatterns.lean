/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerWeightSixteenSelfDual
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.AffineMaps
public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity

/-!
# Canonical rank-seven weight-sixteen patterns

Projective self-dual binary codes of parameters `[16,8,≥4]` give three
rank-seven point-pattern classes.  This file fixes executable representatives
and packages injective affine images as proof-carrying data.  Classification is
expressed by a concrete affine-image certificate, not by an unverified global
existence hypothesis.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The three projective self-dual length-sixteen pattern classes. -/
inductive RankSevenWeightSixteenPatternClass where
  | twoE8
  | d16Plus
  | f16
  deriving DecidableEq, Fintype

/-- Little-endian integer representatives of the three canonical
seven-variable point patterns. -/
def rankSevenWeightSixteenPatternIndices :
    RankSevenWeightSixteenPatternClass → Finset ℕ
  | .twoE8 =>
      [0, 1, 2, 3, 4, 5, 6, 7,
        64, 72, 80, 88, 96, 104, 112, 120].toFinset
  | .d16Plus =>
      [0, 1, 2, 4, 8, 16, 32, 64,
        127, 126, 125, 123, 119, 111, 95, 63].toFinset
  | .f16 =>
      [0, 1, 2, 4, 8, 16, 32, 64,
        126, 87, 55, 17, 31, 5, 3, 105].toFinset

/-- The canonical point set associated with a rank-seven pattern class. -/
def rankSevenWeightSixteenPattern
    (c : RankSevenWeightSixteenPatternClass) :
    Finset (FABL.F₂Cube 7) :=
  (rankSevenWeightSixteenPatternIndices c).image (f₂CubeOfNat 7)

@[simp] theorem card_rankSevenWeightSixteenPattern
    (c : RankSevenWeightSixteenPatternClass) :
    (rankSevenWeightSixteenPattern c).card = 16 := by
  cases c <;> decide

theorem rankSevenWeightSixteenPattern_pairwise_ne :
    Function.Injective rankSevenWeightSixteenPattern := by
  intro c d
  cases c <;> cases d <;> decide

/-- Seven distinguished pattern points whose differences from zero form an
affine basis of the canonical representative. -/
def rankSevenWeightSixteenPatternAffineBasisIndices :
    RankSevenWeightSixteenPatternClass → Fin 7 → ℕ
  | .twoE8 => ![1, 2, 4, 64, 72, 80, 96]
  | .d16Plus => ![1, 2, 4, 8, 16, 32, 64]
  | .f16 => ![1, 2, 4, 8, 16, 32, 64]

/-- The direction family supplied by the canonical affine basis. -/
def rankSevenWeightSixteenPatternAffineBasis
    (c : RankSevenWeightSixteenPatternClass) : Fin 7 → FABL.F₂Cube 7 :=
  fun i ↦ f₂CubeOfNat 7 (rankSevenWeightSixteenPatternAffineBasisIndices c i)

@[simp] theorem zero_mem_rankSevenWeightSixteenPattern
    (c : RankSevenWeightSixteenPatternClass) :
    0 ∈ rankSevenWeightSixteenPattern c := by
  cases c <;> decide

theorem rankSevenWeightSixteenPatternAffineBasis_mem
    (c : RankSevenWeightSixteenPatternClass) (i : Fin 7) :
    rankSevenWeightSixteenPatternAffineBasis c i ∈
      rankSevenWeightSixteenPattern c := by
  cases c <;> fin_cases i <;> decide

theorem linearIndependent_rankSevenWeightSixteenPatternAffineBasis
    (c : RankSevenWeightSixteenPatternClass) :
    LinearIndependent FABL.𝔽₂
      (rankSevenWeightSixteenPatternAffineBasis c) := by
  cases c with
  | d16Plus =>
      have hbasis :
          rankSevenWeightSixteenPatternAffineBasis .d16Plus =
            fun i : Fin 7 ↦ Pi.single i (1 : FABL.𝔽₂) := by
        funext i j
        fin_cases i <;> fin_cases j <;> decide
      rw [hbasis]
      exact Pi.linearIndependent_single_one (Fin 7) FABL.𝔽₂
  | f16 =>
      have hbasis :
          rankSevenWeightSixteenPatternAffineBasis .f16 =
            fun i : Fin 7 ↦ Pi.single i (1 : FABL.𝔽₂) := by
        funext i j
        fin_cases i <;> fin_cases j <;> decide
      rw [hbasis]
      exact Pi.linearIndependent_single_one (Fin 7) FABL.𝔽₂
  | twoE8 =>
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      let e : Fin 7 → FABL.F₂Cube 7 :=
        fun j ↦ Pi.single j (1 : FABL.𝔽₂)
      have hbasis :
          rankSevenWeightSixteenPatternAffineBasis .twoE8 =
            ![e 0, e 1, e 2, e 6, e 3 + e 6, e 4 + e 6, e 5 + e 6] := by
        funext j k
        fin_cases j <;> fin_cases k <;> decide
      rw [hbasis] at hg
      have h0 := congrFun hg (0 : Fin 7)
      have h1 := congrFun hg (1 : Fin 7)
      have h2 := congrFun hg (2 : Fin 7)
      have h3 := congrFun hg (3 : Fin 7)
      have h4 := congrFun hg (4 : Fin 7)
      have h5 := congrFun hg (5 : Fin 7)
      have h6 := congrFun hg (6 : Fin 7)
      have h0' : g 0 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h0
      have h1' : g 1 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h1
      have h2' : g 2 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h2
      have h3' : g 4 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h3
      have h4' : g 5 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h4
      have h5' : g 6 = 0 := by
        simpa [e, Fin.sum_univ_succ] using h5
      have h6' : g 3 + (g 4 + (g 5 + g 6)) = 0 := by
        simpa [e, Fin.sum_univ_succ] using h6
      fin_cases i
      · exact h0'
      · exact h1'
      · exact h2'
      · rw [h3', h4', h5'] at h6'
        simpa using h6'
      · exact h3'
      · exact h4'
      · exact h5'

/-- The Boolean indicator of a canonical rank-seven pattern. -/
def rankSevenWeightSixteenPatternIndicator
    (c : RankSevenWeightSixteenPatternClass) : BooleanFunction 7 :=
  fun x ↦ if x ∈ rankSevenWeightSixteenPattern c then 1 else 0

@[simp] theorem support_rankSevenWeightSixteenPatternIndicator
    (c : RankSevenWeightSixteenPatternClass) :
    support (rankSevenWeightSixteenPatternIndicator c) =
      rankSevenWeightSixteenPattern c := by
  ext x
  simp [support, FABL.f₂OneSupport,
    rankSevenWeightSixteenPatternIndicator]

@[simp] theorem hammingWeight_rankSevenWeightSixteenPatternIndicator
    (c : RankSevenWeightSixteenPatternClass) :
    hammingWeight (rankSevenWeightSixteenPatternIndicator c) = 16 := by
  rw [hammingWeight_eq_card_support,
    support_rankSevenWeightSixteenPatternIndicator,
    card_rankSevenWeightSixteenPattern]

/-- The injective affine image of a canonical rank-seven point pattern. -/
def rankSevenWeightSixteenPatternImage
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) : Finset (FABL.F₂Cube n) :=
  (rankSevenWeightSixteenPattern c).image (sevenVariableAffinePoint d)

theorem card_rankSevenWeightSixteenPatternImage_of_independent
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    (rankSevenWeightSixteenPatternImage c d).card = 16 := by
  rw [rankSevenWeightSixteenPatternImage,
    Finset.card_image_of_injective
      (rankSevenWeightSixteenPattern c)
      (sevenVariableAffinePoint_injective_iff d |>.2 hd),
    card_rankSevenWeightSixteenPattern]

/-- The Boolean word supported on one affine image of a canonical pattern. -/
def rankSevenWeightSixteenPatternWord
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) : BooleanFunction n :=
  fun x ↦ if x ∈ rankSevenWeightSixteenPatternImage c d then 1 else 0

@[simp] theorem support_rankSevenWeightSixteenPatternWord
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) :
    support (rankSevenWeightSixteenPatternWord c d) =
      rankSevenWeightSixteenPatternImage c d := by
  ext x
  simp [support, FABL.f₂OneSupport,
    rankSevenWeightSixteenPatternWord]

theorem hammingWeight_rankSevenWeightSixteenPatternWord_of_independent
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    hammingWeight (rankSevenWeightSixteenPatternWord c d) = 16 := by
  rw [hammingWeight_eq_card_support,
    support_rankSevenWeightSixteenPatternWord,
    card_rankSevenWeightSixteenPatternImage_of_independent c d hd]

/-- Constructive evidence that a word belongs to one of the three rank-seven
affine pattern orbits. -/
structure RankSevenWeightSixteenPatternCertificate
    (h : BooleanFunction n) where
  patternClass : RankSevenWeightSixteenPatternClass
  affineData : SevenVariableAffineMapData n
  independent : LinearIndependent FABL.𝔽₂ affineData.2
  word_eq : h = rankSevenWeightSixteenPatternWord patternClass affineData

theorem RankSevenWeightSixteenPatternCertificate.hammingWeight_eq_sixteen
    {h : BooleanFunction n}
    (certificate : RankSevenWeightSixteenPatternCertificate h) :
    hammingWeight h = 16 := by
  rw [certificate.word_eq]
  exact hammingWeight_rankSevenWeightSixteenPatternWord_of_independent
    certificate.patternClass certificate.affineData certificate.independent

/-- Membership in one specified canonical affine orbit. -/
def IsRankSevenWeightSixteenPatternClass
    (c : RankSevenWeightSixteenPatternClass)
    (h : BooleanFunction n) : Prop :=
  ∃ d : SevenVariableAffineMapData n,
    LinearIndependent FABL.𝔽₂ d.2 ∧
      h = rankSevenWeightSixteenPatternWord c d

theorem exists_patternClass_of_certificate
    {h : BooleanFunction n}
    (certificate : RankSevenWeightSixteenPatternCertificate h) :
    ∃ c, IsRankSevenWeightSixteenPatternClass c h := by
  exact ⟨certificate.patternClass, certificate.affineData,
    certificate.independent, certificate.word_eq⟩

end CryptBoolean
