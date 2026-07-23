/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderLowWeightFlats
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# The weight-twelve dual character sum

The affine-line square-sum argument behind Carlet--Mesnager Proposition
9.2.10(2).  A weight-twelve word has twenty ordered affine-flat
decompositions: ten choices of the common affine line and two orders of the
three-flats.  Thus the representation sum is normalized by `1 / 20`, not by
the `1 / 2` asserted after the source's incorrect uniqueness argument.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightTwelveAffineSubspaceFintype : Fintype
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance weightTwelveAffineSubspaceDecidableEq : DecidableEq
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

abbrev WeightTwelveFlatTriple (n : ℕ) :=
  AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))

/-- An affine line together with two affine three-flats containing it. -/
noncomputable def weightTwelveFlatTriples (n : ℕ) :
    Finset (WeightTwelveFlatTriple n) := by
  classical
  exact ((binaryAffineFlats 1 n).product
    ((binaryAffineFlats 3 n).product (binaryAffineFlats 3 n))).filter
      fun p ↦ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2

/-- The triples for which the common direction of the two three-flats is
strictly larger than the displayed line direction. -/
noncomputable def badWeightTwelveFlatTriples (n : ℕ) :
    Finset (WeightTwelveFlatTriple n) := by
  classical
  exact (weightTwelveFlatTriples n).filter fun p ↦
    p.2.1.direction ⊓ p.2.2.direction ≠ p.1.direction

private theorem weightTwelveFlatTriple_data
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ weightTwelveFlatTriples n) :
    p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 ∧
      p.2.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.1.direction = 3 ∧
      p.2.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.2.direction = 3 ∧
      p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 := by
  classical
  have hpTriple := Finset.mem_filter.mp hp
  have hpProduct := Finset.mem_product.mp hpTriple.1
  have hpThree := Finset.mem_product.mp hpProduct.2
  have hline : p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpProduct.1
  have hfirst : p.2.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.2.1.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpThree.1
  have hsecond : p.2.2 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.2.2.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpThree.2
  exact ⟨hline.1, hline.2, hfirst.1, hfirst.2, hsecond.1,
    hsecond.2, hpTriple.2.1, hpTriple.2.2⟩

private theorem badWeightTwelveFlatTriple_data
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ badWeightTwelveFlatTriples n) :
    p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 ∧
      p.2.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.1.direction = 3 ∧
      p.2.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.2.direction = 3 ∧
      p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
      p.2.1.direction ⊓ p.2.2.direction ≠ p.1.direction := by
  classical
  have hpBad := Finset.mem_filter.mp hp
  exact ⟨(weightTwelveFlatTriple_data hpBad.1).1,
    (weightTwelveFlatTriple_data hpBad.1).2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.2.2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.2.2.2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.2.2.2.2.1,
    (weightTwelveFlatTriple_data hpBad.1).2.2.2.2.2.2.2,
    hpBad.2⟩

private structure BadWeightTwelveFlatTripleWitness
    (p : WeightTwelveFlatTriple n) where
  u : FABL.F₂Cube n
  v : FABL.F₂Cube n
  a : FABL.F₂Cube n
  b : FABL.F₂Cube n
  c : FABL.F₂Cube n
  line_eq : FABL.binaryAffineSubspace (FABL.𝔽₂ ∙ v) u = p.1
  first_eq : FABL.binaryAffineSubspace
    (((FABL.𝔽₂ ∙ v) ⊔ (FABL.𝔽₂ ∙ a)) ⊔ (FABL.𝔽₂ ∙ b)) u = p.2.1
  second_eq : FABL.binaryAffineSubspace
    (((FABL.𝔽₂ ∙ v) ⊔ (FABL.𝔽₂ ∙ a)) ⊔ (FABL.𝔽₂ ∙ c)) u = p.2.2

private noncomputable def badWeightTwelveFlatTripleWitness
    (p : WeightTwelveFlatTriple n)
    (hp : p ∈ badWeightTwelveFlatTriples n) :
    BadWeightTwelveFlatTripleWitness p := by
  classical
  have hdata := badWeightTwelveFlatTriple_data hp
  let u := Classical.choose
    ((AffineSubspace.nonempty_iff_ne_bot p.1).2 hdata.1)
  have hu := Classical.choose_spec
    ((AffineSubspace.nonempty_iff_ne_bot p.1).2 hdata.1)
  have hlinePos : ⊥ < p.1.direction := by
    apply bot_lt_iff_ne_bot.mpr
    intro hbot
    have hrank : Module.finrank FABL.𝔽₂ p.1.direction = 0 := by
      rw [hbot, finrank_bot]
    omega
  let v' := Classical.choose (Submodule.nonzero_mem_of_bot_lt hlinePos)
  have hv := Classical.choose_spec (Submodule.nonzero_mem_of_bot_lt hlinePos)
  let v : FABL.F₂Cube n := v'
  have hv0 : v ≠ 0 := by
    intro hvzero
    apply hv
    apply Subtype.ext
    exact hvzero
  have hspanV : FABL.𝔽₂ ∙ v = p.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 v'.2)
    · rw [finrank_span_singleton hv0, hdata.2.1]
  have hlineFirstDirection : p.1.direction ≤ p.2.1.direction :=
    AffineSubspace.direction_le hdata.2.2.2.2.2.2.1
  have hlineSecondDirection : p.1.direction ≤ p.2.2.direction :=
    AffineSubspace.direction_le hdata.2.2.2.2.2.2.2.1
  have hlineIntersection :
      p.1.direction ≤ p.2.1.direction ⊓ p.2.2.direction :=
    le_inf hlineFirstDirection hlineSecondDirection
  have hlineLt :
      p.1.direction < p.2.1.direction ⊓ p.2.2.direction :=
    lt_of_le_of_ne hlineIntersection hdata.2.2.2.2.2.2.2.2.symm
  let a' := Classical.choose (SetLike.exists_of_lt hlineLt)
  have ha := Classical.choose_spec (SetLike.exists_of_lt hlineLt)
  let a : FABL.F₂Cube n := a'
  let P : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    p.1.direction ⊔ (FABL.𝔽₂ ∙ a)
  have hPrank : Module.finrank FABL.𝔽₂ P = 2 := by
    dsimp only [P]
    rw [Submodule.finrank_sup_span_singleton ha.2, hdata.2.1]
  have hPFirst : P ≤ p.2.1.direction := by
    exact sup_le hlineFirstDirection
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 ha.1.1))
  have hPSecond : P ≤ p.2.2.direction := by
    exact sup_le hlineSecondDirection
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 ha.1.2))
  have hfirstRank : Module.finrank FABL.𝔽₂ p.2.1.direction = 3 :=
    hdata.2.2.2.1
  have hsecondRank : Module.finrank FABL.𝔽₂ p.2.2.direction = 3 :=
    hdata.2.2.2.2.2.1
  have hPFirstRankLt : Module.finrank FABL.𝔽₂ P <
      Module.finrank FABL.𝔽₂ p.2.1.direction := by omega
  have hPSecondRankLt : Module.finrank FABL.𝔽₂ P <
      Module.finrank FABL.𝔽₂ p.2.2.direction := by omega
  have hPFirstLt : P < p.2.1.direction :=
    Submodule.lt_of_le_of_finrank_lt_finrank hPFirst hPFirstRankLt
  have hPSecondLt : P < p.2.2.direction :=
    Submodule.lt_of_le_of_finrank_lt_finrank hPSecond hPSecondRankLt
  let b' := Classical.choose (SetLike.exists_of_lt hPFirstLt)
  have hb := Classical.choose_spec (SetLike.exists_of_lt hPFirstLt)
  let b : FABL.F₂Cube n := b'
  let c' := Classical.choose (SetLike.exists_of_lt hPSecondLt)
  have hc := Classical.choose_spec (SetLike.exists_of_lt hPSecondLt)
  let c : FABL.F₂Cube n := c'
  have hfirstDirection :
      P ⊔ (FABL.𝔽₂ ∙ b) = p.2.1.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le hPFirst
        (Submodule.span_le.2 (Set.singleton_subset_iff.2 hb.1))
    · rw [Submodule.finrank_sup_span_singleton hb.2, hPrank,
        hfirstRank]
  have hsecondDirection :
      P ⊔ (FABL.𝔽₂ ∙ c) = p.2.2.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le hPSecond
        (Submodule.span_le.2 (Set.singleton_subset_iff.2 hc.1))
    · rw [Submodule.finrank_sup_span_singleton hc.2, hPrank,
        hsecondRank]
  have huFirst : u ∈ p.2.1 := hdata.2.2.2.2.2.2.1 hu
  have huSecond : u ∈ p.2.2 := hdata.2.2.2.2.2.2.2.1 hu
  refine ⟨u, v, a, b, c, ?_, ?_, ?_⟩
  · apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (AffineSubspace.self_mem_mk' _ _) hu).2
    rw [AffineSubspace.direction_mk', hspanV]
  · apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (AffineSubspace.self_mem_mk' _ _) huFirst).2
    rw [AffineSubspace.direction_mk']
    simpa only [P, hspanV] using hfirstDirection
  · apply (AffineSubspace.eq_iff_direction_eq_of_mem
      (AffineSubspace.self_mem_mk' _ _) huSecond).2
    rw [AffineSubspace.direction_mk']
    simpa only [P, hspanV] using hsecondDirection

private noncomputable def chosenBadWeightTwelveFlatTripleWitness
    (p : WeightTwelveFlatTriple n)
    (hp : p ∈ badWeightTwelveFlatTriples n) :
    BadWeightTwelveFlatTripleWitness p :=
  badWeightTwelveFlatTripleWitness p hp

private def badWeightTwelveFlatTripleWitnessCode
    {p : WeightTwelveFlatTriple n}
    (w : BadWeightTwelveFlatTripleWitness p) :
    Fin 5 → FABL.F₂Cube n :=
  ![w.u, w.v, w.a, w.b, w.c]

private noncomputable def badWeightTwelveFlatTripleCode
    (p : WeightTwelveFlatTriple n) : Fin 5 → FABL.F₂Cube n := by
  classical
  exact if hp : p ∈ badWeightTwelveFlatTriples n then
    badWeightTwelveFlatTripleWitnessCode
      (chosenBadWeightTwelveFlatTripleWitness p hp)
  else 0

private theorem badWeightTwelveFlatTripleCode_injective_on :
    Set.InjOn (badWeightTwelveFlatTripleCode (n := n))
      (badWeightTwelveFlatTriples n : Set (WeightTwelveFlatTriple n)) := by
  intro p hp q hq hcode
  have hpFin : p ∈ badWeightTwelveFlatTriples n := hp
  have hqFin : q ∈ badWeightTwelveFlatTriples n := hq
  have hcode' :
      badWeightTwelveFlatTripleWitnessCode
          (chosenBadWeightTwelveFlatTripleWitness p hp) =
        badWeightTwelveFlatTripleWitnessCode
          (chosenBadWeightTwelveFlatTripleWitness q hq) := by
    unfold badWeightTwelveFlatTripleCode at hcode
    rw [dif_pos hpFin, dif_pos hqFin] at hcode
    simpa only using hcode
  have h0 := congrFun hcode' (0 : Fin 5)
  have h1 := congrFun hcode' (1 : Fin 5)
  have h2 := congrFun hcode' (2 : Fin 5)
  have h3 := congrFun hcode' (3 : Fin 5)
  have h4 := congrFun hcode' (4 : Fin 5)
  have h0' : (chosenBadWeightTwelveFlatTripleWitness p hp).u =
      (chosenBadWeightTwelveFlatTripleWitness q hq).u := by
    simpa [badWeightTwelveFlatTripleWitnessCode] using h0
  have h1' : (chosenBadWeightTwelveFlatTripleWitness p hp).v =
      (chosenBadWeightTwelveFlatTripleWitness q hq).v := by
    simpa [badWeightTwelveFlatTripleWitnessCode] using h1
  have h2' : (chosenBadWeightTwelveFlatTripleWitness p hp).a =
      (chosenBadWeightTwelveFlatTripleWitness q hq).a := by
    simpa [badWeightTwelveFlatTripleWitnessCode] using h2
  have h3' : (chosenBadWeightTwelveFlatTripleWitness p hp).b =
      (chosenBadWeightTwelveFlatTripleWitness q hq).b := by
    simpa [badWeightTwelveFlatTripleWitnessCode] using h3
  have h4' : (chosenBadWeightTwelveFlatTripleWitness p hp).c =
      (chosenBadWeightTwelveFlatTripleWitness q hq).c := by
    simpa [badWeightTwelveFlatTripleWitnessCode] using h4
  apply Prod.ext
  · rw [← (chosenBadWeightTwelveFlatTripleWitness p hp).line_eq,
      ← (chosenBadWeightTwelveFlatTripleWitness q hq).line_eq,
      h0', h1']
  · apply Prod.ext
    · rw [← (chosenBadWeightTwelveFlatTripleWitness p hp).first_eq,
        ← (chosenBadWeightTwelveFlatTripleWitness q hq).first_eq,
        h0', h1', h2', h3']
    · rw [← (chosenBadWeightTwelveFlatTripleWitness p hp).second_eq,
        ← (chosenBadWeightTwelveFlatTripleWitness q hq).second_eq,
        h0', h1', h2', h4']

/-- Bad affine-line representations inject into five ambient vectors, hence
contribute at most `(2^n)^5` terms. -/
theorem card_badWeightTwelveFlatTriples_le (n : ℕ) :
    (badWeightTwelveFlatTriples n).card ≤ (2 ^ n) ^ 5 := by
  classical
  calc
    (badWeightTwelveFlatTriples n).card ≤
        (Finset.univ : Finset (Fin 5 → FABL.F₂Cube n)).card := by
      apply Finset.card_le_card_of_injOn
        (badWeightTwelveFlatTripleCode (n := n))
      · intro p _hp
        exact Finset.mem_univ _
      · exact badWeightTwelveFlatTripleCode_injective_on
    _ = (2 ^ n) ^ 5 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_f₂Cube]

/-- The affine-line representations whose two three-flats have precisely the
displayed common direction. -/
noncomputable def goodWeightTwelveFlatTriples (n : ℕ) :
    Finset (WeightTwelveFlatTriple n) := by
  classical
  exact (weightTwelveFlatTriples n).filter fun p ↦
    p.2.1.direction ⊓ p.2.2.direction = p.1.direction

private theorem goodWeightTwelveFlatTriple_data
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 ∧
      p.2.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.1.direction = 3 ∧
      p.2.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.2.direction = 3 ∧
      p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
      p.2.1.direction ⊓ p.2.2.direction = p.1.direction := by
  classical
  have hpGood := Finset.mem_filter.mp hp
  exact ⟨(weightTwelveFlatTriple_data hpGood.1).1,
    (weightTwelveFlatTriple_data hpGood.1).2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.2.2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.2.2.2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.2.2.2.2.1,
    (weightTwelveFlatTriple_data hpGood.1).2.2.2.2.2.2.2,
    hpGood.2⟩

/-- The Boolean word represented by a pair of affine three-flats. -/
noncomputable def weightTwelveRepresentationWord
    (p : WeightTwelveFlatTriple n) : BooleanFunction n :=
  binaryAffineFlatIndicator p.2.1 + binaryAffineFlatIndicator p.2.2

noncomputable def weightTwelveFlatTripleCharacter
    (f : BooleanFunction n) (p : WeightTwelveFlatTriple n) : ℝ :=
  binaryAffineFlatCharacter f p.2.1 *
    binaryAffineFlatCharacter f p.2.2

/-- The weight-twelve words in the dual Reed--Muller code. -/
noncomputable def orderTwoWeightTwelveDualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoDualWords n).filter fun h ↦ hammingWeight h = 12

/-- Carlet--Mesnager's `M_f^(12)`, as a canonical dual-code character
sum. -/
noncomputable def orderTwoWeightTwelveCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightTwelveDualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

/-- The character of a represented weight-twelve word is the product of the
two affine-flat characters. -/
theorem weightTwelveRepresentationWord_character
    (f : BooleanFunction n) (p : WeightTwelveFlatTriple n) :
    FABL.binarySign
        (booleanFunctionPairing n f (weightTwelveRepresentationWord p)) =
      weightTwelveFlatTripleCharacter f p := by
  rw [weightTwelveRepresentationWord, map_add, AddChar.map_add_eq_mul]
  rfl

private theorem binaryAffineFlatPoints_inter_eq_line
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    binaryAffineFlatPoints p.2.1 ∩ binaryAffineFlatPoints p.2.2 =
      binaryAffineFlatPoints p.1 := by
  classical
  have hdata := goodWeightTwelveFlatTriple_data hp
  obtain ⟨u, hu⟩ := (AffineSubspace.nonempty_iff_ne_bot p.1).2 hdata.1
  have huFirst : u ∈ p.2.1 := hdata.2.2.2.2.2.2.1 hu
  have huSecond : u ∈ p.2.2 := hdata.2.2.2.2.2.2.2.1 hu
  have huInf : u ∈ p.2.1 ⊓ p.2.2 := by
    exact (AffineSubspace.mem_inf_iff u p.2.1 p.2.2).2
      ⟨huFirst, huSecond⟩
  have hinf : p.2.1 ⊓ p.2.2 = p.1 := by
    apply (AffineSubspace.eq_iff_direction_eq_of_mem huInf hu).2
    rw [AffineSubspace.direction_inf_of_mem_inf huInf]
    exact hdata.2.2.2.2.2.2.2.2
  ext x
  simp only [Finset.mem_inter, mem_binaryAffineFlatPoints]
  rw [← AffineSubspace.mem_inf_iff, hinf]

/-- A precise affine-line representation has Hamming weight twelve. -/
theorem hammingWeight_weightTwelveRepresentationWord
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    hammingWeight (weightTwelveRepresentationWord p) = 12 := by
  have hdata := goodWeightTwelveFlatTriple_data hp
  have hintersection := binaryAffineFlatPoints_inter_eq_line hp
  have hidentity := hammingWeight_add_add_two_mul_card_support_inter
    (binaryAffineFlatIndicator p.2.1) (binaryAffineFlatIndicator p.2.2)
  rw [support_binaryAffineFlatIndicator,
    support_binaryAffineFlatIndicator, hintersection,
    hammingWeight_binaryAffineFlatIndicator p.2.1 hdata.2.2.1,
    hammingWeight_binaryAffineFlatIndicator p.2.2 hdata.2.2.2.2.1,
    card_binaryAffineFlatPoints p.1 hdata.1,
    hdata.2.1, hdata.2.2.2.1, hdata.2.2.2.2.2.1] at hidentity
  norm_num at hidentity
  change hammingWeight
    (binaryAffineFlatIndicator p.2.1 + binaryAffineFlatIndicator p.2.2) = 12
  omega

/-- Every precise affine-line representation produces a weight-twelve word
of the dual Reed--Muller code. -/
theorem weightTwelveRepresentationWord_mem_dualWords
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    weightTwelveRepresentationWord p ∈ orderTwoWeightTwelveDualWords n := by
  classical
  have hpGood := Finset.mem_filter.mp hp
  have hpTriple := Finset.mem_filter.mp hpGood.1
  have hpProduct := Finset.mem_product.mp hpTriple.1
  have hpThree := Finset.mem_product.mp hpProduct.2
  have hfirst := binaryAffineFlatIndicator_mem_reedMuller p.2.1 hpThree.1
  have hsecond := binaryAffineFlatIndicator_mem_reedMuller p.2.2 hpThree.2
  have hsum : weightTwelveRepresentationWord p ∈ reedMuller (n - 3) n := by
    simpa only [weightTwelveRepresentationWord] using
      (reedMuller (n - 3) n).add_mem hfirst hsecond
  simp only [orderTwoWeightTwelveDualWords, orderTwoDualWords,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hsum, hammingWeight_weightTwelveRepresentationWord hp⟩

/-- The finite-fiber interface supplied by the Kasami--Tokura weight-twelve
classification together with the exact count of affine-flat decompositions. -/
def HasWeightTwelveFlatPairClassification (n : ℕ) : Prop :=
  ∀ h : BooleanFunction n,
    ((goodWeightTwelveFlatTriples n).filter fun p ↦
      weightTwelveRepresentationWord p = h).card =
        if h ∈ orderTwoWeightTwelveDualWords n then 20 else 0

/-- The low-weight spectrum interface needed to group the seventh and eighth
moments; in particular it excludes weight ten. -/
def HasOrderTwoLowWeightSpectrum (n : ℕ) : Prop :=
  ∀ h ∈ orderTwoDualWords n, Even (hammingWeight h) →
    hammingWeight h ≤ 16 →
      hammingWeight h = 0 ∨ hammingWeight h = 8 ∨
        hammingWeight h = 12 ∨ hammingWeight h = 14 ∨
          hammingWeight h = 16

private noncomputable def binaryThreeFlatsContaining
    (L : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineFlats 3 n).filter fun A ↦ L ≤ A

/-- The normalized character sum of the affine-line representations used for
the weight-twelve term. -/
noncomputable def weightTwelveRepresentationCharacterSum
    (f : BooleanFunction n) : ℝ :=
  (1 / 20 : ℝ) *
    ∑ p ∈ goodWeightTwelveFlatTriples n,
      weightTwelveFlatTripleCharacter f p

private theorem sum_weightTwelveFlatTriples_eq_sum_sq
    (f : BooleanFunction n) :
    (∑ p ∈ weightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) =
      ∑ L ∈ binaryAffineFlats 1 n,
        (∑ A ∈ binaryThreeFlatsContaining L,
          binaryAffineFlatCharacter f A) ^ 2 := by
  classical
  calc
    (∑ p ∈ weightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) =
        ∑ L ∈ binaryAffineFlats 1 n,
          ∑ A ∈ binaryThreeFlatsContaining L,
            ∑ B ∈ binaryThreeFlatsContaining L,
                binaryAffineFlatCharacter f A *
                binaryAffineFlatCharacter f B := by
      rw [weightTwelveFlatTriples, Finset.sum_filter]
      calc
        (∑ p ∈ (binaryAffineFlats 1 n).product
            ((binaryAffineFlats 3 n).product (binaryAffineFlats 3 n)),
            if p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 then
              weightTwelveFlatTripleCharacter f p else 0) =
            ∑ L ∈ binaryAffineFlats 1 n,
              ∑ q ∈ (binaryAffineFlats 3 n).product
                  (binaryAffineFlats 3 n),
                if L ≤ q.1 ∧ L ≤ q.2 then
                  weightTwelveFlatTripleCharacter f (L, q) else 0 := by
          exact Finset.sum_product _ _ _
        _ = ∑ L ∈ binaryAffineFlats 1 n,
            ∑ A ∈ binaryThreeFlatsContaining L,
              ∑ B ∈ binaryThreeFlatsContaining L,
                binaryAffineFlatCharacter f A *
                  binaryAffineFlatCharacter f B := by
          apply Finset.sum_congr rfl
          intro L _hL
          rw [show (∑ q ∈ (binaryAffineFlats 3 n).product
              (binaryAffineFlats 3 n),
              if L ≤ q.1 ∧ L ≤ q.2 then
                weightTwelveFlatTripleCharacter f (L, q) else 0) =
              ∑ A ∈ binaryAffineFlats 3 n,
                ∑ B ∈ binaryAffineFlats 3 n,
                  if L ≤ A ∧ L ≤ B then
                    weightTwelveFlatTripleCharacter f (L, (A, B)) else 0 by
              exact Finset.sum_product _ _ _]
          simp only [binaryThreeFlatsContaining, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro A _hA
          by_cases hLA : L ≤ A
          · simp only [hLA, true_and, if_true]
            apply Finset.sum_congr rfl
            intro B _hB
            by_cases hLB : L ≤ B <;>
              simp [hLB, weightTwelveFlatTripleCharacter]
          · simp [hLA]
    _ = ∑ L ∈ binaryAffineFlats 1 n,
        (∑ A ∈ binaryThreeFlatsContaining L,
          binaryAffineFlatCharacter f A) ^ 2 := by
      apply Finset.sum_congr rfl
      intro L _hL
      rw [pow_two]
      simp only [Finset.sum_mul, Finset.mul_sum]
      simp only [mul_comm]

private theorem sum_weightTwelveFlatTriples_nonneg
    (f : BooleanFunction n) :
    0 ≤ ∑ p ∈ weightTwelveFlatTriples n,
      weightTwelveFlatTripleCharacter f p := by
  rw [sum_weightTwelveFlatTriples_eq_sum_sq]
  positivity

private theorem weightTwelveFlatTripleCharacter_le_one
    (f : BooleanFunction n) (p : WeightTwelveFlatTriple n) :
    weightTwelveFlatTripleCharacter f p ≤ 1 := by
  rcases binaryAffineFlatCharacter_eq_one_or_neg_one f p.2.1 with hA | hA <;>
    rcases binaryAffineFlatCharacter_eq_one_or_neg_one f p.2.2 with hB | hB <;>
    simp only [weightTwelveFlatTripleCharacter, hA, hB] <;> norm_num

private theorem sum_badWeightTwelveFlatTriples_le
    (f : BooleanFunction n) :
    (∑ p ∈ badWeightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) ≤ (2 ^ n : ℝ) ^ 5 := by
  calc
    (∑ p ∈ badWeightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) ≤
        ∑ _p ∈ badWeightTwelveFlatTriples n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact weightTwelveFlatTripleCharacter_le_one f p
    _ = ((badWeightTwelveFlatTriples n).card : ℝ) := by simp
    _ ≤ ((2 ^ n) ^ 5 : ℕ) := by
      exact_mod_cast card_badWeightTwelveFlatTriples_le n
    _ = (2 ^ n : ℝ) ^ 5 := by norm_num

private theorem sum_goodWeightTwelveFlatTriples_ge
    (f : BooleanFunction n) :
    (∑ p ∈ goodWeightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) ≥ -(2 ^ n : ℝ) ^ 5 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (weightTwelveFlatTriples n)
    (fun p : WeightTwelveFlatTriple n ↦
      p.2.1.direction ⊓ p.2.2.direction ≠ p.1.direction)
    (weightTwelveFlatTripleCharacter f)
  have hgoodFilter :
      (weightTwelveFlatTriples n).filter (fun p ↦
        ¬p.2.1.direction ⊓ p.2.2.direction ≠ p.1.direction) =
        goodWeightTwelveFlatTriples n := by
    classical
    ext p
    simp [goodWeightTwelveFlatTriples]
  rw [show (weightTwelveFlatTriples n).filter (fun p ↦
      p.2.1.direction ⊓ p.2.2.direction ≠ p.1.direction) =
      badWeightTwelveFlatTriples n by rfl, hgoodFilter] at hsplit
  have htotal := sum_weightTwelveFlatTriples_nonneg f
  have hbad := sum_badWeightTwelveFlatTriples_le f
  linarith

/-- The affine representation form of the weight-twelve character sum is at
least `-(2^n)^5 / 20`. -/
theorem weightTwelveRepresentationCharacterSum_ge
    (f : BooleanFunction n) :
    weightTwelveRepresentationCharacterSum f ≥
      -(2 ^ n : ℝ) ^ 5 / 20 := by
  rw [weightTwelveRepresentationCharacterSum]
  have hgood := sum_goodWeightTwelveFlatTriples_ge f
  linarith

private theorem sum_goodWeightTwelveFlatTriples_eq_twenty_mul
    (f : BooleanFunction n)
    (hclassification : HasWeightTwelveFlatPairClassification n) :
    (∑ p ∈ goodWeightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) =
      20 * orderTwoWeightTwelveCharacterSum f := by
  classical
  calc
    (∑ p ∈ goodWeightTwelveFlatTriples n,
        weightTwelveFlatTripleCharacter f p) =
        ∑ h ∈ orderTwoWeightTwelveDualWords n,
          ∑ p ∈ (goodWeightTwelveFlatTriples n).filter
              (fun p ↦ weightTwelveRepresentationWord p = h),
            weightTwelveFlatTripleCharacter f p := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      exact weightTwelveRepresentationWord_mem_dualWords hp
    _ = ∑ h ∈ orderTwoWeightTwelveDualWords n,
        20 * FABL.binarySign (booleanFunctionPairing n f h) := by
      apply Finset.sum_congr rfl
      intro h hh
      calc
        (∑ p ∈ (goodWeightTwelveFlatTriples n).filter
            (fun p ↦ weightTwelveRepresentationWord p = h),
            weightTwelveFlatTripleCharacter f p) =
            ∑ _p ∈ (goodWeightTwelveFlatTriples n).filter
              (fun p ↦ weightTwelveRepresentationWord p = h),
              FABL.binarySign (booleanFunctionPairing n f h) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpWord := (Finset.mem_filter.mp hp).2
          rw [← hpWord, weightTwelveRepresentationWord_character]
        _ = (((goodWeightTwelveFlatTriples n).filter fun p ↦
              weightTwelveRepresentationWord p = h).card : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h) := by simp
        _ = 20 * FABL.binarySign (booleanFunctionPairing n f h) := by
          rw [hclassification h, if_pos hh]
          norm_num
    _ = 20 * orderTwoWeightTwelveCharacterSum f := by
      rw [orderTwoWeightTwelveCharacterSum, Finset.mul_sum]

/-- Under the Kasami--Tokura finite-fiber classification, the canonical
weight-twelve character sum is the affine representation sum. -/
theorem orderTwoWeightTwelveCharacterSum_eq_representation
    (f : BooleanFunction n)
    (hclassification : HasWeightTwelveFlatPairClassification n) :
    orderTwoWeightTwelveCharacterSum f =
      weightTwelveRepresentationCharacterSum f := by
  rw [weightTwelveRepresentationCharacterSum,
    sum_goodWeightTwelveFlatTriples_eq_twenty_mul f hclassification]
  ring

/-- A reusable `O((2^n)^5)` lower bound for the weight-twelve contribution,
conditional only on the cited Kasami--Tokura classification. -/
theorem orderTwoWeightTwelveCharacterSum_ge
    (f : BooleanFunction n)
    (hclassification : HasWeightTwelveFlatPairClassification n) :
    orderTwoWeightTwelveCharacterSum f ≥ -(2 ^ n : ℝ) ^ 5 / 20 := by
  rw [orderTwoWeightTwelveCharacterSum_eq_representation f hclassification]
  exact weightTwelveRepresentationCharacterSum_ge f

end CryptBoolean
