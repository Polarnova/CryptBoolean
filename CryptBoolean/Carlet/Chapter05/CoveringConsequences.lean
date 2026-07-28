/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.CoveringSequences
public import CryptBoolean.Carlet.Chapter04.Resiliency

/-!
# Carlet Chapter 5 consequences of covering sequences

Balancedness and resiliency consequences of the covering-sequence Walsh characterization.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

@[simp] theorem integerWalshTransform_one (b : FABL.F₂Cube n) :
    integerWalshTransform (fun _ ↦ 1) b = if b = 0 then (2 ^ n : ℤ) else 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [integerWalshTransform_cast_eq_rawFourierTransform,
    rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
    FABL.vectorFourierCoeff_eq_expect]
  simp [FABL.expect_vectorWalshCharacter]

private theorem two_mul_two_pow_pred (hn : 0 < n) :
    (2 : ℤ) * 2 ^ (n - 1) = 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp [pow_succ, mul_comm]

/-- A covering sequence at a nonzero level forces balancedness. -/
theorem isBalanced_of_isCoveringSequence_of_ne_zero
    (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ)
    (hcover : IsCoveringSequence f coeff ρ) (hρ : ρ ≠ 0) :
    IsBalanced f := by
  apply isBalanced_iff_walshTransform_zero_eq_zero f |>.mpr
  by_contra hzero
  have htransform :=
    (isCoveringSequence_iff_transform_eq_on_walshSupport f coeff ρ).mp
      hcover 0 hzero
  simp only [integerWalshTransform_zero] at htransform
  omega

/-- Every balanced Boolean function is covered by the constant-one sequence at level
`2^(n-1)`. -/
theorem isCoveringSequence_one_of_isBalanced
    (f : BooleanFunction n) (hbalanced : IsBalanced f) :
    IsCoveringSequence f (fun _ ↦ 1) (2 ^ (n - 1) : ℤ) := by
  have hn : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    change 2 * hammingWeight f = 1 at hbalanced
    omega
  apply (isCoveringSequence_iff_transform_eq_on_walshSupport
    f (fun _ ↦ 1) (2 ^ (n - 1) : ℤ)).mpr
  intro b hb
  have hbzero : b ≠ 0 := by
    intro h
    subst b
    exact hb (isBalanced_iff_walshTransform_zero_eq_zero f |>.mp hbalanced)
  rw [integerWalshTransform_one, if_neg hbzero, integerWalshTransform_one, if_pos rfl]
  rw [← two_mul_two_pow_pred hn]
  ring

/-- A Boolean function is balanced exactly when it admits a covering sequence at a
nonzero level. -/
theorem isBalanced_iff_exists_nontrivialCoveringSequence (f : BooleanFunction n) :
    IsBalanced f ↔
      ∃ (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ),
        IsCoveringSequence f coeff ρ ∧ ρ ≠ 0 := by
  constructor
  · intro hbalanced
    refine ⟨fun _ ↦ 1, (2 ^ (n - 1) : ℤ),
      isCoveringSequence_one_of_isBalanced f hbalanced, ?_⟩
    positivity
  · rintro ⟨coeff, ρ, hcover, hρ⟩
    exact isBalanced_of_isCoveringSequence_of_ne_zero f coeff ρ hcover hρ

/-- A natural number is the minimum weight of a nonzero frequency in an integer
Walsh-transform fiber. -/
def IsMinimumNonzeroTransformFiberWeight
    (coeff : FABL.F₂Cube n → ℤ) (μ : ℤ) (weight : ℕ) : Prop :=
  (∃ b : FABL.F₂Cube n, b ≠ 0 ∧
      integerWalshTransform coeff b = μ ∧
      (FABL.f₂Support b).card = weight) ∧
    ∀ b : FABL.F₂Cube n, b ≠ 0 →
      integerWalshTransform coeff b = μ →
      weight ≤ (FABL.f₂Support b).card

/-- A covering sequence whose distinguished nonzero transform fiber begins in
weight `m + 1` makes the covered function correlation immune of order `m`. -/
theorem isCorrelationImmune_of_coveringSequence_of_minimumTransformFiberWeight
    (m : ℕ) (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ)
    (hn : 0 < n) (hm : m < n)
    (hcover : IsCoveringSequence f coeff ρ)
    (hminimum : IsMinimumNonzeroTransformFiberWeight coeff
      (integerWalshTransform coeff 0 - 2 * ρ) (m + 1)) :
    IsCorrelationImmune m f := by
  apply (theorem_3_correlationImmune_iff_walshTransform_eq_zero
    m f hn hm).mpr
  intro b hb hweight
  by_contra hwalsh
  have htransform :=
    (isCoveringSequence_iff_transform_eq_on_walshSupport f coeff ρ).mp
      hcover b hwalsh
  have hlower := hminimum.2 b hb htransform
  omega

/-- At a nonzero covering level, the same minimum-fiber hypothesis makes the
covered function resilient of order `m`. -/
theorem isResilient_of_coveringSequence_of_minimumTransformFiberWeight
    (m : ℕ) (f : BooleanFunction n) (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ)
    (hn : 0 < n) (hm : m < n)
    (hcover : IsCoveringSequence f coeff ρ) (hρ : ρ ≠ 0)
    (hminimum : IsMinimumNonzeroTransformFiberWeight coeff
      (integerWalshTransform coeff 0 - 2 * ρ) (m + 1)) :
    IsResilient m f :=
  ⟨isCorrelationImmune_of_coveringSequence_of_minimumTransformFiberWeight
      m f coeff ρ hn hm hcover hminimum,
    isBalanced_of_isCoveringSequence_of_ne_zero f coeff ρ hcover hρ⟩

/-- The indicator of the zero Walsh spectrum, regarded as an integer sequence. -/
def walshZeroIndicator (f : BooleanFunction n) (b : FABL.F₂Cube n) : ℤ :=
  if walshTransform f b = 0 then 1 else 0

/-- The inverse integer Walsh transform used in the covering-sequence converses. -/
def walshZeroCoveringSequence (f : BooleanFunction n) : FABL.F₂Cube n → ℤ :=
  integerWalshTransform (walshZeroIndicator f)

/-- The covering level associated with the zero-spectrum construction. -/
def walshZeroCoveringLevel (f : BooleanFunction n) : ℤ :=
  if walshTransform f 0 = 0 then 2 ^ (n - 1) else 0

@[simp] theorem integerWalshTransform_walshZeroCoveringSequence
    (f : BooleanFunction n) (b : FABL.F₂Cube n) :
    integerWalshTransform (walshZeroCoveringSequence f) b =
      if walshTransform f b = 0 then (2 ^ n : ℤ) else 0 := by
  rw [walshZeroCoveringSequence, integerWalshTransform_involution,
    walshZeroIndicator]
  by_cases hwalsh : walshTransform f b = 0 <;> simp [hwalsh]

@[simp] theorem integerWalshTransform_walshZeroCoveringSequence_eq_zero_iff
    (f : BooleanFunction n) (b : FABL.F₂Cube n) :
    integerWalshTransform (walshZeroCoveringSequence f) b = 0 ↔
      walshTransform f b ≠ 0 := by
  rw [integerWalshTransform_walshZeroCoveringSequence]
  by_cases hwalsh : walshTransform f b = 0 <;> simp [hwalsh]

theorem walshZeroCoveringSequence_transformTarget_eq_zero
    (f : BooleanFunction n) (hn : 0 < n) :
    integerWalshTransform (walshZeroCoveringSequence f) 0 -
        2 * walshZeroCoveringLevel f = 0 := by
  rw [integerWalshTransform_walshZeroCoveringSequence]
  by_cases hzero : walshTransform f 0 = 0
  · simp only [hzero, if_pos, walshZeroCoveringLevel]
    rw [← two_mul_two_pow_pred hn]
    ring
  · simp [hzero, walshZeroCoveringLevel]

/-- The zero-spectrum construction is a covering sequence. -/
theorem isCoveringSequence_walshZeroCoveringSequence
    (f : BooleanFunction n) (hn : 0 < n) :
    IsCoveringSequence f (walshZeroCoveringSequence f)
      (walshZeroCoveringLevel f) := by
  apply (isCoveringSequence_iff_transform_eq_on_walshSupport
    f (walshZeroCoveringSequence f) (walshZeroCoveringLevel f)).mpr
  intro b hwalsh
  rw [integerWalshTransform_walshZeroCoveringSequence, if_neg hwalsh,
    walshZeroCoveringSequence_transformTarget_eq_zero f hn]

private theorem minimumTransformFiberWeight_walshZeroCoveringSequence
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m + 1 < n)
    (himmune : IsCorrelationImmune m f)
    (hnotImmune : ¬ IsCorrelationImmune (m + 1) f) :
    IsMinimumNonzeroTransformFiberWeight
      (walshZeroCoveringSequence f) 0 (m + 1) := by
  have hm' : m < n := by omega
  have hlow :=
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hm').mp himmune
  rw [theorem_3_correlationImmune_iff_walshTransform_eq_zero
    (m + 1) f hn hm] at hnotImmune
  push Not at hnotImmune
  obtain ⟨b, hb, hweight, hwalsh⟩ := hnotImmune
  have hweightExact : (FABL.f₂Support b).card = m + 1 := by
    have hnotLow : ¬ (FABL.f₂Support b).card ≤ m := by
      intro hcard
      exact hwalsh (hlow b hb hcard)
    omega
  constructor
  · exact ⟨b, hb,
      integerWalshTransform_walshZeroCoveringSequence_eq_zero_iff f b |>.mpr hwalsh,
      hweightExact⟩
  · intro u hu htransform
    have hwalshU :=
      integerWalshTransform_walshZeroCoveringSequence_eq_zero_iff f u |>.mp
        htransform
    have hnotLow : ¬ (FABL.f₂Support u).card ≤ m := by
      intro hcard
      exact hwalshU (hlow u hu hcard)
    omega

/-- If `f` is correlation immune of order `m` but not of order `m + 1`, then
it admits a covering sequence whose distinguished nonzero transform fiber has
minimum weight `m + 1`. -/
theorem exists_coveringSequence_of_correlationImmune_not_succ
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m + 1 < n)
    (himmune : IsCorrelationImmune m f)
    (hnotImmune : ¬ IsCorrelationImmune (m + 1) f) :
    ∃ (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ),
      IsCoveringSequence f coeff ρ ∧
        IsMinimumNonzeroTransformFiberWeight coeff
          (integerWalshTransform coeff 0 - 2 * ρ) (m + 1) := by
  refine ⟨walshZeroCoveringSequence f, walshZeroCoveringLevel f,
    isCoveringSequence_walshZeroCoveringSequence f hn, ?_⟩
  rw [walshZeroCoveringSequence_transformTarget_eq_zero f hn]
  exact minimumTransformFiberWeight_walshZeroCoveringSequence
    m f hn hm himmune hnotImmune

/-- If `f` is resilient of order `m` but not of order `m + 1`, the converse
covering sequence can be chosen at a nonzero level. -/
theorem exists_nontrivialCoveringSequence_of_resilient_not_succ
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m + 1 < n)
    (hresilient : IsResilient m f)
    (hnotResilient : ¬ IsResilient (m + 1) f) :
    ∃ (coeff : FABL.F₂Cube n → ℤ) (ρ : ℤ),
      IsCoveringSequence f coeff ρ ∧ ρ ≠ 0 ∧
        IsMinimumNonzeroTransformFiberWeight coeff
          (integerWalshTransform coeff 0 - 2 * ρ) (m + 1) := by
  have hnotImmune : ¬ IsCorrelationImmune (m + 1) f := by
    intro himmune
    exact hnotResilient ⟨himmune, hresilient.2⟩
  refine ⟨walshZeroCoveringSequence f, walshZeroCoveringLevel f,
    isCoveringSequence_walshZeroCoveringSequence f hn, ?_, ?_⟩
  · rw [walshZeroCoveringLevel,
      isBalanced_iff_walshTransform_zero_eq_zero f |>.mp hresilient.2]
    exact pow_ne_zero _ (by norm_num)
  · rw [walshZeroCoveringSequence_transformTarget_eq_zero f hn]
    exact minimumTransformFiberWeight_walshZeroCoveringSequence
      m f hn hm hresilient.1 hnotImmune

/-- The integer indicator of the weight-one directions. -/
def weightOneDirectionIndicator (a : FABL.F₂Cube n) : ℤ :=
  if (FABL.f₂Support a).card = 1 then 1 else 0

/-- A Boolean function is regular at level `ρ` when the weight-one direction
indicator covers it at that level. -/
def IsRegularAtLevel (f : BooleanFunction n) (ρ : ℤ) : Prop :=
  IsCoveringSequence f weightOneDirectionIndicator ρ

/-- Carlet's regular Boolean functions are those regular at some integer level. -/
def IsRegular (f : BooleanFunction n) : Prop :=
  ∃ ρ : ℤ, IsRegularAtLevel f ρ

private theorem bitValueInt_eq_if_ne_zero (b : FABL.𝔽₂) :
    bitValueInt b = if b ≠ 0 then 1 else 0 := by
  fin_cases b <;> rfl

/-- The integer Walsh transform of the weight-one direction indicator. -/
theorem integerWalshTransform_weightOneDirectionIndicator
    (b : FABL.F₂Cube n) :
    integerWalshTransform (weightOneDirectionIndicator : FABL.F₂Cube n → ℤ) b =
      (n : ℤ) - 2 * ((FABL.f₂Support b).card : ℤ) := by
  classical
  rw [integerWalshTransform]
  calc
    ∑ a, weightOneDirectionIndicator a *
          bitSignInt (FABL.f₂DotProduct a b) =
        ∑ a ∈ (Finset.univ.filter fun a : FABL.F₂Cube n ↦
          (FABL.f₂Support a).card = 1),
          bitSignInt (FABL.f₂DotProduct a b) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hweight : (FABL.f₂Support a).card = 1 <;>
        simp [weightOneDirectionIndicator, hweight]
    _ = ∑ i : Fin n, bitSignInt (b i) := by
      symm
      apply Finset.sum_bij
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
          FABL.f₂CubeOfFinset ({i} : Finset (Fin n)))
      · intro i _
        have hsupport :
            FABL.f₂Support (FABL.f₂CubeOfFinset ({i} : Finset (Fin n))) = {i} :=
          (FABL.f₂CubeEquivFinset n).right_inv {i}
        simp [hsupport]
      · intro i _ j _ hij
        apply Finset.singleton_injective
        have hsupport := congrArg FABL.f₂Support hij
        calc
          ({i} : Finset (Fin n)) =
              FABL.f₂Support (FABL.f₂CubeOfFinset ({i} : Finset (Fin n))) :=
            ((FABL.f₂CubeEquivFinset n).right_inv {i}).symm
          _ = FABL.f₂Support (FABL.f₂CubeOfFinset
              ({j} : Finset (Fin n))) := hsupport
          _ = {j} := (FABL.f₂CubeEquivFinset n).right_inv {j}
      · intro a ha
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp ha).2
        refine ⟨i, Finset.mem_univ i, ?_⟩
        apply (FABL.f₂CubeEquivFinset n).injective
        simpa [hi] using
          (FABL.f₂CubeEquivFinset n).right_inv ({i} : Finset (Fin n))
      · intro i _
        have hdot :
            FABL.f₂DotProduct (FABL.f₂CubeOfFinset
              ({i} : Finset (Fin n))) b = b i := by
          rw [FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
          have hsupport : FABL.f₂Support
              (FABL.f₂CubeOfFinset ({i} : Finset (Fin n))) = {i} :=
            (FABL.f₂CubeEquivFinset n).right_inv {i}
          rw [hsupport]
          simp [FABL.coordinateSum]
        rw [hdot]
    _ = (n : ℤ) - 2 * ((FABL.f₂Support b).card : ℤ) := by
      simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt,
        bitValueInt_eq_if_ne_zero]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [Finset.sum_boole]
      simp [FABL.f₂Support]

private theorem support_card_eq_of_isRegularAtLevel
    (f : BooleanFunction n) (ρ : ℕ)
    (hregular : IsRegularAtLevel f (ρ : ℤ))
    (b : FABL.F₂Cube n) (hwalsh : walshTransform f b ≠ 0) :
    (FABL.f₂Support b).card = ρ := by
  have htransform :=
    (isCoveringSequence_iff_transform_eq_on_walshSupport
      f weightOneDirectionIndicator (ρ : ℤ)).mp hregular b hwalsh
  rw [integerWalshTransform_weightOneDirectionIndicator,
    integerWalshTransform_weightOneDirectionIndicator] at htransform
  simp [FABL.f₂Support] at htransform
  simpa [FABL.f₂Support] using htransform

/-- A regular Boolean function covered at a positive natural level `ρ` is
resilient of order `ρ - 1`. -/
theorem isResilient_natPred_of_isRegularAtLevel
    (f : BooleanFunction n) (ρ : ℕ) (hn : 0 < n) (hρ : 0 < ρ)
    (hregular : IsRegularAtLevel f (ρ : ℤ)) :
    IsResilient (ρ - 1) f := by
  obtain ⟨b, hwalsh⟩ := exists_walshTransform_ne_zero f
  have hweight := support_card_eq_of_isRegularAtLevel f ρ hregular b hwalsh
  have hρn : ρ ≤ n := by
    calc
      ρ = (FABL.f₂Support b).card := hweight.symm
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have horder : ρ - 1 < n := by omega
  apply (theorem_3_resilient_iff_walshTransform_eq_zero
    (ρ - 1) f hn horder).mpr
  intro u hu
  by_contra hwalshU
  have hweightU :=
    support_card_eq_of_isRegularAtLevel f ρ hregular u hwalshU
  omega

/-- The integer indicator of a finite family of directions. -/
def directionFamilyIndicator (directions : Finset (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : ℤ :=
  if a ∈ directions then 1 else 0

/-- The supports of distinct directions in a family are disjoint. -/
def HasPairwiseDisjointSupports
    (directions : Finset (FABL.F₂Cube n)) : Prop :=
  Set.PairwiseDisjoint (↑directions : Set (FABL.F₂Cube n)) FABL.f₂Support

/-- The transform of a direction-family indicator counts directions having
odd scalar product with the frequency. -/
theorem integerWalshTransform_directionFamilyIndicator
    (directions : Finset (FABL.F₂Cube n)) (b : FABL.F₂Cube n) :
    integerWalshTransform (directionFamilyIndicator directions) b =
      (directions.card : ℤ) - 2 *
        ((directions.filter fun a ↦ FABL.f₂DotProduct a b = 1).card : ℤ) := by
  classical
  rw [integerWalshTransform]
  calc
    ∑ a, directionFamilyIndicator directions a *
          bitSignInt (FABL.f₂DotProduct a b) =
        ∑ a ∈ directions, bitSignInt (FABL.f₂DotProduct a b) := by
      simp [directionFamilyIndicator]
    _ = (directions.card : ℤ) - 2 *
        ((directions.filter fun a ↦ FABL.f₂DotProduct a b = 1).card : ℤ) := by
      simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt, bitValueInt]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
      simp

@[simp] theorem integerWalshTransform_directionFamilyIndicator_zero
    (directions : Finset (FABL.F₂Cube n)) :
    integerWalshTransform (directionFamilyIndicator directions) 0 =
      (directions.card : ℤ) := by
  rw [integerWalshTransform_directionFamilyIndicator]
  simp [FABL.f₂DotProduct]

private theorem support_inter_nonempty_of_f₂DotProduct_eq_one
    (a b : FABL.F₂Cube n) (hdot : FABL.f₂DotProduct a b = 1) :
    (FABL.f₂Support a ∩ FABL.f₂Support b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hinter
  have hzero : FABL.f₂DotProduct a b = 0 := by
    rw [FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
    change (∑ i ∈ FABL.f₂Support a, b i) = 0
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hbi
    have hiSupportB : i ∈ FABL.f₂Support b :=
      (FABL.mem_f₂Support b i).mpr hbi
    have hiInter : i ∈ FABL.f₂Support a ∩ FABL.f₂Support b :=
      Finset.mem_inter.mpr ⟨hi, hiSupportB⟩
    rw [hinter] at hiInter
    simp at hiInter
  rw [hzero] at hdot
  exact zero_ne_one hdot

private theorem card_oddDirections_le_support_card
    (directions : Finset (FABL.F₂Cube n))
    (hdisjoint : HasPairwiseDisjointSupports directions)
    (b : FABL.F₂Cube n) :
    (directions.filter fun a ↦ FABL.f₂DotProduct a b = 1).card ≤
      (FABL.f₂Support b).card := by
  classical
  let oddDirections :=
    directions.filter fun a ↦ FABL.f₂DotProduct a b = 1
  have hinter (a : ↑oddDirections) :
      (FABL.f₂Support a.1 ∩ FABL.f₂Support b).Nonempty :=
    support_inter_nonempty_of_f₂DotProduct_eq_one a.1 b
      (Finset.mem_filter.mp a.2).2
  let chosen : (a : ↑oddDirections) →
      ↑(FABL.f₂Support a.1 ∩ FABL.f₂Support b) :=
    fun a ↦ ⟨(hinter a).choose, (hinter a).choose_spec⟩
  let intoSupport : ↑oddDirections → ↑(FABL.f₂Support b) :=
    fun a ↦ ⟨(chosen a).1, (Finset.mem_inter.mp (chosen a).2).2⟩
  have hinjective : Function.Injective intoSupport := by
    intro a c hequal
    apply Subtype.ext
    by_contra hac
    have haDirections : a.1 ∈ directions := (Finset.mem_filter.mp a.2).1
    have hcDirections : c.1 ∈ directions := (Finset.mem_filter.mp c.2).1
    have hsSupports : Disjoint (FABL.f₂Support a.1) (FABL.f₂Support c.1) :=
      hdisjoint haDirections hcDirections hac
    have hcoordinate : (chosen a).1 = (chosen c).1 :=
      congrArg Subtype.val hequal
    have haChosen : (chosen a).1 ∈ FABL.f₂Support a.1 :=
      (Finset.mem_inter.mp (chosen a).2).1
    have hcChosen : (chosen a).1 ∈ FABL.f₂Support c.1 := by
      rw [hcoordinate]
      exact (Finset.mem_inter.mp (chosen c).2).1
    exact (Finset.disjoint_left.mp hsSupports) haChosen hcChosen
  change oddDirections.card ≤ (FABL.f₂Support b).card
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective intoSupport hinjective

private theorem oddDirections_card_eq_of_coveringSequence
    (directions : Finset (FABL.F₂Cube n)) (f : BooleanFunction n) (ρ : ℕ)
    (hcover : IsCoveringSequence f (directionFamilyIndicator directions) (ρ : ℤ))
    (b : FABL.F₂Cube n) (hwalsh : walshTransform f b ≠ 0) :
    (directions.filter fun a ↦ FABL.f₂DotProduct a b = 1).card = ρ := by
  have htransform :=
    (isCoveringSequence_iff_transform_eq_on_walshSupport
      f (directionFamilyIndicator directions) (ρ : ℤ)).mp hcover b hwalsh
  rw [integerWalshTransform_directionFamilyIndicator,
    integerWalshTransform_directionFamilyIndicator_zero] at htransform
  omega

/-- If the indicator of a family of directions with pairwise disjoint supports
covers `f` at a positive natural level `ρ`, then `f` is resilient of order
`ρ - 1`. -/
theorem isResilient_natPred_of_pairwiseDisjointSupportCoveringSequence
    (directions : Finset (FABL.F₂Cube n))
    (hdisjoint : HasPairwiseDisjointSupports directions)
    (f : BooleanFunction n) (ρ : ℕ) (hn : 0 < n) (hρ : 0 < ρ)
    (hcover : IsCoveringSequence f
      (directionFamilyIndicator directions) (ρ : ℤ)) :
    IsResilient (ρ - 1) f := by
  obtain ⟨b, hwalsh⟩ := exists_walshTransform_ne_zero f
  have hodd := oddDirections_card_eq_of_coveringSequence
    directions f ρ hcover b hwalsh
  have hlower : ρ ≤ (FABL.f₂Support b).card := by
    rw [← hodd]
    exact card_oddDirections_le_support_card directions hdisjoint b
  have hρn : ρ ≤ n := by
    calc
      ρ ≤ (FABL.f₂Support b).card := hlower
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have horder : ρ - 1 < n := by omega
  apply (theorem_3_resilient_iff_walshTransform_eq_zero
    (ρ - 1) f hn horder).mpr
  intro u hu
  by_contra hwalshU
  have hoddU := oddDirections_card_eq_of_coveringSequence
    directions f ρ hcover u hwalshU
  have hlowerU : ρ ≤ (FABL.f₂Support u).card := by
    rw [← hoddU]
    exact card_oddDirections_le_support_card directions hdisjoint u
  omega

end CryptBoolean
