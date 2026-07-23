/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Derivatives
public import CryptBoolean.Carlet.Chapter04.Resiliency
public import FABL.Chapter04.Switching
public import FABL.Chapter06.F₂Polynomials.Encoding

/-!
# Carlet Chapter 4 propagation criteria

Propagation criteria, strict avalanche, coordinate-restriction orders, and extended
propagation criteria.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The nonzero directions of Hamming weight at most `l`. -/
def lowWeightNonzeroDirections (l : ℕ) : Set (FABL.F₂Cube n) :=
  {a | a ≠ 0 ∧ (FABL.f₂Support a).card ≤ l}

/-- Carlet's propagation criterion with respect to a set of directions. -/
def SatisfiesPropagationCriterionOn
    (E : Set (FABL.F₂Cube n)) (f : BooleanFunction n) : Prop :=
  ∀ a ∈ E, IsBalanced (FABL.booleanDerivative f a)

/-- Carlet's propagation criterion `PC(l)`. -/
def SatisfiesPropagationCriterion (l : ℕ) (f : BooleanFunction n) : Prop :=
  SatisfiesPropagationCriterionOn (lowWeightNonzeroDirections l) f

/-- `PC(l)` is propagation with respect to exactly the nonzero directions of weight at most
`l`. -/
theorem satisfiesPropagationCriterion_iff_on_lowWeightNonzeroDirections
    (l : ℕ) (f : BooleanFunction n) :
    SatisfiesPropagationCriterion l f ↔
      SatisfiesPropagationCriterionOn (lowWeightNonzeroDirections l) f := by
  rfl

/-- Balancedness of a directional derivative is equivalent to vanishing autocorrelation in
that direction. -/
theorem isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    IsBalanced (FABL.booleanDerivative f a) ↔ autocorrelation f a = 0 := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  have hcast :
      autocorrelation f a =
        (walshTransform (FABL.booleanDerivative f a) 0 : ℝ) := by
    rw [autocorrelation, walshTransform_cast_eq_sum_realSignView_mul_character]
    simp
  constructor
  · intro h
    rw [hcast]
    exact_mod_cast h
  · intro h
    rw [hcast] at h
    exact_mod_cast h

/-- Carlet's autocorrelation form of `PC(l)`. -/
theorem satisfiesPropagationCriterion_iff_autocorrelation_eq_zero
    (l : ℕ) (f : BooleanFunction n) :
    SatisfiesPropagationCriterion l f ↔
      ∀ a : FABL.F₂Cube n, a ≠ 0 →
        (FABL.f₂Support a).card ≤ l → autocorrelation f a = 0 := by
  rw [SatisfiesPropagationCriterion, SatisfiesPropagationCriterionOn]
  constructor
  · intro h a ha hweight
    exact isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a |>.mp
      (h a ⟨ha, hweight⟩)
  · intro h a ha
    exact isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a |>.mpr
      (h a ha.1 ha.2)

/-- The strict avalanche criterion is `PC(1)`. -/
def SatisfiesStrictAvalancheCriterion (f : BooleanFunction n) : Prop :=
  SatisfiesPropagationCriterion 1 f

/-- SAC is definitionally the first propagation criterion. -/
theorem satisfiesStrictAvalancheCriterion_iff_pc_one
    (f : BooleanFunction n) :
    SatisfiesStrictAvalancheCriterion f ↔ SatisfiesPropagationCriterion 1 f := by
  rfl

/-- Lowering the propagation parameter preserves the criterion. -/
theorem SatisfiesPropagationCriterion.mono
    {l l' : ℕ} {f : BooleanFunction n}
    (hf : SatisfiesPropagationCriterion l f) (hll' : l' ≤ l) :
    SatisfiesPropagationCriterion l' f := by
  intro a ha
  exact hf a ⟨ha.1, ha.2.trans hll'⟩

/-- A coordinate restriction, canonically reindexed by `Fin J.card`, built from FABL's
restriction and Boolean-encoding APIs. -/
noncomputable def coordinateRestriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J) :
    BooleanFunction J.card :=
  FABL.booleanFunctionF₂Encoding
    (FABL.reindexedSignRestriction (signCubeView f) J z)

private noncomputable def fixedBinaryAssignment
    (J : Finset (Fin n)) (z : FABL.FixedSignCube J) : FABL.F₂Cube n :=
  fun i ↦ if hi : i ∈ J then 0 else FABL.binarySignEquiv.symm (z ⟨i, hi⟩)

/-- Evaluation of a coordinate restriction as extension along FABL's canonical free-coordinate
embedding. -/
private theorem coordinateRestriction_apply
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (x : FABL.F₂Cube J.card) :
    coordinateRestriction f J z x =
      f (Function.extend (FABL.freeCoordinateEmbedding J) x
        (fixedBinaryAssignment J z)) := by
  classical
  unfold coordinateRestriction FABL.booleanFunctionF₂Encoding
    FABL.reindexedSignRestriction signCubeView
  rw [FABL.signRestriction_apply]
  let y : FABL.F₂Cube n :=
    (FABL.binaryCubeSignEquiv n).symm
      (FABL.combineSignCube J
        (fun i ↦ FABL.binaryCubeSignEquiv J.card x (J.equivFin i)) z)
  change FABL.binarySignEquiv.symm (FABL.binarySignEquiv (f y)) = _
  rw [FABL.binarySignEquiv.symm_apply_apply]
  dsimp [y]
  congr 1
  apply (FABL.binaryCubeSignEquiv n).injective
  rw [(FABL.binaryCubeSignEquiv n).apply_symm_apply]
  funext i
  by_cases hi : i ∈ J
  · let q : Fin J.card := J.equivFin ⟨i, hi⟩
    have hqi : FABL.freeCoordinateEmbedding J q = i := by
      dsimp [q]
      exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hi⟩
    have hvalue :
        Function.extend (FABL.freeCoordinateEmbedding J) x
            (fixedBinaryAssignment J z) i = x q := by
      rw [← hqi, (FABL.freeCoordinateEmbedding J).injective.extend_apply]
    have hleft :
        FABL.combineSignCube J
            (fun i ↦ FABL.signEncode (x (J.equivFin i))) z i =
          FABL.signEncode (x q) := by
      change FABL.combineSignCube J
          (fun i ↦ FABL.signEncode (x (J.equivFin i))) z
            ((⟨i, hi⟩ : J) : Fin n) = _
      rw [FABL.combineSignCube_apply_free]
    rw [hleft, FABL.binaryCubeSignEquiv_apply, hvalue]
  · have hnotImage : ¬ ∃ q, FABL.freeCoordinateEmbedding J q = i := by
      rintro ⟨q, hqi⟩
      exact hi (by
        rw [← hqi]
        change (J.equivFin.symm q : Fin n) ∈ J
        exact (J.equivFin.symm q).property)
    have hleft :
        FABL.combineSignCube J
            (fun i ↦ FABL.signEncode (x (J.equivFin i))) z i = z ⟨i, hi⟩ := by
      change FABL.combineSignCube J
          (fun i ↦ FABL.signEncode (x (J.equivFin i))) z
            ((⟨i, hi⟩ : FABL.FixedIndex J) : Fin n) = _
      rw [FABL.combineSignCube_apply_fixed]
    rw [hleft, FABL.binaryCubeSignEquiv_apply,
      Function.extend_apply' x (fixedBinaryAssignment J z) i hnotImage]
    simp only [fixedBinaryAssignment, hi, dite_false]
    change z ⟨i, hi⟩ = FABL.binarySignEquiv (FABL.binarySignEquiv.symm (z ⟨i, _⟩))
    rw [FABL.binarySignEquiv.apply_symm_apply]

/-- Extend a direction on the free coordinates by zero on the fixed coordinates. -/
private noncomputable def liftRestrictionDirection
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) : FABL.F₂Cube n :=
  Function.extend (FABL.freeCoordinateEmbedding J) a 0

@[simp] private theorem liftRestrictionDirection_apply_free
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) (i : Fin J.card) :
    liftRestrictionDirection J a (FABL.freeCoordinateEmbedding J i) = a i := by
  rw [liftRestrictionDirection,
    (FABL.freeCoordinateEmbedding J).injective.extend_apply]

private theorem liftRestrictionDirection_apply_fixed
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) (i : Fin n)
    (hi : i ∉ J) : liftRestrictionDirection J a i = 0 := by
  rw [liftRestrictionDirection]
  apply Function.extend_apply'
  rintro ⟨q, hqi⟩
  apply hi
  rw [← hqi]
  change (J.equivFin.symm q : Fin n) ∈ J
  exact (J.equivFin.symm q).property

private theorem liftRestrictionDirection_injective (J : Finset (Fin n)) :
    Function.Injective (liftRestrictionDirection J) := by
  intro a b hab
  funext i
  have hi := congrFun hab (FABL.freeCoordinateEmbedding J i)
  simpa using hi

@[simp] private theorem liftRestrictionDirection_eq_zero_iff
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) :
    liftRestrictionDirection J a = 0 ↔ a = 0 := by
  have hzero : liftRestrictionDirection J (0 : FABL.F₂Cube J.card) = 0 := by
    funext i
    by_cases hi : i ∈ J
    · let q : Fin J.card := J.equivFin ⟨i, hi⟩
      have hqi : FABL.freeCoordinateEmbedding J q = i := by
        dsimp [q]
        exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hi⟩
      rw [← hqi, liftRestrictionDirection_apply_free]
      rfl
    · rw [liftRestrictionDirection_apply_fixed J 0 i hi]
      rfl
  constructor
  · intro h
    apply liftRestrictionDirection_injective J
    exact h.trans hzero.symm
  · rintro rfl
    exact hzero

private theorem f₂Support_liftRestrictionDirection
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) :
    FABL.f₂Support (liftRestrictionDirection J a) =
      (FABL.f₂Support a).map (FABL.freeCoordinateEmbedding J) := by
  classical
  ext i
  rw [FABL.mem_f₂Support, Finset.mem_map]
  constructor
  · intro hi
    by_cases himage : ∃ q, FABL.freeCoordinateEmbedding J q = i
    · obtain ⟨q, hqi⟩ := himage
      refine ⟨q, ?_, hqi⟩
      rw [FABL.mem_f₂Support]
      rw [← hqi] at hi
      simpa using hi
    · exact False.elim (hi (liftRestrictionDirection_apply_fixed J a i (by
        intro hiJ
        let q : Fin J.card := J.equivFin ⟨i, hiJ⟩
        apply himage
        exact ⟨q, by
          dsimp [q]
          exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hiJ⟩⟩)))
  · rintro ⟨q, hq, rfl⟩
    rw [liftRestrictionDirection_apply_free]
    exact (FABL.mem_f₂Support a q).mp hq

@[simp] private theorem card_f₂Support_liftRestrictionDirection
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) :
    (FABL.f₂Support (liftRestrictionDirection J a)).card =
      (FABL.f₂Support a).card := by
  rw [f₂Support_liftRestrictionDirection, Finset.card_map]

/-- Restrict an ambient direction to the canonically enumerated free coordinates. -/
private noncomputable def restrictToFreeDirection
    (J : Finset (Fin n)) (a : FABL.F₂Cube n) : FABL.F₂Cube J.card :=
  fun i ↦ a (FABL.freeCoordinateEmbedding J i)

/-- Extending a direction supported on the free coordinates recovers the ambient direction. -/
private theorem liftRestrictionDirection_restrictToFreeDirection
    (J : Finset (Fin n)) (a : FABL.F₂Cube n)
    (ha : FABL.f₂Support a ⊆ J) :
    liftRestrictionDirection J (restrictToFreeDirection J a) = a := by
  funext i
  by_cases hi : i ∈ J
  · let q : Fin J.card := J.equivFin ⟨i, hi⟩
    have hqi : FABL.freeCoordinateEmbedding J q = i := by
      dsimp [q]
      exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hi⟩
    rw [← hqi, liftRestrictionDirection_apply_free]
    rfl
  · rw [liftRestrictionDirection_apply_fixed J _ i hi]
    symm
    by_contra hai
    exact hi (ha ((FABL.mem_f₂Support a i).mpr hai))

/-- A direction extended by zero is supported on the free coordinates. -/
private theorem f₂Support_liftRestrictionDirection_subset
    (J : Finset (Fin n)) (a : FABL.F₂Cube J.card) :
    FABL.f₂Support (liftRestrictionDirection J a) ⊆ J := by
  rw [f₂Support_liftRestrictionDirection]
  intro i hi
  obtain ⟨q, _hq, rfl⟩ := Finset.mem_map.mp hi
  change (J.equivFin.symm q : Fin n) ∈ J
  exact (J.equivFin.symm q).property

private theorem restrictionInput_add_liftRestrictionDirection
    (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (x a : FABL.F₂Cube J.card) :
    Function.extend (FABL.freeCoordinateEmbedding J) (x + a)
        (fixedBinaryAssignment J z) =
      Function.extend (FABL.freeCoordinateEmbedding J) x
          (fixedBinaryAssignment J z) + liftRestrictionDirection J a := by
  classical
  funext i
  by_cases himage : ∃ q, FABL.freeCoordinateEmbedding J q = i
  · obtain ⟨q, rfl⟩ := himage
    simp [liftRestrictionDirection,
      (FABL.freeCoordinateEmbedding J).injective.extend_apply]
  · rw [Function.extend_apply' (x + a) (fixedBinaryAssignment J z) i himage]
    change fixedBinaryAssignment J z i =
      Function.extend (FABL.freeCoordinateEmbedding J) x
          (fixedBinaryAssignment J z) i + liftRestrictionDirection J a i
    rw [Function.extend_apply' x (fixedBinaryAssignment J z) i himage]
    have hi : i ∉ J := by
      intro hiJ
      apply himage
      let q : Fin J.card := J.equivFin ⟨i, hiJ⟩
      exact ⟨q, by
        dsimp [q]
        exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hiJ⟩⟩
    rw [liftRestrictionDirection_apply_fixed J a i hi]
    simp

/-- Directional differentiation commutes with coordinate restriction when the direction is
supported on the free coordinates. -/
private theorem coordinateRestriction_booleanDerivative
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (a : FABL.F₂Cube J.card) :
    coordinateRestriction (FABL.booleanDerivative f (liftRestrictionDirection J a)) J z =
      FABL.booleanDerivative (coordinateRestriction f J z) a := by
  funext x
  simp only [FABL.booleanDerivative]
  rw [coordinateRestriction_apply, coordinateRestriction_apply,
    coordinateRestriction_apply,
    restrictionInput_add_liftRestrictionDirection]
  rfl

/-- Encoding a sign-valued Boolean function and returning to the sign cube is the identity. -/
private theorem signCubeView_booleanFunctionF₂Encoding
    (g : FABL.BooleanFunction n) :
    signCubeView (FABL.booleanFunctionF₂Encoding g) = g := by
  funext x
  unfold signCubeView FABL.booleanFunctionF₂Encoding
  rw [(FABL.binaryCubeSignEquiv n).apply_symm_apply]
  change FABL.binarySignEquiv (FABL.binarySignEquiv.symm (g x)) = g x
  rw [FABL.binarySignEquiv.apply_symm_apply]

/-- The sign view of the canonical bit-valued coordinate restriction is FABL's reindexed
sign restriction. -/
private theorem signCubeView_coordinateRestriction
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J) :
    signCubeView (coordinateRestriction f J z) =
      FABL.reindexedSignRestriction (signCubeView f) J z := by
  rw [coordinateRestriction, signCubeView_booleanFunctionF₂Encoding]

private theorem mean_reindexedSignRestriction_toReal
    (g : FABL.BooleanFunction n) (J : Finset (Fin n))
    (z : FABL.FixedSignCube J) :
    FABL.mean (FABL.reindexedSignRestriction g J z).toReal =
      FABL.mean (FABL.signRestriction g.toReal J z) := by
  classical
  unfold FABL.mean
  let e : {−1,1}^[J.card] ≃ FABL.FreeSignCube J :=
    Equiv.arrowCongr J.equivFin.symm (Equiv.refl FABL.Sign)
  apply Fintype.expect_equiv e
  intro y
  simp [FABL.BooleanFunction.toReal, FABL.reindexedSignRestriction,
    FABL.signRestriction, e, Equiv.arrowCongr, Function.comp_def]

/-- Balancedness of the canonical bit-valued restriction is exactly balancedness of FABL's
subtype-indexed sign restriction. -/
private theorem isBalanced_coordinateRestriction_iff
    (f : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J) :
    IsBalanced (coordinateRestriction f J z) ↔
      FABL.IsBalanced
        (FABL.signRestriction (signCubeView f).toReal J z) := by
  rw [isBalanced_iff_fabl, FABL.IsBalanced, FABL.IsBalanced,
    signCubeView_coordinateRestriction]
  exact Eq.congr_left (mean_reindexedSignRestriction_toReal (signCubeView f) J z)

private theorem isBalanced_coordinateRestriction_of_isResilient
    (k : ℕ) (f : BooleanFunction n) (J : Finset (Fin n))
    (z : FABL.FixedSignCube J) (hf : IsResilient k f)
    (hcard : Fintype.card (FABL.FixedIndex J) = k) :
    IsBalanced (coordinateRestriction f J z) := by
  rw [isBalanced_coordinateRestriction_iff]
  rw [FABL.IsBalanced]
  exact (hf.1 J z hcard.le).trans
    (isBalanced_iff_fabl f |>.mp hf.2)

private theorem liftFixedFrequency_fixedFrequencyPart_eq_of_subset_compl
    (J S : Finset (Fin n)) (hSJ : S ⊆ Jᶜ) :
    FABL.liftFixedFrequency (FABL.fixedFrequencyPart J S) = S := by
  have hfree : FABL.freeFrequencyPart J S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiS : (i : Fin n) ∈ S := (FABL.mem_freeFrequencyPart J S i).mp hi
    exact (Finset.mem_compl.mp (hSJ hiS)) i.property
  have hsplit := FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart J S
  rw [hfree] at hsplit
  simpa [FABL.liftFreeFrequency] using hsplit

private theorem fourierCoeff_eq_zero_of_all_coordinateRestrictions_balanced
    (g : BooleanFunction n) (J : Finset (Fin n))
    (hbalanced : ∀ z : FABL.FixedSignCube J,
      IsBalanced (coordinateRestriction g J z))
    (S : Finset (Fin n)) (hSJ : S ⊆ Jᶜ) :
    FABL.fourierCoeff (signCubeView g).toReal S = 0 := by
  let T : Finset (FABL.FixedIndex J) := FABL.fixedFrequencyPart J S
  have hlift : FABL.liftFixedFrequency T = S := by
    exact liftFixedFrequency_fixedFrequencyPart_eq_of_subset_compl J S hSJ
  have hrestriction :
      FABL.restrictionFourierCoeff (signCubeView g).toReal J ∅ = 0 := by
    funext z
    change FABL.indexedFourierCoeff
        (FABL.signRestriction (signCubeView g).toReal J z) ∅ = 0
    rw [← FABL.expect_eq_indexedFourierCoeff_empty]
    exact isBalanced_coordinateRestriction_iff g J z |>.mp (hbalanced z)
  have hcoefficient :=
    FABL.indexedFourierCoeff_restrictionFourierCoeff
      (signCubeView g).toReal J (∅ : Finset J) T
  rw [hrestriction] at hcoefficient
  simpa [FABL.indexedFourierCoeff, FABL.liftFreeFrequency, hlift] using hcoefficient.symm

private theorem isBalanced_coordinateRestriction_of_fourierCoeff_zero
    (g : BooleanFunction n) (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (hzero : ∀ S : Finset (Fin n), S ⊆ Jᶜ →
      FABL.fourierCoeff (signCubeView g).toReal S = 0) :
    IsBalanced (coordinateRestriction g J z) := by
  rw [isBalanced_coordinateRestriction_iff, FABL.IsBalanced, FABL.mean,
    FABL.expect_eq_indexedFourierCoeff_empty]
  change FABL.restrictionFourierCoeff (signCubeView g).toReal J ∅ z = 0
  rw [FABL.restrictionFourierCoeff_eq_sum]
  apply Finset.sum_eq_zero
  intro T _hT
  have hsubset : FABL.liftFixedFrequency T ⊆ Jᶜ := by
    intro i hi
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hi
    rw [← hji]
    exact Finset.mem_compl.mpr j.property
  rw [show FABL.liftFreeFrequency (∅ : Finset J) ∪
      FABL.liftFixedFrequency T = FABL.liftFixedFrequency T by
        simp [FABL.liftFreeFrequency],
    hzero (FABL.liftFixedFrequency T) hsubset, zero_mul]

/-- The order-`k` propagation criterion: every restriction fixing exactly `k`
coordinates satisfies `PC(l)`. -/
def SatisfiesPropagationCriterionOfOrder
    (l k : ℕ) (f : BooleanFunction n) : Prop :=
  ∀ (J : Finset (Fin n)) (z : FABL.FixedSignCube J),
    Fintype.card (FABL.FixedIndex J) = k →
      SatisfiesPropagationCriterion l (coordinateRestriction f J z)

private theorem isBalanced_coordinateDerivative_of_order
    {l k : ℕ} {f : BooleanFunction n}
    (hf : SatisfiesPropagationCriterionOfOrder l k f)
    (a : FABL.F₂Cube n) (ha0 : a ≠ 0)
    (haw : (FABL.f₂Support a).card ≤ l)
    (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (hcard : Fintype.card (FABL.FixedIndex J) = k)
    (hasupport : FABL.f₂Support a ⊆ J) :
    IsBalanced (coordinateRestriction (FABL.booleanDerivative f a) J z) := by
  let b : FABL.F₂Cube J.card := restrictToFreeDirection J a
  have hlift : liftRestrictionDirection J b = a :=
    liftRestrictionDirection_restrictToFreeDirection J a hasupport
  have hb0 : b ≠ 0 := by
    intro hb
    apply ha0
    rw [← hlift, hb]
    exact (liftRestrictionDirection_eq_zero_iff J 0).mpr rfl
  have hbw : (FABL.f₂Support b).card ≤ l := by
    rw [← card_f₂Support_liftRestrictionDirection J b, hlift]
    exact haw
  have hbalanced := hf J z hcard b ⟨hb0, hbw⟩
  rw [← coordinateRestriction_booleanDerivative, hlift] at hbalanced
  exact hbalanced

/-- Carlet's order monotonicity: in the source range `k ≤ n - l`, order `k`
implies every lower restriction order. -/
theorem SatisfiesPropagationCriterionOfOrder.mono_order
    {l k k' : ℕ} {f : BooleanFunction n}
    (hf : SatisfiesPropagationCriterionOfOrder l k f)
    (hknl : k ≤ n - l) (hk'k : k' ≤ k) :
    SatisfiesPropagationCriterionOfOrder l k' f := by
  intro J' z' hcard' a ha
  rw [← coordinateRestriction_booleanDerivative]
  let A : FABL.F₂Cube n := liftRestrictionDirection J' a
  have hA0 : A ≠ 0 := by
    simpa [A] using ha.1
  have hAw : (FABL.f₂Support A).card ≤ l := by
    simpa [A] using ha.2
  have hAsupport : FABL.f₂Support A ⊆ J' := by
    exact f₂Support_liftRestrictionDirection_subset J' a
  let K' : Finset (Fin n) := J'ᶜ
  have hK'card : K'.card = k' := by
    dsimp [K']
    rw [Finset.card_compl]
    simpa [FABL.FixedIndex] using hcard'
  have hK'subset : K' ⊆ (FABL.f₂Support A)ᶜ := by
    intro i hiK'
    apply Finset.mem_compl.mpr
    intro hiA
    apply (Finset.mem_compl.mp (show i ∈ J'ᶜ by simpa [K'] using hiK'))
    exact hAsupport hiA
  have hk_available : k ≤ ((FABL.f₂Support A)ᶜ).card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨K, hK'subsetK, hKsubset, hKcard⟩ :=
    Finset.exists_subsuperset_card_eq hK'subset
      (by simpa [hK'card] using hk'k) hk_available
  let J : Finset (Fin n) := Kᶜ
  have hJcard : Fintype.card (FABL.FixedIndex J) = k := by
    simp [J, FABL.FixedIndex, hKcard]
  have hAsubsetJ : FABL.f₂Support A ⊆ J := by
    intro i hiA
    apply Finset.mem_compl.mpr
    intro hiK
    exact (Finset.mem_compl.mp (hKsubset hiK)) hiA
  apply isBalanced_coordinateRestriction_of_fourierCoeff_zero
  intro S hSJ'
  apply fourierCoeff_eq_zero_of_all_coordinateRestrictions_balanced
      (FABL.booleanDerivative f A) J
  · intro z
    exact isBalanced_coordinateDerivative_of_order
      hf A hA0 hAw J z hJcard hAsubsetJ
  · have hSK' : S ⊆ K' := by
      simpa [K'] using hSJ'
    have hSK : S ⊆ K := hSK'.trans hK'subsetK
    simpa [J] using hSK

/-- Lowering the propagation parameter preserves every fixed-coordinate order. -/
theorem SatisfiesPropagationCriterionOfOrder.mono_level
    {l l' k : ℕ} {f : BooleanFunction n}
    (hf : SatisfiesPropagationCriterionOfOrder l k f) (hl'l : l' ≤ l) :
    SatisfiesPropagationCriterionOfOrder l' k f := by
  intro J z hcard
  exact (hf J z hcard).mono hl'l

/-- SAC of order `k` is `PC(1)` of order `k`. -/
def SatisfiesStrictAvalancheCriterionOfOrder
    (k : ℕ) (f : BooleanFunction n) : Prop :=
  SatisfiesPropagationCriterionOfOrder 1 k f

/-- SAC of order `k` is exactly `PC(1)` of order `k`. -/
theorem satisfiesStrictAvalancheCriterionOfOrder_iff_pc_one
    (k : ℕ) (f : BooleanFunction n) :
    SatisfiesStrictAvalancheCriterionOfOrder k f ↔
      SatisfiesPropagationCriterionOfOrder 1 k f := by
  rfl

/-- The extended propagation criterion `EPC(l)` of order `k`: each derivative in a
nonzero direction of weight at most `l` is `k`-resilient. -/
def SatisfiesExtendedPropagationCriterion
    (l k : ℕ) (f : BooleanFunction n) : Prop :=
  ∀ a : FABL.F₂Cube n, a ≠ 0 →
    (FABL.f₂Support a).card ≤ l →
      IsResilient k (FABL.booleanDerivative f a)

/-- The extended criterion is stronger than the corresponding order-`k` propagation
criterion. -/
theorem SatisfiesExtendedPropagationCriterion.toPropagationCriterionOfOrder
    {l k : ℕ} {f : BooleanFunction n}
    (hf : SatisfiesExtendedPropagationCriterion l k f) :
    SatisfiesPropagationCriterionOfOrder l k f := by
  intro J z hcard a ha
  rw [← coordinateRestriction_booleanDerivative]
  apply isBalanced_coordinateRestriction_of_isResilient k
  · apply hf (liftRestrictionDirection J a)
    · simpa using ha.1
    · simpa using ha.2
  · exact hcard

end CryptBoolean
