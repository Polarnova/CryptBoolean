/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierOperations
public import FABL.Chapter06.Pseudorandomness.CorrelationImmunity
public import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations

/-!
# Carlet Chapter 4 resiliency and correlation immunity

Coordinate-restriction definitions and their exact Walsh-zero characterizations.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The sign-cube view of a bit-valued Boolean function. -/
def signCubeView (f : BooleanFunction n) : FABL.BooleanFunction n :=
  fun x ↦ FABL.signEncode (f ((FABL.binaryCubeSignEquiv n).symm x))

/-- The real view of `signCubeView` is the canonical binary sign encoding transported
across FABL's cube equivalence. -/
theorem signCubeView_toReal (f : BooleanFunction n) :
    (signCubeView f).toReal =
      FABL.binaryFunctionOnSignCube (realSignView f) := by
  funext x
  simp [signCubeView, FABL.BooleanFunction.toReal,
    FABL.binaryFunctionOnSignCube, realSignView,
    FABL.realSignEncodedFunction, FABL.signEncodedFunction]

/-- A bit-valued Boolean function is correlation immune of order `m` when fixing at most
`m` input coordinates leaves its output distribution unchanged. -/
def IsCorrelationImmune (m : ℕ) (f : BooleanFunction n) : Prop :=
  ∀ (J : Finset (Fin n)) (z : FABL.FixedSignCube J),
    Fintype.card (FABL.FixedIndex J) ≤ m →
      FABL.mean
          (FABL.signRestriction
            (signCubeView f).toReal J z) =
        FABL.mean (signCubeView f).toReal

/-- A bit-valued Boolean function is resilient of order `m` when it is correlation immune
of order `m` and balanced. -/
def IsResilient (m : ℕ) (f : BooleanFunction n) : Prop :=
  IsCorrelationImmune m f ∧ IsBalanced f

private theorem mean_signRestriction_univ
    (g : {−1,1}^[n] → ℝ)
    (z : FABL.FixedSignCube (Finset.univ : Finset (Fin n))) :
    FABL.mean (FABL.signRestriction g Finset.univ z) = FABL.mean g := by
  have h := FABL.mean_signRestriction_sub_mean_eq_sum_nonempty
    g (Finset.univ : Finset (Fin n)) z
  have hempty
      (T : Finset (FABL.FixedIndex (Finset.univ : Finset (Fin n)))) :
      T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact i.property (Finset.mem_univ (i : Fin n))
  simp_rw [hempty] at h
  exact sub_eq_zero.mp (by simpa using h)

/-- The coordinate-restriction definition of correlation immunity is exactly FABL's
zero low-degree Fourier regularity predicate after decoding to the sign cube. -/
theorem isCorrelationImmune_iff_fabl
    (m : ℕ) (f : BooleanFunction n) :
    IsCorrelationImmune m f ↔
      FABL.IsCorrelationImmune m (signCubeView f) := by
  rw [IsCorrelationImmune, FABL.IsCorrelationImmune]
  exact FABL.isLowDegreeFourierRegular_zero_iff_forall_mean_signRestriction_eq
    (signCubeView f).toReal m |>.symm

/-- A raw Walsh coefficient vanishes exactly when the corresponding normalized FABL
vector-Fourier coefficient vanishes. -/
theorem walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    walshTransform f u = 0 ↔
      FABL.vectorFourierCoeff (realSignView f) u = 0 := by
  constructor
  · intro h
    have hreal : (walshTransform f u : ℝ) = 0 := by
      exact_mod_cast h
    rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff] at hreal
    exact (mul_eq_zero.mp hreal).resolve_left (by positivity)
  · intro h
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero, walshTransform_eq_two_pow_mul_vectorFourierCoeff, h,
      mul_zero]

/-- Carlet balancedness agrees with FABL balancedness after decoding to the sign cube. -/
theorem isBalanced_iff_fabl (f : BooleanFunction n) :
    IsBalanced f ↔
      FABL.IsBalanced (signCubeView f).toReal := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero,
    walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero,
    FABL.IsBalanced, signCubeView_toReal,
    FABL.mean_eq_fourierCoeff_empty]
  have hsupport : FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
    ext i
    simp [FABL.f₂Support]
  rw [← hsupport,
    ← FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]

/-- Carlet resiliency agrees with FABL resiliency after decoding to the sign cube. -/
theorem isResilient_iff_fabl (m : ℕ) (f : BooleanFunction n) :
    IsResilient m f ↔
      FABL.IsResilient m (signCubeView f) := by
  rw [IsResilient, FABL.IsResilient, isCorrelationImmune_iff_fabl,
    isBalanced_iff_fabl]

/-- Carlet Definition 3: when `n > 0` and `m < n`, resiliency is equivalent to
balancedness of every restriction obtained by fixing at most `m` coordinates. -/
theorem isResilient_iff_forall_coordinateRestriction_balanced
    (m : ℕ) (f : BooleanFunction n) (_hn : 0 < n) (_hm : m < n) :
    IsResilient m f ↔
      ∀ (J : Finset (Fin n)) (z : FABL.FixedSignCube J),
        Fintype.card (FABL.FixedIndex J) ≤ m →
          FABL.IsBalanced
            (FABL.signRestriction
              (signCubeView f).toReal J z) := by
  constructor
  · rintro ⟨himmune, hbalanced⟩ J z hcard
    rw [FABL.IsBalanced, himmune J z hcard]
    exact isBalanced_iff_fabl f |>.mp hbalanced
  · intro hrestrictions
    let z : FABL.FixedSignCube (Finset.univ : Finset (Fin n)) :=
      fun i ↦ False.elim (i.property (Finset.mem_univ (i : Fin n)))
    have huniv := hrestrictions (Finset.univ : Finset (Fin n)) z
      (by simp [FABL.FixedIndex])
    have hmean : FABL.mean (signCubeView f).toReal = 0 := by
      rw [← mean_signRestriction_univ
        (signCubeView f).toReal z]
      exact huniv
    refine ⟨?_, isBalanced_iff_fabl f |>.mpr hmean⟩
    intro J z hcard
    exact (hrestrictions J z hcard).trans hmean.symm

private theorem liftFixedFrequency_fixedFrequencyPart_eq_of_subset_compl
    (J S : Finset (Fin n)) (hSJ : S ⊆ Jᶜ) :
    FABL.liftFixedFrequency (FABL.fixedFrequencyPart J S) = S := by
  have hfree : FABL.freeFrequencyPart J S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiS : (i : Fin n) ∈ S := (FABL.mem_freeFrequencyPart J S i).mp hi
    have hiCompl : (i : Fin n) ∈ Jᶜ := hSJ hiS
    exact (Finset.mem_compl.mp hiCompl) i.property
  have hsplit := FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart J S
  rw [hfree] at hsplit
  simpa [FABL.liftFreeFrequency] using hsplit

private theorem fourierCoeff_eq_indexedFourierCoeff_mean_restrictions
    (g : {−1,1}^[n] → ℝ) (J S : Finset (Fin n)) (hSJ : S ⊆ Jᶜ) :
    FABL.fourierCoeff g S =
      FABL.indexedFourierCoeff
        (fun z : FABL.FixedSignCube J ↦
          FABL.mean (FABL.signRestriction g J z))
        (FABL.fixedFrequencyPart J S) := by
  let T : Finset (FABL.FixedIndex J) := FABL.fixedFrequencyPart J S
  have hlift : FABL.liftFixedFrequency T = S := by
    simpa [T] using
      liftFixedFrequency_fixedFrequencyPart_eq_of_subset_compl J S hSJ
  have hmean :
      (fun z : FABL.FixedSignCube J ↦
          FABL.mean (FABL.signRestriction g J z)) =
        FABL.restrictionFourierCoeff g J ∅ := by
    funext z
    change (𝔼 y, FABL.signRestriction g J z y) =
      FABL.indexedFourierCoeff (FABL.signRestriction g J z) ∅
    exact FABL.expect_eq_indexedFourierCoeff_empty _
  rw [hmean, FABL.indexedFourierCoeff_restrictionFourierCoeff]
  simp [T, FABL.liftFreeFrequency, hlift]

/-- Carlet Definition 3, footnote 24: for `n > 0` and `m < n`, requiring
unchanged output distribution after fixing exactly `m` coordinates is equivalent
to correlation immunity under all restrictions fixing at most `m` coordinates. -/
theorem isCorrelationImmune_iff_fixing_exactly
    (m : ℕ) (f : BooleanFunction n) (_hn : 0 < n) (hm : m < n) :
    IsCorrelationImmune m f ↔
      ∀ (J : Finset (Fin n)) (z : FABL.FixedSignCube J),
        Fintype.card (FABL.FixedIndex J) = m →
          FABL.mean (FABL.signRestriction (signCubeView f).toReal J z) =
            FABL.mean (signCubeView f).toReal := by
  constructor
  · intro h J z hcard
    exact h J z hcard.le
  · intro hexact
    apply isCorrelationImmune_iff_fabl m f |>.mpr
    rw [FABL.IsCorrelationImmune, FABL.IsLowDegreeFourierRegular]
    intro S hS hSm
    have hm_le_n : m ≤ Fintype.card (Fin n) := by
      simpa using (Nat.le_of_lt hm)
    obtain ⟨K, hSK, hKcard⟩ :=
      Finset.exists_superset_card_eq hSm hm_le_n
    let J : Finset (Fin n) := Kᶜ
    have hfixed : Fintype.card (FABL.FixedIndex J) = m := by
      simp [J, FABL.FixedIndex, hKcard]
    have hSJ : S ⊆ Jᶜ := by
      simpa [J] using hSK
    let T : Finset (FABL.FixedIndex J) := FABL.fixedFrequencyPart J S
    have hcoefficient :=
      fourierCoeff_eq_indexedFourierCoeff_mean_restrictions
        (signCubeView f).toReal J S hSJ
    change FABL.fourierCoeff (signCubeView f).toReal S =
      FABL.indexedFourierCoeff
        (fun z : FABL.FixedSignCube J ↦
          FABL.mean (FABL.signRestriction (signCubeView f).toReal J z)) T
      at hcoefficient
    have hmeanfun :
        (fun z : FABL.FixedSignCube J ↦
          FABL.mean (FABL.signRestriction (signCubeView f).toReal J z)) =
        fun _ ↦ FABL.mean (signCubeView f).toReal := by
      funext z
      exact hexact J z hfixed
    rw [hmeanfun] at hcoefficient
    have hlift : FABL.liftFixedFrequency T = S := by
      simpa [T] using
        liftFixedFrequency_fixedFrequencyPart_eq_of_subset_compl J S hSJ
    have hT : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hTempty
      have : S = ∅ := by
        rw [← hlift, hTempty]
        simp [FABL.liftFixedFrequency]
      exact hS.ne_empty this
    have hexpect :
        (𝔼 z : FABL.FixedSignCube J, FABL.indexedMonomial T z) = 0 := by
      have horthogonal :=
        FABL.expect_indexedMonomial_mul T
          (∅ : Finset (FABL.FixedIndex J))
      simpa [FABL.indexedMonomial, hT.ne_empty] using horthogonal
    have hconstant :
        FABL.indexedFourierCoeff
          (fun _ : FABL.FixedSignCube J ↦
            FABL.mean (signCubeView f).toReal) T = 0 := by
      rw [FABL.indexedFourierCoeff]
      change (𝔼 z : FABL.FixedSignCube J,
        FABL.mean (signCubeView f).toReal * FABL.indexedMonomial T z) = 0
      rw [← Finset.mul_expect, hexpect, mul_zero]
    rw [hconstant] at hcoefficient
    simp [hcoefficient]

/-- Carlet Definition 3, footnote 25: for `n > 0` and `m < n`, requiring
balancedness after fixing exactly `m` coordinates is equivalent to resiliency
under all restrictions fixing at most `m` coordinates. -/
theorem isResilient_iff_fixing_exactly
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m < n) :
    IsResilient m f ↔
      ∀ (J : Finset (Fin n)) (z : FABL.FixedSignCube J),
        Fintype.card (FABL.FixedIndex J) = m →
          FABL.IsBalanced
            (FABL.signRestriction (signCubeView f).toReal J z) := by
  constructor
  · intro hresilient J z hcard
    exact (isResilient_iff_forall_coordinateRestriction_balanced
      m f hn hm |>.mp hresilient) J z hcard.le
  · intro hexact
    have hm_le_n : m ≤ Fintype.card (Fin n) := by
      simpa using (Nat.le_of_lt hm)
    obtain ⟨K, _hK, hKcard⟩ :=
      Finset.exists_superset_card_eq
        (s := (∅ : Finset (Fin n))) (by simp) hm_le_n
    let J : Finset (Fin n) := Kᶜ
    have hfixed : Fintype.card (FABL.FixedIndex J) = m := by
      simp [J, FABL.FixedIndex, hKcard]
    have hcoefficient :=
      fourierCoeff_eq_indexedFourierCoeff_mean_restrictions
        (signCubeView f).toReal J ∅ (by simp)
    have hmeanfun :
        (fun z : FABL.FixedSignCube J ↦
          FABL.mean (FABL.signRestriction (signCubeView f).toReal J z)) =
        fun _ ↦ 0 := by
      funext z
      exact hexact J z hfixed
    rw [hmeanfun] at hcoefficient
    have hmean : FABL.mean (signCubeView f).toReal = 0 := by
      rw [FABL.mean_eq_fourierCoeff_empty, hcoefficient]
      simp [FABL.indexedFourierCoeff]
    refine ⟨isCorrelationImmune_iff_fixing_exactly m f hn hm |>.mpr ?_,
      isBalanced_iff_fabl f |>.mpr hmean⟩
    intro J z hcard
    exact (hexact J z hcard).trans hmean.symm

private theorem f₂Support_nonempty_iff_ne_zero (u : FABL.F₂Cube n) :
    (FABL.f₂Support u).Nonempty ↔ u ≠ 0 := by
  constructor
  · intro h hu
    subst u
    have hzero : FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ := by
      ext i
      simp [FABL.f₂Support]
    rw [hzero] at h
    exact h.ne_empty rfl
  · intro hu
    rw [Finset.nonempty_iff_ne_empty]
    intro hsupport
    apply hu
    apply (FABL.f₂CubeEquivFinset n).injective
    change FABL.f₂Support u = FABL.f₂Support (0 : FABL.F₂Cube n)
    rw [hsupport]
    ext i
    simp [FABL.f₂Support]

/-- Carlet Theorem 3, correlation-immunity form: for `n > 0` and `m < n`,
correlation immunity of order `m` is equivalent to vanishing of every nonzero
raw Walsh coefficient whose frequency has Hamming weight at most `m`. -/
theorem theorem_3_correlationImmune_iff_walshTransform_eq_zero
    (m : ℕ) (f : BooleanFunction n) (_hn : 0 < n) (_hm : m < n) :
    IsCorrelationImmune m f ↔
      ∀ u : FABL.F₂Cube n, u ≠ 0 →
        (FABL.f₂Support u).card ≤ m → walshTransform f u = 0 := by
  constructor
  · intro himmune u hu hweight
    have hfab :
        FABL.IsCorrelationImmune m (signCubeView f) :=
      isCorrelationImmune_iff_fabl m f |>.mp himmune
    rw [FABL.IsCorrelationImmune, FABL.IsLowDegreeFourierRegular] at hfab
    have hbound := hfab (FABL.f₂Support u)
      (f₂Support_nonempty_iff_ne_zero u |>.mpr hu) hweight
    have hcoeff :
        FABL.fourierCoeff (signCubeView f).toReal
            (FABL.f₂Support u) = 0 :=
      abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
    rw [signCubeView_toReal] at hcoeff
    apply walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero f u |>.mpr
    exact (FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube
      (realSignView f) u).trans hcoeff
  · intro hwalsh
    apply isCorrelationImmune_iff_fabl m f |>.mpr
    rw [FABL.IsCorrelationImmune, FABL.IsLowDegreeFourierRegular]
    intro S hS hcard
    let u : FABL.F₂Cube n := FABL.f₂CubeOfFinset S
    have hsupport : FABL.f₂Support u = S := by
      exact (FABL.f₂CubeEquivFinset n).right_inv S
    have hu : u ≠ 0 := by
      apply f₂Support_nonempty_iff_ne_zero u |>.mp
      simpa [hsupport] using hS
    have hvector : FABL.vectorFourierCoeff (realSignView f) u = 0 :=
      walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero f u |>.mp
        (hwalsh u hu (by simpa [hsupport] using hcard))
    have hcoeff :
        FABL.fourierCoeff (signCubeView f).toReal S = 0 := by
      rw [signCubeView_toReal, ← hsupport]
      exact (FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube
        (realSignView f) u).symm.trans hvector
    simp [hcoeff]

/-- Carlet Theorem 3, resilient form: for `n > 0` and `m < n`, resiliency of
order `m` is equivalent to vanishing of every raw Walsh coefficient whose
frequency has Hamming weight at most `m`, including the zero frequency. -/
theorem theorem_3_resilient_iff_walshTransform_eq_zero
    (m : ℕ) (f : BooleanFunction n) (hn : 0 < n) (hm : m < n) :
    IsResilient m f ↔
      ∀ u : FABL.F₂Cube n, (FABL.f₂Support u).card ≤ m →
        walshTransform f u = 0 := by
  constructor
  · rintro ⟨himmune, hbalanced⟩ u hweight
    by_cases hu : u = 0
    · subst u
      exact isBalanced_iff_walshTransform_zero_eq_zero f |>.mp hbalanced
    · exact theorem_3_correlationImmune_iff_walshTransform_eq_zero
        m f hn hm |>.mp himmune u hu hweight
  · intro hwalsh
    refine ⟨theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hm |>.mpr ?_, ?_⟩
    · intro u _hu hweight
      exact hwalsh u hweight
    · apply isBalanced_iff_walshTransform_zero_eq_zero f |>.mpr
      apply hwalsh 0
      simp [FABL.f₂Support]

/-- Translating the input multiplies a raw Walsh coefficient by the corresponding
Walsh character value. -/
theorem walshTransform_domainTranslate_cast
    (f : BooleanFunction n) (b u : FABL.F₂Cube n) :
    (walshTransform (FABL.domainTranslate f b) u : ℝ) =
      FABL.vectorWalshCharacter u b * (walshTransform f u : ℝ) := by
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  change (2 ^ n : ℝ) *
      FABL.vectorFourierCoeff (fun x ↦ realSignView f (x + b)) u = _
  rw [FABL.vectorFourierCoeff_translate_add]
  ring

/-- Carlet's translation invariance of resiliency: an additive input translation
preserves every resilient order in the source range `n > 0`, `m < n`. -/
theorem isResilient_domainTranslate
    (m : ℕ) (f : BooleanFunction n) (b : FABL.F₂Cube n)
    (hn : 0 < n) (hm : m < n) (hf : IsResilient m f) :
    IsResilient m (FABL.domainTranslate f b) := by
  rw [theorem_3_resilient_iff_walshTransform_eq_zero m f hn hm] at hf
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    m (FABL.domainTranslate f b) hn hm]
  intro u hweight
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, walshTransform_domainTranslate_cast]
  have hzero : (walshTransform f u : ℝ) = 0 := by
    exact_mod_cast hf u hweight
  rw [hzero, mul_zero]

end CryptBoolean
