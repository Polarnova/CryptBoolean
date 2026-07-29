/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import CryptBoolean.Carlet.Chapter04.AutocorrelationBounds
public import CryptBoolean.Carlet.Chapter04.LinearStructureSpectrum
public import CryptBoolean.Carlet.Chapter04.PropagationCriteria
public import CryptBoolean.Carlet.Chapter06.Bentness
public import CryptBoolean.Carlet.Chapter06.GeometricCharacterization
public import CryptBoolean.Carlet.Chapter08.AffineFlatWalshCharacterization

import FABL.Chapter05.DegreeOneWeight

/-!
# Propagation criteria and nonlinearity

The Walsh-square and nonlinearity bounds obtained from a propagating
subspace, together with the equality restriction for coordinate propagation.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance propagationNonlinearitySubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

private theorem walshSquareCosetSum_eq_of_balanced_derivatives_on_subspace
    (f : BooleanFunction n) (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (l : ℕ) (hfinrank : Module.finrank FABL.𝔽₂ F = l)
    (hbalanced : ∀ a : F, a ≠ 0 →
      IsBalanced (FABL.booleanDerivative f a.1))
    (u : FABL.F₂Cube n) :
    (∑ e : FABL.perpendicularSubspace F,
        (walshTransform f (u + e.1) : ℝ) ^ 2) =
      (2 : ℝ) ^ (2 * n - l) := by
  let E := FABL.perpendicularSubspace F
  have hperp : FABL.perpendicularSubspace E = F := by
    exact FABL.perpendicularSubspace_perpendicularSubspace F
  have hcard : Nat.card E = 2 ^ (n - l) := by
    dsimp [E]
    rw [FABL.card_submodule_eq_two_pow_finrank,
      FABL.finrank_perpendicularSubspace, hfinrank]
  have hsum :
      (∑ a : F,
          FABL.vectorWalshCharacter u a.1 * autocorrelation f a.1) =
        (2 : ℝ) ^ n := by
    rw [Finset.sum_eq_single (0 : F)]
    · simp [autocorrelation_zero]
    · intro a _ha ha
      have habalanced := hbalanced a ha
      rw [(isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
        f a.1).mp habalanced, mul_zero]
    · intro hzero
      exact (hzero (Finset.mem_univ _)).elim
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) E u 0
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  rw [hperp, hcard] at hpoisson
  have hrelation :
      (∑ e : E, (walshTransform f (u + e.1) : ℝ) ^ 2) =
        (2 : ℝ) ^ (n - l) *
          ∑ a : F,
            FABL.vectorWalshCharacter u a.1 * autocorrelation f a.1 := by
    simpa [E] using hpoisson
  rw [hsum, ← pow_add] at hrelation
  have hln : l ≤ n := by
    rw [← hfinrank]
    simpa using F.finrank_le
  simpa [E, show n - l + n = 2 * n - l by omega] using hrelation

/-- A propagating `l`-dimensional subspace bounds every squared raw Walsh
coefficient by `2^(2n-l)`. -/
theorem walshTransform_sq_le_of_balanced_derivatives_on_subspace
    (f : BooleanFunction n) (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (l : ℕ) (hfinrank : Module.finrank FABL.𝔽₂ F = l)
    (hbalanced : ∀ a : F, a ≠ 0 →
      IsBalanced (FABL.booleanDerivative f a.1))
    (u : FABL.F₂Cube n) :
    (walshTransform f u : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * n - l) := by
  have hsum :=
    walshSquareCosetSum_eq_of_balanced_derivatives_on_subspace
      f F l hfinrank hbalanced u
  have hterm :
      (walshTransform f (u + (0 : FABL.perpendicularSubspace F).1) : ℝ) ^ 2 ≤
        ∑ e : FABL.perpendicularSubspace F,
          (walshTransform f (u + e.1) : ℝ) ^ 2 := by
    exact Finset.single_le_sum
      (fun e _he ↦ sq_nonneg (walshTransform f (u + e.1) : ℝ))
      (Finset.mem_univ (0 : FABL.perpendicularSubspace F))
  simpa [hsum] using hterm

private theorem two_rpow_sub_half_sq
    (l n : ℕ) (hln : l ≤ n) :
    ((2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2)) ^ 2 =
      (2 : ℝ) ^ (2 * n - l) := by
  rw [pow_two, ← Real.rpow_add (by positivity), ← Real.rpow_natCast]
  push_cast [Nat.cast_sub (by omega : l ≤ 2 * n)]
  congr 1
  ring

private theorem abs_walshTransform_le_of_sq_le
    (f : BooleanFunction n) (l : ℕ) (hln : l ≤ n)
    (hsq : ∀ u, (walshTransform f u : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (2 * n - l))
    (u : FABL.F₂Cube n) :
    |(walshTransform f u : ℝ)| ≤
      (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, two_rpow_sub_half_sq l n hln]
  exact hsq u

private theorem maxWalshMagnitude_cast_le_of_forall_abs_le
    (f : BooleanFunction n) (C : ℝ)
    (hbound : ∀ u, |(walshTransform f u : ℝ)| ≤ C) :
    (maxWalshMagnitude f : ℝ) ≤ C := by
  classical
  unfold maxWalshMagnitude
  obtain ⟨u, _hu, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    Finset.univ_nonempty (fun a ↦ (walshTransform f a).natAbs)
  rw [hmax, Nat.cast_natAbs, Int.cast_abs]
  exact hbound u

private theorem propagationNonlinearityBound_expression
    (n l : ℕ) :
    (2 : ℝ) ^ n / 2 -
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) / 2 =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2 - 1) := by
  have hfirst :
      (2 : ℝ) ^ ((n : ℝ) - 1) = (2 : ℝ) ^ n / 2 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one, Real.rpow_natCast]
  have hsecond :
      (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2 - 1) =
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) / 2 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [hfirst, hsecond]

/-- A propagating `l`-dimensional subspace gives Carlet's real-exponent
nonlinearity lower bound. -/
theorem nonlinearity_lowerBound_of_balanced_derivatives_on_subspace
    (f : BooleanFunction n) (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (l : ℕ) (hfinrank : Module.finrank FABL.𝔽₂ F = l)
    (hbalanced : ∀ a : F, a ≠ 0 →
      IsBalanced (FABL.booleanDerivative f a.1)) :
    (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2 - 1) ≤
      (nonlinearity f : ℝ) := by
  have hln : l ≤ n := by
    rw [← hfinrank]
    simpa using F.finrank_le
  have hsquare (u : FABL.F₂Cube n) :=
    walshTransform_sq_le_of_balanced_derivatives_on_subspace
      f F l hfinrank hbalanced u
  have hmax :
      (maxWalshMagnitude f : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) :=
    maxWalshMagnitude_cast_le_of_forall_abs_le f _
      (abs_walshTransform_le_of_sq_le f l hln hsquare)
  rw [nonlinearity_cast_eq_relation_35,
    ← propagationNonlinearityBound_expression n l]
  linarith

/-- `PC(l)` bounds every squared raw Walsh coefficient by `2^(2n-l)`. -/
theorem walshTransform_sq_le_of_satisfiesPropagationCriterion
    (f : BooleanFunction n) (l : ℕ) (hln : l ≤ n)
    (hpc : SatisfiesPropagationCriterion l f)
    (u : FABL.F₂Cube n) :
    (walshTransform f u : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * n - l) := by
  classical
  have hcardBound : n - l ≤ #(Finset.univ : Finset (Fin n)) := by
    simp
  obtain ⟨I, _hI, hIcard⟩ := Finset.exists_subset_card_eq hcardBound
  let F : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.F₂DecisionTree.coordinateZeroSubspace I
  have hfinrank : Module.finrank FABL.𝔽₂ F = l := by
    dsimp [F]
    rw [finrank_coordinateZeroSubspace, hIcard]
    omega
  apply walshTransform_sq_le_of_balanced_derivatives_on_subspace
    f F l hfinrank
  intro a ha
  apply hpc a.1
  refine ⟨?_, ?_⟩
  · intro hazero
    exact ha (Subtype.ext hazero)
  · have hasupport : FABL.f₂Support a.1 ⊆ Iᶜ := by
      intro i hi
      rw [Finset.mem_compl]
      intro hiI
      have hai :=
        (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff I a.1).mp
          a.2 i hiI
      exact (FABL.mem_f₂Support a.1 i).mp hi hai
    have hcard := Finset.card_le_card hasupport
    rw [Finset.card_compl, Fintype.card_fin, hIcard] at hcard
    omega

/-- Carlet's nonlinearity lower bound for a function satisfying `PC(l)`. -/
theorem nonlinearity_lowerBound_of_satisfiesPropagationCriterion
    (f : BooleanFunction n) (l : ℕ) (hln : l ≤ n)
    (hpc : SatisfiesPropagationCriterion l f) :
    (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2 - 1) ≤
      (nonlinearity f : ℝ) := by
  have hsquare (u : FABL.F₂Cube n) :=
    walshTransform_sq_le_of_satisfiesPropagationCriterion
      f l hln hpc u
  have hmax :
      (maxWalshMagnitude f : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) :=
    maxWalshMagnitude_cast_le_of_forall_abs_le f _
      (abs_walshTransform_le_of_sq_le f l hln hsquare)
  rw [nonlinearity_cast_eq_relation_35,
    ← propagationNonlinearityBound_expression n l]
  linarith

private theorem coordinateZeroSubspace_walshSquareSum_eq_of_pc
    (f : BooleanFunction n) (l : ℕ)
    (hpc : SatisfiesPropagationCriterion l f)
    (I : Finset (Fin n)) (hIcard : I.card = l)
    (u : FABL.F₂Cube n) :
    (∑ e : FABL.F₂DecisionTree.coordinateZeroSubspace I,
        (walshTransform f (u + e.1) : ℝ) ^ 2) =
      (2 : ℝ) ^ (2 * n - l) := by
  let E := FABL.F₂DecisionTree.coordinateZeroSubspace I
  have hcard : Nat.card E = 2 ^ (n - l) := by
    dsimp [E]
    rw [FABL.card_submodule_eq_two_pow_finrank,
      finrank_coordinateZeroSubspace, hIcard]
  have hperpSum :
      (∑ a : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter u a.1 * autocorrelation f a.1) =
        (2 : ℝ) ^ n := by
    rw [Finset.sum_eq_single (0 : FABL.perpendicularSubspace E)]
    · simp [autocorrelation_zero]
    · intro a _ha ha
      have hane : a.1 ≠ 0 := by
        intro hzero
        exact ha (Subtype.ext hzero)
      have hasupport : FABL.f₂Support a.1 ⊆ I := by
        exact
          FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
            I a.1 a.2
      have haweight : (FABL.f₂Support a.1).card ≤ l := by
        exact (Finset.card_le_card hasupport).trans_eq hIcard
      have hbalanced : IsBalanced (FABL.booleanDerivative f a.1) :=
        hpc a.1 ⟨hane, haweight⟩
      rw [(isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
        f a.1).mp hbalanced, mul_zero]
    · intro hzero
      exact (hzero (Finset.mem_univ _)).elim
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) E u 0
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  have hrelation :
      (∑ e : E, (walshTransform f (u + e.1) : ℝ) ^ 2) =
        (2 : ℝ) ^ (n - l) *
          ∑ a : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter u a.1 * autocorrelation f a.1 := by
    rw [hcard] at hpoisson
    simpa [E] using hpoisson
  rw [hperpSum, ← pow_add] at hrelation
  have hln : l ≤ n := by
    have hcardLe := I.card_le_univ
    rw [hIcard] at hcardLe
    simpa using hcardLe
  simpa [E, show n - l + n = 2 * n - l by omega] using hrelation

private theorem walshTransform_eq_zero_of_coset_sum_eq_peak
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (u : FABL.F₂Cube n)
    (hsum : (∑ e : E, (walshTransform f (u + e.1) : ℝ) ^ 2) =
      (walshTransform f u : ℝ) ^ 2)
    (e : E) (he : e ≠ 0) :
    walshTransform f (u + e.1) = 0 := by
  classical
  have hdecomp := Finset.sum_erase_add
    (s := (Finset.univ : Finset E))
    (f := fun d ↦ (walshTransform f (u + d.1) : ℝ) ^ 2)
    (Finset.mem_univ (0 : E))
  have hrest :
      ∑ d ∈ (Finset.univ : Finset E).erase 0,
        (walshTransform f (u + d.1) : ℝ) ^ 2 = 0 := by
    have htermZero :
        (walshTransform f (u + (0 : E).1) : ℝ) ^ 2 =
          (walshTransform f u : ℝ) ^ 2 := by simp
    rw [htermZero] at hdecomp
    linarith
  have hsquare : (walshTransform f (u + e.1) : ℝ) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _hd ↦ sq_nonneg (walshTransform f (u + d.1) : ℝ))).mp
        hrest e (by simp [he])
  exact_mod_cast (sq_eq_zero_iff.mp hsquare)

private theorem f₂Support_f₂CubeOfFinset
    (I : Finset (Fin n)) :
    FABL.f₂Support (FABL.f₂CubeOfFinset I) = I :=
  (FABL.f₂CubeEquivFinset n).right_inv I

private theorem f₂CubeOfFinset_ne_zero_of_nonempty
    {I : Finset (Fin n)} (hI : I.Nonempty) :
    FABL.f₂CubeOfFinset I ≠ 0 := by
  intro hzero
  have hsupport := congrArg FABL.f₂Support hzero
  rw [f₂Support_f₂CubeOfFinset, show FABL.f₂Support (0 : FABL.F₂Cube n) = ∅ by
    ext i
    simp [FABL.mem_f₂Support]] at hsupport
  exact hI.ne_empty hsupport

private theorem isLinearStructure_of_autocorrelation_sq_eq
    (f : BooleanFunction n) (a : FABL.F₂Cube n)
    (hsquare : autocorrelation f a ^ 2 = (2 : ℝ) ^ (2 * n)) :
    IsLinearStructure f a := by
  have hpow : ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ (2 * n) := by
    rw [two_mul, pow_add, pow_two]
  have hor :
      autocorrelation f a = (2 : ℝ) ^ n ∨
        autocorrelation f a = -((2 : ℝ) ^ n) := by
    rw [← hpow] at hsquare
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsquare
  rcases hor with hpositive | hnegative
  · have hweight : hammingWeight (FABL.booleanDerivative f a) = 0 := by
      rw [autocorrelation_eq_two_pow_sub_two_derivative_weight] at hpositive
      exact_mod_cast (by linarith :
        (hammingWeight (FABL.booleanDerivative f a) : ℝ) = 0)
    refine ⟨0, fun x ↦ congrFun (hammingNorm_eq_zero.mp hweight) x⟩
  · have hderivative :=
      (autocorrelation_eq_neg_two_pow_iff_derivative_eq_one f a).mp hnegative
    refine ⟨1, fun x ↦ congrFun hderivative x⟩

private theorem peak_forces_insert_linearStructure
    (f : BooleanFunction n) (l : ℕ)
    (hpc : SatisfiesPropagationCriterion l f)
    (I : Finset (Fin n)) (hIcard : I.card = l)
    (t : Fin n) (ht : t ∉ I)
    (hroom : l + 1 ≤ n)
    (u : FABL.F₂Cube n)
    (hpeak : (walshTransform f u : ℝ) ^ 2 =
      (2 : ℝ) ^ (2 * n - l)) :
    IsLinearStructure f (FABL.f₂CubeOfFinset (insert t I)) := by
  classical
  let E := FABL.F₂DecisionTree.coordinateZeroSubspace I
  let J := insert t I
  let E' := FABL.F₂DecisionTree.coordinateZeroSubspace J
  have hJcard : J.card = l + 1 := by
    simp [J, ht, hIcard]
  have hbaseSum :
      (∑ e : E, (walshTransform f (u + e.1) : ℝ) ^ 2) =
        (walshTransform f u : ℝ) ^ 2 := by
    rw [hpeak]
    simpa [E] using
      coordinateZeroSubspace_walshSquareSum_eq_of_pc
        f l hpc I hIcard u
  have hsmallSum :
      (∑ e : E', (walshTransform f (u + e.1) : ℝ) ^ 2) =
        (walshTransform f u : ℝ) ^ 2 := by
    have hsumAtZero :
        (∑ e : E', (walshTransform f (u + e.1) : ℝ) ^ 2) =
          (walshTransform f (u + (0 : E').1) : ℝ) ^ 2 := by
      apply Finset.sum_eq_single (0 : E')
      · intro e _he hezero
        let eE : E := ⟨e.1, by
          apply (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff I e.1).mpr
          intro i hi
          exact
            (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff J e.1).mp
              e.2 i (by simp [J, hi])⟩
        have heEzero : eE ≠ 0 := by
          intro hzero
          apply hezero
          apply Subtype.ext
          change e.1 = 0
          exact congrArg (fun z : E ↦ z.1) hzero
        have hwalshZero := walshTransform_eq_zero_of_coset_sum_eq_peak
          f E u hbaseSum eE heEzero
        rw [show eE.1 = e.1 from rfl] at hwalshZero
        rw [hwalshZero]
        norm_num
      · intro hzero
        exact (hzero (Finset.mem_univ _)).elim
    simpa using hsumAtZero
  let a := FABL.f₂CubeOfFinset J
  have haSupport : FABL.f₂Support a = J := by
    exact f₂Support_f₂CubeOfFinset J
  have haMem : a ∈ FABL.perpendicularSubspace E' := by
    exact
      (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
        J a).2 (by rw [haSupport])
  let a' : FABL.perpendicularSubspace E' := ⟨a, haMem⟩
  have haNe : a' ≠ 0 := by
    intro hzero
    have hvalue : a = 0 := congrArg Subtype.val hzero
    exact f₂CubeOfFinset_ne_zero_of_nonempty
      (by simp [J]) hvalue
  have hperpSum :
      (∑ x : FABL.perpendicularSubspace E',
          FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1) =
        (2 : ℝ) ^ n +
          FABL.vectorWalshCharacter u a * autocorrelation f a := by
    have hrest :
        ∑ x ∈ (Finset.univ.erase (0 : FABL.perpendicularSubspace E')).erase a',
          FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1 = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxData := Finset.mem_erase.mp hx
      have hxa : x ≠ a' := hxData.1
      have hxzero : x ≠ 0 := (Finset.mem_erase.mp hxData.2).1
      have hxsupport : FABL.f₂Support x.1 ⊆ J := by
        exact
          FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
            J x.1 x.2
      have hproper : FABL.f₂Support x.1 ⊂ J := by
        refine (Finset.ssubset_iff_subset_ne).2 ⟨hxsupport, ?_⟩
        intro heq
        apply hxa
        apply Subtype.ext
        apply (FABL.f₂CubeEquivFinset n).injective
        change FABL.f₂Support x.1 = FABL.f₂Support a
        rw [haSupport]
        exact heq
      have hxweight : (FABL.f₂Support x.1).card ≤ l := by
        have hlt := Finset.card_lt_card hproper
        rw [hJcard] at hlt
        omega
      have hbalanced := hpc x.1 ⟨by
        intro hzero
        exact hxzero (Subtype.ext hzero), hxweight⟩
      rw [(isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
        f x.1).mp hbalanced, mul_zero]
    have hsplitZero := Finset.sum_erase_add
      (s := (Finset.univ : Finset (FABL.perpendicularSubspace E')))
      (f := fun x ↦
        FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1)
      (Finset.mem_univ (0 : FABL.perpendicularSubspace E'))
    have haMemErase :
        a' ∈ (Finset.univ : Finset (FABL.perpendicularSubspace E')).erase 0 := by
      simp [haNe]
    have hsplitA := Finset.sum_erase_add
      (s := (Finset.univ : Finset (FABL.perpendicularSubspace E')).erase 0)
      (f := fun x ↦
        FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1)
      haMemErase
    calc
      (∑ x : FABL.perpendicularSubspace E',
          FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1) =
          (∑ x ∈ (Finset.univ.erase
              (0 : FABL.perpendicularSubspace E')),
            FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1) +
            FABL.vectorWalshCharacter u (0 : FABL.perpendicularSubspace E').1 *
              autocorrelation f (0 : FABL.perpendicularSubspace E').1 :=
        hsplitZero.symm
      _ = ((∑ x ∈ (Finset.univ.erase
              (0 : FABL.perpendicularSubspace E')).erase a',
            FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1) +
            FABL.vectorWalshCharacter u a'.1 * autocorrelation f a'.1) +
            FABL.vectorWalshCharacter u (0 : FABL.perpendicularSubspace E').1 *
              autocorrelation f (0 : FABL.perpendicularSubspace E').1 := by
        rw [hsplitA]
      _ = _ := by rw [hrest]; simp [a', a, autocorrelation_zero]; ring
  have hcard : Nat.card E' = 2 ^ (n - l - 1) := by
    dsimp [E']
    rw [FABL.card_submodule_eq_two_pow_finrank,
      finrank_coordinateZeroSubspace, hJcard]
    congr 1
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) E' u 0
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  rw [hcard] at hpoisson
  have hpoissonRelation :
      (∑ e : E', (walshTransform f (u + e.1) : ℝ) ^ 2) =
        (2 : ℝ) ^ (n - l - 1) *
          ∑ x : FABL.perpendicularSubspace E',
            FABL.vectorWalshCharacter u x.1 * autocorrelation f x.1 := by
    simpa [E'] using hpoisson
  rw [hperpSum] at hpoissonRelation
  have hrelation :
      (2 : ℝ) ^ (2 * n - l) =
        (2 : ℝ) ^ (n - l - 1) *
          ((2 : ℝ) ^ n +
            FABL.vectorWalshCharacter u a * autocorrelation f a) := by
    rw [← hpeak, ← hsmallSum]
    exact hpoissonRelation
  have hexponent : 2 * n - l = (n - l - 1) + (n + 1) := by omega
  have hbracket :
      (2 : ℝ) ^ n +
          FABL.vectorWalshCharacter u a * autocorrelation f a =
        (2 : ℝ) ^ (n + 1) := by
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (n - l - 1) ≠ 0)
    calc
      (2 : ℝ) ^ (n - l - 1) *
          ((2 : ℝ) ^ n +
            FABL.vectorWalshCharacter u a * autocorrelation f a) =
          (2 : ℝ) ^ (2 * n - l) := hrelation.symm
      _ = (2 : ℝ) ^ (n - l - 1) * (2 : ℝ) ^ (n + 1) := by
        rw [hexponent, pow_add]
  have hproduct :
      FABL.vectorWalshCharacter u a * autocorrelation f a =
        (2 : ℝ) ^ n := by
    rw [pow_succ] at hbracket
    nlinarith
  have hcharacter : (FABL.vectorWalshCharacter u a) ^ 2 = (1 : ℝ) := by
    rcases FABL.vectorWalshCharacter_eq_neg_one_or_one u a with h | h <;>
      rw [h] <;> norm_num
  have haSquare : autocorrelation f a ^ 2 = (2 : ℝ) ^ (2 * n) := by
    have hsquare := congrArg (fun z : ℝ ↦ z ^ 2) hproduct
    rw [mul_pow, hcharacter, one_mul] at hsquare
    calc
      autocorrelation f a ^ 2 = ((2 : ℝ) ^ n) ^ 2 := hsquare
      _ = (2 : ℝ) ^ (2 * n) := by rw [two_mul, pow_add, pow_two]
  exact isLinearStructure_of_autocorrelation_sq_eq f a haSquare

private theorem even_of_walshTransform_sq_eq_two_pow
    (f : BooleanFunction n) (u : FABL.F₂Cube n) (m : ℕ)
    (hsquare : (walshTransform f u : ℝ) ^ 2 = (2 : ℝ) ^ m) :
    Even m := by
  have hsquareInt : walshTransform f u ^ 2 = (2 ^ m : ℤ) := by
    exact_mod_cast hsquare
  have hsquareNat : (walshTransform f u).natAbs ^ 2 = 2 ^ m := by
    simpa [Int.natAbs_pow] using congrArg Int.natAbs hsquareInt
  have hfactor := congrArg (fun k : ℕ ↦ k.factorization 2) hsquareNat
  rw [Nat.factorization_pow, Nat.factorization_pow_self (by norm_num)] at hfactor
  change 2 * (walshTransform f u).natAbs.factorization 2 = m at hfactor
  exact ⟨(walshTransform f u).natAbs.factorization 2, by omega⟩

private theorem f₂CubeOfFinset_insert_add_insert
    (I : Finset (Fin n)) (a b : Fin n)
    (haI : a ∉ I) (hbI : b ∉ I) (hab : a ≠ b) :
    FABL.f₂CubeOfFinset (insert a I) +
        FABL.f₂CubeOfFinset (insert b I) =
      FABL.f₂CubeOfFinset {a, b} := by
  funext i
  by_cases hiI : i ∈ I
  · have hia : i ≠ a := by
      intro hia
      subst i
      exact haI hiI
    have hib : i ≠ b := by
      intro hib
      subst i
      exact hbI hiI
    simp [FABL.f₂CubeOfFinset_apply, hiI, hia, hib,
      ZModModule.add_self]
  · by_cases hia : i = a
    · subst i
      simp [FABL.f₂CubeOfFinset_apply, haI, hab]
    · by_cases hib : i = b
      · subst i
        simp [FABL.f₂CubeOfFinset_apply, hbI, Ne.symm hab]
      · simp [FABL.f₂CubeOfFinset_apply, hiI, hia, hib]

private theorem exists_abs_walshTransform_eq_maxWalshMagnitude
    (f : BooleanFunction n) :
    ∃ u, |(walshTransform f u : ℝ)| = (maxWalshMagnitude f : ℝ) := by
  classical
  unfold maxWalshMagnitude
  obtain ⟨u, _hu, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    Finset.univ_nonempty (fun a ↦ (walshTransform f a).natAbs)
  refine ⟨u, ?_⟩
  rw [hmax, Nat.cast_natAbs, Int.cast_abs]

/-- Equality in the propagation nonlinearity bound is possible only at the
odd-dimensional `PC(n-1)` endpoint or the even-dimensional bent endpoint. -/
theorem propagationCriterion_nonlinearity_equality_parameters
    (f : BooleanFunction n) (l : ℕ) (hl : 1 ≤ l) (hln : l ≤ n)
    (hpc : SatisfiesPropagationCriterion l f)
    (hequality : (nonlinearity f : ℝ) =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2 - 1)) :
    (Odd n ∧ l = n - 1) ∨ (Even n ∧ l = n) := by
  have hmax :
      (maxWalshMagnitude f : ℝ) =
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) := by
    rw [nonlinearity_cast_eq_relation_35,
      ← propagationNonlinearityBound_expression n l] at hequality
    linarith
  obtain ⟨u, hu⟩ := exists_abs_walshTransform_eq_maxWalshMagnitude f
  have huabs :
      |(walshTransform f u : ℝ)| =
        (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) := by
    rw [hu, hmax]
  have huSquare :
      (walshTransform f u : ℝ) ^ 2 =
        (2 : ℝ) ^ (2 * n - l) := by
    rw [← sq_abs, huabs, two_rpow_sub_half_sq l n hln]
  by_cases hbent : IsBent f
  · have heven := even_of_isBent f hbent
    have hbentMax := maxWalshMagnitude_eq_two_pow_half_of_isBent f hbent
    have hrpow :
        (2 : ℝ) ^ ((n : ℝ) / 2) =
          (2 : ℝ) ^ ((n : ℝ) - (l : ℝ) / 2) := by
      calc
        (2 : ℝ) ^ ((n : ℝ) / 2) = (2 : ℝ) ^ (n / 2) := by
          rw [← sqrt_two_pow_eq_rpow, sqrt_two_pow_eq_pow_half heven]
        _ = (maxWalshMagnitude f : ℝ) := by
          exact_mod_cast hbentMax.symm
        _ = _ := hmax
    have hexponent :
        (n : ℝ) / 2 = (n : ℝ) - (l : ℝ) / 2 :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
        hrpow
    right
    refine ⟨heven, ?_⟩
    exact_mod_cast (by linarith : (l : ℝ) = n)
  · have hevenExponent :=
      even_of_walshTransform_sq_eq_two_pow f u (2 * n - l) huSquare
    rcases hevenExponent with ⟨k, hk⟩
    have hkLe : k ≤ n := by omega
    have hlEven : Even l := ⟨n - k, by omega⟩
    have hlTwo : 2 ≤ l := by
      rcases hlEven with ⟨r, hr⟩
      omega
    have hlLt : l < n := by
      by_contra hnot
      have hnl : n ≤ l := Nat.le_of_not_gt hnot
      have hleq : l = n := Nat.le_antisymm hln hnl
      apply hbent
      apply (isBent_iff_satisfiesPropagationCriterion_dimension f).2
      simpa [hleq] using hpc
    have hendpoint : n - 1 ≤ l := by
      by_contra hnot
      have hroom : l + 2 ≤ n := by omega
      let a : Fin n := ⟨l, by omega⟩
      let b : Fin n := ⟨l + 1, by omega⟩
      let I : Finset (Fin n) := Finset.Iio a
      have haI : a ∉ I := by simp [I]
      have hbI : b ∉ I := by simp [I, a, b]
      have hab : a ≠ b := by
        intro hab
        have hval := congrArg Fin.val hab
        simp [a, b] at hval
      have hIcard : I.card = l := by simp [I, a]
      have hlinearA := peak_forces_insert_linearStructure
        f l hpc I hIcard a haI (by omega) u huSquare
      have hlinearB := peak_forces_insert_linearStructure
        f l hpc I hIcard b hbI (by omega) u huSquare
      have hsum :
          FABL.f₂CubeOfFinset (insert a I) +
              FABL.f₂CubeOfFinset (insert b I) =
            FABL.f₂CubeOfFinset {a, b} :=
        f₂CubeOfFinset_insert_add_insert I a b haI hbI hab
      have hlinearSum :
          IsLinearStructure f (FABL.f₂CubeOfFinset {a, b}) := by
        rw [← hsum]
        exact hlinearA.add hlinearB
      have hpairNe : FABL.f₂CubeOfFinset {a, b} ≠ 0 :=
        f₂CubeOfFinset_ne_zero_of_nonempty (by simp)
      have hpairWeight :
          (FABL.f₂Support (FABL.f₂CubeOfFinset {a, b})).card ≤ l := by
        rw [f₂Support_f₂CubeOfFinset]
        simp [hab, hlTwo]
      have hbalanced := hpc (FABL.f₂CubeOfFinset {a, b})
        ⟨hpairNe, hpairWeight⟩
      have hautoZero :=
        (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
          f (FABL.f₂CubeOfFinset {a, b})).mp hbalanced
      have hautoSquare := autocorrelation_sq_of_mem_linearKernel
        f (FABL.f₂CubeOfFinset {a, b})
        ((mem_linearKernel f _).2 hlinearSum)
      rw [hautoZero] at hautoSquare
      have hpositive : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
      nlinarith
    have hlEq : l = n - 1 := by omega
    left
    refine ⟨?_, hlEq⟩
    rcases hlEven with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    omega

end CryptBoolean
