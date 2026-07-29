/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.RandomNonlinearityAsymptotics
public import CryptBoolean.Carlet.Chapter09.GeneralProperties
public import FABL.Chapter03.LowDegreeSpectralConcentration
public import FABL.Chapter04.Switching
public import FABL.Chapter05.MajorityLargestFourierCoefficient

/-!
# Majority functions

Carlet Chapter 9: symmetry, normality, algebraic immunity, and exact
nonlinearity of majority and its four threshold conventions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The affine involution that complements every binary input coordinate. -/
noncomputable def binaryComplementAffineEquiv (n : ℕ) :
    FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n :=
  AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube n) 1

@[simp] theorem binaryComplementAffineEquiv_apply (x : FABL.F₂Cube n) :
    binaryComplementAffineEquiv n x = FABL.binaryCubeComplement x := by
  funext i
  simp [binaryComplementAffineEquiv, FABL.binaryCubeComplement, add_comm]

/-- The strict majority threshold, equal to one exactly above half weight. -/
noncomputable def carletStrictMajority (n : ℕ) : BooleanFunction n :=
  FABL.booleanFunctionF₂Encoding (FABL.majority n)

/-- The strict minority threshold, equal to one exactly below half weight. -/
noncomputable def carletStrictMinority (n : ℕ) : BooleanFunction n :=
  carletStrictMajority n ∘ binaryComplementAffineEquiv n

/-- The weak minority threshold, equal to one at weights at most half. -/
noncomputable def carletWeakMinority (n : ℕ) : BooleanFunction n :=
  carletStrictMajority n + 1

/-- Carlet's majority function, with a tie included in the one-set. -/
noncomputable def carletMajority (n : ℕ) : BooleanFunction n :=
  carletStrictMinority n + 1

/-- Positive sign coordinates are the complement of the binary support. -/
private theorem positiveCoordinateSet_binaryCubeSignEquiv
    (x : FABL.F₂Cube n) :
    FABL.positiveCoordinateSet (FABL.binaryCubeSignEquiv n x) =
      (FABL.f₂Support x)ᶜ := by
  ext i
  by_cases hi : x i = 0
  · simp [FABL.positiveCoordinateSet, FABL.f₂Support,
      FABL.binaryCubeSignEquiv_apply, hi]
  · have hiOne : x i = 1 := Fin.eq_one_of_ne_zero _ hi
    simp [FABL.positiveCoordinateSet, FABL.f₂Support,
      FABL.binaryCubeSignEquiv_apply, hiOne]

/-- The sign-cube positive-coordinate count is binary co-weight. -/
private theorem positiveCoordinateCount_binaryCubeSignEquiv
    (x : FABL.F₂Cube n) :
    FABL.positiveCoordinateCount (FABL.binaryCubeSignEquiv n x) =
      n - (FABL.f₂Support x).card := by
  rw [FABL.positiveCoordinateCount,
    positiveCoordinateSet_binaryCubeSignEquiv, Finset.card_compl]
  simp

/-- Complementing every binary coordinate complements its support. -/
theorem f₂Support_binaryCubeComplement (x : FABL.F₂Cube n) :
    FABL.f₂Support (FABL.binaryCubeComplement x) =
      (FABL.f₂Support x)ᶜ := by
  ext i
  by_cases hi : x i = 0
  · simp [FABL.f₂Support, FABL.binaryCubeComplement, hi]
  · have hiOne : x i = 1 := Fin.eq_one_of_ne_zero _ hi
    simp [FABL.f₂Support, FABL.binaryCubeComplement, hiOne]

/-- Complementing an input subtracts its Hamming weight from the dimension. -/
theorem card_f₂Support_binaryCubeComplement (x : FABL.F₂Cube n) :
    (FABL.f₂Support (FABL.binaryCubeComplement x)).card =
      n - (FABL.f₂Support x).card := by
  rw [f₂Support_binaryCubeComplement, Finset.card_compl]
  simp

/-- The encoded FABL majority is the strict binary majority threshold. -/
theorem carletStrictMajority_apply_eq_one_iff (x : FABL.F₂Cube n) :
    carletStrictMajority n x = 1 ↔
      n < 2 * (FABL.f₂Support x).card := by
  have hcard : (FABL.f₂Support x).card ≤ n := by
    simpa using Finset.card_le_univ (FABL.f₂Support x)
  change FABL.binarySignEquiv.symm
      (FABL.majority n (FABL.binaryCubeSignEquiv n x)) = 1 ↔ _
  rw [FABL.majority,
    FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub,
    positiveCoordinateCount_binaryCubeSignEquiv]
  unfold FABL.thresholdSign
  split_ifs with h
  · simp only [FABL.binarySignEquiv]
    simp only [Equiv.symm_mk, Equiv.coe_fn_mk, ↓reduceIte, zero_ne_one,
      false_iff, not_lt]
    have hreal :
        (2 : ℝ) * ((FABL.f₂Support x).card : ℝ) ≤ n := by
      rw [Nat.cast_sub hcard] at h
      norm_num at h ⊢
      linarith
    exact_mod_cast hreal
  · simp only [FABL.binarySignEquiv]
    simp only [Equiv.symm_mk, Equiv.coe_fn_mk, neg_units_ne_self,
      ↓reduceIte, true_iff]
    have hneg := lt_of_not_ge h
    rw [Nat.cast_sub hcard] at hneg
    have hreal :
        (n : ℝ) < 2 * ((FABL.f₂Support x).card : ℝ) := by
      norm_num at hneg ⊢
      linarith
    exact_mod_cast hreal

/-- The input-complement convention is the strict minority threshold. -/
theorem carletStrictMinority_apply_eq_one_iff (x : FABL.F₂Cube n) :
    carletStrictMinority n x = 1 ↔
      2 * (FABL.f₂Support x).card < n := by
  have hcard : (FABL.f₂Support x).card ≤ n := by
    simpa using Finset.card_le_univ (FABL.f₂Support x)
  rw [carletStrictMinority, Function.comp_apply,
    binaryComplementAffineEquiv_apply,
    carletStrictMajority_apply_eq_one_iff,
    card_f₂Support_binaryCubeComplement]
  omega

/-- Output complementation gives the weak minority threshold. -/
theorem carletWeakMinority_apply_eq_one_iff (x : FABL.F₂Cube n) :
    carletWeakMinority n x = 1 ↔
      2 * (FABL.f₂Support x).card ≤ n := by
  rw [carletWeakMinority]
  change carletStrictMajority n x + 1 = 1 ↔ _
  constructor
  · intro h
    have hzero : carletStrictMajority n x = 0 := by
      by_contra hne
      have hone := Fin.eq_one_of_ne_zero _ hne
      rw [hone] at h
      have hfalse : (0 : FABL.𝔽₂) = 1 := by
        calc
          0 = 1 + 1 := (ZModModule.add_self 1).symm
          _ = 1 := h
      exact zero_ne_one hfalse
    by_contra hnot
    have hone := (carletStrictMajority_apply_eq_one_iff x).2 (by omega)
    rw [hzero] at hone
    exact zero_ne_one hone
  · intro h
    have hzero : carletStrictMajority n x = 0 := by
      by_contra hne
      have hone := Fin.eq_one_of_ne_zero _ hne
      have := (carletStrictMajority_apply_eq_one_iff x).1 hone
      omega
    simp [hzero]

/-- Carlet's convention is the weak majority threshold. -/
theorem carletMajority_apply_eq_one_iff (x : FABL.F₂Cube n) :
    carletMajority n x = 1 ↔
      n ≤ 2 * (FABL.f₂Support x).card := by
  have hcard : (FABL.f₂Support x).card ≤ n := by
    simpa using Finset.card_le_univ (FABL.f₂Support x)
  rw [carletMajority, carletStrictMinority]
  change carletStrictMajority n (binaryComplementAffineEquiv n x) + 1 = 1 ↔ _
  rw [binaryComplementAffineEquiv_apply]
  have hstrict := carletStrictMajority_apply_eq_one_iff
    (FABL.binaryCubeComplement x)
  rw [card_f₂Support_binaryCubeComplement] at hstrict
  constructor
  · intro h
    have hzero :
        carletStrictMajority n (FABL.binaryCubeComplement x) = 0 := by
      by_contra hne
      have hone := Fin.eq_one_of_ne_zero _ hne
      rw [hone] at h
      have hfalse : (0 : FABL.𝔽₂) = 1 := by
        calc
          0 = 1 + 1 := (ZModModule.add_self 1).symm
          _ = 1 := h
      exact zero_ne_one hfalse
    have hnlt : ¬ n < 2 * (n - (FABL.f₂Support x).card) := by
      intro hlt
      have hone := hstrict.2 hlt
      rw [hzero] at hone
      exact zero_ne_one hone
    omega
  · intro h
    have hnlt : ¬ n < 2 * (n - (FABL.f₂Support x).card) := by
      omega
    have hzero :
        carletStrictMajority n (FABL.binaryCubeComplement x) = 0 := by
      by_contra hne
      have hone := Fin.eq_one_of_ne_zero _ hne
      exact hnlt (hstrict.1 hone)
    simp [hzero]

/-- Carlet's majority threshold is equivalently Hamming weight at least `⌈n/2⌉`. -/
theorem carletMajority_apply_eq_one_iff_ceiling_half
    (x : FABL.F₂Cube n) :
    carletMajority n x = 1 ↔
      (n + 1) / 2 ≤ (FABL.f₂Support x).card := by
  rw [carletMajority_apply_eq_one_iff]
  omega

/-- Binary Hamming weight determines Carlet's majority value. -/
theorem carletMajority_eq_of_support_card_eq
    (x y : FABL.F₂Cube n)
    (hweight : (FABL.f₂Support x).card =
      (FABL.f₂Support y).card) :
    carletMajority n x = carletMajority n y := by
  by_cases hx : carletMajority n x = 1
  · have hy : carletMajority n y = 1 :=
      (carletMajority_apply_eq_one_iff y).2 (by
        rw [← hweight]
        exact (carletMajority_apply_eq_one_iff x).1 hx)
    rw [hx, hy]
  · have hxZero : carletMajority n x = 0 := by
      by_contra hne
      exact hx (Fin.eq_one_of_ne_zero _ hne)
    have hyZero : carletMajority n y = 0 := by
      by_contra hne
      have hyOne := Fin.eq_one_of_ne_zero _ hne
      apply hx
      exact (carletMajority_apply_eq_one_iff x).2 (by
        rw [hweight]
        exact (carletMajority_apply_eq_one_iff y).1 hyOne)
    rw [hxZero, hyZero]

/-- Carlet's majority is invariant under every coordinate permutation. -/
theorem carletMajority_symmetric :
    FABL.IsSymmetric (fun x : FABL.SignCube n ↦
      carletMajority n ((FABL.binaryCubeSignEquiv n).symm x)) := by
  intro π x
  apply carletMajority_eq_of_support_card_eq
  have hpositive := FABL.positiveCoordinateCount_permuteInput π x
  have hleft := positiveCoordinateCount_binaryCubeSignEquiv
    ((FABL.binaryCubeSignEquiv n).symm (FABL.permuteInput π x))
  have hright := positiveCoordinateCount_binaryCubeSignEquiv
    ((FABL.binaryCubeSignEquiv n).symm x)
  simp only [Equiv.apply_symm_apply] at hleft hright
  rw [hpositive] at hleft
  have hleftLe :
      (FABL.f₂Support
        ((FABL.binaryCubeSignEquiv n).symm
          (FABL.permuteInput π x))).card ≤ n := by
    simpa using Finset.card_le_univ
      (FABL.f₂Support
        ((FABL.binaryCubeSignEquiv n).symm
          (FABL.permuteInput π x)))
  have hrightLe :
      (FABL.f₂Support ((FABL.binaryCubeSignEquiv n).symm x)).card ≤ n := by
    simpa using Finset.card_le_univ
      (FABL.f₂Support ((FABL.binaryCubeSignEquiv n).symm x))
  omega

/-- Majority is constant on a coordinate flat of dimension `⌊n/2⌋`. -/
theorem carletMajority_isKNormal (hn : 0 < n) :
    IsKNormal (carletMajority n) (n / 2) := by
  let I : Finset (Fin n) :=
    Finset.univ.filter fun i ↦ (i : ℕ) < (n + 1) / 2
  let H := FABL.F₂DecisionTree.coordinateZeroSubspace I
  let a : FABL.F₂Cube n := FABL.f₂CubeOfFinset I
  have hceilLe : (n + 1) / 2 ≤ n := by omega
  have hIcard : I.card = (n + 1) / 2 := by
    simp [I, Fin.card_filter_val_lt, hceilLe]
  have hfinrank : Module.finrank FABL.𝔽₂ H = n / 2 := by
    have hcodimension :=
      FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace I
    rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace] at hcodimension
    have hle : Module.finrank FABL.𝔽₂ H ≤ n := by
      simpa using H.finrank_le
    dsimp [H] at hcodimension ⊢
    rw [hIcard] at hcodimension
    omega
  refine ⟨H, a, hfinrank, 1, ?_⟩
  intro x hx
  apply (carletMajority_apply_eq_one_iff x).2
  have hxadd : x + a ∈ H :=
    (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).1 hx
  have hsubset : I ⊆ FABL.f₂Support x := by
    intro i hi
    have hzero :=
      (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff
        I (x + a)).1 hxadd i hi
    change x i + a i = 0 at hzero
    rw [show a i = 1 by
      simp [a, FABL.f₂CubeOfFinset_apply, hi]] at hzero
    have hxi : x i = 1 := by
      have hadd := congrArg (fun z : FABL.𝔽₂ ↦ z + 1) hzero
      simpa [add_assoc] using hadd
    simp [FABL.f₂Support, hxi]
  have hweight : I.card ≤ (FABL.f₂Support x).card :=
    Finset.card_le_card hsubset
  rw [hIcard] at hweight
  omega

/-- Low-weight evaluations determine every Boolean function of bounded ANF degree. -/
private theorem eq_zero_of_degree_le_of_eq_zero_on_low_weight
    (g : BooleanFunction n) (d : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ d)
    (hzero : ∀ x : FABL.F₂Cube n,
      (FABL.f₂Support x).card ≤ d → g x = 0) :
    g = 0 := by
  have hcoeff : FABL.anfCoeff g = 0 := by
    funext S
    by_cases hS : FABL.anfCoeff g S = 0
    · exact hS
    · have hcard : S.card ≤ d :=
        (FABL.algebraicDegree_le_iff (FABL.anfCoeff g) d).mp
          hdegree S hS
      rw [FABL.anfCoeff]
      apply Finset.sum_eq_zero
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hsupport :
          FABL.f₂Support (FABL.f₂CubeOfFinset T) = T := by
        simpa using (FABL.f₂CubeEquivFinset n).apply_symm_apply T
      rw [hzero (FABL.f₂CubeOfFinset T) (by
        rw [hsupport]
        exact (Finset.card_le_card hT).trans hcard)]
  calc
    g = FABL.anfEval (FABL.anfCoeff g) :=
      (FABL.anfEval_anfCoeff g).symm
    _ = FABL.anfEval 0 := by rw [hcoeff]
    _ = 0 := by
      funext x
      simp [FABL.anfEval]

/-- Every annihilator witness for majority has degree at least `⌈n/2⌉`. -/
private theorem ceiling_half_le_degree_of_majority_witness
    (g : BooleanFunction n)
    (hg : IsAlgebraicImmunityWitness (carletMajority n) g) :
    (n + 1) / 2 ≤ FABL.functionAlgebraicDegree g := by
  by_contra hnot
  have hdegree :
      FABL.functionAlgebraicDegree g < (n + 1) / 2 :=
    Nat.lt_of_not_ge hnot
  rcases hg with hg | hg
  · let q : BooleanFunction n := g ∘ binaryComplementAffineEquiv n
    have hqDegree :
        FABL.functionAlgebraicDegree q =
          FABL.functionAlgebraicDegree g :=
      FABL.functionAlgebraicDegree_comp_affineEquiv g
        (binaryComplementAffineEquiv n)
    have hqZero : q = 0 := by
      apply eq_zero_of_degree_le_of_eq_zero_on_low_weight
        q (FABL.functionAlgebraicDegree g)
      · rw [hqDegree]
      · intro x hx
        have hweight :
            n ≤ 2 *
              (FABL.f₂Support (binaryComplementAffineEquiv n x)).card := by
          rw [binaryComplementAffineEquiv_apply,
            card_f₂Support_binaryCubeComplement]
          have hxcard : (FABL.f₂Support x).card ≤ n := by
            simpa using Finset.card_le_univ (FABL.f₂Support x)
          omega
        have hf : carletMajority n (binaryComplementAffineEquiv n x) = 1 :=
          (carletMajority_apply_eq_one_iff _).2 hweight
        have hproduct := congrFun hg.2 (binaryComplementAffineEquiv n x)
        change carletMajority n (binaryComplementAffineEquiv n x) *
            g (binaryComplementAffineEquiv n x) = 0 at hproduct
        rw [hf, one_mul] at hproduct
        exact hproduct
    apply hg.1
    funext x
    have hqx := congrFun hqZero (binaryComplementAffineEquiv n x)
    change g (binaryComplementAffineEquiv n
      (binaryComplementAffineEquiv n x)) = 0 at hqx
    simpa using hqx
  · have hgZero : g = 0 := by
      apply eq_zero_of_degree_le_of_eq_zero_on_low_weight
        g (FABL.functionAlgebraicDegree g) (by rfl)
      intro x hx
      have hfZero : carletMajority n x = 0 := by
        by_contra hne
        have hfOne := Fin.eq_one_of_ne_zero _ hne
        have hweight := (carletMajority_apply_eq_one_iff x).1 hfOne
        omega
      have hproduct := congrFun hg.2 x
      change (carletMajority n x + 1) * g x = 0 at hproduct
      rw [hfZero, zero_add, one_mul] at hproduct
      exact hproduct
    exact hg.1 hgZero

/-- Majority has optimal algebraic immunity `⌈n/2⌉`. -/
theorem algebraicImmunity_carletMajority :
    algebraicImmunity (carletMajority n) = (n + 1) / 2 := by
  apply Nat.le_antisymm (algebraicImmunity_le_ceiling_half _)
  obtain ⟨g, hg, hdegree⟩ :=
    exists_witness_functionAlgebraicDegree_eq_algebraicImmunity
      (carletMajority n)
  rw [← hdegree]
  exact ceiling_half_le_degree_of_majority_witness g hg

/-- The strict minority convention is an affine input reindexing. -/
theorem carletStrictMinority_eq_affineReindexing :
    carletStrictMinority n =
      carletStrictMajority n ∘ binaryComplementAffineEquiv n := by
  rfl

/-- The weak minority convention is output complementation. -/
theorem carletWeakMinority_eq_outputComplement :
    carletWeakMinority n = carletStrictMajority n + 1 := by
  rfl

/-- Carlet's convention is affine input reindexing followed by output complementation. -/
theorem carletMajority_eq_affineReindexing_add_one :
    carletMajority n =
      (carletStrictMajority n ∘ binaryComplementAffineEquiv n) + 1 := by
  rfl

/-- Strict majority has optimal algebraic immunity. -/
theorem algebraicImmunity_carletStrictMajority :
    algebraicImmunity (carletStrictMajority n) = (n + 1) / 2 := by
  calc
    algebraicImmunity (carletStrictMajority n) =
        algebraicImmunity (carletStrictMinority n) :=
      (algebraicImmunity_comp_affineEquiv
        (carletStrictMajority n) (binaryComplementAffineEquiv n)).symm
    _ = algebraicImmunity (carletMajority n) :=
      (algebraicImmunity_add_constant_one
        (carletStrictMinority n)).symm
    _ = (n + 1) / 2 := algebraicImmunity_carletMajority

/-- Strict minority has optimal algebraic immunity. -/
theorem algebraicImmunity_carletStrictMinority :
    algebraicImmunity (carletStrictMinority n) = (n + 1) / 2 := by
  rw [carletStrictMinority_eq_affineReindexing,
    algebraicImmunity_comp_affineEquiv,
    algebraicImmunity_carletStrictMajority]

/-- Weak minority has optimal algebraic immunity. -/
theorem algebraicImmunity_carletWeakMinority :
    algebraicImmunity (carletWeakMinority n) = (n + 1) / 2 := by
  rw [carletWeakMinority_eq_outputComplement,
    algebraicImmunity_add_constant_one,
    algebraicImmunity_carletStrictMajority]

/-- The `+1` slice of odd majority is even majority. -/
private theorem firstCoordinateSlice_majority_odd_one (r : ℕ) :
    FABL.firstCoordinateSlice (FABL.majority (2 * r + 1)).toReal 1 =
      (FABL.majority (2 * r)).toReal := by
  funext x
  unfold FABL.firstCoordinateSlice FABL.BooleanFunction.toReal FABL.majority
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, FABL.signValue_one]
  congr 1
  let s : ℝ := ∑ i, FABL.signValue (x i)
  have hs :
      s = 2 * FABL.positiveCoordinateCount x - (2 * r : ℕ) :=
    FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub x
  by_cases hnonnegative : 0 ≤ s
  · rw [FABL.thresholdSign_of_nonneg hnonnegative,
      FABL.thresholdSign_of_nonneg (by
        dsimp [s] at hnonnegative ⊢
        linarith)]
  · have hnegative : s < 0 := lt_of_not_ge hnonnegative
    have hcount : FABL.positiveCoordinateCount x < r := by
      rw [hs] at hnegative
      norm_num at hnegative
      exact hnegative
    have hcountReal :
        (FABL.positiveCoordinateCount x : ℝ) + 1 ≤ r := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcount)
    have hplusNegative : 1 + s < 0 := by
      rw [hs]
      push_cast
      linarith
    rw [FABL.thresholdSign_of_neg hnegative,
      FABL.thresholdSign_of_neg hplusNegative]

/-- A positive first-coordinate slice adds the corresponding two ambient coefficients. -/
private theorem fourierCoeff_firstCoordinateSlice_one_eq_add
    {d : ℕ} (f : FABL.SignCube (d + 1) → ℝ)
    (S : Finset (Fin d)) :
    FABL.fourierCoeff (FABL.firstCoordinateSlice f 1) S =
      FABL.fourierCoeff f (FABL.tailFrequency S) +
        FABL.fourierCoeff f (insert 0 (FABL.tailFrequency S)) := by
  have hmean := FABL.fourierCoeff_tailFrequency f S
  have hdifference := FABL.fourierCoeff_insert_zero_tailFrequency f S
  linarith

/-- Tail-frequency embedding preserves cardinality. -/
private theorem card_tailFrequency {d : ℕ} (S : Finset (Fin d)) :
    (FABL.tailFrequency S).card = S.card := by
  simp [FABL.tailFrequency]

/-- Every even-majority coefficient is bounded by the central odd influence. -/
private theorem abs_fourierCoeff_majority_even_le
    (r : ℕ) (S : Finset (Fin (2 * r))) :
    |FABL.fourierCoeff (FABL.majority (2 * r)).toReal S| ≤
      FABL.oddMajorityInfluence r := by
  rw [← firstCoordinateSlice_majority_odd_one r,
    fourierCoeff_firstCoordinateSlice_one_eq_add]
  rcases Nat.even_or_odd S.card with hSeven | hSodd
  · have htailEven : Even (FABL.tailFrequency S).card := by
      simpa [card_tailFrequency] using hSeven
    rw [FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      (show Odd (2 * r + 1) by exact ⟨r, by omega⟩) _ htailEven,
      zero_add]
    have hle := FABL.abs_fourierCoeff_majority_le_singleton r
      (insert 0 (FABL.tailFrequency S)) 0
    rw [FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence] at hle
    exact hle
  · have hinsertEven : Even (insert 0 (FABL.tailFrequency S)).card := by
      rw [Finset.card_insert_of_notMem]
      · rw [card_tailFrequency]
        exact hSodd.add_one
      · simp [FABL.tailFrequency]
    rw [FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      (show Odd (2 * r + 1) by exact ⟨r, by omega⟩) _ hinsertEven,
      add_zero]
    have hle := FABL.abs_fourierCoeff_majority_le_singleton r
      (FABL.tailFrequency S) 0
    rw [FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence] at hle
    exact hle

/-- The zero-frequency even-majority coefficient attains the central odd influence. -/
private theorem abs_fourierCoeff_majority_even_empty (r : ℕ) :
    |FABL.fourierCoeff (FABL.majority (2 * r)).toReal ∅| =
      FABL.oddMajorityInfluence r := by
  rw [← firstCoordinateSlice_majority_odd_one r,
    fourierCoeff_firstCoordinateSlice_one_eq_add]
  have htail :
      FABL.tailFrequency (∅ : Finset (Fin (2 * r))) = ∅ := by
    simp [FABL.tailFrequency]
  rw [htail]
  have hzero :=
    FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      (show Odd (2 * r + 1) by exact ⟨r, by omega⟩)
      (∅ : Finset (Fin (2 * r + 1))) (by simp)
  rw [hzero, zero_add]
  rw [show insert 0 (∅ : Finset (Fin (2 * r + 1))) = {0} by simp,
    FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence,
    abs_of_pos (FABL.oddMajorityInfluence_pos r)]

/-- The exact Fourier infinity norm of even majority. -/
theorem fourierInfinityNorm_majority_even (r : ℕ) :
    FABL.fourierInfinityNorm (FABL.majority (2 * r)).toReal =
      FABL.oddMajorityInfluence r := by
  apply le_antisymm
  · unfold FABL.fourierInfinityNorm
    apply Finset.sup'_le
    intro S _
    exact abs_fourierCoeff_majority_even_le r S
  · unfold FABL.fourierInfinityNorm
    have hle := Finset.le_sup'
      (fun S : Finset (Fin (2 * r)) ↦
        |FABL.fourierCoeff (FABL.majority (2 * r)).toReal S|)
      (Finset.mem_univ (∅ : Finset (Fin (2 * r))))
    rwa [abs_fourierCoeff_majority_even_empty] at hle

/-- The exact Fourier infinity norm of odd majority. -/
theorem fourierInfinityNorm_majority_odd (r : ℕ) :
    FABL.fourierInfinityNorm (FABL.majority (2 * r + 1)).toReal =
      FABL.oddMajorityInfluence r := by
  apply le_antisymm
  · unfold FABL.fourierInfinityNorm
    apply Finset.sup'_le
    intro S _
    have hle := FABL.abs_fourierCoeff_majority_le_singleton r S 0
    rwa [FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence] at hle
  · unfold FABL.fourierInfinityNorm
    have hle := Finset.le_sup'
      (fun S : Finset (Fin (2 * r + 1)) ↦
        |FABL.fourierCoeff (FABL.majority (2 * r + 1)).toReal S|)
      (Finset.mem_univ ({0} : Finset (Fin (2 * r + 1))))
    rw [FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence,
      abs_of_pos (FABL.oddMajorityInfluence_pos r)] at hle
    exact hle

/-- The maximum raw Walsh magnitude of strict majority in even dimension. -/
theorem maxWalshMagnitude_carletStrictMajority_even (r : ℕ) :
    maxWalshMagnitude (carletStrictMajority (2 * r)) =
      Nat.choose (2 * r) r := by
  apply Nat.cast_injective (R := ℝ)
  rw [maxWalshMagnitude_cast_eq_spectralInfinityNorm,
    carletStrictMajority,
    spectralInfinityNorm_encoding_eq_fourierInfinityNorm,
    fourierInfinityNorm_majority_even]
  unfold FABL.oddMajorityInfluence
  field_simp

/-- The maximum raw Walsh magnitude of strict majority in odd dimension. -/
theorem maxWalshMagnitude_carletStrictMajority_odd (r : ℕ) :
    maxWalshMagnitude (carletStrictMajority (2 * r + 1)) =
      2 * Nat.choose (2 * r) r := by
  apply Nat.cast_injective (R := ℝ)
  rw [maxWalshMagnitude_cast_eq_spectralInfinityNorm,
    carletStrictMajority,
    spectralInfinityNorm_encoding_eq_fourierInfinityNorm,
    fourierInfinityNorm_majority_odd]
  unfold FABL.oddMajorityInfluence
  push_cast
  rw [show (2 : ℝ) ^ (2 * r + 1) =
      2 * (2 : ℝ) ^ (2 * r) by rw [pow_succ']]
  field_simp

/-- The central coefficient in positive even dimension is twice its predecessor-row value. -/
private theorem choose_two_mul_eq_two_mul_choose_pred
    (r : ℕ) (hr : 0 < r) :
    Nat.choose (2 * r) r = 2 * Nat.choose (2 * r - 1) r := by
  have hpascal := Nat.choose_succ_succ (2 * r - 1) (r - 1)
  have hsymmetry := Nat.choose_symm (show r ≤ 2 * r - 1 by omega)
  have hleft : (2 * r - 1) - r = r - 1 := by omega
  rw [hleft] at hsymmetry
  have htop : (2 * r - 1).succ = 2 * r := by omega
  have hbottom : (r - 1).succ = r := by omega
  rw [htop, hbottom, hsymmetry] at hpascal
  omega

/-- Exact nonlinearity of strict majority in odd dimension. -/
theorem nonlinearity_carletStrictMajority_odd (r : ℕ) :
    nonlinearity (carletStrictMajority (2 * r + 1)) =
      2 ^ (2 * r) - Nat.choose (2 * r) r := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude
    (carletStrictMajority (2 * r + 1))
  rw [maxWalshMagnitude_carletStrictMajority_odd] at hrelation
  have hpower : 2 ^ (2 * r + 1) = 2 * 2 ^ (2 * r) := by
    rw [pow_succ']
  rw [hpower] at hrelation
  omega

/-- Exact nonlinearity of strict majority in positive even dimension. -/
theorem nonlinearity_carletStrictMajority_even
    (r : ℕ) (hr : 0 < r) :
    nonlinearity (carletStrictMajority (2 * r)) =
      2 ^ (2 * r - 1) - Nat.choose (2 * r - 1) r := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude
    (carletStrictMajority (2 * r))
  rw [maxWalshMagnitude_carletStrictMajority_even,
    choose_two_mul_eq_two_mul_choose_pred r hr] at hrelation
  have hpower : 2 ^ (2 * r) = 2 * 2 ^ (2 * r - 1) := by
    calc
      2 ^ (2 * r) = 2 ^ ((2 * r - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (2 * r - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (2 * r - 1) := by omega
  rw [hpower] at hrelation
  omega

/-- Exact nonlinearity of strict majority in every positive dimension. -/
theorem nonlinearity_carletStrictMajority (hn : 0 < n) :
    nonlinearity (carletStrictMajority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) (n / 2) := by
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp heven
    subst n
    have hrPositive : 0 < r := by omega
    simpa using nonlinearity_carletStrictMajority_even r hrPositive
  · obtain ⟨r, hr⟩ := hodd
    subst n
    have hhalf : (2 * r + 1) / 2 = r := by omega
    rw [hhalf]
    simpa using nonlinearity_carletStrictMajority_odd r

/-- Output complementation preserves nonlinearity. -/
theorem nonlinearity_add_constant_one (f : BooleanFunction n) :
    nonlinearity (f + 1) = nonlinearity f := by
  have hone : (1 : BooleanFunction n) = FABL.affineFunction 1 0 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
  rw [hone]
  exact nonlinearity_add_affineFunction f 1 0

/-- Every majority threshold convention has the same nonlinearity. -/
theorem nonlinearity_carletMajority_eq_strictMajority :
    nonlinearity (carletMajority n) =
      nonlinearity (carletStrictMajority n) := by
  calc
    nonlinearity (carletMajority n) =
        nonlinearity (carletStrictMinority n) :=
      nonlinearity_add_constant_one (carletStrictMinority n)
    _ = nonlinearity (carletStrictMajority n) :=
      nonlinearity_comp_affineEquiv
        (carletStrictMajority n) (binaryComplementAffineEquiv n)

/-- Exact nonlinearity of Carlet's majority in every positive dimension. -/
theorem nonlinearity_carletMajority (hn : 0 < n) :
    nonlinearity (carletMajority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) (n / 2) := by
  rw [nonlinearity_carletMajority_eq_strictMajority]
  exact nonlinearity_carletStrictMajority hn

/-- Exact even-dimensional majority nonlinearity. -/
theorem nonlinearity_carletMajority_of_even
    (hn : 0 < n) (_heven : Even n) :
    nonlinearity (carletMajority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) (n / 2) :=
  nonlinearity_carletMajority hn

/-- Exact odd-dimensional majority nonlinearity. -/
theorem nonlinearity_carletMajority_of_odd
    (hodd : Odd n) :
    nonlinearity (carletMajority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) ((n - 1) / 2) := by
  have hn : 0 < n := by
    obtain ⟨r, rfl⟩ := hodd
    omega
  rw [nonlinearity_carletMajority hn]
  congr 2
  obtain ⟨r, rfl⟩ := hodd
  omega

/-- Weak minority has the same exact nonlinearity as strict majority. -/
theorem nonlinearity_carletWeakMinority (hn : 0 < n) :
    nonlinearity (carletWeakMinority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) (n / 2) := by
  rw [carletWeakMinority_eq_outputComplement,
    nonlinearity_add_constant_one]
  exact nonlinearity_carletStrictMajority hn

/-- Strict minority has the same exact nonlinearity as strict majority. -/
theorem nonlinearity_carletStrictMinority (hn : 0 < n) :
    nonlinearity (carletStrictMinority n) =
      2 ^ (n - 1) - Nat.choose (n - 1) (n / 2) := by
  rw [carletStrictMinority_eq_affineReindexing,
    nonlinearity_comp_affineEquiv]
  exact nonlinearity_carletStrictMajority hn

end CryptBoolean
