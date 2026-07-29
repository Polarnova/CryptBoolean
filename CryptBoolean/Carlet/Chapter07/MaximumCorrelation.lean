/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Restrictions
public import CryptBoolean.Carlet.Chapter04.LinearStructureSpectrum
public import CryptBoolean.Carlet.Chapter04.MaximumCorrelation
public import CryptBoolean.Carlet.Chapter05.Affine

/-!
# Walsh support and maximum correlation of resilient functions

The Walsh-support count and the exact maximum-correlation specialization from
Carlet Chapter 7.
-/

open Finset Set
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The number of frequencies supported in `I` whose weight exceeds `m`. -/
theorem card_highWeightFrequenciesSupportedIn_eq_sum_choose
    (I : Finset (Fin n)) (m : ℕ) :
    #((Finset.univ : Finset (FABL.F₂Cube n)).filter fun u ↦
        FABL.f₂Support u ⊆ I ∧ m < (FABL.f₂Support u).card) =
      ∑ j ∈ Finset.Icc (m + 1) I.card, I.card.choose j := by
  classical
  have hcard :
      #((Finset.univ : Finset (FABL.F₂Cube n)).filter fun u ↦
          FABL.f₂Support u ⊆ I ∧ m < (FABL.f₂Support u).card) =
        #(I.powerset.filter fun S ↦ m < S.card) := by
    apply Finset.card_bij'
        (fun u _hu ↦ FABL.f₂Support u)
        (fun S _hS ↦ FABL.f₂CubeOfFinset S)
    · intro u hu
      rw [Finset.mem_filter] at hu ⊢
      exact ⟨Finset.mem_powerset.mpr hu.2.1, hu.2.2⟩
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      have hsupport :
          FABL.f₂Support (FABL.f₂CubeOfFinset S) = S :=
        (FABL.f₂CubeEquivFinset n).right_inv S
      exact ⟨Finset.mem_univ _, by simpa [hsupport] using hS⟩
    · intro u _hu
      exact (FABL.f₂CubeEquivFinset n).left_inv u
    · intro S _hS
      exact (FABL.f₂CubeEquivFinset n).right_inv S
  rw [hcard, Finset.card_eq_sum_ones]
  calc
    (∑ S ∈ I.powerset.filter (fun S ↦ m < S.card), 1) =
        ∑ j ∈ Finset.Icc (m + 1) I.card,
          ∑ S ∈ I.powerset.filter (fun S ↦ m < S.card)
              with S.card = j, 1 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S hS
      rw [Finset.mem_filter] at hS
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_iff.mpr hS.2,
        Finset.card_le_card (Finset.mem_powerset.mp hS.1)⟩
    _ = ∑ j ∈ Finset.Icc (m + 1) I.card, I.card.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.card_eq_sum_ones, ← Finset.card_powersetCard]
      congr 1
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hSI, _hmS⟩, hSj⟩
        exact ⟨hSI, hSj⟩
      · rintro ⟨hSI, hSj⟩
        have hmj : m < j := by
          rw [Finset.mem_Icc] at hj
          omega
        exact ⟨⟨hSI, by simpa [hSj] using hmj⟩, hSj⟩

/-- An `m`-resilient function has at most the high-weight binomial tail of
nonzero Walsh frequencies supported inside a prescribed coordinate set. -/
theorem card_walshSupport_filter_subset_le_sum_choose_of_isResilient
    (f : BooleanFunction n) (I : Finset (Fin n)) (m : ℕ)
    (hm : m < n) (hf : IsResilient m f) :
    #((walshSupport f).filter fun u ↦ FABL.f₂Support u ⊆ I) ≤
      ∑ j ∈ Finset.Icc (m + 1) I.card, I.card.choose j := by
  classical
  have hzero :=
    theorem_3_resilient_iff_walshTransform_eq_zero
      m f (Nat.zero_lt_of_lt hm) hm |>.mp hf
  calc
    #((walshSupport f).filter fun u ↦ FABL.f₂Support u ⊆ I) ≤
        #((Finset.univ : Finset (FABL.F₂Cube n)).filter fun u ↦
          FABL.f₂Support u ⊆ I ∧ m < (FABL.f₂Support u).card) := by
      apply Finset.card_le_card
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨Finset.mem_univ u, hu.2, ?_⟩
      by_contra hweight
      have hle : (FABL.f₂Support u).card ≤ m := by omega
      exact (mem_walshSupport f u |>.mp hu.1) (hzero u hle)
    _ = ∑ j ∈ Finset.Icc (m + 1) I.card, I.card.choose j :=
      card_highWeightFrequenciesSupportedIn_eq_sum_choose I m

private theorem affineFunction_dependsOn_of_f₂Support_subset
    (b : FABL.𝔽₂) (u : FABL.F₂Cube n) (I : Finset (Fin n))
    (huI : FABL.f₂Support u ⊆ I) :
    DependsOn (FABL.affineFunction b u) (I : Set (Fin n)) := by
  intro x y hxy
  unfold FABL.affineFunction
  congr 1
  rw [FABL.f₂DotProduct_eq_coordinateSum_f₂Support,
    FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
  change (∑ i ∈ FABL.f₂Support u, x i) =
    ∑ i ∈ FABL.f₂Support u, y i
  apply Finset.sum_congr rfl
  intro i hi
  exact hxy i (huI hi)

private theorem abs_walshTransform_div_le_maximumCorrelation_of_support_subset
    (f : BooleanFunction n) (u : FABL.F₂Cube n) (I : Finset (Fin n))
    (huI : FABL.f₂Support u ⊆ I) :
    |(walshTransform f u : ℝ)| / (2 : ℝ) ^ n ≤ maximumCorrelation f I := by
  have hdepends (b : FABL.𝔽₂) :
      DependsOn (FABL.affineFunction b u) (I : Set (Fin n)) :=
    affineFunction_dependsOn_of_f₂Support_subset b u I huI
  by_cases hwalsh : (0 : ℝ) ≤ (walshTransform f u : ℝ)
  · obtain ⟨q, hq⟩ :=
      (exists_coordinateSignChoice_iff_dependsOn I
        (FABL.affineFunction 0 u)).mpr (hdepends 0)
    have hle := Finset.le_sup'
      (fun q : CoordinateSignChoice I ↦
        normalizedCorrelation f (coordinateBooleanFunction I q))
      (Finset.mem_univ q)
    have hle' :
        normalizedCorrelation f (FABL.affineFunction 0 u) ≤
          maximumCorrelation f I := by
      simpa [maximumCorrelation, hq] using hle
    rw [normalizedCorrelation, walshTransform_add_affineFunction] at hle'
    simpa [abs_of_nonneg hwalsh, bitSignInt] using hle'
  · have hwalshNeg : (walshTransform f u : ℝ) < 0 := lt_of_not_ge hwalsh
    obtain ⟨q, hq⟩ :=
      (exists_coordinateSignChoice_iff_dependsOn I
        (FABL.affineFunction 1 u)).mpr (hdepends 1)
    have hle := Finset.le_sup'
      (fun q : CoordinateSignChoice I ↦
        normalizedCorrelation f (coordinateBooleanFunction I q))
      (Finset.mem_univ q)
    have hle' :
        normalizedCorrelation f (FABL.affineFunction 1 u) ≤
          maximumCorrelation f I := by
      simpa [maximumCorrelation, hq] using hle
    rw [normalizedCorrelation, walshTransform_add_affineFunction] at hle'
    simpa [abs_of_neg hwalshNeg, bitSignInt] using hle'

/-- For an `m`-resilient function and `|I| = m+1`, maximum correlation with
functions on `I` is the normalized magnitude of the unique possible Walsh
coefficient supported on all of `I`. -/
theorem maximumCorrelation_eq_abs_walshTransform_f₂CubeOfFinset_div_of_isResilient
    (f : BooleanFunction n) (I : Finset (Fin n)) (m : ℕ)
    (hm : m < n) (hI : I.card = m + 1) (hf : IsResilient m f) :
    maximumCorrelation f I =
      |(walshTransform f (FABL.f₂CubeOfFinset I) : ℝ)| / (2 : ℝ) ^ n := by
  let uI : FABL.F₂Cube n := FABL.f₂CubeOfFinset I
  have huISupport : FABL.f₂Support uI = I :=
    (FABL.f₂CubeEquivFinset n).right_inv I
  have hzero :=
    theorem_3_resilient_iff_walshTransform_eq_zero
      m f (Nat.zero_lt_of_lt hm) hm |>.mp hf
  have hsquare :
      restrictedWalshSquareSum f I =
        (walshTransform f uI : ℝ) ^ 2 := by
    rw [restrictedWalshSquareSum_eq_sum_filter]
    apply Finset.sum_eq_single uI
    · intro u hu hune
      rw [Finset.mem_filter] at hu
      have hsupportNe : FABL.f₂Support u ≠ I := by
        intro hsupport
        apply hune
        apply (FABL.f₂CubeEquivFinset n).injective
        simpa [FABL.f₂CubeEquivFinset_apply, huISupport] using hsupport
      have hweightLt :
          (FABL.f₂Support u).card < I.card :=
        Finset.card_lt_card (hu.2.ssubset_of_ne hsupportNe)
      have hweight : (FABL.f₂Support u).card ≤ m := by omega
      rw [hzero u hweight]
      norm_num
    · intro hnotMem
      exfalso
      apply hnotMem
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ uI, by simp [huISupport]⟩
  apply le_antisymm
  · calc
      maximumCorrelation f I ≤
          Real.sqrt (restrictedWalshSquareSum f I) / (2 : ℝ) ^ n :=
        maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div f I
      _ = |(walshTransform f uI : ℝ)| / (2 : ℝ) ^ n := by
        rw [hsquare, Real.sqrt_sq_eq_abs]
  · exact abs_walshTransform_div_le_maximumCorrelation_of_support_subset
      f uI I (by simp [huISupport])

end CryptBoolean
