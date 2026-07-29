/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter04.AutocorrelationBounds
public import CryptBoolean.Carlet.Chapter04.PropagationCriteria

/-!
# Resiliency and propagation tradeoff

The necessary parameter inequality for resilient functions satisfying a
propagation criterion.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance propagationTradeoffSubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

/-- An `m`-resilient `PC(l)` Boolean function satisfies `m+l ≤ n-1`. -/
theorem resilient_propagationCriterion_parameter_tradeoff
    (f : BooleanFunction n) (m l : ℕ) (hm : m < n)
    (hresilient : IsResilient m f)
    (hpc : SatisfiesPropagationCriterion l f) :
    m + l ≤ n - 1 := by
  classical
  by_contra htradeoff
  have hlevel : n - m ≤ l := by omega
  have hcardBound :
      n - m ≤ #(Finset.univ : Finset (Fin n)) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨I, _hIuniv, hIcard⟩ :=
    Finset.exists_subset_card_eq hcardBound
  let E : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.F₂DecisionTree.coordinateZeroSubspace I
  have hwalshZero :=
    theorem_3_resilient_iff_walshTransform_eq_zero
      m f (Nat.zero_lt_of_lt hm) hm |>.mp hresilient
  have hpcZero :=
    satisfiesPropagationCriterion_iff_autocorrelation_eq_zero l f |>.mp hpc
  have hsupportE (u : E) : FABL.f₂Support u.1 ⊆ Iᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiI
    have hui :
        u.1 i = 0 :=
      (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff I u.1).mp
        u.2 i hiI
    have hne : u.1 i ≠ 0 := by
      simpa [FABL.f₂Support] using hi
    exact hne hui
  have hweightE (u : E) : (FABL.f₂Support u.1).card ≤ m := by
    have hle := Finset.card_le_card (hsupportE u)
    rw [Finset.card_compl, Fintype.card_fin, hIcard] at hle
    omega
  have hleft :
      (∑ u : E, (walshTransform f u.1 : ℝ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro u _hu
    rw [hwalshZero u.1 (hweightE u)]
    norm_num
  have hsupportPerp
      (e : FABL.perpendicularSubspace E) :
      FABL.f₂Support e.1 ⊆ I := by
    exact
      FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
        I e.1 e.2
  have hweightPerp
      (e : FABL.perpendicularSubspace E) :
      (FABL.f₂Support e.1).card ≤ l := by
    calc
      (FABL.f₂Support e.1).card ≤ I.card :=
        Finset.card_le_card (hsupportPerp e)
      _ = n - m := hIcard
      _ ≤ l := hlevel
  have hright :
      (∑ e : FABL.perpendicularSubspace E, autocorrelation f e.1) =
        (2 : ℝ) ^ n := by
    rw [Finset.sum_eq_single
      (0 : FABL.perpendicularSubspace E)]
    · exact autocorrelation_zero f
    · intro e _he hene
      apply hpcZero e.1
      · intro hezero
        apply hene
        exact Subtype.ext hezero
      · exact hweightPerp e
    · intro hzero
      exact (hzero (Finset.mem_univ _)).elim
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) E 0 0
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  have hrelation :
      (∑ u : E, (walshTransform f u.1 : ℝ) ^ 2) =
        (Nat.card E : ℝ) *
          ∑ e : FABL.perpendicularSubspace E, autocorrelation f e.1 := by
    simpa using hpoisson
  rw [hleft, hright] at hrelation
  have hcardPositive : (0 : ℝ) < Nat.card E := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card E)
  have hpowPositive : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  nlinarith

end CryptBoolean
