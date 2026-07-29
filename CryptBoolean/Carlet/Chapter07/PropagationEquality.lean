/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.LinearStructureSpectrum
public import CryptBoolean.Carlet.Chapter05.QuadraticRank
public import CryptBoolean.Carlet.Chapter07.PropagationTradeoff

import FABL.Chapter05.DegreeOneWeight

/-!
# Equality in the resiliency--propagation tradeoff

The equality classification cited by Carlet in Section 7.4.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance propagationEqualitySubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

private theorem f₂Support_f₂CubeOfFinset
    (I : Finset (Fin n)) :
    FABL.f₂Support (FABL.f₂CubeOfFinset I) = I :=
  (FABL.f₂CubeEquivFinset n).right_inv I

private theorem f₂CubeOfFinset_ne_zero_of_nonempty
    {I : Finset (Fin n)} (hI : I.Nonempty) :
    FABL.f₂CubeOfFinset I ≠ 0 := by
  obtain ⟨i, hi⟩ := hI
  intro hzero
  have hvalue := congrFun hzero i
  simp [FABL.f₂CubeOfFinset_apply, hi] at hvalue

private theorem booleanDerivative_f₂CubeOfFinset_eq_one_of_tradeoff_equality
    (f : BooleanFunction n) (m l : ℕ) (hl : 0 < l)
    (hresilient : IsResilient m f)
    (hpc : SatisfiesPropagationCriterion l f)
    (hequality : m + l = n - 1)
    (I : Finset (Fin n)) (hIcard : I.card = l + 1) :
    FABL.booleanDerivative f (FABL.f₂CubeOfFinset I) = 1 := by
  classical
  have hn : 0 < n := by omega
  have hm : m < n := by omega
  have hIle : I.card ≤ n := by
    simpa using I.card_le_univ
  let E : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.F₂DecisionTree.coordinateZeroSubspace I
  have hwalshZero :=
    theorem_3_resilient_iff_walshTransform_eq_zero
      m f hn hm |>.mp hresilient
  have hpcZero :=
    satisfiesPropagationCriterion_iff_autocorrelation_eq_zero l f |>.mp hpc
  have hleft :
      (∑ u : E, (walshTransform f u.1 : ℝ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro u _hu
    have husupport : FABL.f₂Support u.1 ⊆ Iᶜ := by
      intro i hi
      rw [Finset.mem_compl]
      intro hiI
      have hui :
          u.1 i = 0 :=
        (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff I u.1).mp
          u.2 i hiI
      exact (FABL.mem_f₂Support u.1 i).mp hi hui
    have huweight : (FABL.f₂Support u.1).card ≤ m := by
      have hle := Finset.card_le_card husupport
      rw [Finset.card_compl, Fintype.card_fin, hIcard] at hle
      omega
    rw [hwalshZero u.1 huweight]
    norm_num
  have hvSupport :
      FABL.f₂Support (FABL.f₂CubeOfFinset I) ⊆ I := by
    rw [f₂Support_f₂CubeOfFinset I]
  have hvMem :
      FABL.f₂CubeOfFinset I ∈ FABL.perpendicularSubspace E := by
    exact
      (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
        I (FABL.f₂CubeOfFinset I)).2 hvSupport
  let v : FABL.perpendicularSubspace E :=
    ⟨FABL.f₂CubeOfFinset I, hvMem⟩
  have hvNe : v ≠ 0 := by
    intro hzero
    exact
      f₂CubeOfFinset_ne_zero_of_nonempty
        (Finset.card_pos.mp (by omega : 0 < I.card))
        (congrArg Subtype.val hzero)
  have hzeroNe : (0 : FABL.perpendicularSubspace E) ≠ v :=
    Ne.symm hvNe
  have hright :
      (∑ e : FABL.perpendicularSubspace E, autocorrelation f e.1) =
        (2 : ℝ) ^ n + autocorrelation f v.1 := by
    calc
      (∑ e : FABL.perpendicularSubspace E, autocorrelation f e.1) =
          ∑ e : FABL.perpendicularSubspace E,
            ((if e = 0 then (2 : ℝ) ^ n else 0) +
              (if e = v then autocorrelation f v.1 else 0)) := by
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hezero : e = 0
        · subst e
          simp [autocorrelation_zero, hzeroNe]
        · by_cases hev : e = v
          · subst e
            simp [hvNe]
          · simp only [if_neg hezero, if_neg hev, zero_add]
            apply hpcZero e.1
            · intro heval
              exact hezero (Subtype.ext heval)
            · have hesupport :
                  FABL.f₂Support e.1 ⊆ I :=
                FABL.F₂DecisionTree.f₂Support_subset_of_mem_perpendicular_coordinateZeroSubspace
                  I e.1 e.2
              have hproper :
                  FABL.f₂Support e.1 ⊂ I := by
                refine (Finset.ssubset_iff_subset_ne).2 ⟨hesupport, ?_⟩
                intro heq
                apply hev
                apply Subtype.ext
                apply (FABL.f₂CubeEquivFinset n).injective
                change FABL.f₂Support e.1 = FABL.f₂Support v.1
                rw [show v.1 = FABL.f₂CubeOfFinset I from rfl,
                  f₂Support_f₂CubeOfFinset I]
                exact heq
              have hcardLt :=
                Finset.card_lt_card hproper
              omega
      _ = (2 : ℝ) ^ n + autocorrelation f v.1 := by
        rw [Finset.sum_add_distrib]
        simp
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
  have hautocorrelation :
      autocorrelation f v.1 = -((2 : ℝ) ^ n) := by
    nlinarith
  exact
    (autocorrelation_eq_neg_two_pow_iff_derivative_eq_one f v.1).mp
      hautocorrelation

private theorem resilient_propagation_equality_m_eq_zero
    (f : BooleanFunction n) (m l : ℕ) (hl : 0 < l)
    (hresilient : IsResilient m f)
    (hpc : SatisfiesPropagationCriterion l f)
    (hequality : m + l = n - 1) :
    m = 0 := by
  classical
  by_contra hm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hn : 0 < n := by omega
  have hcapacity : l + 2 ≤ n := by omega
  let a : Fin n := ⟨l, by omega⟩
  let b : Fin n := ⟨l + 1, by omega⟩
  let K : Finset (Fin n) := Finset.Iio a
  let I : Finset (Fin n) := insert a K
  let J : Finset (Fin n) := insert b K
  have hab : a ≠ b := by
    intro hab
    have hval := congrArg Fin.val hab
    simp [a, b] at hval
  have haK : a ∉ K := by
    simp [K]
  have hbK : b ∉ K := by
    simp [K, a, b]
  have hKcard : K.card = l := by
    simp [K, a]
  have hIcard : I.card = l + 1 := by
    simp [I, haK, hKcard]
  have hJcard : J.card = l + 1 := by
    simp [J, hbK, hKcard]
  have hI :=
    booleanDerivative_f₂CubeOfFinset_eq_one_of_tradeoff_equality
      f m l hl hresilient hpc hequality I hIcard
  have hJ :=
    booleanDerivative_f₂CubeOfFinset_eq_one_of_tradeoff_equality
      f m l hl hresilient hpc hequality J hJcard
  have hsum :
      FABL.f₂CubeOfFinset I + FABL.f₂CubeOfFinset J =
        FABL.f₂CubeOfFinset {a, b} := by
    funext q
    by_cases hqK : q ∈ K
    · have hqa : q ≠ a := by
        intro hqa
        subst q
        exact haK hqK
      have hqb : q ≠ b := by
        intro hqb
        subst q
        exact hbK hqK
      simp [FABL.f₂CubeOfFinset_apply, I, J, hqK, hqa, hqb,
        ZModModule.add_self]
    · by_cases hqa : q = a
      · subst q
        simp [FABL.f₂CubeOfFinset_apply, I, J, haK, hab]
      · by_cases hqb : q = b
        · subst q
          simp [FABL.f₂CubeOfFinset_apply, I, J, hbK, Ne.symm hab]
        · simp [FABL.f₂CubeOfFinset_apply, I, J, hqK, hqa, hqb]
  have hderivativeZero :
      FABL.booleanDerivative f (FABL.f₂CubeOfFinset {a, b}) = 0 := by
    rw [← hsum]
    funext x
    rw [booleanDerivative_add_direction, hI, hJ]
    exact ZModModule.add_self 1
  by_cases hlOne : l = 1
  · have hpairCard : ({a, b} : Finset (Fin n)).card = l + 1 := by
      simp [hab, hlOne]
    have hderivativeOne :=
      booleanDerivative_f₂CubeOfFinset_eq_one_of_tradeoff_equality
        f m l hl hresilient hpc hequality ({a, b} : Finset (Fin n))
          hpairCard
    have hvalue := congrFun (hderivativeZero.symm.trans hderivativeOne) 0
    simp at hvalue
  · have htwoLe : 2 ≤ l := by omega
    have hpairSupport :
        FABL.f₂Support (FABL.f₂CubeOfFinset {a, b}) = {a, b} :=
      f₂Support_f₂CubeOfFinset {a, b}
    have hpairNe : FABL.f₂CubeOfFinset ({a, b} : Finset (Fin n)) ≠ 0 :=
      f₂CubeOfFinset_ne_zero_of_nonempty (by simp)
    have hpcZero :=
      satisfiesPropagationCriterion_iff_autocorrelation_eq_zero l f |>.mp hpc
    have hautocorrelationZero :
        autocorrelation f (FABL.f₂CubeOfFinset {a, b}) = 0 := by
      apply hpcZero _ hpairNe
      rw [hpairSupport]
      simp [hab]
      omega
    have hautocorrelationPow :
        autocorrelation f (FABL.f₂CubeOfFinset {a, b}) = (2 : ℝ) ^ n :=
      by
        rw [autocorrelation_eq_two_pow_sub_two_derivative_weight,
          hderivativeZero]
        simp
    rw [hautocorrelationZero] at hautocorrelationPow
    have hpowPositive : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    linarith

/-- Equality in the resiliency--propagation tradeoff at positive propagation
order is possible only in odd dimension, with balancedness and `PC(n-1)`. -/
theorem resilient_propagationCriterion_equality_classification
    (f : BooleanFunction n) (m l : ℕ) (hl : 0 < l)
    (hresilient : IsResilient m f)
    (hpc : SatisfiesPropagationCriterion l f)
    (hequality : m + l = n - 1) :
    Odd n ∧ l = n - 1 ∧ m = 0 := by
  classical
  have hn : 0 < n := by omega
  have hm : m = 0 :=
    resilient_propagation_equality_m_eq_zero
      f m l hl hresilient hpc hequality
  have hlEq : l = n - 1 := by omega
  let v : FABL.F₂Cube n :=
    FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))
  have hvNe : v ≠ 0 := by
    apply f₂CubeOfFinset_ne_zero_of_nonempty
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hzeroNe : (0 : FABL.F₂Cube n) ≠ v := Ne.symm hvNe
  have hunivCard :
      (Finset.univ : Finset (Fin n)).card = l + 1 := by
    simp
    omega
  have hvDerivative : FABL.booleanDerivative f v = 1 := by
    exact
      booleanDerivative_f₂CubeOfFinset_eq_one_of_tradeoff_equality
        f m l hl hresilient hpc hequality Finset.univ hunivCard
  have hvAutocorrelation : autocorrelation f v = -((2 : ℝ) ^ n) :=
    (autocorrelation_eq_neg_two_pow_iff_derivative_eq_one f v).2
      hvDerivative
  have hpcZero :=
    satisfiesPropagationCriterion_iff_autocorrelation_eq_zero l f |>.mp hpc
  have hautocorrelation :
      autocorrelation f = fun a ↦
        if a = 0 then (2 : ℝ) ^ n
        else if a = v then -((2 : ℝ) ^ n) else 0 := by
    funext a
    by_cases haZero : a = 0
    · subst a
      simp [autocorrelation_zero]
    · by_cases haFull : a = v
      · subst a
        simp [hvNe, hvAutocorrelation]
      · rw [if_neg haZero, if_neg haFull]
        apply hpcZero a haZero
        have hcardLe : (FABL.f₂Support a).card ≤ n := by
          calc
            (FABL.f₂Support a).card ≤
                (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
            _ = n := by simp
        have hcardNe : (FABL.f₂Support a).card ≠ n := by
          intro hcard
          have hsupport : FABL.f₂Support a = Finset.univ := by
            apply Finset.eq_univ_of_card
            simpa using hcard
          apply haFull
          apply (FABL.f₂CubeEquivFinset n).injective
          change FABL.f₂Support a = FABL.f₂Support v
          rw [show v = FABL.f₂CubeOfFinset Finset.univ from rfl,
            f₂Support_f₂CubeOfFinset Finset.univ]
          exact hsupport
        rw [hlEq]
        omega
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  have huComplement : u ∉ walshHyperplane v := by
    have hsupport :=
      (booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl
        f v hvNe).mp hvDerivative
    exact hsupport ((mem_walshSupport f u).2 hu)
  have hdotNe : FABL.f₂DotProduct u v ≠ 0 := by
    intro hdot
    exact huComplement ((mem_walshHyperplane_iff v u).2 hdot)
  have hdot : FABL.f₂DotProduct u v = 1 :=
    Fin.eq_one_of_ne_zero _ hdotNe
  have hcharacter : FABL.vectorWalshCharacter u v = (-1 : ℝ) := by
    rw [FABL.vectorWalshCharacter_apply, hdot, FABL.binarySign_one]
  have hWalshReal :
      (walshTransform f u : ℝ) ^ 2 = (2 : ℝ) ^ (n + 1) := by
    calc
      (walshTransform f u : ℝ) ^ 2 =
          rawFourierTransform (autocorrelation f) u :=
        (rawFourierTransform_autocorrelation f u).symm
      _ = (2 : ℝ) ^ (n + 1) := by
        rw [rawFourierTransform, hautocorrelation]
        change
          (∑ x, (if x = 0 then (2 : ℝ) ^ n
            else if x = v then -((2 : ℝ) ^ n) else 0) *
              FABL.vectorWalshCharacter u x) =
            (2 : ℝ) ^ (n + 1)
        calc
          (∑ x, (if x = 0 then (2 : ℝ) ^ n
              else if x = v then -((2 : ℝ) ^ n) else 0) *
                FABL.vectorWalshCharacter u x) =
              ∑ x, (
                (if x = 0 then
                    (2 : ℝ) ^ n * FABL.vectorWalshCharacter u x else 0) +
                (if x = v then
                    -((2 : ℝ) ^ n) * FABL.vectorWalshCharacter u x else 0)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hxZero : x = 0
            · subst x
              simp [hzeroNe]
            · simp [hxZero]
          _ = (2 : ℝ) ^ n * FABL.vectorWalshCharacter u 0 +
                -((2 : ℝ) ^ n) * FABL.vectorWalshCharacter u v := by
            rw [Finset.sum_add_distrib,
              Fintype.sum_ite_eq', Fintype.sum_ite_eq']
          _ = (2 : ℝ) ^ (n + 1) := by
            simp [hcharacter, pow_succ]
            ring
  have hWalshInt :
      walshTransform f u ^ 2 = (2 : ℤ) ^ (n + 1) := by
    exact_mod_cast hWalshReal
  have heven : Even (n + 1) :=
    even_exponent_of_int_sq_eq_two_pow
      (walshTransform f u) (n + 1) hWalshInt
  have hnOdd : Odd n := by
    simpa [Nat.even_add_one, Nat.not_even_iff_odd] using heven
  exact ⟨hnOdd, hlEq, hm⟩

end CryptBoolean
