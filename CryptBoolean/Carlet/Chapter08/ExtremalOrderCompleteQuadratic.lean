/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.QuadraticRank
public import CryptBoolean.Carlet.Chapter06.CompleteQuadratic
public import CryptBoolean.Carlet.Chapter08.OrderCharacterization

/-!
# Complete quadratic functions at extremal propagation order

The sufficient direction of Carlet's extremal high-order propagation
classification, together with affine-addition invariance at fixed order.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The polar frequency of the complete quadratic function is the total
coordinate sum plus the corresponding coordinate. -/
theorem completeQuadraticPolarFrequency_apply_eq_sum_add
    (a : FABL.F₂Cube n) (i : Fin n) :
    completeQuadraticPolarFrequency a i = (∑ j, a j) + a i := by
  classical
  have huniv :
      (∑ j : Fin n, a j) =
        a i + ∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j := by
    rw [← Finset.sum_add_sum_compl ({i} : Finset (Fin n))]
    simp
  rw [completeQuadraticPolarFrequency]
  calc
    (∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j) =
        (a i + a i) + ∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j := by
      rw [ZModModule.add_self, zero_add]
    _ = (a i + ∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j) + a i := by
      abel
    _ = (∑ j, a j) + a i := by rw [← huniv]

/-- Every derivative of the complete quadratic function is the affine
function whose linear part is its polar frequency. -/
theorem booleanDerivative_completeQuadraticBit_eq_affineFunction
    (a : FABL.F₂Cube n) :
    FABL.booleanDerivative
        (FABL.completeQuadraticBit : BooleanFunction n) a =
      FABL.affineFunction (FABL.completeQuadraticBit a)
        (completeQuadraticPolarFrequency a) := by
  funext x
  have hpolar :=
    quadraticPolarKernel_completeQuadraticBit_eq_dotProduct a x
  have hzero :
      FABL.booleanDerivative
          (FABL.completeQuadraticBit : BooleanFunction n) a 0 =
        FABL.completeQuadraticBit a := by
    simp [FABL.booleanDerivative, FABL.completeQuadraticBit]
  rw [quadraticPolarKernel, hzero] at hpolar
  change
    FABL.booleanDerivative
        (FABL.completeQuadraticBit : BooleanFunction n) a x =
      FABL.completeQuadraticBit a +
        FABL.f₂DotProduct (completeQuadraticPolarFrequency a) x
  calc
    FABL.booleanDerivative
        (FABL.completeQuadraticBit : BooleanFunction n) a x =
        (FABL.booleanDerivative
            (FABL.completeQuadraticBit : BooleanFunction n) a x +
          FABL.completeQuadraticBit a) + FABL.completeQuadraticBit a := by
            rw [add_assoc, ZModModule.add_self, add_zero]
    _ = FABL.f₂DotProduct (completeQuadraticPolarFrequency a) x +
        FABL.completeQuadraticBit a := by rw [hpolar]
    _ = FABL.completeQuadraticBit a +
        FABL.f₂DotProduct (completeQuadraticPolarFrequency a) x := add_comm _ _

/-- Disjoint directions and frequencies whose combined support omits a
coordinate cannot coincide through the complete-quadratic polar map. -/
theorem ne_completeQuadraticPolarFrequency_of_disjoint_of_support_card_add_lt
    (a b : FABL.F₂Cube n) (hab : (a, b) ≠ (0, 0))
    (hdisjoint : Disjoint (FABL.f₂Support a) (FABL.f₂Support b))
    (hcard : (FABL.f₂Support a).card + (FABL.f₂Support b).card < n) :
    b ≠ completeQuadraticPolarFrequency a := by
  intro hb
  by_cases ha : a = 0
  · subst a
    have hbzero : b = 0 := by
      rw [hb]
      funext i
      simp [completeQuadraticPolarFrequency]
    exact hab (by simp [hbzero])
  · let total : FABL.𝔽₂ := ∑ i, a i
    by_cases htotal : total = 0
    · have hfrequency : completeQuadraticPolarFrequency a = a := by
        funext i
        rw [completeQuadraticPolarFrequency_apply_eq_sum_add]
        change total + a i = a i
        rw [htotal, zero_add]
      have hself : Disjoint (FABL.f₂Support a) (FABL.f₂Support a) := by
        simpa [hb, hfrequency] using hdisjoint
      have hempty : FABL.f₂Support a = ∅ :=
        (Finset.disjoint_self_iff_empty (FABL.f₂Support a)).mp hself
      apply ha
      apply (FABL.f₂CubeEquivFinset n).injective
      change FABL.f₂Support a = FABL.f₂Support (0 : FABL.F₂Cube n)
      rw [hempty]
      simp [FABL.f₂Support]
    · have htotalOne : total = 1 := Fin.eq_one_of_ne_zero total htotal
      have hfrequency :
          completeQuadraticPolarFrequency a =
            FABL.binaryCubeComplement a := by
        funext i
        rw [completeQuadraticPolarFrequency_apply_eq_sum_add]
        change total + a i = FABL.binaryCubeComplement a i
        rw [htotalOne]
        simp [FABL.binaryCubeComplement, add_comm]
      have hsupport :
          FABL.f₂Support b = (FABL.f₂Support a)ᶜ := by
        rw [hb, hfrequency]
        ext i
        by_cases hi : a i = 0
        · simp [FABL.mem_f₂Support, FABL.binaryCubeComplement, hi]
        · have hiOne : a i = 1 := Fin.eq_one_of_ne_zero (a i) hi
          simp [FABL.mem_f₂Support, FABL.binaryCubeComplement, hiOne]
      have hacard : (FABL.f₂Support a).card ≤ n := by
        simpa using Finset.card_le_univ (FABL.f₂Support a)
      have hbcard :
          (FABL.f₂Support b).card =
            n - (FABL.f₂Support a).card := by
        rw [hsupport, Finset.card_compl]
        simp
      omega

private theorem booleanDerivative_add_affineFunction_eq_add_constantAffine
    (f : BooleanFunction n) (c : FABL.𝔽₂)
    (u a : FABL.F₂Cube n) :
    FABL.booleanDerivative (f + FABL.affineFunction c u) a =
      FABL.booleanDerivative f a +
        FABL.affineFunction (FABL.f₂DotProduct u a) 0 := by
  have hfunction :
      f + FABL.affineFunction c u =
        fun x ↦ f x + FABL.affineFunction c u x := by
    funext x
    rfl
  rw [hfunction]
  calc
    FABL.booleanDerivative
        (fun x ↦ f x + FABL.affineFunction c u x) a =
        fun x ↦ FABL.booleanDerivative f a x + FABL.f₂DotProduct u a := by
      exact booleanDerivative_add_affineFunction f c u a
    _ = FABL.booleanDerivative f a +
        FABL.affineFunction (FABL.f₂DotProduct u a) 0 := by
      funext x
      simp [FABL.affineFunction, FABL.f₂DotProduct]

/-- Binary differentiation commutes with translation of the input domain. -/
theorem booleanDerivative_domainTranslate
    (f : BooleanFunction n) (z a : FABL.F₂Cube n) :
    FABL.booleanDerivative (FABL.domainTranslate f z) a =
      FABL.domainTranslate (FABL.booleanDerivative f a) z := by
  funext x
  simp only [FABL.booleanDerivative, FABL.domainTranslate_apply]
  congr 1
  abel_nf

/-- Translating the input preserves propagation criteria at every fixed
coordinate order in the nonvacuous Walsh-characterization range. -/
theorem satisfiesPropagationCriterionOfOrder_domainTranslate_iff
    (l k : ℕ) (f : BooleanFunction n) (z : FABL.F₂Cube n)
    (hparameters : l + k ≤ n) :
    SatisfiesPropagationCriterionOfOrder l k (FABL.domainTranslate f z) ↔
      SatisfiesPropagationCriterionOfOrder l k f := by
  rw [satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k (FABL.domainTranslate f z) hparameters,
    satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k f hparameters]
  constructor
  · intro h a b ha hb hab hdisjoint
    have hzero := h a b ha hb hab hdisjoint
    rw [booleanDerivative_domainTranslate] at hzero
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero]
    have hzeroReal :
        (walshTransform
          (FABL.domainTranslate (FABL.booleanDerivative f a) z) b : ℝ) = 0 := by
      exact_mod_cast hzero
    rw [walshTransform_domainTranslate_cast] at hzeroReal
    rcases FABL.vectorWalshCharacter_eq_neg_one_or_one b z with hsign | hsign
    · simpa [hsign] using hzeroReal
    · simpa [hsign] using hzeroReal
  · intro h a b ha hb hab hdisjoint
    have hzero := h a b ha hb hab hdisjoint
    rw [booleanDerivative_domainTranslate]
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero, walshTransform_domainTranslate_cast]
    have hzeroReal : (walshTransform (FABL.booleanDerivative f a) b : ℝ) = 0 := by
      exact_mod_cast hzero
    rw [hzeroReal, mul_zero]

/-- Adding an affine function preserves propagation criteria at every fixed
order in the nonvacuous Walsh-characterization range. -/
theorem satisfiesPropagationCriterionOfOrder_add_affineFunction_iff
    (l k : ℕ) (f : BooleanFunction n) (c : FABL.𝔽₂)
    (u : FABL.F₂Cube n) (hparameters : l + k ≤ n) :
    SatisfiesPropagationCriterionOfOrder l k
        (f + FABL.affineFunction c u) ↔
      SatisfiesPropagationCriterionOfOrder l k f := by
  rw [satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k (f + FABL.affineFunction c u) hparameters,
    satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k f hparameters]
  constructor
  · intro h a b ha hb hab hdisjoint
    have hzero := h a b ha hb hab hdisjoint
    rw [booleanDerivative_add_affineFunction_eq_add_constantAffine] at hzero
    rw [walshTransform_add_affineFunction] at hzero
    simp only [add_zero] at hzero
    have hsign : bitSignInt (FABL.f₂DotProduct u a) ≠ 0 := by
      by_cases hdot : FABL.f₂DotProduct u a = 0
      · simp [hdot, bitSignInt]
      · have hdotOne :=
          Fin.eq_one_of_ne_zero (FABL.f₂DotProduct u a) hdot
        simp [hdotOne, bitSignInt]
    exact (mul_eq_zero.mp hzero).resolve_left hsign
  · intro h a b ha hb hab hdisjoint
    have hzero := h a b ha hb hab hdisjoint
    rw [booleanDerivative_add_affineFunction_eq_add_constantAffine]
    rw [walshTransform_add_affineFunction]
    simp only [add_zero, hzero, mul_zero]

/-- The complete quadratic function satisfies `PC(l)` of order `k` whenever
the eligible direction and frequency supports cannot cover every coordinate. -/
theorem satisfiesPropagationCriterionOfOrder_completeQuadraticBit
    (l k : ℕ) (hparameters : l + k < n) :
    SatisfiesPropagationCriterionOfOrder l k
      (FABL.completeQuadraticBit : BooleanFunction n) := by
  apply
    (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
      l k (FABL.completeQuadraticBit : BooleanFunction n)
      hparameters.le).2
  intro a b ha hb hab hdisjoint
  rw [booleanDerivative_completeQuadraticBit_eq_affineFunction,
    walshTransform_affineFunction]
  apply if_neg
  apply ne_completeQuadraticPolarFrequency_of_disjoint_of_support_card_add_lt
    a b hab hdisjoint
  omega

/-- Every affine translate of the complete quadratic function satisfies the
same order propagation criterion below the support-covering boundary. -/
theorem satisfiesPropagationCriterionOfOrder_completeQuadraticBit_add_affineFunction
    (l k : ℕ) (c : FABL.𝔽₂) (u : FABL.F₂Cube n)
    (hparameters : l + k < n) :
    SatisfiesPropagationCriterionOfOrder l k
      ((FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u) := by
  exact
    (satisfiesPropagationCriterionOfOrder_add_affineFunction_iff
      l k (FABL.completeQuadraticBit : BooleanFunction n) c u
      hparameters.le).2
        (satisfiesPropagationCriterionOfOrder_completeQuadraticBit
          l k hparameters)

/-- The complete quadratic function plus an arbitrary affine function
satisfies Carlet's extremal criterion `PC(l)` of order `n-l-2`. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_completeQuadraticBit_add_affineFunction
    (l : ℕ) (c : FABL.𝔽₂) (u : FABL.F₂Cube n)
    (hl : l + 2 ≤ n) :
    SatisfiesPropagationCriterionOfOrder l (n - l - 2)
      ((FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u) := by
  apply satisfiesPropagationCriterionOfOrder_completeQuadraticBit_add_affineFunction
  omega

end CryptBoolean
