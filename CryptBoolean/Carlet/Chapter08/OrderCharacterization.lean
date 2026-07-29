/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.PropagationCriteria
public import CryptBoolean.Carlet.Chapter04.SupportDualDistance

/-!
# Walsh characterization of propagation criteria of order

Carlet Proposition 36: extended propagation and propagation of order are
characterized by low-weight Walsh zeros of directional derivatives.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The Walsh transform of a derivative is Carlet's displayed signed
derivative character sum. -/
theorem walshTransform_booleanDerivative_eq_sum_bitSignInt
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) :
    walshTransform (FABL.booleanDerivative f a) b =
      ∑ x, bitSignInt
        (f x + f (x + a) + FABL.f₂DotProduct b x) := by
  rfl

private theorem f₂Support_card_pos_of_ne_zero
    (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    0 < (FABL.f₂Support a).card := by
  rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
  intro hsupport
  apply ha
  apply (FABL.f₂CubeEquivFinset n).injective
  change FABL.f₂Support a = FABL.f₂Support (0 : FABL.F₂Cube n)
  rw [hsupport]
  ext i
  simp [FABL.f₂Support]

/-- The zero-direction derivative has zero Walsh transform at every nonzero
frequency. -/
theorem walshTransform_booleanDerivative_zero_direction
    (f : BooleanFunction n) (b : FABL.F₂Cube n) (hb : b ≠ 0) :
    walshTransform (FABL.booleanDerivative f 0) b = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero,
    walshTransform_cast_eq_sum_realSignView_mul_character]
  calc
    ∑ x, realSignView (FABL.booleanDerivative f 0) x *
          FABL.vectorWalshCharacter b x =
        ∑ x, FABL.vectorWalshCharacter b x := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, FABL.booleanDerivative,
        ZModModule.add_self]
    _ = 0 := sum_vectorWalshCharacter_eq_zero b hb

/-- Carlet Proposition 36, extended form: `EPC(l)` of order `k` is equivalent
to the low-weight Walsh zeros of every directional derivative, including the
automatic boundary `a = 0`, `b ≠ 0`. -/
theorem satisfiesExtendedPropagationCriterion_iff_walshTransform_booleanDerivative_eq_zero
    (l k : ℕ) (f : BooleanFunction n) (hparameters : l + k ≤ n) :
    SatisfiesExtendedPropagationCriterion l k f ↔
      ∀ (a b : FABL.F₂Cube n),
        (FABL.f₂Support a).card ≤ l →
        (FABL.f₂Support b).card ≤ k →
        (a, b) ≠ (0, 0) →
          walshTransform (FABL.booleanDerivative f a) b = 0 := by
  constructor
  · intro hepc a b haweight hbweight hab
    by_cases ha : a = 0
    · subst a
      apply walshTransform_booleanDerivative_zero_direction
      intro hb
      apply hab
      simp [hb]
    · have hl : 0 < l :=
        (f₂Support_card_pos_of_ne_zero a ha).trans_le haweight
      have hn : 0 < n := by omega
      have hk : k < n := by omega
      exact
        (theorem_3_resilient_iff_walshTransform_eq_zero
          k (FABL.booleanDerivative f a) hn hk).mp
            (hepc a ha haweight) b hbweight
  · intro hzero a ha haweight
    have hl : 0 < l :=
      (f₂Support_card_pos_of_ne_zero a ha).trans_le haweight
    have hn : 0 < n := by omega
    have hk : k < n := by omega
    apply (theorem_3_resilient_iff_walshTransform_eq_zero
      k (FABL.booleanDerivative f a) hn hk).mpr
    intro b hbweight
    apply hzero a b haweight hbweight
    intro hab
    apply ha
    simpa using congrArg Prod.fst hab

private theorem satisfiesPropagationCriterionOfOrder_iff_nonzeroDerivativeWalsh
    (l k : ℕ) (f : BooleanFunction n) (hparameters : l + k ≤ n) :
    SatisfiesPropagationCriterionOfOrder l k f ↔
      ∀ (a : FABL.F₂Cube n), a ≠ 0 →
        (FABL.f₂Support a).card ≤ l →
          ∀ b : FABL.F₂Cube n,
            (FABL.f₂Support b).card ≤ k →
            Disjoint (FABL.f₂Support a) (FABL.f₂Support b) →
              walshTransform (FABL.booleanDerivative f a) b = 0 := by
  constructor
  · intro hpc a ha haweight b hbweight hdisjoint
    have hbsubset : FABL.f₂Support b ⊆ (FABL.f₂Support a)ᶜ := by
      intro i hiB
      rw [Finset.mem_compl]
      intro hiA
      exact Finset.disjoint_left.mp hdisjoint hiA hiB
    have hkavailable : k ≤ ((FABL.f₂Support a)ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨K, hbK, hKcomplement, hKcard⟩ :=
      Finset.exists_subsuperset_card_eq hbsubset hbweight hkavailable
    let J : Finset (Fin n) := Kᶜ
    have hfixed : Fintype.card (FABL.FixedIndex J) = k := by
      simp [J, FABL.FixedIndex, hKcard]
    have haJ : FABL.f₂Support a ⊆ J := by
      intro i hiA
      apply Finset.mem_compl.mpr
      intro hiK
      exact (Finset.mem_compl.mp (hKcomplement hiK)) hiA
    have hbJ : FABL.f₂Support b ⊆ Jᶜ := by
      simpa [J] using hbK
    have hrestrictions :
        ∀ z : FABL.FixedSignCube J,
          IsBalanced
            (coordinateRestriction (FABL.booleanDerivative f a) J z) := by
      intro z
      exact
        (satisfiesPropagationCriterionOfOrder_iff_derivativeRestrictions_balanced
          l k f).mp hpc a ha haweight J z hfixed haJ
    exact
      (all_coordinateRestrictions_balanced_iff_walshTransform_eq_zero
        (FABL.booleanDerivative f a) J).mp hrestrictions b hbJ
  · intro hzero
    apply
      (satisfiesPropagationCriterionOfOrder_iff_derivativeRestrictions_balanced
        l k f).mpr
    intro a ha haweight J z hfixed haJ
    have hJcard : Jᶜ.card = k := by
      rw [Finset.card_compl]
      simpa [FABL.FixedIndex] using hfixed
    have hrestrictions :
        ∀ z : FABL.FixedSignCube J,
          IsBalanced
            (coordinateRestriction (FABL.booleanDerivative f a) J z) := by
      apply
        (all_coordinateRestrictions_balanced_iff_walshTransform_eq_zero
          (FABL.booleanDerivative f a) J).mpr
      intro b hbJ
      apply hzero a ha haweight b
      · calc
          (FABL.f₂Support b).card ≤ Jᶜ.card :=
            Finset.card_le_card hbJ
          _ = k := hJcard
      · rw [Finset.disjoint_left]
        intro i hiA hiB
        exact (Finset.mem_compl.mp (hbJ hiB)) (haJ hiA)
    exact hrestrictions z

/-- Carlet Proposition 36, restriction form: `PC(l)` of order `k` is
equivalent to the same derivative Walsh zeros when the direction and frequency
have disjoint supports. The `a = 0`, `b ≠ 0` boundary is retained explicitly. -/
theorem satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
    (l k : ℕ) (f : BooleanFunction n) (hparameters : l + k ≤ n) :
    SatisfiesPropagationCriterionOfOrder l k f ↔
      ∀ (a b : FABL.F₂Cube n),
        (FABL.f₂Support a).card ≤ l →
        (FABL.f₂Support b).card ≤ k →
        (a, b) ≠ (0, 0) →
        Disjoint (FABL.f₂Support a) (FABL.f₂Support b) →
          walshTransform (FABL.booleanDerivative f a) b = 0 := by
  constructor
  · intro hpc a b haweight hbweight hab hdisjoint
    by_cases ha : a = 0
    · subst a
      apply walshTransform_booleanDerivative_zero_direction
      intro hb
      apply hab
      simp [hb]
    · exact
        (satisfiesPropagationCriterionOfOrder_iff_nonzeroDerivativeWalsh
          l k f hparameters).mp hpc
            a ha haweight b hbweight hdisjoint
  · intro hzero
    apply
      (satisfiesPropagationCriterionOfOrder_iff_nonzeroDerivativeWalsh
        l k f hparameters).mpr
    intro a ha haweight b hbweight hdisjoint
    apply hzero a b haweight hbweight
    · intro hab
      apply ha
      simpa using congrArg Prod.fst hab
    · exact hdisjoint

end CryptBoolean
