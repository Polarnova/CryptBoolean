/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.SupportCode

/-!
# Alternate support-code claims

Carlet reports two further support-code characterizations after Proposition 16.
Finite four-variable examples show that both converses require hypotheses absent
from the printed statements.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The nonzero words of the support code have exactly the two distinct
weights `r` and `s`. -/
def SupportCodeHasExactlyTwoNonzeroWeightValues
    (f : BooleanFunction n) (r s : ℕ) : Prop :=
  r ≠ s ∧ 0 < r ∧ 0 < s ∧
    (∀ v : FABL.F₂Cube n, supportCodewordWeight f v ≠ 0 →
      supportCodewordWeight f v = r ∨ supportCodewordWeight f v = s) ∧
    (∃ v : FABL.F₂Cube n, supportCodewordWeight f v = r) ∧
    ∃ v : FABL.F₂Cube n, supportCodewordWeight f v = s

/-- The first reported alternative: full dimension and two nonzero weights
whose sum is the code length. -/
def HasSupportCodeWeightSumAlternative (f : BooleanFunction n) : Prop :=
  Module.finrank FABL.𝔽₂ (supportCode f) = n ∧
    ∃ r s : ℕ,
      SupportCodeHasExactlyTwoNonzeroWeightValues f r s ∧
        r + s = hammingWeight f

/-- The second reported alternative: even length and two nonzero weights, one
of which is `2^(n-2)`. -/
def HasSupportCodeEvenLengthQuarterWeightAlternative
    (f : BooleanFunction n) : Prop :=
  Even (hammingWeight f) ∧
    ∃ r s : ℕ,
      SupportCodeHasExactlyTwoNonzeroWeightValues f r s ∧
        (r = 2 ^ (n - 2) ∨ s = 2 ^ (n - 2))

/-- The complement of one nonzero point in the four-dimensional cube. -/
def supportCodeWeightSumCounterexample : BooleanFunction 4 :=
  fun x ↦ if x = ![1, 0, 0, 0] then 0 else 1

/-- A nonconstant linear function in the four-dimensional cube. -/
def supportCodeQuarterWeightCounterexample : BooleanFunction 4 :=
  fun x ↦ x 2 + x 3

private theorem hammingWeight_supportCodeWeightSumCounterexample :
    hammingWeight supportCodeWeightSumCounterexample = 15 := by
  decide +revert

private theorem supportCodeMap_supportCodeWeightSumCounterexample_injective :
    Function.Injective (supportCodeMap supportCodeWeightSumCounterexample) := by
  decide +revert

private theorem supportCodeWeightSumCounterexample_two_weights :
    SupportCodeHasExactlyTwoNonzeroWeightValues
      supportCodeWeightSumCounterexample 7 8 := by
  rw [SupportCodeHasExactlyTwoNonzeroWeightValues]
  decide +revert

private theorem hammingWeight_supportCodeQuarterWeightCounterexample :
    hammingWeight supportCodeQuarterWeightCounterexample = 8 := by
  decide +revert

private theorem supportCodeQuarterWeightCounterexample_two_weights :
    SupportCodeHasExactlyTwoNonzeroWeightValues
      supportCodeQuarterWeightCounterexample 4 8 := by
  rw [SupportCodeHasExactlyTwoNonzeroWeightValues]
  decide +revert

private theorem not_isBent_supportCodeWeightSumCounterexample :
    ¬ IsBent supportCodeWeightSumCounterexample := by
  intro hf
  have hwalsh := natAbs_walshTransform_eq_two_pow_half_of_isBent
    supportCodeWeightSumCounterexample hf 0
  rw [walshTransform_zero_eq_two_pow_sub_two_weight,
    hammingWeight_supportCodeWeightSumCounterexample] at hwalsh
  norm_num at hwalsh

private theorem not_isBent_supportCodeQuarterWeightCounterexample :
    ¬ IsBent supportCodeQuarterWeightCounterexample := by
  intro hf
  have hwalsh := natAbs_walshTransform_eq_two_pow_half_of_isBent
    supportCodeQuarterWeightCounterexample hf 0
  rw [walshTransform_zero_eq_two_pow_sub_two_weight,
    hammingWeight_supportCodeQuarterWeightCounterexample] at hwalsh
  norm_num at hwalsh

/-- Full dimension and two distinct nonzero weights summing to the support
size do not characterize bentness without an additional hypothesis. -/
theorem supportCodeWeightSumAlternative_not_characterize_bent :
    HasSupportCodeWeightSumAlternative supportCodeWeightSumCounterexample ∧
      ¬ IsBent supportCodeWeightSumCounterexample := by
  refine ⟨⟨?_, 7, 8, supportCodeWeightSumCounterexample_two_weights, ?_⟩,
    not_isBent_supportCodeWeightSumCounterexample⟩
  · exact (finrank_supportCode_eq_n_iff_injective _).2
      supportCodeMap_supportCodeWeightSumCounterexample_injective
  · rw [hammingWeight_supportCodeWeightSumCounterexample]

/-- Even length and two distinct nonzero weights including `2^(n-2)` do not
characterize bentness without an additional hypothesis. -/
theorem supportCodeEvenLengthQuarterWeightAlternative_not_characterize_bent :
    HasSupportCodeEvenLengthQuarterWeightAlternative
        supportCodeQuarterWeightCounterexample ∧
      ¬ IsBent supportCodeQuarterWeightCounterexample := by
  refine ⟨⟨?_, 4, 8, supportCodeQuarterWeightCounterexample_two_weights, ?_⟩,
    not_isBent_supportCodeQuarterWeightCounterexample⟩
  · rw [hammingWeight_supportCodeQuarterWeightCounterexample]
    exact even_iff_two_dvd.mpr (by norm_num)
  · left
    norm_num

end CryptBoolean
