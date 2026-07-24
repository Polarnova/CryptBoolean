/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightSpectrum
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightTwelve

/-!
# The low-weight spectrum used by the order-two moment argument

This module packages the minimum-distance and weight-ten exclusions into the
finite spectrum interface used to group the seventh and eighth moments.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Below weight sixteen, the only even weights in the codimension-three
dual code are `0, 8, 12, 14, 16`. -/
theorem hasOrderTwoLowWeightSpectrum (hn : 3 ≤ n) :
    HasOrderTwoLowWeightSpectrum n := by
  intro h hh heven hupper
  have hdual : h ∈ reedMuller (n - 3) n := by
    simpa only [orderTwoDualWords, Finset.mem_filter, Finset.mem_univ,
      true_and] using hh
  by_cases hzero : h = 0
  · left
    simp [hzero]
  · have hdegree : FABL.functionAlgebraicDegree h ≤ n - 3 := by
      simpa only [mem_reedMuller_iff] using hdual
    have hlower :=
      two_pow_sub_le_hammingWeight_of_degree_le h hdegree hzero
    have hexponent : n - (n - 3) = 3 := by omega
    rw [hexponent] at hlower
    norm_num at hlower
    have hnotTen :=
      hammingWeight_ne_ten_of_mem_reedMuller_codimension_three
        h hn hdual
    obtain ⟨k, hk⟩ := heven
    omega

end CryptBoolean
