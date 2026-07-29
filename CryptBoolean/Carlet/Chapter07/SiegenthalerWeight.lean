/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.WalshDivisibility
public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree
public import CryptBoolean.Carlet.Chapter07.WalshDivisibility

/-!
# The weight-strengthened Siegenthaler bound

Carlet Chapter 7, footnote 47.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A correlation-immune Boolean function whose weight has one additional
factor of two satisfies the resilient form of Siegenthaler's degree bound. -/
theorem functionAlgebraicDegree_le_sub_sub_one_of_isCorrelationImmune_of_weight
    (f : BooleanFunction n) (m : ℕ) (hm : m < n)
    (hf : IsCorrelationImmune m f)
    (hweight : 2 ^ (m + 1) ∣ hammingWeight f) :
    FABL.functionAlgebraicDegree f ≤ n - m - 1 := by
  by_cases hinterior : m + 2 ≤ n
  · have hdiv :=
      two_pow_m_add_two_dvd_walshTransform_of_isCorrelationImmune_of_weight
        f m hinterior hf hweight
    have hdegree :=
      functionAlgebraicDegree_le_of_two_pow_dvd_walshTransform
        f (m + 2) (by omega) (by omega) hinterior hdiv
    omega
  · have hmEndpoint : m = n - 1 := by omega
    have hdegreeOne :
        FABL.functionAlgebraicDegree f ≤ 1 := by
      have hdegree :=
        functionAlgebraicDegree_le_sub_of_isCorrelationImmune f m hf hm
      omega
    obtain ⟨b, a, rfl⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one f hdegreeOne
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        have hzero :
            FABL.affineFunction 0 (0 : FABL.F₂Cube n) =
              (0 : BooleanFunction n) := by
          funext x
          simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
        rw [hzero, FABL.functionAlgebraicDegree_zero]
        omega
      · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
        subst b
        have hone :
            FABL.affineFunction 1 (0 : FABL.F₂Cube n) =
              (1 : BooleanFunction n) := by
          funext x
          simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
        rw [hone, FABL.functionAlgebraicDegree_one]
        omega
    · have hdiv :
          2 ^ n ∣ 2 ^ (n - 1) := by
        simpa [hmEndpoint, hammingWeight_affineFunction_of_ne_zero b a ha,
          show n - 1 + 1 = n by omega] using hweight
      have hexponents : n ≤ n - 1 :=
        (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdiv
      omega

end CryptBoolean
