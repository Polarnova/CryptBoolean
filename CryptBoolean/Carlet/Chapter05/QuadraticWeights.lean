/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.QuadraticRank

/-!
# Weights of quadratic Boolean functions
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance quadraticWeightSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

/-- A nonbalanced quadratic function has the kernel-determined Walsh square. -/
theorem walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hnotBalanced : ¬ IsBalanced f) :
    walshTransform f 0 ^ 2 =
      (2 : ℤ) ^ (n + Module.finrank FABL.𝔽₂ (linearKernel f)) := by
  classical
  have hconstant : ∀ a : linearKernel f, f a.1 = f 0 := by
    by_contra hnotConstant
    exact hnotBalanced
      ((isBalanced_iff_not_constant_on_linearKernel_of_degree_le_two
        f hdegree).mpr hnotConstant)
  have hrelation :=
    walshTransform_zero_sq_eq_two_pow_mul_sum_linearKernel f hdegree
  have hsum :
      (∑ a : linearKernel f,
          bitSignInt (FABL.booleanDerivative f a.1 0)) =
        (Fintype.card (linearKernel f) : ℤ) := by
    calc
      (∑ a : linearKernel f,
          bitSignInt (FABL.booleanDerivative f a.1 0)) =
          ∑ _a : linearKernel f, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        simp only [FABL.booleanDerivative, zero_add, hconstant a,
          ZModModule.add_self, bitSignInt]
        rfl
      _ = (Fintype.card (linearKernel f) : ℤ) := by simp
  have hcard : Fintype.card (linearKernel f) =
      2 ^ Module.finrank FABL.𝔽₂ (linearKernel f) := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := FABL.𝔽₂)
        (V := linearKernel f), Nat.card_zmod]
  rw [hsum, hcard] at hrelation
  simpa [pow_add] using hrelation

/-- The dimension plus the linear-kernel dimension is even in the
nonbalanced case of Carlet Theorem 4. -/
theorem even_dimension_add_finrank_linearKernel_of_not_balanced
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hnotBalanced : ¬ IsBalanced f) :
    Even (n + Module.finrank FABL.𝔽₂ (linearKernel f)) :=
  even_exponent_of_int_sq_eq_two_pow (walshTransform f 0)
    (n + Module.finrank FABL.𝔽₂ (linearKernel f))
    (walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
      f hdegree hnotBalanced)

/-- The nonbalanced weights in Carlet Theorem 4. -/
theorem quadratic_weight_eq_two_pow_sub_or_add
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hnotBalanced : ¬ IsBalanced f) :
    hammingWeight f =
        2 ^ (n - 1) -
          2 ^ ((n + Module.finrank FABL.𝔽₂ (linearKernel f)) / 2 - 1) ∨
      hammingWeight f =
        2 ^ (n - 1) +
          2 ^ ((n + Module.finrank FABL.𝔽₂ (linearKernel f)) / 2 - 1) := by
  let k := Module.finrank FABL.𝔽₂ (linearKernel f)
  have heven : Even (n + k) :=
    even_dimension_add_finrank_linearKernel_of_not_balanced
      f hdegree hnotBalanced
  obtain ⟨t, ht⟩ := heven
  have hhalf : (n + k) / 2 = t := by omega
  have htpos : 0 < t := by omega
  have hk : k ≤ n := by
    have h := Submodule.finrank_le (linearKernel f)
    simpa only [Module.finrank_pi, Fintype.card_fin] using h
  have htn : t ≤ n := by omega
  have hsq :=
    walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
      f hdegree hnotBalanced
  have hpowSquare : (2 : ℤ) ^ (n + k) = ((2 : ℤ) ^ t) ^ 2 := by
    rw [ht, pow_add, pow_two]
  rw [hpowSquare] at hsq
  have hwalsh : walshTransform f 0 = (2 : ℤ) ^ t ∨
      walshTransform f 0 = -((2 : ℤ) ^ t) :=
    eq_or_eq_neg_of_sq_eq_sq _ _ hsq
  have hzero := walshTransform_zero_eq_two_pow_sub_two_weight f
  have hnpow : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
    calc
      (2 : ℤ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by ring
  have htpow : (2 : ℤ) ^ t = 2 * (2 : ℤ) ^ (t - 1) := by
    calc
      (2 : ℤ) ^ t = 2 ^ ((t - 1) + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (t - 1) := by ring
  rw [show Module.finrank FABL.𝔽₂ (linearKernel f) = k by rfl,
    hhalf]
  rcases hwalsh with hpositive | hnegative
  · left
    have hweightInt : (hammingWeight f : ℤ) =
        (2 : ℤ) ^ (n - 1) - (2 : ℤ) ^ (t - 1) := by
      rw [hpositive, hnpow, htpow] at hzero
      omega
    have hpowle : 2 ^ (t - 1) ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hweightInt
  · right
    have hweightInt : (hammingWeight f : ℤ) =
        (2 : ℤ) ^ (n - 1) + (2 : ℤ) ^ (t - 1) := by
      rw [hnegative, hnpow, htpow] at hzero
      omega
    exact_mod_cast hweightInt

/-- Carlet Theorem 4, including balancedness, parity, and the two possible
nonbalanced weights. -/
theorem theorem_4_quadratic_weight
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (IsBalanced f ↔ ¬ ∀ a : linearKernel f, f a.1 = f 0) ∧
      (¬ IsBalanced f →
        Even (n + Module.finrank FABL.𝔽₂ (linearKernel f)) ∧
          (hammingWeight f =
              2 ^ (n - 1) -
                2 ^ ((n + Module.finrank FABL.𝔽₂ (linearKernel f)) / 2 - 1) ∨
            hammingWeight f =
              2 ^ (n - 1) +
                2 ^ ((n + Module.finrank FABL.𝔽₂ (linearKernel f)) / 2 - 1))) := by
  refine ⟨isBalanced_iff_not_constant_on_linearKernel_of_degree_le_two
    f hdegree, ?_⟩
  intro hnotBalanced
  exact ⟨even_dimension_add_finrank_linearKernel_of_not_balanced
      f hdegree hnotBalanced,
    quadratic_weight_eq_two_pow_sub_or_add f hn hdegree hnotBalanced⟩

end CryptBoolean
