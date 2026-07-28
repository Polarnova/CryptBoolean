/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.CoveringSequences
public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree

/-!
# McEliece--Ax divisibility for Boolean character sums

The character sum of a positive-degree Boolean polynomial in `n` variables
is divisible by the power of two whose exponent is the ceiling of `n` by
the algebraic degree.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem bitSignInt_finset_sum {α : Type*}
    (s : Finset α) (g : α → FABL.𝔽₂) :
    bitSignInt (∑ i ∈ s, g i) = ∏ i ∈ s, bitSignInt (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bitSignInt]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, bitSignInt_add, ih]

private theorem bitSignInt_anfEval_eq_prod
    (c : FABL.ANFCoefficients n) (x : FABL.F₂Cube n) :
    bitSignInt (FABL.anfEval c x) =
      ∏ S ∈ FABL.anfSupport c, bitSignInt (FABL.anfMonomial S x) := by
  classical
  rw [FABL.anfEval]
  have hsum :
      (∑ S : Finset (Fin n), c S * FABL.anfMonomial S x) =
        ∑ S ∈ FABL.anfSupport c, FABL.anfMonomial S x := by
    rw [FABL.anfSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _hS
    by_cases hc : c S = 0
    · simp [hc]
    · have hcOne : c S = 1 := Fin.eq_one_of_ne_zero (c S) hc
      simp [hcOne]
  rw [hsum, bitSignInt_finset_sum]

private theorem bitSignInt_anfEval_eq_powersetSum
    (c : FABL.ANFCoefficients n) (x : FABL.F₂Cube n) :
    bitSignInt (FABL.anfEval c x) =
      ∑ B ∈ (FABL.anfSupport c).powerset,
        (-2 : ℤ) ^ B.card *
          ∏ S ∈ B, bitValueInt (FABL.anfMonomial S x) := by
  classical
  rw [bitSignInt_anfEval_eq_prod]
  simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt]
  conv_lhs =>
    enter [2, S]
    rw [show 1 - 2 * bitValueInt (FABL.anfMonomial S x) =
      1 + (-2) * bitValueInt (FABL.anfMonomial S x) by ring]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro B _hB
  rw [Finset.prod_mul_distrib, Finset.prod_const]

private theorem prod_bitValueInt_anfMonomial_f₂CubeOfFinset
    (B : Finset (Finset (Fin n))) (U : Finset (Fin n)) :
    (∏ S ∈ B,
        bitValueInt (FABL.anfMonomial S (FABL.f₂CubeOfFinset U))) =
      if B.biUnion id ⊆ U then 1 else 0 := by
  classical
  simp_rw [FABL.anfMonomial_f₂CubeOfFinset]
  have hbit (T : Finset (Fin n)) :
      bitValueInt (if T ⊆ U then 1 else 0) =
        if T ⊆ U then 1 else 0 := by
    by_cases hT : T ⊆ U <;> simp [hT, bitValueInt]
  simp_rw [hbit]
  rw [Finset.prod_boole]
  by_cases hU : B.biUnion id ⊆ U
  · rw [if_pos hU, if_pos]
    exact Finset.biUnion_subset.mp hU
  · rw [if_neg hU, if_neg]
    intro hAll
    exact hU (Finset.biUnion_subset.mpr hAll)

private theorem sum_prod_bitValueInt_anfMonomial
    (B : Finset (Finset (Fin n))) :
    (∑ x : FABL.F₂Cube n,
        ∏ S ∈ B, bitValueInt (FABL.anfMonomial S x)) =
      (2 : ℤ) ^ (n - (B.biUnion id).card) := by
  classical
  calc
    (∑ x : FABL.F₂Cube n,
        ∏ S ∈ B, bitValueInt (FABL.anfMonomial S x)) =
        ∑ U : Finset (Fin n),
          ∏ S ∈ B,
            bitValueInt (FABL.anfMonomial S (FABL.f₂CubeOfFinset U)) := by
      apply Fintype.sum_equiv (FABL.f₂CubeEquivFinset n)
      intro x
      have hx : FABL.f₂CubeOfFinset (FABL.f₂Support x) = x := by
        simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
      simp only [FABL.f₂CubeEquivFinset_apply, hx]
    _ = ∑ U : Finset (Fin n),
          if B.biUnion id ⊆ U then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro U _hU
      exact prod_bitValueInt_anfMonomial_f₂CubeOfFinset B U
    _ = ((Finset.Icc (B.biUnion id) Finset.univ).card : ℤ) := by
      rw [Finset.sum_boole]
      have hfilter :
          Finset.univ.filter (fun U : Finset (Fin n) ↦ B.biUnion id ⊆ U) =
            Finset.Icc (B.biUnion id) Finset.univ := by
        ext U
        simp [Finset.mem_Icc]
      rw [hfilter]
    _ = (2 : ℤ) ^ (n - (B.biUnion id).card) := by
      rw [Finset.card_Icc_finset (Finset.subset_univ _)]
      simp

private theorem ceilDiv_le_card_add_codim_biUnion
    (B : Finset (Finset (Fin n))) (d : ℕ) (hd : 0 < d)
    (hcard : ∀ S ∈ B, S.card ≤ d) :
    n ⌈/⌉ d ≤ B.card + (n - (B.biUnion id).card) := by
  classical
  let u := (B.biUnion id).card
  let k := B.card
  have hu : u ≤ n := by
    dsimp [u]
    simpa using Finset.card_le_univ (B.biUnion id)
  have hud : u ≤ d * k := by
    dsimp [u, k]
    simpa [Nat.mul_comm] using
      (Finset.card_biUnion_le_card_mul B id d hcard)
  rw [ceilDiv_le_iff_le_mul hd]
  calc
    n = u + (n - u) := (Nat.add_sub_of_le hu).symm
    _ ≤ d * k + d * (n - u) := Nat.add_le_add hud (by
      simpa using Nat.mul_le_mul_right (n - u)
        (Nat.one_le_iff_ne_zero.mpr hd.ne'))
    _ = d * (k + (n - u)) := by ring

private theorem two_pow_ceilDiv_dvd_powersetTerm
    (B : Finset (Finset (Fin n))) (d : ℕ) (hd : 0 < d)
    (hcard : ∀ S ∈ B, S.card ≤ d) :
    (2 : ℤ) ^ (n ⌈/⌉ d) ∣
      (-2 : ℤ) ^ B.card * (2 : ℤ) ^ (n - (B.biUnion id).card) := by
  classical
  have hexponent := ceilDiv_le_card_add_codim_biUnion B d hd hcard
  apply (pow_dvd_pow (2 : ℤ) hexponent).trans
  refine ⟨(-1 : ℤ) ^ B.card, ?_⟩
  rw [pow_add]
  calc
    (-2 : ℤ) ^ B.card * (2 : ℤ) ^ (n - (B.biUnion id).card) =
        ((-1 : ℤ) ^ B.card * (2 : ℤ) ^ B.card) *
          (2 : ℤ) ^ (n - (B.biUnion id).card) := by
      rw [← mul_pow]
      norm_num
    _ = ((2 : ℤ) ^ B.card *
          (2 : ℤ) ^ (n - (B.biUnion id).card)) *
        (-1 : ℤ) ^ B.card := by ring

/-- The McEliece--Ax divisibility exponent for a positive-degree Boolean
function: its zero-frequency character sum is divisible by
`2 ^ ⌈n / d⌉` whenever its algebraic degree is at most `d`. -/
theorem two_pow_ceilDiv_dvd_booleanCharacterSum_of_degree_le
    (f : BooleanFunction n) (d : ℕ) (hd : 0 < d)
    (hdegree : FABL.functionAlgebraicDegree f ≤ d) :
    (2 : ℤ) ^ (n ⌈/⌉ d) ∣ ∑ x, bitSignInt (f x) := by
  classical
  let A := FABL.anfSupport (FABL.anfCoeff f)
  have hsum :
      (∑ x, bitSignInt (f x)) =
        ∑ B ∈ A.powerset,
          (-2 : ℤ) ^ B.card *
            (2 : ℤ) ^ (n - (B.biUnion id).card) := by
    calc
      (∑ x, bitSignInt (f x)) =
          ∑ x, bitSignInt (FABL.anfEval (FABL.anfCoeff f) x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [congrFun (FABL.anfEval_anfCoeff f) x]
      _ = ∑ x, ∑ B ∈ A.powerset,
            (-2 : ℤ) ^ B.card *
              ∏ S ∈ B, bitValueInt (FABL.anfMonomial S x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact bitSignInt_anfEval_eq_powersetSum (FABL.anfCoeff f) x
      _ = ∑ B ∈ A.powerset,
            (-2 : ℤ) ^ B.card *
              ∑ x, ∏ S ∈ B,
                bitValueInt (FABL.anfMonomial S x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro B _hB
        rw [Finset.mul_sum]
      _ = ∑ B ∈ A.powerset,
            (-2 : ℤ) ^ B.card *
              (2 : ℤ) ^ (n - (B.biUnion id).card) := by
        apply Finset.sum_congr rfl
        intro B _hB
        rw [sum_prod_bitValueInt_anfMonomial B]
  rw [hsum]
  apply Finset.dvd_sum
  intro B hB
  apply two_pow_ceilDiv_dvd_powersetTerm B d hd
  intro S hSB
  have hSA : S ∈ A := (Finset.mem_powerset.mp hB) hSB
  exact (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) d).mp
    hdegree S (by simpa [A] using hSA)

end CryptBoolean
