/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.PropagationCriteria
public import CryptBoolean.Carlet.Chapter06.HadamardDifferenceSet
public import FABL.Chapter06.F₂Polynomials.ExtremalBounds

/-!
# Algebraic degree of propagation functions

The general degree bound for a nontrivial propagation criterion.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Every nonzero difference occurs an even number of times inside a subset of
the binary cube. -/
theorem differenceMultiplicity_even
    (D : Finset (FABL.F₂Cube n)) (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    Even (differenceMultiplicity D a) := by
  classical
  have hexists : ∃ i : Fin n, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  let S : Finset (FABL.F₂Cube n) := D.filter fun x ↦ x + a ∈ D
  let S₀ : Finset (FABL.F₂Cube n) := S.filter fun x ↦ x i = 0
  let S₁ : Finset (FABL.F₂Cube n) := S.filter fun x ↦ x i ≠ 0
  have hstable (x : FABL.F₂Cube n) (hx : x ∈ S) : x + a ∈ S := by
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.2, ?_⟩
    simpa [add_assoc, ZModModule.add_self] using hx.1
  let e : {x // x ∈ S₀} ≃ {x // x ∈ S₁} :=
    { toFun := fun x ↦ ⟨x.1 + a, by
        have hx := x.2
        dsimp [S₀] at hx
        rw [Finset.mem_filter] at hx
        dsimp [S₁]
        rw [Finset.mem_filter]
        refine ⟨hstable x.1 hx.1, ?_⟩
        intro hzero
        have hvalue : a i = 0 := by
          have := congrArg (fun z : FABL.𝔽₂ ↦ z - x.1 i) hzero
          simpa [hx.2] using this
        exact hi hvalue⟩
      invFun := fun x ↦ ⟨x.1 + a, by
        have hx := x.2
        dsimp [S₁] at hx
        rw [Finset.mem_filter] at hx
        dsimp [S₀]
        rw [Finset.mem_filter]
        refine ⟨hstable x.1 hx.1, ?_⟩
        have hxi : x.1 i = 1 := Fin.eq_one_of_ne_zero _ hx.2
        have hai : a i = 1 := Fin.eq_one_of_ne_zero _ hi
        simp [hxi, hai]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp [add_assoc, ZModModule.add_self]
      right_inv := by
        intro x
        apply Subtype.ext
        simp [add_assoc, ZModModule.add_self] }
  have hcard : S₀.card = S₁.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_congr e
  have hpartition : S₀.card + S₁.card = S.card := by
    simpa [S₀, S₁] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (p := fun x : FABL.F₂Cube n ↦ x i = 0))
  refine ⟨S₀.card, ?_⟩
  unfold differenceMultiplicity
  change S.card = S₀.card + S₀.card
  omega

/-- Carlet Section 8.1: a Boolean function satisfying a nontrivial `PC(l)`
in dimension at least three has algebraic degree at most `n-1`. -/
theorem functionAlgebraicDegree_le_pred_of_satisfiesPropagationCriterion
    (f : BooleanFunction n) (l : ℕ) (hn : 3 ≤ n) (hl : 1 ≤ l)
    (_hlt : l < n) (hpc : SatisfiesPropagationCriterion l f) :
    FABL.functionAlgebraicDegree f ≤ n - 1 := by
  by_contra hdegree
  have hdegreeEq : FABL.functionAlgebraicDegree f = n := by
    have hdimension := FABL.functionAlgebraicDegree_le_dimension f
    omega
  have hweightOdd : Odd (hammingWeight f) := by
    rw [hammingWeight_eq_card_support]
    exact
      (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
        f (by omega)).mp hdegreeEq
  let i : Fin n := ⟨0, by omega⟩
  let a : FABL.F₂Cube n := Pi.single i 1
  have ha : a ≠ 0 := by
    intro hzero
    have hvalue := congrFun hzero i
    simp [a] at hvalue
  have haCard : (FABL.f₂Support a).card = 1 := by
    rw [show FABL.f₂Support a = {i} by
      ext j
      simp [FABL.f₂Support, a, Pi.single_apply]]
    simp
  have hbalanced : IsBalanced (FABL.booleanDerivative f a) :=
    hpc a ⟨ha, by omega⟩
  have hderivativeWeight :
      2 * hammingWeight (FABL.booleanDerivative f a) = 2 ^ n :=
    hbalanced
  have hmultiplicity :=
    hammingWeight_booleanDerivative_add_two_mul_differenceMultiplicity f a
  have hmultiplicityEven := differenceMultiplicity_even (support f) a ha
  rcases hweightOdd with ⟨q, hq⟩
  rcases hmultiplicityEven with ⟨r, hr⟩
  have hpow : 2 ^ n = 8 * 2 ^ (n - 3) := by
    calc
      2 ^ n = 2 ^ ((n - 3) + 3) := by congr 1; omega
      _ = 8 * 2 ^ (n - 3) := by rw [pow_add]; norm_num; omega
  omega

end CryptBoolean
