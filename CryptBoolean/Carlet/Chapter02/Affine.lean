/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AlgebraicDegree

/-!
# Carlet Chapter 2 affine Boolean functions

Affine functions are represented on the canonical additive binary cube.  Their
ANF and degree facts are derived from the canonical coefficient transform.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The affine Boolean function `x ↦ b + a · x`. -/
def affineFunction (b : FABL.𝔽₂) (a : FABL.F₂Cube n) : BooleanFunction n :=
  fun x ↦ b + FABL.f₂DotProduct a x

/-- The ANF coefficients of an affine function. -/
def affineCoefficients (b : FABL.𝔽₂) (a : FABL.F₂Cube n) : ANFCoefficients n :=
  fun S ↦ if S = ∅ then b else if S.card = 1 then ∑ i ∈ S, a i else 0

/-- Evaluating the affine coefficient family gives the affine function. -/
theorem anfEval_affineCoefficients
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    anfEval (affineCoefficients b a) = affineFunction b a := by
  classical
  funext x
  rw [anfEval, affineFunction, FABL.f₂DotProduct]
  let relevant : Finset (Finset (Fin n)) :=
    {∅} ∪ Finset.univ.filter (fun S ↦ S.card = 1)
  have hreduce :
      ∑ S ∈ relevant, affineCoefficients b a S * anfMonomial S x =
        ∑ S, affineCoefficients b a S * anfMonomial S x := by
    apply Finset.sum_subset
    · intro S hS
      simp
    · intro S _ hS
      have hne : S ≠ ∅ := by
        intro h
        apply hS
        simp [relevant, h]
      have hcard : S.card ≠ 1 := by
        intro h
        apply hS
        simp [relevant, h]
      simp [affineCoefficients, hne, hcard]
  rw [← hreduce]
  have hdisjoint : Disjoint ({∅} : Finset (Finset (Fin n)))
      (Finset.univ.filter (fun S ↦ S.card = 1)) := by
    simp
  rw [Finset.sum_union hdisjoint]
  simp only [Finset.sum_singleton]
  have hsingletons :
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) ↦ S.card = 1),
          affineCoefficients b a S * anfMonomial S x =
        ∑ i, affineCoefficients b a {i} * anfMonomial {i} x := by
    apply Finset.sum_bij (fun S hS ↦ (card_eq_one.mp (by simpa using hS)).choose)
    · intro S hS
      simp
    · intro S hS T hT heq
      obtain ⟨i, hi⟩ := card_eq_one.mp (by simpa using hS)
      obtain ⟨j, hj⟩ := card_eq_one.mp (by simpa using hT)
      subst hi
      subst hj
      simpa using heq
    · intro i _
      refine ⟨{i}, ⟨by simp, ?_⟩⟩
      simp
    · intro S hS
      obtain ⟨i, rfl⟩ := card_eq_one.mp (by simpa using hS)
      simp
  rw [hsingletons]
  simp [affineCoefficients, anfMonomial, dotProduct]

/-- The canonical ANF transform recovers the affine coefficient family. -/
theorem anfCoeff_affineFunction (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    anfCoeff (affineFunction b a) = affineCoefficients b a := by
  apply anfEval_injective
  rw [anfEval_anfCoeff, anfEval_affineCoefficients]

/-- Affine functions have algebraic degree at most one. -/
theorem functionAlgebraicDegree_affineFunction_le_one
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    functionAlgebraicDegree (affineFunction b a) ≤ 1 := by
  rw [functionAlgebraicDegree, anfCoeff_affineFunction, algebraicDegree_le_iff]
  intro S hS
  by_contra hcard
  have hne : S ≠ ∅ := by
    intro h
    subst h
    simp at hcard
  have hnotone : S.card ≠ 1 := by omega
  exact hS (by simp [affineCoefficients, hne, hnotone])

/-- Every Boolean function of algebraic degree at most one is affine. -/
theorem exists_affineFunction_of_functionAlgebraicDegree_le_one
    (f : BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ 1) :
    ∃ b a, f = affineFunction b a := by
  let b := anfCoeff f ∅
  let a : FABL.F₂Cube n := fun i ↦ anfCoeff f {i}
  refine ⟨b, a, ?_⟩
  rw [← anfEval_anfCoeff f, ← anfEval_affineCoefficients]
  congr 1
  funext S
  by_cases hS0 : S = ∅
  · subst S
    simp [affineCoefficients, b]
  · by_cases hScard : S.card = 1
    · obtain ⟨i, rfl⟩ := card_eq_one.mp hScard
      simp [affineCoefficients, a]
    · have hcard : 1 < S.card := by
        have hpos : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hS0)
        omega
      have hzero : anfCoeff f S = 0 := by
        by_contra hne
        have hle := (algebraicDegree_le_iff (anfCoeff f) 1).mp hdegree S hne
        omega
      simp [affineCoefficients, hS0, hScard, hzero]

/-- Every coordinate of an affine map on the binary cube has algebraic degree at most one. -/
theorem functionAlgebraicDegree_affineMap_coordinate_le_one
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube n) (i : Fin n) :
    functionAlgebraicDegree (fun x ↦ L x i) ≤ 1 := by
  have hlinear : FABL.IsF₂Linear (fun x ↦ L.linear x i) := by
    intro x y
    exact congrArg (fun z ↦ z i) (L.linear.map_add x y)
  obtain ⟨a, ha⟩ := (FABL.isF₂Linear_iff_exists_dotProduct _).mp hlinear
  have hcoordinate : (fun x ↦ L x i) = affineFunction (L 0 i) a := by
    funext x
    have hdecomp : L x = L.linear x + L 0 := by
      simpa using congrFun (AffineMap.decomp L) x
    calc
      L x i = L.linear x i + L 0 i := by
        simpa using congrArg (fun z ↦ z i) hdecomp
      _ = FABL.f₂DotProduct a x + L 0 i := by rw [ha x]
      _ = L 0 i + FABL.f₂DotProduct a x := add_comm _ _
      _ = affineFunction (L 0 i) a x := rfl
  rw [hcoordinate]
  exact functionAlgebraicDegree_affineFunction_le_one (L 0 i) a

/-- Substituting affine coordinates into a square-free monomial does not increase its degree. -/
theorem functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (S : Finset (Fin n)) :
    functionAlgebraicDegree (fun x ↦ anfMonomial S (L x)) ≤ S.card := by
  calc
    functionAlgebraicDegree (fun x ↦ anfMonomial S (L x)) ≤
        ∑ i ∈ S, functionAlgebraicDegree (fun x ↦ L x i) := by
      have hfunctions : (∏ i ∈ S, (fun x ↦ L x i)) =
          (fun x ↦ anfMonomial S (L x)) := by
        funext x
        simp [anfMonomial, Finset.prod_apply]
      rw [← hfunctions]
      exact functionAlgebraicDegree_finset_prod_le S (fun i x ↦ L x i)
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact functionAlgebraicDegree_affineMap_coordinate_le_one L i
    _ = S.card := by simp

/-- Composition with an affine map on the binary cube cannot increase algebraic degree. -/
theorem functionAlgebraicDegree_comp_affineMap_le
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    functionAlgebraicDegree (f ∘ L) ≤ functionAlgebraicDegree f := by
  classical
  let term : Finset (Fin n) → BooleanFunction n :=
    fun S x ↦ anfCoeff f S * anfMonomial S (L x)
  have hsum : f ∘ L = ∑ S, term S := by
    funext x
    simp only [Function.comp_apply, Fintype.sum_apply, term]
    exact (congrFun (anfEval_anfCoeff f) (L x)).symm
  rw [hsum]
  exact functionAlgebraicDegree_finset_sum_le Finset.univ term
      (functionAlgebraicDegree f) (by
        intro S _
        by_cases hS : anfCoeff f S = 0
        · have hterm : term S = 0 := by
            funext x
            simp [term, hS]
          rw [hterm]
          rw [functionAlgebraicDegree_zero]
          exact Nat.zero_le _
        · have hSone : anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
          have hterm : term S = fun x ↦ anfMonomial S (L x) := by
            funext x
            simp [term, hSone]
          rw [hterm]
          apply (functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card L S).trans
          exact (algebraicDegree_le_iff (anfCoeff f) _).mp
            (by rfl) S hS)

/-- Carlet, p. 12: algebraic degree is invariant under affine equivalences of the binary cube. -/
theorem functionAlgebraicDegree_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    functionAlgebraicDegree (f ∘ L) = functionAlgebraicDegree f := by
  apply Nat.le_antisymm
  · exact functionAlgebraicDegree_comp_affineMap_le f L.toAffineMap
  · have h := functionAlgebraicDegree_comp_affineMap_le (f ∘ L) L.symm.toAffineMap
    have hcomp : (f ∘ L) ∘ L.symm.toAffineMap = f := by
      funext x
      simp
    rw [hcomp] at h
    exact h

/-- The real sign view of an affine function is a constant sign times a Walsh character. -/
theorem realSignView_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (x : FABL.F₂Cube n) :
    realSignView (affineFunction b a) x =
      FABL.binarySign b * FABL.vectorWalshCharacter a x := by
  rw [realSignView, FABL.realSignEncodedFunction, FABL.signEncodedFunction,
    affineFunction, FABL.signValue_signEncode_eq_binarySign,
    FABL.vectorWalshCharacter_apply]
  exact AddChar.map_add_eq_mul FABL.binarySign b (FABL.f₂DotProduct a x)

/-- A nonconstant affine Boolean function is balanced. -/
theorem isBalanced_affineFunction_of_ne_zero
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    IsBalanced (affineFunction b a) := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, walshTransform_cast_eq_sum_realSignView_mul_character]
  simp_rw [realSignView_affineFunction]
  have hexpect := FABL.expect_vectorWalshCharacter a
  rw [if_neg ha] at hexpect
  rw [Fintype.expect_eq_sum_div_card] at hexpect
  have hsum : ∑ x, FABL.vectorWalshCharacter a x = 0 := by
    have hcard : (Fintype.card (FABL.F₂Cube n) : ℝ) ≠ 0 := by positivity
    exact (div_eq_zero_iff.mp hexpect).resolve_right hcard
  calc
    ∑ x, FABL.binarySign b * FABL.vectorWalshCharacter a x *
        FABL.vectorWalshCharacter 0 x =
        FABL.binarySign b * ∑ x, FABL.vectorWalshCharacter a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = 0 := by rw [hsum, mul_zero]

/-- A nonconstant affine Boolean function has weight `2^(n-1)`. -/
theorem hammingWeight_affineFunction_of_ne_zero
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    hammingWeight (affineFunction b a) = 2 ^ (n - 1) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    apply ha
    funext i
    exact Fin.elim0 i
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hbalanced := isBalanced_affineFunction_of_ne_zero b a ha
  change 2 * hammingWeight (affineFunction b a) = 2 ^ (m + 1) at hbalanced
  rw [pow_succ] at hbalanced
  simp only [Nat.succ_sub_one]
  omega

/-- Raw distance scales FABL's relative Hamming distance by the cube cardinality. -/
theorem hammingDistance_eq_two_pow_mul_relativeHammingDist
    (f g : BooleanFunction n) :
    (hammingDistance f g : ℝ) =
      (2 ^ n : ℝ) * FABL.relativeHammingDist f g := by
  rw [hammingDistance, FABL.relativeHammingDist, card_f₂Cube]
  norm_num
  field_simp

end CryptBoolean
