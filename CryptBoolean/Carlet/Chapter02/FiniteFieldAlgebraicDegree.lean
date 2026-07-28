/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FiniteField
public import CryptBoolean.Carlet.Chapter02.AlgebraicDegree

import Mathlib.Combinatorics.Colex

/-!
# Binary degree of finite-field univariate representations

The algebraic degree of a Boolean function in binary coordinates is the maximum binary
Hamming weight of an exponent occurring in its canonical bounded univariate representation.
The proof uses a private `GF(2^n)`-valued algebraic-normal-form layer to cross the coefficient
field without introducing a second public Boolean-function representation.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable section

private abbrev ExtensionCubeFunction (n : ℕ) :=
  FABL.F₂Cube n → BinaryGaloisField n

private abbrev ExtensionAnfCoefficients (n : ℕ) :=
  Finset (Fin n) → BinaryGaloisField n

private def extensionAnfMonomial {n : ℕ} (S : Finset (Fin n))
    (x : FABL.F₂Cube n) : BinaryGaloisField n :=
  algebraMap FABL.𝔽₂ (BinaryGaloisField n) (FABL.anfMonomial S x)

private def extensionAnfEval {n : ℕ} (c : ExtensionAnfCoefficients n)
    (x : FABL.F₂Cube n) : BinaryGaloisField n :=
  ∑ S, c S * extensionAnfMonomial S x

private def extensionAnfCoeff {n : ℕ} (F : ExtensionCubeFunction n) :
    ExtensionAnfCoefficients n :=
  fun S ↦ ∑ T ∈ S.powerset, F (FABL.f₂CubeOfFinset T)

private def extensionAnfSupport {n : ℕ} (c : ExtensionAnfCoefficients n) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun S ↦ c S ≠ 0

private def extensionAlgebraicDegree {n : ℕ} (c : ExtensionAnfCoefficients n) : ℕ :=
  (extensionAnfSupport c).sup Finset.card

private def extensionFunctionAlgebraicDegree {n : ℕ} (F : ExtensionCubeFunction n) : ℕ :=
  extensionAlgebraicDegree (extensionAnfCoeff F)

private theorem extensionAlgebraicDegree_le_iff {n : ℕ}
    (c : ExtensionAnfCoefficients n) (r : ℕ) :
    extensionAlgebraicDegree c ≤ r ↔ ∀ S, c S ≠ 0 → S.card ≤ r := by
  classical
  rw [extensionAlgebraicDegree, Finset.sup_le_iff]
  constructor
  · intro h S hS
    exact h S (by simpa [extensionAnfSupport] using hS)
  · intro h S hS
    exact h S (by simpa [extensionAnfSupport] using hS)

private theorem extensionAnfMonomial_f₂CubeOfFinset {n : ℕ}
    (S U : Finset (Fin n)) :
    extensionAnfMonomial S (FABL.f₂CubeOfFinset U) = if S ⊆ U then 1 else 0 := by
  rw [extensionAnfMonomial, FABL.anfMonomial_f₂CubeOfFinset]
  by_cases h : S ⊆ U <;> simp [h]

private theorem extensionAnfEval_f₂CubeOfFinset {n : ℕ}
    (c : ExtensionAnfCoefficients n) (U : Finset (Fin n)) :
    extensionAnfEval c (FABL.f₂CubeOfFinset U) = ∑ S ∈ U.powerset, c S := by
  classical
  rw [extensionAnfEval]
  calc
    ∑ S, c S * extensionAnfMonomial S (FABL.f₂CubeOfFinset U) =
        ∑ S, (if S ⊆ U then c S else 0) := by
      refine Finset.sum_congr rfl (fun S _ ↦ ?_)
      rw [extensionAnfMonomial_f₂CubeOfFinset]
      by_cases h : S ⊆ U <;> simp [h]
    _ = ∑ S ∈ Finset.univ.filter (fun S ↦ S ⊆ U), c S := by
      rw [Finset.sum_filter]
    _ = ∑ S ∈ U.powerset, c S := by
      refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext S
      simp [Finset.mem_powerset]

private theorem extensionAnfEval_extensionAnfCoeff_f₂CubeOfFinset {n : ℕ}
    (F : ExtensionCubeFunction n) (U : Finset (Fin n)) :
    extensionAnfEval (extensionAnfCoeff F) (FABL.f₂CubeOfFinset U) =
      F (FABL.f₂CubeOfFinset U) := by
  classical
  rw [extensionAnfEval_f₂CubeOfFinset]
  simp only [extensionAnfCoeff]
  have step1 : ∀ S ∈ U.powerset,
      (∑ T ∈ S.powerset, F (FABL.f₂CubeOfFinset T)) =
        ∑ T ∈ U.powerset,
          (if T ⊆ S then F (FABL.f₂CubeOfFinset T) else 0) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hsub : S.powerset = U.powerset.filter (fun T ↦ T ⊆ S) := by
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hS, h⟩, fun h ↦ h.2⟩
    rw [hsub, Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset,
          (if T ⊆ S then F (FABL.f₂CubeOfFinset T) else 0)) =
        if T = U then F (FABL.f₂CubeOfFinset U) else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hset : U.powerset.filter (fun S ↦ T ⊆ S) = Finset.Icc T U := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
    rw [← Finset.sum_filter, hset, Finset.sum_const,
      Finset.card_Icc_finset hT]
    by_cases hTU : T = U
    · subst hTU
      rw [if_pos rfl, Nat.sub_self, pow_zero, one_nsmul]
    · rw [if_neg hTU]
      have hlt : T.card < U.card := Finset.card_lt_card (hT.ssubset_of_ne hTU)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hlt).ne'
      rw [hm, pow_succ, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero]
  rw [Finset.sum_congr rfl step2, Finset.sum_ite_eq' U.powerset U,
    if_pos (Finset.mem_powerset.mpr (subset_refl U))]

private theorem extensionAnfEval_extensionAnfCoeff {n : ℕ}
    (F : ExtensionCubeFunction n) :
    extensionAnfEval (extensionAnfCoeff F) = F := by
  classical
  funext x
  have hx : FABL.f₂CubeOfFinset (FABL.f₂Support x) = x := by
    simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
  rw [← hx, extensionAnfEval_extensionAnfCoeff_f₂CubeOfFinset]

private theorem extensionAnfEval_injective {n : ℕ}
    {c d : ExtensionAnfCoefficients n} (h : extensionAnfEval c = extensionAnfEval d) :
    c = d := by
  apply FABL.coefficients_eq_of_powerset_sum_eq
  intro U
  rw [← extensionAnfEval_f₂CubeOfFinset,
    ← extensionAnfEval_f₂CubeOfFinset, h]

private theorem extensionAnfCoeff_map_boolean {n : ℕ}
    (f : FABL.F₂BooleanFunction n) (S : Finset (Fin n)) :
    extensionAnfCoeff
        (fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)) S =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (FABL.anfCoeff f S) := by
  classical
  simp [extensionAnfCoeff, FABL.anfCoeff, map_sum]

private theorem extensionFunctionAlgebraicDegree_map_boolean {n : ℕ}
    (f : FABL.F₂BooleanFunction n) :
    extensionFunctionAlgebraicDegree
        (fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)) =
      FABL.functionAlgebraicDegree f := by
  classical
  rw [extensionFunctionAlgebraicDegree, FABL.functionAlgebraicDegree,
    extensionAlgebraicDegree, FABL.algebraicDegree]
  congr 1
  ext S
  simp [extensionAnfSupport, FABL.anfSupport, extensionAnfCoeff_map_boolean]

private theorem extensionAnfCoeff_add {n : ℕ} (F G : ExtensionCubeFunction n) :
    extensionAnfCoeff (F + G) =
      fun S ↦ extensionAnfCoeff F S + extensionAnfCoeff G S := by
  classical
  funext S
  simp [extensionAnfCoeff, Finset.sum_add_distrib]

private theorem extensionAlgebraicDegree_add_le_max {n : ℕ}
    (c d : ExtensionAnfCoefficients n) :
    extensionAlgebraicDegree (fun S ↦ c S + d S) ≤
      max (extensionAlgebraicDegree c) (extensionAlgebraicDegree d) := by
  rw [extensionAlgebraicDegree_le_iff]
  intro S hsum
  have hcd : c S ≠ 0 ∨ d S ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (by rw [h.1, h.2, add_zero])
  cases hcd with
  | inl hc =>
      exact (extensionAlgebraicDegree_le_iff c _).mp le_rfl S hc |>.trans
        (Nat.le_max_left _ _)
  | inr hd =>
      exact (extensionAlgebraicDegree_le_iff d _).mp le_rfl S hd |>.trans
        (Nat.le_max_right _ _)

private theorem extensionFunctionAlgebraicDegree_add_le_max {n : ℕ}
    (F G : ExtensionCubeFunction n) :
    extensionFunctionAlgebraicDegree (F + G) ≤
      max (extensionFunctionAlgebraicDegree F) (extensionFunctionAlgebraicDegree G) := by
  rw [extensionFunctionAlgebraicDegree, extensionAnfCoeff_add,
    extensionFunctionAlgebraicDegree, extensionFunctionAlgebraicDegree]
  exact extensionAlgebraicDegree_add_le_max (extensionAnfCoeff F) (extensionAnfCoeff G)

private def extensionAnfMul {n : ℕ}
    (c d : ExtensionAnfCoefficients n) : ExtensionAnfCoefficients n :=
  fun U ↦ ∑ S, ∑ T, if U = S ∪ T then c S * d T else 0

private theorem extensionAnfMonomial_mul {n : ℕ} (S T : Finset (Fin n))
    (x : FABL.F₂Cube n) :
    extensionAnfMonomial S x * extensionAnfMonomial T x =
      extensionAnfMonomial (S ∪ T) x := by
  simp [extensionAnfMonomial, ← map_mul, FABL.anfMonomial_mul]

private theorem extensionAnfEval_extensionAnfMul {n : ℕ}
    (c d : ExtensionAnfCoefficients n) (x : FABL.F₂Cube n) :
    extensionAnfEval (extensionAnfMul c d) x =
      extensionAnfEval c x * extensionAnfEval d x := by
  classical
  rw [extensionAnfEval, extensionAnfEval, extensionAnfEval]
  simp only [extensionAnfMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (S ∪ T),
    if_pos (Finset.mem_univ (S ∪ T)), ← extensionAnfMonomial_mul]
  ring

private theorem extensionAnfCoeff_mul {n : ℕ} (F G : ExtensionCubeFunction n) :
    extensionAnfCoeff (F * G) =
      extensionAnfMul (extensionAnfCoeff F) (extensionAnfCoeff G) := by
  apply extensionAnfEval_injective
  rw [extensionAnfEval_extensionAnfCoeff]
  funext x
  rw [extensionAnfEval_extensionAnfMul,
    extensionAnfEval_extensionAnfCoeff, extensionAnfEval_extensionAnfCoeff]
  rfl

private theorem extensionAlgebraicDegree_anfMul_le_add {n : ℕ}
    (c d : ExtensionAnfCoefficients n) :
    extensionAlgebraicDegree (extensionAnfMul c d) ≤
      extensionAlgebraicDegree c + extensionAlgebraicDegree d := by
  rw [extensionAlgebraicDegree_le_iff]
  intro U hU
  rw [extensionAnfMul] at hU
  obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, _, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hUnion : U = S ∪ T := by
    by_contra hne
    simp [hne] at hT
  have hmul : c S * d T ≠ 0 := by
    simpa [hUnion] using hT
  have hc : c S ≠ 0 := (mul_ne_zero_iff.mp hmul).1
  have hd : d T ≠ 0 := (mul_ne_zero_iff.mp hmul).2
  have hScard : S.card ≤ extensionAlgebraicDegree c :=
    (extensionAlgebraicDegree_le_iff c _).mp le_rfl S hc
  have hTcard : T.card ≤ extensionAlgebraicDegree d :=
    (extensionAlgebraicDegree_le_iff d _).mp le_rfl T hd
  rw [hUnion]
  exact (Finset.card_union_le S T).trans (Nat.add_le_add hScard hTcard)

private theorem extensionFunctionAlgebraicDegree_mul_le_add {n : ℕ}
    (F G : ExtensionCubeFunction n) :
    extensionFunctionAlgebraicDegree (F * G) ≤
      extensionFunctionAlgebraicDegree F + extensionFunctionAlgebraicDegree G := by
  rw [extensionFunctionAlgebraicDegree, extensionAnfCoeff_mul,
    extensionFunctionAlgebraicDegree, extensionFunctionAlgebraicDegree]
  exact extensionAlgebraicDegree_anfMul_le_add (extensionAnfCoeff F) (extensionAnfCoeff G)

private theorem extensionAnfCoeff_smul {n : ℕ}
    (a : BinaryGaloisField n) (F : ExtensionCubeFunction n) :
    extensionAnfCoeff (a • F) = fun S ↦ a * extensionAnfCoeff F S := by
  classical
  funext S
  simp [extensionAnfCoeff, Finset.mul_sum]

private theorem extensionFunctionAlgebraicDegree_smul_le {n : ℕ}
    (a : BinaryGaloisField n) (F : ExtensionCubeFunction n) :
    extensionFunctionAlgebraicDegree (a • F) ≤ extensionFunctionAlgebraicDegree F := by
  rw [extensionFunctionAlgebraicDegree, extensionAnfCoeff_smul]
  apply (extensionAlgebraicDegree_le_iff _ _).mpr
  intro S hS
  exact (extensionAlgebraicDegree_le_iff (extensionAnfCoeff F) _).mp le_rfl S
    (fun hzero ↦ hS (by rw [hzero, mul_zero]))

private theorem extensionFunctionAlgebraicDegree_finset_sum_le {n : ℕ}
    {ι : Type*} (s : Finset ι) (F : ι → ExtensionCubeFunction n) (r : ℕ)
    (hF : ∀ i ∈ s, extensionFunctionAlgebraicDegree (F i) ≤ r) :
    extensionFunctionAlgebraicDegree (∑ i ∈ s, F i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : (0 : ExtensionCubeFunction n) =
          fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n)
            ((0 : FABL.F₂BooleanFunction n) x) := by
        funext x
        simp
      rw [Finset.sum_empty, hzero, extensionFunctionAlgebraicDegree_map_boolean]
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply (extensionFunctionAlgebraicDegree_add_le_max (F a) (∑ i ∈ s, F i)).trans
      apply max_le
      · exact hF a (Finset.mem_insert_self a s)
      · exact ih (fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))

private theorem extensionFunctionAlgebraicDegree_finset_prod_le {n : ℕ}
    {ι : Type*} (s : Finset ι) (F : ι → ExtensionCubeFunction n) :
    extensionFunctionAlgebraicDegree (∏ i ∈ s, F i) ≤
      ∑ i ∈ s, extensionFunctionAlgebraicDegree (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (1 : ExtensionCubeFunction n) =
          fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n)
            ((1 : FABL.F₂BooleanFunction n) x) := by
        funext x
        simp
      rw [Finset.prod_empty, Finset.sum_empty, hone,
        extensionFunctionAlgebraicDegree_map_boolean]
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (extensionFunctionAlgebraicDegree_mul_le_add (F a) (∏ i ∈ s, F i)).trans
        (Nat.add_le_add_left ih _)

private theorem extensionAnfCoeff_univ_eq_sum {n : ℕ}
    (F : ExtensionCubeFunction n) :
    extensionAnfCoeff F Finset.univ = ∑ x, F x := by
  classical
  rw [extensionAnfCoeff, Finset.powerset_univ]
  symm
  apply Fintype.sum_equiv (FABL.f₂CubeEquivFinset n)
  intro x
  have hx : FABL.f₂CubeOfFinset (FABL.f₂Support x) = x := by
    simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
  change F x = F (FABL.f₂CubeOfFinset (FABL.f₂Support x))
  rw [hx]

/-- Carlet p. 17: the binary weight of an exponent is the Hamming weight of its base-two
expansion. -/
def binaryWeight (k : ℕ) : ℕ := k.bitIndices.length

private def extensionCoordinateBit {n : ℕ} (i : Fin n) : ExtensionCubeFunction n :=
  fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n) (x i)

private theorem extensionFunctionAlgebraicDegree_coordinateBit {n : ℕ} (i : Fin n) :
    extensionFunctionAlgebraicDegree (extensionCoordinateBit i) = 1 := by
  have hcoordinate : extensionCoordinateBit i =
      fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n)
        (FABL.anfMonomial {i} x) := by
    funext x
    simp [extensionCoordinateBit, FABL.anfMonomial]
  rw [hcoordinate, extensionFunctionAlgebraicDegree_map_boolean,
    FABL.functionAlgebraicDegree_anfMonomial]
  simp

private def extensionFrobeniusCoordinateFunction {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (t : ℕ) :
    ExtensionCubeFunction n :=
  fun x ↦ (θ x) ^ (2 ^ t)

private theorem extensionFrobeniusCoordinateFunction_eq_sum {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (t : ℕ) :
    extensionFrobeniusCoordinateFunction θ t =
      ∑ i, (θ (Pi.single i 1) ^ (2 ^ t)) • extensionCoordinateBit i := by
  classical
  funext x
  have hx : x = ∑ i, Pi.single i (x i) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hθ : θ x = ∑ i,
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (x i) * θ (Pi.single i 1) := by
    calc
      θ x = θ (∑ i, Pi.single i (x i)) := congrArg θ hx
      _ = ∑ i, θ (Pi.single i (x i)) := by rw [map_sum]
      _ = ∑ i, algebraMap FABL.𝔽₂ (BinaryGaloisField n) (x i) *
          θ (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle : Pi.single i (x i) = x i • Pi.single i (1 : FABL.𝔽₂) := by
          ext j
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]
        rw [hsingle, map_smul]
        exact Algebra.smul_def _ _
  rw [extensionFrobeniusCoordinateFunction, hθ, sum_pow_char_pow]
  simp only [Finset.sum_apply, Pi.smul_apply, extensionCoordinateBit, mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  have hbit : (algebraMap FABL.𝔽₂ (BinaryGaloisField n) (x i)) ^ (2 ^ t) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (x i) := by
    by_cases hxi : x i = 0
    · simp [hxi]
    · have hxi_one : x i = 1 := Fin.eq_one_of_ne_zero (x i) hxi
      simp [hxi_one]
  rw [hbit]
  exact mul_comm _ _

private theorem extensionFunctionAlgebraicDegree_frobeniusCoordinate_le_one {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (t : ℕ) :
    extensionFunctionAlgebraicDegree (extensionFrobeniusCoordinateFunction θ t) ≤ 1 := by
  rw [extensionFrobeniusCoordinateFunction_eq_sum]
  apply extensionFunctionAlgebraicDegree_finset_sum_le
  intro i _
  exact (extensionFunctionAlgebraicDegree_smul_le _ _).trans
    (extensionFunctionAlgebraicDegree_coordinateBit i).le

private def extensionCoordinatePowerFunction {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (k : ℕ) :
    ExtensionCubeFunction n :=
  ∏ t ∈ k.bitIndices.toFinset, extensionFrobeniusCoordinateFunction θ t

private theorem extensionCoordinatePowerFunction_apply {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (k : ℕ)
    (x : FABL.F₂Cube n) :
    extensionCoordinatePowerFunction θ k x = (θ x) ^ k := by
  classical
  rw [extensionCoordinatePowerFunction]
  simp only [Finset.prod_apply, extensionFrobeniusCoordinateFunction]
  calc
    (∏ t ∈ k.bitIndices.toFinset, (θ x) ^ (2 ^ t)) =
        (θ x) ^ (∑ t ∈ k.bitIndices.toFinset, 2 ^ t) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = (θ x) ^ k := by rw [Finset.sum_toFinset_bitIndices_two_pow]

private theorem extensionFunctionAlgebraicDegree_coordinatePower_le_binaryWeight {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n) (k : ℕ) :
    extensionFunctionAlgebraicDegree (extensionCoordinatePowerFunction θ k) ≤ binaryWeight k := by
  classical
  calc
    extensionFunctionAlgebraicDegree (extensionCoordinatePowerFunction θ k) ≤
        ∑ t ∈ k.bitIndices.toFinset,
          extensionFunctionAlgebraicDegree (extensionFrobeniusCoordinateFunction θ t) :=
      extensionFunctionAlgebraicDegree_finset_prod_le _ _
    _ ≤ ∑ _t ∈ k.bitIndices.toFinset, 1 := by
      gcongr with t ht
      exact extensionFunctionAlgebraicDegree_frobeniusCoordinate_le_one θ t
    _ = binaryWeight k := by
      simp [binaryWeight, List.toFinset_card_of_nodup Nat.bitIndices_nodup]

private def truncatedBinarySupport (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ k.testBit i

private def truncatedBinaryWeight (n k : ℕ) : ℕ :=
  (truncatedBinarySupport n k).card

private theorem truncatedBinaryWeight_eq_sum_testBit (n k : ℕ) :
    truncatedBinaryWeight n k = ∑ i : Fin n, (k.testBit i).toNat := by
  classical
  rw [truncatedBinaryWeight, truncatedBinarySupport, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases k.testBit i <;> rfl

private theorem binaryWeight_eq_truncatedBinaryWeight
    (n k : ℕ) (hk : k < 2 ^ n) :
    binaryWeight k = truncatedBinaryWeight n k := by
  classical
  rw [binaryWeight, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  apply Finset.card_bij
    (fun i hi ↦ ⟨i, by
      by_contra hni
      have hfalse : k.testBit i = false := Nat.testBit_eq_false_of_lt
        (hk.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hni)))
      have htrue : k.testBit i := Nat.mem_bitIndices.mp (by simpa using hi)
      simp [hfalse] at htrue⟩)
  · intro i hi
    simp only [truncatedBinarySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.mem_bitIndices.mp (by simpa using hi)
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro i hi
    refine ⟨(i : ℕ), ?_, ?_⟩
    · simpa [truncatedBinarySupport] using
        (Nat.mem_bitIndices.mpr
          (show k.testBit (i : ℕ) from (by simpa [truncatedBinarySupport] using hi)))
    · apply Fin.ext
      rfl

private theorem binaryWeight_two_pow_sub_one_sub
    (n k : ℕ) (hk : k < 2 ^ n) :
    binaryWeight (2 ^ n - 1 - k) = n - binaryWeight k := by
  have hcomp_lt : 2 ^ n - 1 - k < 2 ^ n :=
    (Nat.sub_le (2 ^ n - 1) k).trans_lt
      (Nat.sub_lt (Nat.two_pow_pos n) (by omega))
  rw [binaryWeight_eq_truncatedBinaryWeight n _ hcomp_lt,
    binaryWeight_eq_truncatedBinaryWeight n k hk,
    truncatedBinaryWeight_eq_sum_testBit,
    truncatedBinaryWeight_eq_sum_testBit]
  have hterm (i : Fin n) :
      ((2 ^ n - 1 - k).testBit i).toNat + (k.testBit i).toNat = 1 := by
    rw [show 2 ^ n - 1 - k = 2 ^ n - (k + 1) by omega,
      Nat.testBit_two_pow_sub_succ hk (i : ℕ)]
    simp only [Fin.isLt, decide_true, Bool.true_and]
    cases k.testBit (i : ℕ) <;> decide
  have hsum :
      (∑ i : Fin n, ((2 ^ n - 1 - k).testBit i).toNat) +
          ∑ i : Fin n, (k.testBit i).toNat = n := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i
      _ = n := by simp
  omega

private theorem sum_pow_binaryGaloisField {n m : ℕ}
    [Fintype (BinaryGaloisField n)] (hn : n ≠ 0) :
    ∑ x : BinaryGaloisField n, x ^ m =
      if m = 0 then 0 else if 2 ^ n - 1 ∣ m then 1 else 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact FiniteField.cast_card_eq_zero _
  · rw [if_neg hm]
    let φ : (BinaryGaloisField n)ˣ ↪ BinaryGaloisField n :=
      ⟨fun x ↦ x, Units.val_injective⟩
    have himage : Finset.univ.map φ = Finset.univ \ {0} := by
      ext x
      simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
        true_and, Finset.mem_sdiff, Finset.mem_singleton, φ] using! isUnit_iff_ne_zero
    calc
      ∑ x : BinaryGaloisField n, x ^ m =
          ∑ x ∈ Finset.univ \ {(0 : BinaryGaloisField n)}, x ^ m := by
        rw [← Finset.sum_sdiff ({0} : Finset (BinaryGaloisField n)).subset_univ,
          Finset.sum_singleton, zero_pow hm, add_zero]
      _ = ∑ x : (BinaryGaloisField n)ˣ, ((x : BinaryGaloisField n) ^ m) := by
        simp [φ, ← himage, Finset.univ.sum_map φ]
      _ = if Fintype.card (BinaryGaloisField n) - 1 ∣ m then -1 else 0 :=
        FiniteField.sum_pow_units _ _
      _ = if 2 ^ n - 1 ∣ m then 1 else 0 := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn]
        split_ifs <;> simp [CharTwo.neg_eq]

private theorem univariate_coefficient_eq_weighted_sum {n i : ℕ} (hn : n ≠ 0)
    [Fintype (BinaryGaloisField n)]
    (P : (BinaryGaloisField n)[X])
    (hP : P.degree < (2 ^ n : ℕ)) (hi0 : 0 < i) (hi : i < 2 ^ n) :
    P.coeff i = ∑ x : BinaryGaloisField n, P.eval x * x ^ (2 ^ n - 1 - i) := by
  classical
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  have hmod_pos : 0 < 2 ^ n - 1 := Nat.sub_pos_of_lt hq
  have hPnat : P.natDegree < 2 ^ n := by
    by_cases hzero : P = 0
    · subst P
      exact pow_pos (by omega : 0 < 2) n
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hP
  symm
  calc
    (∑ x : BinaryGaloisField n, P.eval x * x ^ (2 ^ n - 1 - i)) =
        ∑ x : BinaryGaloisField n,
          ∑ j ∈ P.support, (P.coeff j * x ^ j) * x ^ (2 ^ n - 1 - i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    _ = ∑ j ∈ P.support, P.coeff j *
          ∑ x : BinaryGaloisField n, x ^ (j + (2 ^ n - 1 - i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [← pow_add]
    _ = P.coeff i := by
      rw [Finset.sum_eq_single i]
      · have hexp : i + (2 ^ n - 1 - i) = 2 ^ n - 1 := by omega
        rw [hexp, sum_pow_binaryGaloisField hn, if_neg hmod_pos.ne', if_pos dvd_rfl,
          mul_one]
      · intro j hj hji
        have hjq : j < 2 ^ n :=
          (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hPnat
        by_cases hexp_zero : j + (2 ^ n - 1 - i) = 0
        · rw [sum_pow_binaryGaloisField hn, if_pos hexp_zero, mul_zero]
        · have hexp_pos : 0 < j + (2 ^ n - 1 - i) := Nat.pos_of_ne_zero hexp_zero
          have hnotdvd : ¬2 ^ n - 1 ∣ j + (2 ^ n - 1 - i) := by
            intro hdvd
            have hlt_two : j + (2 ^ n - 1 - i) < 2 * (2 ^ n - 1) := by omega
            have heq : j + (2 ^ n - 1 - i) = 2 ^ n - 1 := by
              obtain ⟨a, ha⟩ := hdvd
              have ha_pos : 0 < a := by
                by_contra ha0
                have ha_zero : a = 0 := Nat.eq_zero_of_not_pos ha0
                rw [ha_zero, mul_zero] at ha
                omega
              have ha_lt : a < 2 := by
                by_contra ha2
                have htwo_le : 2 ≤ a := Nat.le_of_not_gt ha2
                have hmul := Nat.mul_le_mul_left (2 ^ n - 1) htwo_le
                rw [← ha] at hmul
                omega
              interval_cases a
              simpa using ha
            omega
          rw [sum_pow_binaryGaloisField hn, if_neg hexp_zero, if_neg hnotdvd,
            mul_zero]
      · intro hiSupport
        have hcoeff : P.coeff i = 0 := by
          by_contra hne
          exact hiSupport (Polynomial.mem_support_iff.mpr hne)
        rw [hcoeff, zero_mul]

private theorem extension_univariate_eval_eq_power_sum {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (P : (BinaryGaloisField n)[X]) :
    (fun x ↦ P.eval (θ x)) =
      ∑ j ∈ P.support, P.coeff j • extensionCoordinatePowerFunction θ j := by
  classical
  funext x
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [extensionCoordinatePowerFunction_apply]
  exact (smul_eq_mul _ _).symm

private theorem functionAlgebraicDegree_le_of_univariate_weight_le {n d : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FABL.F₂BooleanFunction n) (P : (BinaryGaloisField n)[X])
    (heval : ∀ x, P.eval (θ x) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x))
    (hweight : ∀ j ∈ P.support, binaryWeight j ≤ d) :
    FABL.functionAlgebraicDegree f ≤ d := by
  have hmapped :
      (fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)) =
        fun x ↦ P.eval (θ x) := by
    funext x
    exact (heval x).symm
  rw [← extensionFunctionAlgebraicDegree_map_boolean, hmapped,
    extension_univariate_eval_eq_power_sum]
  apply extensionFunctionAlgebraicDegree_finset_sum_le
  intro j hj
  exact (extensionFunctionAlgebraicDegree_smul_le _ _).trans
    ((extensionFunctionAlgebraicDegree_coordinatePower_le_binaryWeight θ j).trans
      (hweight j hj))

private theorem univariate_coefficient_eq_zero_of_functionAlgebraicDegree_lt_weight
    {n i : ℕ} (hn : n ≠ 0)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FABL.F₂BooleanFunction n) (P : (BinaryGaloisField n)[X])
    (hP : P.degree < (2 ^ n : ℕ))
    (heval : ∀ x, P.eval (θ x) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x))
    (hi0 : 0 < i) (hi : i < 2 ^ n)
    (hweight : FABL.functionAlgebraicDegree f < binaryWeight i) :
    P.coeff i = 0 := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  rw [univariate_coefficient_eq_weighted_sum hn P hP hi0 hi]
  let F : ExtensionCubeFunction n :=
    fun x ↦ algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)
  let G : ExtensionCubeFunction n :=
    extensionCoordinatePowerFunction θ (2 ^ n - 1 - i)
  have hFGdegree : extensionFunctionAlgebraicDegree (F * G) < n := by
    have hF : extensionFunctionAlgebraicDegree F = FABL.functionAlgebraicDegree f :=
      extensionFunctionAlgebraicDegree_map_boolean f
    have hG : extensionFunctionAlgebraicDegree G ≤ n - binaryWeight i := by
      exact (extensionFunctionAlgebraicDegree_coordinatePower_le_binaryWeight θ _).trans_eq
        (binaryWeight_two_pow_sub_one_sub n i hi)
    calc
      extensionFunctionAlgebraicDegree (F * G) ≤
          extensionFunctionAlgebraicDegree F + extensionFunctionAlgebraicDegree G :=
        extensionFunctionAlgebraicDegree_mul_le_add F G
      _ ≤ FABL.functionAlgebraicDegree f + (n - binaryWeight i) := by omega
      _ < n := by
        have hiweight : binaryWeight i ≤ n := by
          rw [binaryWeight_eq_truncatedBinaryWeight n i hi, truncatedBinaryWeight]
          simpa using Finset.card_le_univ (truncatedBinarySupport n i)
        omega
  have htop : extensionAnfCoeff (F * G) Finset.univ = 0 := by
    by_contra hne
    have hle := (extensionAlgebraicDegree_le_iff (extensionAnfCoeff (F * G)) _).mp
      le_rfl Finset.univ hne
    have : n ≤ extensionFunctionAlgebraicDegree (F * G) := by
      simpa [extensionFunctionAlgebraicDegree] using hle
    omega
  calc
    (∑ x : BinaryGaloisField n, P.eval x * x ^ (2 ^ n - 1 - i)) =
        ∑ x : FABL.F₂Cube n, P.eval (θ x) * (θ x) ^ (2 ^ n - 1 - i) := by
      exact Fintype.sum_equiv θ.toEquiv.symm _ _ (fun x ↦ by simp)
    _ = ∑ x : FABL.F₂Cube n, (F * G) x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [Pi.mul_apply, F, G, extensionCoordinatePowerFunction_apply, heval]
    _ = extensionAnfCoeff (F * G) Finset.univ :=
      (extensionAnfCoeff_univ_eq_sum (F * G)).symm
    _ = 0 := htop

private theorem functionAlgebraicDegree_le_iff_univariate_support_weight_le
    {n d : ℕ} (hn : n ≠ 0)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FABL.F₂BooleanFunction n) (P : (BinaryGaloisField n)[X])
    (hP : P.degree < (2 ^ n : ℕ))
    (heval : ∀ x, P.eval (θ x) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)) :
    FABL.functionAlgebraicDegree f ≤ d ↔
      ∀ j ∈ P.support, binaryWeight j ≤ d := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  classical
  constructor
  · intro hdegree j hj
    have hPnat : P.natDegree < 2 ^ n := by
      by_cases hzero : P = 0
      · subst P
        exact pow_pos (by omega : 0 < 2) n
      · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hP
    have hjlt : j < 2 ^ n :=
      (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hPnat
    by_cases hjzero : j = 0
    · subst j
      simp [binaryWeight]
    · by_contra hweight
      have hstrict : FABL.functionAlgebraicDegree f < binaryWeight j :=
        hdegree.trans_lt (Nat.lt_of_not_ge hweight)
      have hcoeff := univariate_coefficient_eq_zero_of_functionAlgebraicDegree_lt_weight
        hn θ f P hP heval (Nat.pos_of_ne_zero hjzero) hjlt hstrict
      exact (Polynomial.mem_support_iff.mp hj) hcoeff
  · exact fun hweight ↦
      functionAlgebraicDegree_le_of_univariate_weight_le θ f P heval hweight

/-- Carlet p. 17: the binary degree of a univariate polynomial is the maximum binary weight
among the exponents of its nonzero coefficients. -/
noncomputable def univariateBinaryDegree {n : ℕ}
    (P : (BinaryGaloisField n)[X]) : ℕ :=
  P.support.sup binaryWeight

private theorem functionAlgebraicDegree_eq_univariateBinaryDegree_of_eval
    {n : ℕ} (hn : n ≠ 0)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FABL.F₂BooleanFunction n) (P : (BinaryGaloisField n)[X])
    (hP : P.degree < (2 ^ n : ℕ))
    (heval : ∀ x, P.eval (θ x) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f x)) :
    FABL.functionAlgebraicDegree f = univariateBinaryDegree P := by
  apply Nat.le_antisymm
  · rw [functionAlgebraicDegree_le_iff_univariate_support_weight_le hn θ f P hP heval]
    intro j hj
    exact Finset.le_sup hj
  · rw [univariateBinaryDegree]
    apply Finset.sup_le
    intro j hj
    exact (functionAlgebraicDegree_le_iff_univariate_support_weight_le
      hn θ f P hP heval).mp le_rfl j hj

/-- Carlet p. 17: after any binary linear identification with `GF(2^n)`, coordinate ANF
degree equals the binary degree of the canonical bounded univariate representation. -/
theorem functionAlgebraicDegree_eq_univariateBinaryDegree {n : ℕ} (hn : n ≠ 0)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FABL.F₂BooleanFunction n) :
    FABL.functionAlgebraicDegree f =
      univariateBinaryDegree
        (univariateRepresentation fun z ↦
          algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f (θ.symm z))) := by
  let P := univariateRepresentation fun z : BinaryGaloisField n ↦
    algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f (θ.symm z))
  apply functionAlgebraicDegree_eq_univariateBinaryDegree_of_eval hn θ f P
  · simpa [P, GaloisField.card 2 n hn] using
      degree_univariateRepresentation_lt_card
        (fun z : BinaryGaloisField n ↦
          algebraMap FABL.𝔽₂ (BinaryGaloisField n) (f (θ.symm z)))
  · intro x
    simp [P, eval_univariateRepresentation]

end

end CryptBoolean
