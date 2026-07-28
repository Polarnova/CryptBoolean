/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.QuadraticBent
public import FABL.Chapter06.F₂Polynomials.CompleteQuadraticDecomposition
public import Mathlib.Data.Sym.Card

/-!
# Carlet Chapter 6 complete quadratic bent function

Relation (56), its Hamming-weight description, and the triviality of the
polar radical in even dimension.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The complete quadratic function has algebraic degree at most two. -/
theorem functionAlgebraicDegree_completeQuadraticBit_le_two :
    FABL.functionAlgebraicDegree
      (FABL.completeQuadraticBit : BooleanFunction n) ≤ 2 := by
  classical
  have hfunction :
      (FABL.completeQuadraticBit : BooleanFunction n) =
        ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          FABL.anfMonomial ({i, j} : Finset (Fin n)) := by
    funext x
    rw [FABL.completeQuadraticBit]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    rw [FABL.anfMonomial, Finset.prod_pair hij]
  rw [hfunction]
  apply FABL.functionAlgebraicDegree_finset_sum_le Finset.univ _ 2
  intro i _hi
  apply FABL.functionAlgebraicDegree_finset_sum_le (Finset.Ioi i) _ 2
  intro j _hj
  exact (FABL.functionAlgebraicDegree_anfMonomial_le_card
    ({i, j} : Finset (Fin n))).trans Finset.card_le_two

/-- Relation (56): the complete quadratic value is the parity of the number
of unordered pairs in the support, namely `choose(weight, 2)` modulo two. -/
theorem completeQuadraticBit_eq_choose_support_card
    (x : FABL.F₂Cube n) :
    FABL.completeQuadraticBit x =
      (Nat.choose (FABL.f₂Support x).card 2 : FABL.𝔽₂) := by
  classical
  let pairProduct : Sym2 (Fin n) → FABL.𝔽₂ :=
    Sym2.lift ⟨fun i j ↦ x i * x j, fun i j ↦ mul_comm (x i) (x j)⟩
  let allPairs : Finset (Sym2 (Fin n)) :=
    (Finset.univ : Finset (Fin n)).sym2.filter fun q ↦ ¬q.IsDiag
  let supportPairs : Finset (Sym2 (Fin n)) :=
    (FABL.f₂Support x).sym2.filter fun q ↦ ¬q.IsDiag
  have hsym :
      FABL.completeQuadraticBit x = ∑ q ∈ allPairs, pairProduct q := by
    dsimp only [allPairs]
    rw [Finset.sum_sym2_filter_not_isDiag, FABL.completeQuadraticBit]
    calc
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, x i * x j) =
          ∑ i : Fin n, ∑ j : Fin n,
            if i < j then x i * x j else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rfl
      _ = ∑ ij : Fin n × Fin n,
          if ij.1 < ij.2 then x ij.1 * x ij.2 else 0 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ ij ∈
          (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ij ↦ ij.1 < ij.2),
          pairProduct s(ij.1, ij.2) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ij _hij
        by_cases hij : ij.1 < ij.2
        · simp [pairProduct]
        · rfl
      _ = ∑ ij ∈
          (Finset.univ : Finset (Fin n)).offDiag.filter
            (fun ij ↦ ij.1 < ij.2),
          pairProduct s(ij.1, ij.2) := by
        congr 1
        ext ij
        simp only [Finset.mem_filter, Finset.mem_univ,
          Finset.mem_offDiag, true_and]
        constructor
        · intro hij
          exact ⟨hij.ne, hij⟩
        · exact fun hij ↦ hij.2
  have hpairProduct (q : Sym2 (Fin n)) :
      pairProduct q =
        if q ∈ (FABL.f₂Support x).sym2 then 1 else 0 := by
    induction q using Sym2.inductionOn with
    | _ i j =>
        by_cases hi : x i = 0
        · simp [pairProduct, hi, FABL.mem_f₂Support]
        · have hiOne : x i = 1 := Fin.eq_one_of_ne_zero (x i) hi
          by_cases hj : x j = 0
          · simp [pairProduct, hi, hj, FABL.mem_f₂Support]
          · have hjOne : x j = 1 := Fin.eq_one_of_ne_zero (x j) hj
            simp [pairProduct, hiOne, hjOne, FABL.mem_f₂Support]
  have hsum :
      (∑ q ∈ allPairs, pairProduct q) =
        ∑ _q ∈ supportPairs, (1 : FABL.𝔽₂) := by
    calc
      (∑ q ∈ allPairs, pairProduct q) =
          ∑ q ∈ allPairs,
            if q ∈ (FABL.f₂Support x).sym2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hpairProduct q
      _ = ∑ _q ∈
          allPairs.filter (fun q ↦ q ∈ (FABL.f₂Support x).sym2),
          (1 : FABL.𝔽₂) := by
        exact (Finset.sum_filter (s := allPairs)
          (p := fun q ↦ q ∈ (FABL.f₂Support x).sym2)
          (f := fun _q ↦ (1 : FABL.𝔽₂))).symm
      _ = ∑ _q ∈ supportPairs, (1 : FABL.𝔽₂) := by
        congr 1
        ext q
        simpa only [allPairs, supportPairs, Finset.mem_filter,
          Finset.sym2_univ, Finset.mem_univ, true_and] using
            (and_comm :
              (¬q.IsDiag ∧ q ∈ (FABL.f₂Support x).sym2) ↔
                q ∈ (FABL.f₂Support x).sym2 ∧ ¬q.IsDiag)
  have hcard :
      supportPairs.card = Nat.choose (FABL.f₂Support x).card 2 := by
    dsimp only [supportPairs]
    rw [Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag,
      Sym2.card_image_offDiag]
  rw [hsym, hsum, ← hcard]
  simp

/-- The coefficient vector representing the polar form of the complete
quadratic function in its second argument. -/
def completeQuadraticPolarFrequency (a : FABL.F₂Cube n) : FABL.F₂Cube n :=
  fun i ↦ ∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j

/-- The polar kernel of the complete quadratic function is the sum of its
mixed quadratic terms. -/
theorem quadraticPolarKernel_completeQuadraticBit_eq_crossSum
    (a b : FABL.F₂Cube n) :
    quadraticPolarKernel
        (FABL.completeQuadraticBit : BooleanFunction n) a b =
      ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (a i * b j + b i * a j) := by
  rw [quadraticPolarKernel_eq]
  simp only [FABL.completeQuadraticBit, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

/-- The polar form of the complete quadratic function is represented by the
sum of all coordinates other than the indexed coordinate. -/
theorem quadraticPolarKernel_completeQuadraticBit_eq_dotProduct
    (a b : FABL.F₂Cube n) :
    quadraticPolarKernel
        (FABL.completeQuadraticBit : BooleanFunction n) a b =
      FABL.f₂DotProduct (completeQuadraticPolarFrequency a) b := by
  classical
  rw [quadraticPolarKernel_completeQuadraticBit_eq_crossSum,
    FABL.f₂DotProduct, dotProduct]
  simp only [completeQuadraticPolarFrequency]
  have hupper :
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, b i * a j) =
        ∑ i : Fin n, (∑ j ∈ Finset.Ioi i, a j) * b i := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.mul_sum]
    ring
  have hlower :
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, a i * b j) =
        ∑ j : Fin n, (∑ i ∈ Finset.Iio j, a i) * b j := by
    calc
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, a i * b j) =
          ∑ i : Fin n, ∑ j : Fin n,
            if i < j then a i * b j else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j _hj
          rfl
      _ = ∑ j : Fin n, ∑ i : Fin n,
          if i < j then a i * b j else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (∑ i ∈ Finset.Iio j, a i) * b j := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [← Finset.sum_filter]
        have hfilter :
            (Finset.univ.filter fun i : Fin n ↦ i < j) =
              Finset.Iio j := by
          ext i
          simp
        rw [hfilter, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
        (a i * b j + b i * a j)) =
        (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, b i * a j) +
          ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, a i * b j := by
      simp only [Finset.sum_add_distrib]
      abel
    _ = ∑ i : Fin n,
        ((∑ j ∈ Finset.Ioi i, a j) +
          ∑ j ∈ Finset.Iio i, a j) * b i := by
      rw [hupper, hlower, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i : Fin n,
        (∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j) * b i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_disjUnion (Finset.disjoint_Ioi_Iio i),
        Finset.Ioi_disjUnion_Iio]

/-- In even dimension the polar-frequency map of the complete quadratic
function has trivial kernel. -/
theorem completeQuadraticPolarFrequency_eq_zero_of_even
    (hn : Even n) {a : FABL.F₂Cube n}
    (ha : completeQuadraticPolarFrequency a = 0) :
    a = 0 := by
  classical
  let total : FABL.𝔽₂ := ∑ i, a i
  have haTotal (i : Fin n) : a i = total := by
    have hi := congrFun ha i
    change (∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j) = 0 at hi
    have huniv :
        (∑ j : Fin n, a j) =
          a i + ∑ j ∈ ({i} : Finset (Fin n))ᶜ, a j := by
      rw [← Finset.sum_add_sum_compl ({i} : Finset (Fin n))]
      simp
    rw [hi, add_zero] at huniv
    simpa only [total] using huniv.symm
  have htotal : total = 0 := by
    calc
      total = ∑ i : Fin n, a i := rfl
      _ = ∑ _i : Fin n, total := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact haTotal i
      _ = n • total := by simp
      _ = 0 := by
        rcases hn with ⟨k, rfl⟩
        rw [add_nsmul]
        exact CharTwo.add_self_eq_zero _
  funext i
  rw [haTotal i, htotal]
  rfl

/-- In even dimension the polar radical of the complete quadratic function is
trivial. -/
theorem quadraticRadical_completeQuadraticBit_eq_bot (hn : Even n) :
    quadraticRadical
        (FABL.completeQuadraticBit : BooleanFunction n)
        functionAlgebraicDegree_completeQuadraticBit_le_two = ⊥ := by
  classical
  ext a
  constructor
  · intro ha
    have hpolar :=
      (mem_quadraticRadical_iff
        (FABL.completeQuadraticBit : BooleanFunction n)
        functionAlgebraicDegree_completeQuadraticBit_le_two a).mp ha
    have hfrequency : completeQuadraticPolarFrequency a = 0 := by
      funext i
      have hi := hpolar (Pi.single i (1 : FABL.𝔽₂))
      rw [quadraticPolarKernel_completeQuadraticBit_eq_dotProduct] at hi
      simpa [FABL.f₂DotProduct, dotProduct_single] using hi
    have haZero :=
      completeQuadraticPolarFrequency_eq_zero_of_even hn hfrequency
    simp [haZero]
  · intro ha
    have haZero : a = 0 := by simpa using ha
    subst a
    exact Submodule.zero_mem _

/-- FABL's complete quadratic Boolean function is bent in every even
dimension, including the zero-dimensional boundary. -/
theorem isBent_completeQuadraticBit (hn : Even n) :
    IsBent (FABL.completeQuadraticBit : BooleanFunction n) := by
  exact (isBent_iff_quadraticRadical_eq_bot
    (FABL.completeQuadraticBit : BooleanFunction n)
    functionAlgebraicDegree_completeQuadraticBit_le_two).2
      (quadraticRadical_completeQuadraticBit_eq_bot hn)

/-- In dimension zero Relation (56) is the empty sum. -/
@[simp] theorem completeQuadraticBit_zero_dimension
    (x : FABL.F₂Cube 0) :
    FABL.completeQuadraticBit x = 0 := by
  simp [FABL.completeQuadraticBit]

/-- The zero-dimensional complete quadratic function is bent under the
zero-dimensional convention for bent functions. -/
theorem isBent_completeQuadraticBit_zero_dimension :
    IsBent (FABL.completeQuadraticBit : BooleanFunction 0) :=
  isBent_completeQuadraticBit (Even.zero)

/-- In dimension two Relation (56) consists of its single quadratic
monomial. -/
@[simp] theorem completeQuadraticBit_two_dimension
    (x : FABL.F₂Cube 2) :
    FABL.completeQuadraticBit x = x 0 * x 1 := by
  have hzero : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have hone : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  rw [FABL.completeQuadraticBit, Fin.sum_univ_two, hzero, hone]
  simp

/-- The first positive-dimensional instance of Relation (56) is bent. -/
theorem isBent_completeQuadraticBit_two_dimension :
    IsBent (FABL.completeQuadraticBit : BooleanFunction 2) :=
  isBent_completeQuadraticBit (by decide)

end CryptBoolean
