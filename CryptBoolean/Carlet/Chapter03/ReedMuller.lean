/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine

/-!
# Carlet Chapter 3 Reed--Muller codes

The Reed--Muller family is the subspace of Boolean functions of bounded
algebraic degree. This module closes its dimension, cardinality, and general
minimum-distance formulas.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n r s : ℕ}

/-- Carlet's Reed--Muller code `R(r,n)`, represented without a redundant
general coding-theory wrapper. -/
noncomputable def reedMuller (r n : ℕ) : Submodule FABL.𝔽₂ (BooleanFunction n) where
  carrier := {f | functionAlgebraicDegree f ≤ r}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (functionAlgebraicDegree_add_le_max f g).trans (max_le hf hg)
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · subst c
      simp
    · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
      subst c
      simpa using hf

/-- Membership in `R(r,n)` is exactly the algebraic-degree bound. -/
@[simp] theorem mem_reedMuller_iff (f : BooleanFunction n) :
    f ∈ reedMuller r n ↔ functionAlgebraicDegree f ≤ r :=
  Iff.rfl

/-- Reed--Muller codes are nested in their order. -/
theorem reedMuller_mono (hrs : r ≤ s) :
    reedMuller r n ≤ reedMuller s n := by
  intro f hf
  exact hf.trans hrs

private theorem anfCoeff_anfEval (c : ANFCoefficients n) :
    anfCoeff (anfEval c) = c := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]

private noncomputable def extendLowDegreeCoefficients
    (r n : ℕ) (c : ↥(FABL.lowDegreeFourierFamily n r) → FABL.𝔽₂) :
    ANFCoefficients n :=
  fun S ↦ if hS : S ∈ FABL.lowDegreeFourierFamily n r then c ⟨S, hS⟩ else 0

private noncomputable def reedMullerAnfEquiv (r n : ℕ) :
    reedMuller r n ≃ₗ[FABL.𝔽₂] (↥(FABL.lowDegreeFourierFamily n r) → FABL.𝔽₂) where
  toFun f S := anfCoeff f.1 S.1
  invFun c :=
    ⟨anfEval (extendLowDegreeCoefficients r n c), by
      rw [mem_reedMuller_iff, functionAlgebraicDegree, anfCoeff_anfEval,
        algebraicDegree_le_iff]
      intro S hS
      by_contra hSr
      have hSmem : S ∉ FABL.lowDegreeFourierFamily n r := by
        simpa using hSr
      exact hS (by simp [extendLowDegreeCoefficients, hSmem])⟩
  left_inv f := by
    apply Subtype.ext
    change anfEval (extendLowDegreeCoefficients r n fun S ↦ anfCoeff f.1 S.1) = f.1
    calc
      _ = anfEval (anfCoeff f.1) := by
        apply congrArg anfEval
        funext S
        by_cases hS : S.card ≤ r
        · have hSmem : S ∈ FABL.lowDegreeFourierFamily n r := by simpa
          simp [extendLowDegreeCoefficients, hSmem]
        · have hcoeff : anfCoeff f.1 S = 0 := by
            by_contra hne
            have := (algebraicDegree_le_iff (anfCoeff f.1) r).mp f.2 S hne
            exact hS this
          have hSmem : S ∉ FABL.lowDegreeFourierFamily n r := by
            simpa only [FABL.mem_lowDegreeFourierFamily, not_le] using (not_le.mp hS)
          simp [extendLowDegreeCoefficients, hSmem, hcoeff]
      _ = f.1 := anfEval_anfCoeff f.1
  right_inv c := by
    funext S
    change anfCoeff (anfEval (extendLowDegreeCoefficients r n c)) S.1 = c S
    rw [anfCoeff_anfEval]
    simp [extendLowDegreeCoefficients]
  map_add' f g := by
    funext S
    change anfCoeff (f.1 + g.1) S.1 = anfCoeff f.1 S.1 + anfCoeff g.1 S.1
    rw [anfCoeff_add]
  map_smul' c f := by
    by_cases hc : c = 0
    · subst c
      funext S
      simp
    · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
      subst c
      simp

/-- Carlet's dimension formula for the Reed--Muller code `R(r,n)`. -/
theorem reedMuller_finrank :
    Module.finrank FABL.𝔽₂ (reedMuller r n) =
      ∑ j ∈ Finset.range (r + 1), Nat.choose n j := by
  rw [LinearEquiv.finrank_eq (reedMullerAnfEquiv r n),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
    FABL.card_lowDegreeFourierFamily_eq_sum_choose]

/-- The number of Reed--Muller codewords is `2` raised to the number of
square-free monomials of degree at most `r`. -/
theorem reedMuller_card :
    Nat.card (reedMuller r n) =
      2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) := by
  rw [Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := reedMuller r n),
    Nat.card_zmod, reedMuller_finrank]

private def firstCoordinateSlice {n : ℕ} (f : BooleanFunction (n + 1))
    (b : FABL.𝔽₂) : BooleanFunction n :=
  fun x ↦ f (Fin.cons b x)

private theorem f₂CubeOfFinset_tailFrequency {n : ℕ} (T : Finset (Fin n)) :
    FABL.f₂CubeOfFinset (FABL.tailFrequency T) =
      Fin.cons 0 (FABL.f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]

private theorem f₂CubeOfFinset_insert_zero_tailFrequency {n : ℕ}
    (T : Finset (Fin n)) :
    FABL.f₂CubeOfFinset (insert 0 (FABL.tailFrequency T)) =
      Fin.cons 1 (FABL.f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [FABL.f₂CubeOfFinset]
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_zero {n : ℕ}
    (f : BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    anfCoeff (firstCoordinateSlice f 0) S = anfCoeff f (FABL.tailFrequency S) := by
  classical
  simp only [anfCoeff, firstCoordinateSlice]
  apply Finset.sum_bij (fun T _ ↦ FABL.tailFrequency T)
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    exact Finset.map_subset_map.mpr hT
  · intro T₁ hT₁ T₂ hT₂ heq
    exact Finset.map_injective (Fin.succEmb n) heq
  · intro U hU
    rw [Finset.mem_powerset] at hU
    obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
    exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
  · intro T hT
    rw [f₂CubeOfFinset_tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_one {n : ℕ}
    (f : BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    anfCoeff (firstCoordinateSlice f 1) S =
      anfCoeff f (FABL.tailFrequency S) +
        anfCoeff f (insert 0 (FABL.tailFrequency S)) := by
  classical
  have hsplit := Finset.sum_powerset_insert (FABL.zero_notMem_tailFrequency S)
    (fun U ↦ f (FABL.f₂CubeOfFinset U))
  have htail :
      (∑ U ∈ (FABL.tailFrequency S).powerset,
          f (FABL.f₂CubeOfFinset U)) = anfCoeff (firstCoordinateSlice f 0) S := by
    rw [anfCoeff_firstCoordinateSlice_zero]
    rfl
  have hone :
      (∑ U ∈ (FABL.tailFrequency S).powerset,
          f (FABL.f₂CubeOfFinset (insert 0 U))) =
        anfCoeff (firstCoordinateSlice f 1) S := by
    simp only [anfCoeff, firstCoordinateSlice]
    symm
    apply Finset.sum_bij (fun T _ ↦ FABL.tailFrequency T)
    · intro T hT
      rw [Finset.mem_powerset] at hT ⊢
      exact Finset.map_subset_map.mpr hT
    · intro T₁ hT₁ T₂ hT₂ heq
      exact Finset.map_injective (Fin.succEmb n) heq
    · intro U hU
      rw [Finset.mem_powerset] at hU
      obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
      exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
    · intro T hT
      rw [f₂CubeOfFinset_insert_zero_tailFrequency]
  have hcoeff : anfCoeff f (insert 0 (FABL.tailFrequency S)) =
      anfCoeff (firstCoordinateSlice f 0) S +
        anfCoeff (firstCoordinateSlice f 1) S := by
    simpa only [anfCoeff, htail, hone] using hsplit
  rw [← anfCoeff_firstCoordinateSlice_zero]
  rw [hcoeff, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem hammingWeight_firstCoordinateSlices {n : ℕ}
    (f : BooleanFunction (n + 1)) :
    hammingWeight f = hammingWeight (firstCoordinateSlice f 0) +
      hammingWeight (firstCoordinateSlice f 1) := by
  classical
  simp only [hammingWeight_eq_card_support, support, Finset.card_filter]
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (n + 1) ↦ FABL.𝔽₂)).symm
    (fun x ↦ if f x = 1 then 1 else 0)
    (fun bx ↦ if f (Fin.cons bx.1 bx.2) = 1 then 1 else 0)
    (fun x ↦ by rw [← Fin.cons_self_tail x]; rfl)]
  rw [Fintype.sum_prod_type]
  have htwo : (Finset.univ : Finset FABL.𝔽₂) = {0, 1} := rfl
  rw [htwo]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton]
  rfl

private theorem functionAlgebraicDegree_firstCoordinateSlice_zero_le {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (firstCoordinateSlice f 0) ≤ k := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
    (FABL.tailFrequency S) hS
  simpa using hcard

private theorem functionAlgebraicDegree_firstCoordinateSlice_one_le {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (firstCoordinateSlice f 1) ≤ k := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  rw [anfCoeff_firstCoordinateSlice_one] at hS
  have hne : anfCoeff f (FABL.tailFrequency S) ≠ 0 ∨
      anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hS (by rw [h.1, h.2, add_zero])
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  rcases hne with htail | hinsert
  · have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
      (FABL.tailFrequency S) htail
    simpa using hcard
  · have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
      (insert 0 (FABL.tailFrequency S)) hinsert
    rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
      FABL.card_tailFrequency] at hcard
    omega

private theorem functionAlgebraicDegree_firstCoordinateSlice_le {n k : ℕ}
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂)
    (hdegree : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (firstCoordinateSlice f b) ≤ k := by
  by_cases hb : b = 0
  · subst b
    exact functionAlgebraicDegree_firstCoordinateSlice_zero_le f hdegree
  · have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
    subst b
    exact functionAlgebraicDegree_firstCoordinateSlice_one_le f hdegree

private theorem functionAlgebraicDegree_firstCoordinateSlice_one_le_pred {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k)
    (hzero : firstCoordinateSlice f 0 = 0) :
    functionAlgebraicDegree (firstCoordinateSlice f 1) ≤ k - 1 := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  have hzeroCoeff : anfCoeff (firstCoordinateSlice f 0) S = 0 := by rw [hzero]; simp
  rw [anfCoeff_firstCoordinateSlice_one, ← anfCoeff_firstCoordinateSlice_zero,
    hzeroCoeff, zero_add] at hS
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
    (insert 0 (FABL.tailFrequency S)) hS
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hcard
  omega

private theorem functionAlgebraicDegree_firstCoordinateSlice_zero_le_pred {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k)
    (hone : firstCoordinateSlice f 1 = 0) :
    functionAlgebraicDegree (firstCoordinateSlice f 0) ≤ k - 1 := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  have honeCoeff : anfCoeff (firstCoordinateSlice f 1) S = 0 := by rw [hone]; simp
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hinsert : anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
    intro hinsert
    have hrel := anfCoeff_firstCoordinateSlice_one f S
    rw [honeCoeff, hinsert, add_zero] at hrel
    exact hS hrel.symm
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
    (insert 0 (FABL.tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hcard
  omega

private theorem exists_anfCoeff_ne_zero {n : ℕ} (f : BooleanFunction n) (hf : f ≠ 0) :
    ∃ S, anfCoeff f S ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  rw [← anfEval_anfCoeff f]
  funext x
  simp [anfEval, h]

private theorem degree_bound_pos_of_slice_one_ne_zero {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k)
    (hzero : firstCoordinateSlice f 0 = 0)
    (hone : firstCoordinateSlice f 1 ≠ 0) : 0 < k := by
  obtain ⟨S, hS⟩ := exists_anfCoeff_ne_zero (firstCoordinateSlice f 1) hone
  have hzeroCoeff : anfCoeff (firstCoordinateSlice f 0) S = 0 := by rw [hzero]; simp
  have hinsert : anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
    rw [anfCoeff_firstCoordinateSlice_one, ← anfCoeff_firstCoordinateSlice_zero,
      hzeroCoeff, zero_add] at hS
    exact hS
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
    (insert 0 (FABL.tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hcard
  omega

private theorem degree_bound_pos_of_slice_zero_ne_zero {n k : ℕ}
    (f : BooleanFunction (n + 1)) (hdegree : functionAlgebraicDegree f ≤ k)
    (hone : firstCoordinateSlice f 1 = 0)
    (hzero : firstCoordinateSlice f 0 ≠ 0) : 0 < k := by
  obtain ⟨S, hS⟩ := exists_anfCoeff_ne_zero (firstCoordinateSlice f 0) hzero
  have honeCoeff : anfCoeff (firstCoordinateSlice f 1) S = 0 := by rw [hone]; simp
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hinsert : anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
    intro hinsert
    have hrel := anfCoeff_firstCoordinateSlice_one f S
    rw [honeCoeff, hinsert, add_zero] at hrel
    exact hS hrel.symm
  have hdegree' : algebraicDegree (anfCoeff f) ≤ k := hdegree
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdegree'
    (insert 0 (FABL.tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hcard
  omega

private theorem eq_zero_of_firstCoordinateSlices_eq_zero {n : ℕ}
    (f : BooleanFunction (n + 1)) (hzero : firstCoordinateSlice f 0 = 0)
    (hone : firstCoordinateSlice f 1 = 0) : f = 0 := by
  funext x
  rw [← Fin.cons_self_tail x]
  by_cases hx : x 0 = 0
  · rw [hx]
    exact congrFun hzero (Fin.tail x)
  · have hxone : x 0 = 1 := Fin.eq_one_of_ne_zero _ hx
    rw [hxone]
    exact congrFun hone (Fin.tail x)

/-- Carlet Theorem 1: a nonzero Boolean function of algebraic degree at most `r`
has Hamming weight at least `2^(n-r)`. -/
theorem two_pow_sub_le_hammingWeight_of_degree_le
    (f : BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ r) (hf : f ≠ 0) :
    2 ^ (n - r) ≤ hammingWeight f := by
  induction n generalizing r with
  | zero =>
      let x₀ : FABL.F₂Cube 0 := fun i ↦ Fin.elim0 i
      have hx₀ : f x₀ ≠ 0 := by
        intro hx
        apply hf
        funext x
        rw [Subsingleton.elim x x₀, hx]
        rfl
      have hx₀one : f x₀ = 1 := Fin.eq_one_of_ne_zero _ hx₀
      simp only [Nat.zero_sub, pow_zero]
      rw [hammingWeight_eq_card_support]
      exact Finset.card_pos.mpr ⟨x₀, (mem_support f x₀).mpr hx₀one⟩
  | succ n ih =>
      let fzero : BooleanFunction n := firstCoordinateSlice f 0
      let fone : BooleanFunction n := firstCoordinateSlice f 1
      have hweight : hammingWeight f = hammingWeight fzero + hammingWeight fone := by
        simpa [fzero, fone] using hammingWeight_firstCoordinateSlices f
      by_cases hzero : fzero = 0
      · have hone : fone ≠ 0 := by
          intro hone
          apply hf
          exact eq_zero_of_firstCoordinateSlices_eq_zero f
            (by simpa [fzero] using hzero) (by simpa [fone] using hone)
        have hr : 0 < r := degree_bound_pos_of_slice_one_ne_zero f hdegree
          (by simpa [fzero] using hzero) (by simpa [fone] using hone)
        have honeDegree : functionAlgebraicDegree fone ≤ r - 1 := by
          simpa [fone] using functionAlgebraicDegree_firstCoordinateSlice_one_le_pred f hdegree
            (by simpa [fzero] using hzero)
        have hbound := ih fone honeDegree hone
        have hexp : (n + 1) - r = n - (r - 1) := by omega
        rw [hweight, hzero]
        rw [show hammingWeight (0 : BooleanFunction n) = 0 by simp,
          zero_add, hexp]
        exact hbound
      · by_cases hone : fone = 0
        · have hr : 0 < r := degree_bound_pos_of_slice_zero_ne_zero f hdegree
            (by simpa [fone] using hone) (by simpa [fzero] using hzero)
          have hzeroDegree : functionAlgebraicDegree fzero ≤ r - 1 := by
            simpa [fzero] using functionAlgebraicDegree_firstCoordinateSlice_zero_le_pred f hdegree
              (by simpa [fone] using hone)
          have hbound := ih fzero hzeroDegree hzero
          have hexp : (n + 1) - r = n - (r - 1) := by omega
          rw [hweight, hone]
          rw [show hammingWeight (0 : BooleanFunction n) = 0 by simp,
            add_zero, hexp]
          exact hbound
        · have hzeroDegree : functionAlgebraicDegree fzero ≤ r := by
            simpa [fzero] using functionAlgebraicDegree_firstCoordinateSlice_le f 0 hdegree
          have honeDegree : functionAlgebraicDegree fone ≤ r := by
            simpa [fone] using functionAlgebraicDegree_firstCoordinateSlice_le f 1 hdegree
          have hzeroBound := ih fzero hzeroDegree hzero
          have honeBound := ih fone honeDegree hone
          have hpow : 2 ^ ((n + 1) - r) ≤ 2 ^ (n - r) + 2 ^ (n - r) := by
            by_cases hrn : r ≤ n
            · rw [show (n + 1) - r = (n - r) + 1 by omega, pow_succ]
              omega
            · have hrn' : n < r := by omega
              rw [show (n + 1) - r = 0 by omega, show n - r = 0 by omega]
              norm_num
          rw [hweight]
          exact hpow.trans (Nat.add_le_add hzeroBound honeBound)

/-- Carlet Theorem 1 in coding form: distinct words of `R(r,n)` have raw
Hamming distance at least `2^(n-r)`. -/
theorem reedMuller_distance_lower_bound
    {f g : BooleanFunction n} (hf : f ∈ reedMuller r n)
    (hg : g ∈ reedMuller r n) (hfg : f ≠ g) :
    2 ^ (n - r) ≤ hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add]
  apply two_pow_sub_le_hammingWeight_of_degree_le (f + g)
  · exact (functionAlgebraicDegree_add_le_max f g).trans (max_le hf hg)
  · intro hadd
    apply hfg
    funext x
    have hx := congrFun hadd x
    change f x + g x = 0 at hx
    exact (add_eq_zero_iff_eq_neg.mp hx).trans (ZMod.neg_eq_self_mod_two (g x))

/-- Every affine function belongs to the first-order Reed--Muller code. -/
theorem affineFunction_mem_reedMuller_one
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    affineFunction b a ∈ reedMuller 1 n :=
  functionAlgebraicDegree_affineFunction_le_one b a

/-- The weight of the constant-one Boolean function is the cube cardinality. -/
theorem hammingWeight_affineFunction_one_zero :
    hammingWeight (affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n)) = 2 ^ n := by
  classical
  rw [hammingWeight_eq_card_support, support]
  have hfilter :
      (Finset.univ.filter fun x : FABL.F₂Cube n ↦
        affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube n) x = 1) = Finset.univ := by
    ext x
    simp [affineFunction, FABL.f₂DotProduct]
  rw [hfilter, Finset.card_univ, card_f₂Cube]

/-- A nonzero Boolean function of degree at most one has weight at least
`2^(n-1)`.  This is Carlet Theorem 1 for first-order Reed--Muller codes. -/
theorem two_pow_sub_one_le_hammingWeight_of_degree_le_one
    (f : BooleanFunction n) (hdegree : functionAlgebraicDegree f ≤ 1)
    (hf : f ≠ 0) :
    2 ^ (n - 1) ≤ hammingWeight f :=
  two_pow_sub_le_hammingWeight_of_degree_le f hdegree hf

/-- Distinct first-order Reed--Muller codewords have distance at least
`2^(n-1)`. -/
theorem reedMuller_one_distance_lower_bound
    {f g : BooleanFunction n} (hf : f ∈ reedMuller 1 n)
    (hg : g ∈ reedMuller 1 n) (hfg : f ≠ g) :
    2 ^ (n - 1) ≤ hammingDistance f g :=
  reedMuller_distance_lower_bound hf hg hfg

/-- Distinct Reed--Muller codewords always have positive raw Hamming distance. -/
theorem reedMuller_distance_pos
    {f g : BooleanFunction n} (_hf : f ∈ reedMuller r n)
    (_hg : g ∈ reedMuller r n) (hfg : f ≠ g) :
    0 < hammingDistance f g := by
  rw [hammingDistance, hammingDist_pos]
  exact hfg

end CryptBoolean
