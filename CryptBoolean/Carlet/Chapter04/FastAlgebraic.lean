/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AnnihilatorLinearSystem
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Carlet Chapter 4 fast algebraic relations

The dimension argument producing low-degree relations, optimality against such relations, and
the algebraic-immunity lower bound on a nonzero product.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n e d : ℕ}

/-- The two low-degree coefficient counts exceed the Boolean-function-space dimension whenever
the two degree bounds add to at least the number of variables. -/
theorem two_pow_lt_sum_choose_add_sum_choose_of_add_ge
    (n e d : ℕ) (hed : n ≤ e + d) :
    2 ^ n <
      (∑ i ∈ Finset.range (e + 1), Nat.choose n i) +
      ∑ i ∈ Finset.range (d + 1), Nat.choose n i := by
  by_cases hen : e ≤ n
  · have hne : n - e ≤ d := by omega
    have hsubset : Finset.range (n - e + 1) ⊆ Finset.range (d + 1) :=
      Finset.range_mono (by omega)
    have hsmallLarge :
        (∑ i ∈ Finset.range (n - e + 1), Nat.choose n i) ≤
          ∑ i ∈ Finset.range (d + 1), Nat.choose n i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro i _hi _hnot
        exact Nat.zero_le _)
    have hreflect := Finset.sum_Ico_reflect
      (fun i ↦ Nat.choose n i) 0 (n := n) (m := n - e + 1) (by omega)
    have hsymm :
        (∑ i ∈ Finset.range (n - e + 1), Nat.choose n i) =
          ∑ i ∈ Finset.Ico e (n + 1), Nat.choose n i := by
      have hsub : n + 1 - (n - e + 1) = e := by omega
      rw [hsub] at hreflect
      rw [Finset.range_eq_Ico]
      calc
        (∑ i ∈ Finset.Ico 0 (n - e + 1), Nat.choose n i) =
            ∑ i ∈ Finset.Ico 0 (n - e + 1), Nat.choose n (n - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          symm
          exact Nat.choose_symm (by
            have := Finset.mem_Ico.mp hi
            omega)
        _ = ∑ i ∈ Finset.Ico e (n + 1), Nat.choose n i := by
          simpa using hreflect
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun i ↦ Nat.choose n i) (show e ≤ n + 1 by omega)
    have hfirst :
        (∑ i ∈ Finset.range (e + 1), Nat.choose n i) =
          (∑ i ∈ Finset.range e, Nat.choose n i) + Nat.choose n e := by
      rw [Finset.sum_range_succ]
    have hfull := Nat.sum_range_choose n
    have hchoose : 0 < Nat.choose n e := Nat.choose_pos hen
    rw [hsymm] at hsmallLarge
    rw [hfirst]
    omega
  · have hnen : n + 1 ≤ e + 1 := by omega
    have hsubset : Finset.range (n + 1) ⊆ Finset.range (e + 1) :=
      Finset.range_mono hnen
    have hfullLe :
        (∑ i ∈ Finset.range (n + 1), Nat.choose n i) ≤
          ∑ i ∈ Finset.range (e + 1), Nat.choose n i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro i _hi _hnot
        exact Nat.zero_le _)
    have hzeroMem : 0 ∈ Finset.range (d + 1) := by simp
    have honeLe : 1 ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose n i := by
      simpa using Finset.single_le_sum
        (fun i (_hi : i ∈ Finset.range (d + 1)) ↦ Nat.zero_le (Nat.choose n i))
        hzeroMem
    rw [Nat.sum_range_choose] at hfullLe
    omega

/-- Carlet's equivalent numerical form of the dimension condition. -/
theorem sum_choose_add_sum_choose_gt_iff
    (n e d : ℕ) :
    2 ^ n <
        (∑ i ∈ Finset.range (e + 1), Nat.choose n i) +
        ∑ i ∈ Finset.range (d + 1), Nat.choose n i ↔
      n ≤ e + d := by
  constructor
  · intro hsum
    by_contra hed
    have hedlt : e + d < n := Nat.lt_of_not_ge hed
    have hd : d ≤ n := by omega
    have hreflect := Finset.sum_Ico_reflect
      (fun i ↦ Nat.choose n i) 0 (n := n) (m := d + 1) (by omega)
    have hsub : n + 1 - (d + 1) = n - d := by omega
    rw [hsub] at hreflect
    have hsymm :
        (∑ i ∈ Finset.range (d + 1), Nat.choose n i) =
          ∑ i ∈ Finset.Ico (n - d) (n + 1), Nat.choose n i := by
      rw [Finset.range_eq_Ico]
      calc
        (∑ i ∈ Finset.Ico 0 (d + 1), Nat.choose n i) =
            ∑ i ∈ Finset.Ico 0 (d + 1), Nat.choose n (n - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          symm
          exact Nat.choose_symm (by
            have := Finset.mem_Ico.mp hi
            omega)
        _ = ∑ i ∈ Finset.Ico (n - d) (n + 1), Nat.choose n i := by
          simpa using hreflect
    let low := Finset.range (e + 1)
    let high := Finset.Ico (n - d) (n + 1)
    have hdisjoint : Disjoint low high := by
      rw [Finset.disjoint_left]
      intro i hilow hihigh
      have hilow' := Finset.mem_range.mp hilow
      have hihigh' := Finset.mem_Ico.mp hihigh
      omega
    have hsubset : low ∪ high ⊆ Finset.range (n + 1) := by
      intro i hi
      rcases Finset.mem_union.mp hi with hilow | hihigh
      · exact Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hilow
          omega)
      · exact Finset.mem_range.mpr (Finset.mem_Ico.mp hihigh).2
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro i _hi _hnot
      exact Nat.zero_le (Nat.choose n i))
    rw [Finset.sum_union hdisjoint, Nat.sum_range_choose] at hle
    change
      (∑ i ∈ Finset.range (e + 1), Nat.choose n i) +
          ∑ i ∈ high, Nat.choose n i ≤ 2 ^ n at hle
    rw [← hsymm] at hle
    omega
  · exact two_pow_lt_sum_choose_add_sum_choose_of_add_ge n e d

/-- The linear map whose kernel consists of bounded-degree relations `f*g=h`. -/
noncomputable def fastAlgebraicRelationLinearMap
    (f : BooleanFunction n) (e d : ℕ) :
    (reedMuller e n × reedMuller d n) →ₗ[FABL.𝔽₂] BooleanFunction n where
  toFun p := f * p.1.1 + p.2.1
  map_add' p q := by
    ext x
    change f x * (p.1.1 x + q.1.1 x) + (p.2.1 x + q.2.1 x) =
      (f x * p.1.1 x + p.2.1 x) + (f x * q.1.1 x + q.2.1 x)
    ring
  map_smul' a p := by
    ext x
    change f x * (a * p.1.1 x) + a * p.2.1 x =
      a * (f x * p.1.1 x + p.2.1 x)
    ring

/-- Carlet's dimension argument: if `e+d≥n`, there is a nonzero `g` of degree at most `e`
whose product with `f` has degree at most `d`. -/
theorem exists_fastAlgebraicRelation_of_add_ge
    (f : BooleanFunction n) (hed : n ≤ e + d) :
    ∃ g h : BooleanFunction n,
      g ≠ 0 ∧
      FABL.functionAlgebraicDegree g ≤ e ∧
      FABL.functionAlgebraicDegree h ≤ d ∧
      f * g = h := by
  let L := fastAlgebraicRelationLinearMap f e d
  have hdim :
      Module.finrank FABL.𝔽₂ (BooleanFunction n) <
        Module.finrank FABL.𝔽₂ (reedMuller e n × reedMuller d n) := by
    rw [Module.finrank_prod, reedMuller_finrank, reedMuller_finrank,
      Module.finrank_fintype_fun_eq_card, FABL.card_f₂Cube]
    exact two_pow_lt_sum_choose_add_sum_choose_of_add_ge n e d hed
  have hnotInjective : ¬ Function.Injective L := by
    intro hinjective
    have := LinearMap.finrank_le_finrank_of_injective hinjective
    omega
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    exact hnotInjective ((LinearMap.ker_eq_bot).mp hbot)
  obtain ⟨p, hpKernel, hpNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hpMap : L p = 0 := (LinearMap.mem_ker.mp hpKernel)
  have hrelation : f * p.1.1 = p.2.1 := by
    funext x
    have hx := congrFun hpMap x
    change f x * p.1.1 x + p.2.1 x = 0 at hx
    exact (eq_neg_of_add_eq_zero_left hx).trans
      (ZMod.neg_eq_self_mod_two (p.2.1 x))
  have hpFirstNe : p.1 ≠ 0 := by
    intro hpFirst
    have hpFirstVal : p.1.1 = 0 := congrArg Subtype.val hpFirst
    have hpSecondVal : p.2.1 = 0 := by
      rw [← hrelation, hpFirstVal, mul_zero]
    have hpSecond : p.2 = 0 := Subtype.ext hpSecondVal
    apply hpNe
    exact Prod.ext hpFirst hpSecond
  exact ⟨p.1.1, p.2.1,
    fun hzero ↦ hpFirstNe (Subtype.ext hzero), p.1.2, p.2.2, hrelation⟩

/-- Optimality against fast algebraic attacks: every nonzero multiplicand relation has total
degree at least `n`. -/
def IsFastAlgebraicallyOptimal (f : BooleanFunction n) : Prop :=
  ∀ g h : BooleanFunction n,
    g ≠ 0 → f * g = h →
      n ≤ FABL.functionAlgebraicDegree g + FABL.functionAlgebraicDegree h

/-- The quantified lower-bound definition is equivalent to absence of a subcritical relation. -/
theorem isFastAlgebraicallyOptimal_iff_no_lowDegreeRelation
    (f : BooleanFunction n) :
    IsFastAlgebraicallyOptimal f ↔
      ¬ ∃ g h : BooleanFunction n,
        g ≠ 0 ∧ f * g = h ∧
          FABL.functionAlgebraicDegree g + FABL.functionAlgebraicDegree h < n := by
  constructor
  · intro hf
    rintro ⟨g, h, hg, hrelation, hdegree⟩
    exact (Nat.not_lt_of_ge (hf g h hg hrelation)) hdegree
  · intro hf g h hg hrelation
    by_contra hdegree
    exact hf ⟨g, h, hg, hrelation, Nat.lt_of_not_ge hdegree⟩

/-- A nonzero product in a fast algebraic relation has degree at least the algebraic immunity. -/
theorem algebraicImmunity_le_degree_of_mul_eq_of_ne_zero
    (f g h : BooleanFunction n) (hrelation : f * g = h) (hh : h ≠ 0) :
    algebraicImmunity f ≤ FABL.functionAlgebraicDegree h := by
  apply algebraicImmunity_le_functionAlgebraicDegree f h
  right
  refine ⟨hh, ?_⟩
  calc
    (f + 1) * h = (f + 1) * (f * g) := by rw [hrelation]
    _ = ((f + 1) * f) * g := by rw [mul_assoc]
    _ = 0 * g := by
      rw [add_mul, one_mul, booleanFunction_mul_self,
        ZModModule.add_self]
    _ = 0 := zero_mul g

end CryptBoolean
