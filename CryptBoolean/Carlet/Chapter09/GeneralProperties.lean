/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerDuality
public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter05.Normality
public import CryptBoolean.Carlet.Chapter05.QuadraticValues

/-!
# General properties of algebraic immunity

Carlet Chapter 9: complementation, the odd-dimensional one-sided criterion,
normality and weight bounds, and stability under low-degree perturbations.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m n k : ℕ}

private theorem isAlgebraicImmunityWitness_add_one_iff
    (f g : BooleanFunction n) :
    IsAlgebraicImmunityWitness (f + 1) g ↔
      IsAlgebraicImmunityWitness f g := by
  have hcancel : (f + 1) + 1 = f := by
    funext x
    change f x + 1 + 1 = f x
    rw [add_assoc, ZModModule.add_self, add_zero]
  simp only [IsAlgebraicImmunityWitness, hcancel, or_comm]

/-- Algebraic immunity is invariant under complementation. -/
theorem algebraicImmunity_add_constant_one (f : BooleanFunction n) :
    algebraicImmunity (f + 1) = algebraicImmunity f := by
  apply Nat.le_antisymm
  · obtain ⟨g, hg, hdegree⟩ :=
      exists_witness_functionAlgebraicDegree_eq_algebraicImmunity f
    calc
      algebraicImmunity (f + 1) ≤ FABL.functionAlgebraicDegree g :=
        algebraicImmunity_le_functionAlgebraicDegree (f + 1) g
          ((isAlgebraicImmunityWitness_add_one_iff f g).2 hg)
      _ = algebraicImmunity f := hdegree
  · obtain ⟨g, hg, hdegree⟩ :=
      exists_witness_functionAlgebraicDegree_eq_algebraicImmunity (f + 1)
    calc
      algebraicImmunity f ≤ FABL.functionAlgebraicDegree g :=
        algebraicImmunity_le_functionAlgebraicDegree f g
          ((isAlgebraicImmunityWitness_add_one_iff f g).1 hg)
      _ = algebraicImmunity (f + 1) := hdegree

/-- A `k`-normal `n`-variable Boolean function has algebraic immunity at most `n-k`. -/
theorem algebraicImmunity_le_sub_of_isKNormal
    (f : BooleanFunction n) (hf : IsKNormal f k) :
    algebraicImmunity f ≤ n - k := by
  obtain ⟨H, a, hfinrank, b, hconstant⟩ := hf
  let q := affineFlatIndicator H a
  have haMem : a ∈ FABL.binaryAffineSubspace H a := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem, ZModModule.add_self]
    exact H.zero_mem
  have hqNe : q ≠ 0 := by
    intro hzero
    have ha := congrFun hzero a
    have hqa : q a = 1 := by
      exact (affineFlatIndicator_apply_eq_one_iff H a a).2 haMem
    rw [hqa] at ha
    exact one_ne_zero ha
  have hproduct : (f + fun _ ↦ b) * q = 0 := by
    funext x
    by_cases hx : x ∈ FABL.binaryAffineSubspace H a
    · change (f x + b) * q x = 0
      rw [hconstant x hx, ZModModule.add_self]
      simp
    · simp [q, affineFlatIndicator, hx]
  have hwitness : IsAlgebraicImmunityWitness f q := by
    by_cases hb : b = 0
    · subst b
      left
      refine ⟨hqNe, ?_⟩
      change (f + (0 : BooleanFunction n)) * q = 0 at hproduct
      simpa using hproduct
    · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
      subst b
      right
      change (f + (1 : BooleanFunction n)) * q = 0 at hproduct
      exact ⟨hqNe, hproduct⟩
  calc
    algebraicImmunity f ≤ FABL.functionAlgebraicDegree q :=
      algebraicImmunity_le_functionAlgebraicDegree f q hwitness
    _ = FABL.f₂Codimension H :=
      functionAlgebraicDegree_affineFlatIndicator H a
    _ = n - k := by
      rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace, hfinrank]

private theorem exists_lowDegree_annihilator_of_hammingWeight_lt_sum_choose
    (f : BooleanFunction n) (d : ℕ)
    (hweight : hammingWeight f <
      ∑ i ∈ Finset.range (d + 1), Nat.choose n i) :
    ∃ g : BooleanFunction n,
      g ≠ 0 ∧ FABL.functionAlgebraicDegree g ≤ d ∧ f * g = 0 := by
  let L := annihilatorEvaluationLinearMap f d
  have hdim :
      Module.finrank FABL.𝔽₂ (↥(support f) → FABL.𝔽₂) <
        Module.finrank FABL.𝔽₂
          (↥(FABL.lowDegreeFourierFamily n d) → FABL.𝔽₂) := by
    rw [annihilatorEvaluationLinearMap_codomain_finrank,
      annihilatorEvaluationLinearMap_domain_finrank]
    exact hweight
  have hnotInjective : ¬ Function.Injective L := by
    intro hinjective
    have := LinearMap.finrank_le_finrank_of_injective hinjective
    omega
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    exact hnotInjective ((LinearMap.ker_eq_bot).mp hbot)
  obtain ⟨c, hcKernel, hcNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  let q : reedMuller d n := (reedMullerAnfEquiv d n).symm c
  have hqSubtypeNe : q ≠ 0 := by
    intro hzero
    apply hcNe
    have hmap := congrArg (reedMullerAnfEquiv d n) hzero
    simpa [q] using hmap
  have hqNe : q.1 ≠ 0 := by
    intro hzero
    apply hqSubtypeNe
    exact Subtype.ext hzero
  have hproduct : f * q.1 = 0 :=
    (mem_ker_annihilatorEvaluationLinearMap_iff f c).1 hcKernel
  exact ⟨q.1, hqNe, q.2, hproduct⟩

/-- The weight of a Boolean function is at least the number of monomials of
degree strictly below its algebraic immunity. -/
theorem sum_choose_below_algebraicImmunity_le_hammingWeight
    (f : BooleanFunction n) :
    (∑ i ∈ Finset.range (algebraicImmunity f), Nat.choose n i) ≤
      hammingWeight f := by
  by_cases hzero : algebraicImmunity f = 0
  · simp [hzero]
  · by_contra hbound
    have hlt : hammingWeight f <
        ∑ i ∈ Finset.range (algebraicImmunity f), Nat.choose n i :=
      Nat.lt_of_not_ge hbound
    obtain ⟨g, hgNe, hgDegree, hgProduct⟩ :=
      exists_lowDegree_annihilator_of_hammingWeight_lt_sum_choose
        f (algebraicImmunity f - 1) (by
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hzero)] using hlt)
    have hAI := algebraicImmunity_le_functionAlgebraicDegree f g
      (Or.inl ⟨hgNe, hgProduct⟩)
    omega

private theorem sum_choose_to_complement_eq_two_pow_sub_sum_choose_below
    (a n : ℕ) (ha : a ≤ n) :
    (∑ i ∈ Finset.range (n - a + 1), Nat.choose n i) =
      2 ^ n - ∑ i ∈ Finset.range a, Nat.choose n i := by
  have hreflect := Finset.sum_Ico_reflect
    (fun i ↦ Nat.choose n i) 0 (n := n) (m := a) (by omega)
  have hsub : n + 1 - a = n - a + 1 := by omega
  rw [hsub] at hreflect
  have hsymm :
      (∑ i ∈ Finset.range a, Nat.choose n i) =
        ∑ i ∈ Finset.Ico (n - a + 1) (n + 1), Nat.choose n i := by
    rw [Finset.range_eq_Ico]
    calc
      (∑ i ∈ Finset.Ico 0 a, Nat.choose n i) =
          ∑ i ∈ Finset.Ico 0 a, Nat.choose n (n - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact Nat.choose_symm (by
          have := Finset.mem_Ico.mp hi
          omega)
      _ = ∑ i ∈ Finset.Ico (n - a + 1) (n + 1), Nat.choose n i := by
        simpa using hreflect
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i ↦ Nat.choose n i) (show n - a + 1 ≤ n + 1 by omega)
  have hfull := Nat.sum_range_choose n
  rw [← hsymm] at hsplit
  omega

/-- The weight of a Boolean function is at most the complementary binomial
sum determined by its algebraic immunity. -/
theorem hammingWeight_le_sum_choose_to_sub_algebraicImmunity
    (f : BooleanFunction n) :
    hammingWeight f ≤
      ∑ i ∈ Finset.range (n - algebraicImmunity f + 1), Nat.choose n i := by
  have hAILe : algebraicImmunity f ≤ n :=
    (algebraicImmunity_le_ceiling_half f).trans (by omega)
  have hlower :=
    sum_choose_below_algebraicImmunity_le_hammingWeight (f + 1)
  rw [algebraicImmunity_add_constant_one] at hlower
  have hone : (1 : BooleanFunction n) = FABL.affineFunction 1 0 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
  have hcomplement : hammingWeight (f + 1) = 2 ^ n - hammingWeight f := by
    rw [hone]
    exact hammingWeight_add_constant_one f
  rw [hcomplement] at hlower
  have hweightLe : hammingWeight f ≤ 2 ^ n := by
    rw [hammingWeight_eq_card_support, ← FABL.card_f₂Cube]
    exact Finset.card_le_univ _
  have hsub : hammingWeight f ≤
      2 ^ n - ∑ i ∈ Finset.range (algebraicImmunity f), Nat.choose n i := by
    omega
  rw [← sum_choose_to_complement_eq_two_pow_sub_sum_choose_below
    (algebraicImmunity f) n hAILe] at hsub
  exact hsub

/-- In odd dimension, every function with optimal algebraic immunity is balanced. -/
theorem isBalanced_of_odd_of_algebraicImmunity_eq_ceiling_half
    (f : BooleanFunction n) (hn : Odd n)
    (hAI : algebraicImmunity f = (n + 1) / 2) :
    IsBalanced f := by
  obtain ⟨m, hm⟩ := hn
  subst n
  have hhalf : ((2 * m + 1 + 1) / 2) = m + 1 := by omega
  have hcomplement : 2 * m + 1 - (m + 1) + 1 = m + 1 := by omega
  have hsum :
      (∑ i ∈ Finset.range (m + 1), Nat.choose (2 * m + 1) i) = 4 ^ m :=
    Nat.sum_range_choose_halfway m
  have hlower := sum_choose_below_algebraicImmunity_le_hammingWeight f
  have hupper := hammingWeight_le_sum_choose_to_sub_algebraicImmunity f
  rw [hAI, hhalf, hsum] at hlower
  rw [hAI, hhalf, hcomplement, hsum] at hupper
  have hweight : hammingWeight f = 4 ^ m := by omega
  have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    omega
  unfold IsBalanced
  rw [hweight, hpow]

private theorem no_lowDegree_complement_annihilator_of_odd_balanced
    (f : BooleanFunction (2 * m + 1)) (hbalanced : IsBalanced f)
    (hnoAnnihilator : ∀ g : BooleanFunction (2 * m + 1),
      g ≠ 0 → FABL.functionAlgebraicDegree g ≤ m → f * g ≠ 0)
    (g : BooleanFunction (2 * m + 1))
    (hg : IsAnnihilator (f + 1) g)
    (hgDegree : FABL.functionAlgebraicDegree g ≤ m) : False := by
  let L := annihilatorEvaluationLinearMap f m
  have hInjective : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro c hc
      have hproduct :=
        (mem_ker_annihilatorEvaluationLinearMap_iff f c).1 hc
      have hcZero : c = 0 := by
        by_contra hcNe
        let q : reedMuller m (2 * m + 1) :=
          (reedMullerAnfEquiv m (2 * m + 1)).symm c
        have hqSubtypeNe : q ≠ 0 := by
          intro hzero
          apply hcNe
          have hmap := congrArg
            (reedMullerAnfEquiv m (2 * m + 1)) hzero
          simpa [q] using hmap
        have hqNe : q.1 ≠ 0 := by
          intro hzero
          apply hqSubtypeNe
          exact Subtype.ext hzero
        exact (hnoAnnihilator q.1 hqNe q.2) hproduct
      simp [hcZero]
    · exact bot_le
  have hpow : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    omega
  have hweight : hammingWeight f = 4 ^ m := by
    unfold IsBalanced at hbalanced
    rw [hpow] at hbalanced
    omega
  have hdim :
      Module.finrank FABL.𝔽₂
          (↥(FABL.lowDegreeFourierFamily (2 * m + 1) m) → FABL.𝔽₂) =
        Module.finrank FABL.𝔽₂ (↥(support f) → FABL.𝔽₂) := by
    rw [annihilatorEvaluationLinearMap_domain_finrank,
      annihilatorEvaluationLinearMap_codomain_finrank, hweight]
    exact Nat.sum_range_choose_halfway m
  have hSurjective : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hInjective
  have hxExists : ∃ x, g x ≠ 0 := by
    by_contra h
    push Not at h
    apply hg.1
    funext x
    exact h x
  obtain ⟨x, hxNe⟩ := hxExists
  have hxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hxNe
  have hfxOne : f x = 1 := by
    by_cases hfx : f x = 0
    · have hxProduct := congrFun hg.2 x
      change (f x + 1) * g x = 0 at hxProduct
      rw [hfx, zero_add, one_mul] at hxProduct
      exact (hxNe hxProduct).elim
    · exact Fin.eq_one_of_ne_zero _ hfx
  have hxSupport : x ∈ support f := (mem_support f x).2 hfxOne
  let target : ↥(support f) → FABL.𝔽₂ :=
    fun z ↦ if z.1 = x then 1 else 0
  obtain ⟨c, hc⟩ := hSurjective target
  let q : reedMuller m (2 * m + 1) :=
    (reedMullerAnfEquiv m (2 * m + 1)).symm c
  have hqApply (z : ↥(support f)) :
      q.1 z.1 = if z.1 = x then 1 else 0 := by
    have hz := congrFun hc z
    change q.1 z.1 = target z at hz
    exact hz
  have hgDual : g ∈ reedMullerDual m (2 * m + 1) := by
    rw [reedMullerDual_eq (by omega : m < 2 * m + 1)]
    have horder : 2 * m + 1 - m - 1 = m := by omega
    rw [horder]
    exact hgDegree
  rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hgDual
  have hpairZero : booleanFunctionPairing (2 * m + 1) q.1 g = 0 :=
    hgDual q.1 q.2
  rw [booleanFunctionPairing_apply] at hpairZero
  have hpairOne : (∑ z, q.1 z * g z) = 1 := by
    rw [Fintype.sum_eq_single x]
    · have hqx := hqApply ⟨x, hxSupport⟩
      rw [if_pos rfl] at hqx
      simp [hqx, hxOne]
    · intro z hzx
      by_cases hfz : f z = 0
      · have hzProduct := congrFun hg.2 z
        change (f z + 1) * g z = 0 at hzProduct
        rw [hfz, zero_add, one_mul] at hzProduct
        simp [hzProduct]
      · have hfzOne : f z = 1 := Fin.eq_one_of_ne_zero _ hfz
        have hzSupport : z ∈ support f := (mem_support f z).2 hfzOne
        have hqz := hqApply ⟨z, hzSupport⟩
        rw [if_neg hzx] at hqz
        simp [hqz]
  exact zero_ne_one (hpairZero.symm.trans hpairOne)

/-- Proposition 38: for odd `n`, a balanced function with no nonzero
annihilator of degree at most `(n-1)/2` has optimal algebraic immunity. -/
theorem algebraicImmunity_eq_ceiling_half_of_odd_balanced_of_no_annihilator
    (f : BooleanFunction n) (hn : Odd n) (hbalanced : IsBalanced f)
    (hnoAnnihilator : ∀ g : BooleanFunction n,
      g ≠ 0 → FABL.functionAlgebraicDegree g ≤ (n - 1) / 2 → f * g ≠ 0) :
    algebraicImmunity f = (n + 1) / 2 := by
  obtain ⟨m, hm⟩ := hn
  subst n
  apply Nat.le_antisymm
  · exact algebraicImmunity_le_ceiling_half f
  · by_contra hbound
    obtain ⟨g, hg, hdegree⟩ :=
      exists_witness_functionAlgebraicDegree_eq_algebraicImmunity f
    have hgDegree : FABL.functionAlgebraicDegree g ≤ m := by omega
    rcases hg with hg | hg
    · have hdegreeBound : FABL.functionAlgebraicDegree g ≤
          ((2 * m + 1 - 1) / 2) := by omega
      exact (hnoAnnihilator g hg.1 hdegreeBound) hg.2
    · exact no_lowDegree_complement_annihilator_of_odd_balanced
        f hbalanced (by
          intro q hqNe hqDegree
          apply hnoAnnihilator q hqNe
          omega) g hg hgDegree

/-- Adding a Boolean function of degree `r` can increase algebraic immunity by at most `r`. -/
theorem algebraicImmunity_add_le_add_functionAlgebraicDegree
    (f h : BooleanFunction n) :
    algebraicImmunity (f + h) ≤
      algebraicImmunity f + FABL.functionAlgebraicDegree h := by
  obtain ⟨g, hg, hdegree⟩ :=
    exists_witness_functionAlgebraicDegree_eq_algebraicImmunity f
  let d := algebraicImmunity f + FABL.functionAlgebraicDegree h
  have hgDegree : FABL.functionAlgebraicDegree g ≤ d := by
    dsimp [d]
    omega
  have hproductDegree :
      FABL.functionAlgebraicDegree ((f + h) * g) ≤ d := by
    rcases hg with hg | hg
    · have hproduct : (f + h) * g = h * g := by
        rw [add_mul, hg.2, zero_add]
      rw [hproduct]
      exact (FABL.functionAlgebraicDegree_mul_le_add h g).trans (by
        dsimp [d]
        omega)
    · have hfg : f * g = g := by
        have hzero := hg.2
        rw [add_mul, one_mul] at hzero
        exact (eq_neg_of_add_eq_zero_left hzero).trans
          (ZModModule.neg_eq_self g)
      have hproduct : (f + h) * g = g + h * g := by
        rw [add_mul, hfg]
      rw [hproduct]
      exact (FABL.functionAlgebraicDegree_add_le_max g (h * g)).trans
        (max_le hgDegree
          ((FABL.functionAlgebraicDegree_mul_le_add h g).trans (by
            dsimp [d]
            omega)))
  obtain ⟨q, hqNe, hqDegree, hqProduct⟩ :=
    (exists_lowDegreeRelation_iff_exists_algebraicImmunityWitness
      (f + h) d).1
      ⟨g, (f + h) * g, hg.elim And.left And.left, hgDegree,
        hproductDegree, rfl⟩
  have hqWitness : IsAlgebraicImmunityWitness (f + h) q := by
    rcases hqProduct with hqProduct | hqProduct
    · exact Or.inl ⟨hqNe, hqProduct⟩
    · exact Or.inr ⟨hqNe, hqProduct⟩
  exact (algebraicImmunity_le_functionAlgebraicDegree (f + h) q hqWitness).trans
    hqDegree

/-- Symmetric lower form of stability under low-degree perturbations. -/
theorem algebraicImmunity_sub_functionAlgebraicDegree_le_add
    (f h : BooleanFunction n) :
    algebraicImmunity f - FABL.functionAlgebraicDegree h ≤
      algebraicImmunity (f + h) := by
  have hbound := algebraicImmunity_add_le_add_functionAlgebraicDegree (f + h) h
  have hcancel : (f + h) + h = f := by
    funext x
    change f x + h x + h x = f x
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [hcancel] at hbound
  omega

end CryptBoolean
