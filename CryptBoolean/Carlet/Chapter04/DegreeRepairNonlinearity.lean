/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity

/-!
# Degree repair with bounded nonlinearity loss

The Sarkar--Maitra two-point repair of a balanced Boolean function, and its
application to the odd-dimensional high-nonlinearity family.
-/

open Finset
open Module
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem hammingWeight_comp_equiv
    (f : BooleanFunction n) (e : Equiv.Perm (FABL.F₂Cube n)) :
    hammingWeight (f ∘ e) = hammingWeight f := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  change
    (Finset.univ.filter fun x : FABL.F₂Cube n ↦ f (e x) = 1).card =
      (Finset.univ.filter fun x : FABL.F₂Cube n ↦ f x = 1).card
  rw [Finset.card_filter, Finset.card_filter]
  change
    (∑ x, if f (e x) = 1 then (1 : ℕ) else 0) =
      ∑ x, if f x = 1 then (1 : ℕ) else 0
  exact Equiv.sum_comp e (fun x ↦ if f x = 1 then (1 : ℕ) else 0)

private theorem mem_binaryAffineLine_iff
    (x₀ x₁ x : FABL.F₂Cube n) :
    x ∈ FABL.binaryAffineSubspace
        (Submodule.span FABL.𝔽₂ {x₁ + x₀}) x₀ ↔
      x = x₀ ∨ x = x₁ := by
  rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    by_cases hc₀ : c = 0
    · subst c
      left
      simp only [zero_smul] at hc
      have hx : x + x₀ = 0 := hc.symm
      exact (add_eq_zero_iff_eq_neg.mp hx).trans (ZModModule.neg_eq_self x₀)
    · have hc₁ : c = 1 := Fin.eq_one_of_ne_zero c hc₀
      subst c
      right
      simp only [one_smul] at hc
      exact add_right_cancel hc.symm
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [zero_smul, ZModModule.add_self]⟩
    · exact ⟨1, by simp⟩

private theorem add_affineLineIndicator_eq_comp_swap
    (f : BooleanFunction n) (x₀ x₁ : FABL.F₂Cube n)
    (hx₀ : f x₀ = 0) (hx₁ : f x₁ = 1) :
    f + affineFlatIndicator
        (Submodule.span FABL.𝔽₂ {x₁ + x₀}) x₀ =
      f ∘ Equiv.swap x₀ x₁ := by
  funext x
  by_cases h₀ : x = x₀
  · subst x
    simp [Pi.add_apply, affineFlatIndicator,
      mem_binaryAffineLine_iff, hx₀, hx₁]
  · by_cases h₁ : x = x₁
    · subst x
      simp [Pi.add_apply, affineFlatIndicator,
        mem_binaryAffineLine_iff, hx₀, hx₁]
    · simp [Pi.add_apply, affineFlatIndicator,
        mem_binaryAffineLine_iff, h₀, h₁,
        Equiv.swap_apply_of_ne_of_ne]

/-- Nonlinearity is one-Lipschitz with respect to raw Hamming distance. -/
theorem nonlinearity_le_hammingDistance_add_nonlinearity
    (f g : BooleanFunction n) :
    nonlinearity f ≤ hammingDistance f g + nonlinearity g := by
  classical
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun p ↦ hammingDistance g (FABL.affineFunction p.1 p.2))
  have hcandidate :
      nonlinearity f ≤ hammingDistance f (FABL.affineFunction p.1 p.2) := by
    exact Finset.inf'_le
      (fun q : FABL.𝔽₂ × FABL.F₂Cube n ↦
        hammingDistance f (FABL.affineFunction q.1 q.2))
      (Finset.mem_univ p)
  have htriangle := hammingDist_triangle f g (FABL.affineFunction p.1 p.2)
  change hammingDistance f (FABL.affineFunction p.1 p.2) ≤
    hammingDistance f g + hammingDistance g (FABL.affineFunction p.1 p.2) at htriangle
  change nonlinearity g = hammingDistance g (FABL.affineFunction p.1 p.2) at hmin
  rw [← hmin] at htriangle
  exact hcandidate.trans htriangle

/-- Sarkar--Maitra Propositions 2--3: in dimension at least two, a balanced
Boolean function can be repaired to algebraic degree `n - 1` by changing at
most two values, with nonlinearity loss at most two. -/
theorem exists_isBalanced_degree_pred_nonlinearity_ge_sub_two
    (f : BooleanFunction n) (hn : 2 ≤ n) (hf : IsBalanced f) :
    ∃ g : BooleanFunction n,
      IsBalanced g ∧
        FABL.functionAlgebraicDegree g = n - 1 ∧
        nonlinearity f - 2 ≤ nonlinearity g := by
  classical
  have hnpos : 0 < n := by omega
  have hweight : hammingWeight f = 2 ^ (n - 1) := by
    rw [IsBalanced] at hf
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      have hnEq : n = (n - 1) + 1 := by omega
      calc
        2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (fun k : ℕ ↦ 2 ^ k) hnEq
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
    rw [hpow] at hf
    omega
  have hsupportCard : (support f).card = 2 ^ (n - 1) := by
    rw [← hammingWeight_eq_card_support]
    exact hweight
  have heven : Even (support f).card := by
    rw [hsupportCard, show n - 1 = (n - 2) + 1 by omega, pow_succ]
    exact ⟨2 ^ (n - 2), by omega⟩
  have hdegreeLe : FABL.functionAlgebraicDegree f ≤ n - 1 := by
    have hle := FABL.functionAlgebraicDegree_le_dimension f
    have hne : FABL.functionAlgebraicDegree f ≠ n := by
      intro hdegree
      have hodd :=
        (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
          f hnpos).mp hdegree
      exact (Nat.not_odd_iff_even.mpr heven) hodd
    omega
  by_cases hdegree : FABL.functionAlgebraicDegree f = n - 1
  · exact ⟨f, hf, hdegree, by omega⟩
  · have hdegreeLow : FABL.functionAlgebraicDegree f ≤ n - 2 := by
      omega
    have hsupportNonempty : (support f).Nonempty := by
      apply Finset.card_pos.mp
      rw [hsupportCard]
      exact Nat.two_pow_pos _
    obtain ⟨x₁, hx₁mem⟩ := hsupportNonempty
    have hx₁ : f x₁ = 1 := (mem_support f x₁).mp hx₁mem
    have hsupportLt :
        (support f).card < Fintype.card (FABL.F₂Cube n) := by
      rw [hsupportCard, card_f₂Cube]
      have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        have hnEq : n = (n - 1) + 1 := by omega
        calc
          2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (fun k : ℕ ↦ 2 ^ k) hnEq
          _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
      rw [hpow]
      have hpositive : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
      omega
    have hx₀exists : ∃ x₀ : FABL.F₂Cube n, x₀ ∉ support f := by
      by_contra h
      have hall : ∀ x₀ : FABL.F₂Cube n, x₀ ∈ support f := by
        intro x₀
        by_contra hx₀
        exact h ⟨x₀, hx₀⟩
      have huniv : support f = Finset.univ := Finset.eq_univ_of_forall hall
      have := congrArg Finset.card huniv
      simp only [Finset.card_univ] at this
      omega
    obtain ⟨x₀, hx₀notMem⟩ := hx₀exists
    have hx₀ : f x₀ = 0 := by
      by_contra hx₀ne
      have hx₀one : f x₀ = 1 := Fin.eq_one_of_ne_zero _ hx₀ne
      exact hx₀notMem ((mem_support f x₀).mpr hx₀one)
    have hxne : x₁ ≠ x₀ := by
      intro h
      subst x₁
      rw [hx₀] at hx₁
      exact zero_ne_one hx₁
    have hdirection : x₁ + x₀ ≠ 0 := by
      intro hzero
      apply hxne
      exact (add_eq_zero_iff_eq_neg.mp hzero).trans
        (ZModModule.neg_eq_self x₀)
    let H : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
      Submodule.span FABL.𝔽₂ {x₁ + x₀}
    let p : BooleanFunction n := affineFlatIndicator H x₀
    let g : BooleanFunction n := f + p
    have hfinrank : Module.finrank FABL.𝔽₂ H = 1 := by
      dsimp [H]
      exact finrank_span_singleton hdirection
    have hpDegree : FABL.functionAlgebraicDegree p = n - 1 := by
      rw [show p = affineFlatIndicator H x₀ by rfl,
        functionAlgebraicDegree_affineFlatIndicator,
        FABL.f₂Codimension, FABL.finrank_perpendicularSubspace,
        hfinrank]
    have hgSwap : g = f ∘ Equiv.swap x₀ x₁ := by
      dsimp [g, p, H]
      exact add_affineLineIndicator_eq_comp_swap f x₀ x₁ hx₀ hx₁
    have hgBalanced : IsBalanced g := by
      rw [IsBalanced, hgSwap, hammingWeight_comp_equiv]
      exact hf
    have hdistance : hammingDistance f g = 2 := by
      rw [hammingDistance_eq_hammingWeight_add]
      have hcancel : f + g = p := by
        dsimp [g]
        funext x
        simp only [Pi.add_apply]
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [hcancel, show p = affineFlatIndicator H x₀ by rfl,
        hammingWeight_affineFlatIndicator, hfinrank]
      norm_num
    have hgDegreeLe : FABL.functionAlgebraicDegree g ≤ n - 1 := by
      dsimp [g]
      have hle := FABL.functionAlgebraicDegree_add_le_max f p
      rw [hpDegree] at hle
      exact hle.trans (max_le hdegreeLe le_rfl)
    have hgDegreeGe : n - 1 ≤ FABL.functionAlgebraicDegree g := by
      by_contra hnot
      have hgLow : FABL.functionAlgebraicDegree g ≤ n - 2 := by omega
      have hpEq : f + g = p := by
        dsimp [g]
        funext x
        simp only [Pi.add_apply]
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      have hle := FABL.functionAlgebraicDegree_add_le_max f g
      rw [hpEq, hpDegree] at hle
      have hmax :
          max (FABL.functionAlgebraicDegree f)
              (FABL.functionAlgebraicDegree g) ≤ n - 2 :=
        max_le hdegreeLow hgLow
      omega
    have hgDegree : FABL.functionAlgebraicDegree g = n - 1 := by omega
    have hnonlinearity :=
      nonlinearity_le_hammingDistance_add_nonlinearity f g
    rw [hdistance] at hnonlinearity
    exact ⟨g, hgBalanced, hgDegree, by omega⟩

/-- Carlet footnote 22, degree-constrained family: for every odd `n ≥ 15`
there is a balanced Boolean function of algebraic degree `n - 1` whose
nonlinearity strictly exceeds the odd-dimensional quadratic bound. -/
theorem exists_isBalanced_degree_pred_nonlinearity_gt_quadraticBound_of_odd
    (hn : Odd n) (hn15 : 15 ≤ n) :
    ∃ f : BooleanFunction n,
      IsBalanced f ∧
        FABL.functionAlgebraicDegree f = n - 1 ∧
        2 ^ (n - 1) - 2 ^ ((n - 1) / 2) < nonlinearity f := by
  obtain ⟨k, hk⟩ := hn
  have hk7 : 7 ≤ k := by omega
  let m := k - 6
  have hm : 1 ≤ m := by
    dsimp [m]
    omega
  have hnform : n = 13 + (m + m) := by
    dsimp [m]
    omega
  rw [hnform]
  obtain ⟨f, hbalanced, hdegree, hrepair⟩ :=
    exists_isBalanced_degree_pred_nonlinearity_ge_sub_two
      (maitraKavutYucelBentExtension m) (by omega)
      (isBalanced_maitraKavutYucelBentExtension m)
  refine ⟨f, hbalanced, hdegree, ?_⟩
  rw [nonlinearity_maitraKavutYucelBentExtension] at hrepair
  have hsub : 13 + (m + m) - 1 = 12 + (m + m) := by omega
  have hhalf : (12 + (m + m)) / 2 = 6 + m := by omega
  rw [hsub, hhalf]
  have htwo : 2 ≤ 2 ^ m := by
    rw [show 2 = 2 ^ 1 by norm_num]
    exact Nat.pow_le_pow_right (by omega) hm
  have hsix : 2 ^ (6 + m) = 64 * 2 ^ m := by
    rw [pow_add]
    norm_num
  have hlarge : 64 * 2 ^ m ≤ 2 ^ (12 + (m + m)) := by
    rw [← hsix]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hgap : 60 * 2 ^ m + 2 < 64 * 2 ^ m := by omega
  have hstrict :
      2 ^ (12 + (m + m)) - 64 * 2 ^ m <
        (2 ^ (12 + (m + m)) - 60 * 2 ^ m) - 2 := by
    omega
  rw [hsix]
  exact hstrict.trans_le hrepair

end CryptBoolean
