/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.IndirectSum
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Indirect sums of resilient Boolean functions

Carlet Theorem 14 and Relation (66) for the indirect sum of two pairs of
Boolean functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s t m : ℕ}

private theorem two_mul_bitSignInt_indirectIdentity
    (a b c d : FABL.𝔽₂) :
    2 * bitSignInt (a + c + (a + b) * (c + d)) =
      bitSignInt a * (bitSignInt c + bitSignInt d) +
        bitSignInt b * (bitSignInt c - bitSignInt d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    decide

private theorem indirectIdentity_add_characters
    (a b c d u v : FABL.𝔽₂) :
    a + c + (a + b) * (c + d) + (u + v) =
      (a + u) + (c + v) +
        ((a + u) + (b + u)) * ((c + v) + (d + v)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases u <;> fin_cases v <;> decide

private theorem two_mul_walshTerm_indirectSum_append
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    2 * walshTerm (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b)
        (Fin.append x y) =
      walshTerm f₁ a x * (walshTerm g₁ b y + walshTerm g₂ b y) +
        walshTerm f₂ a x * (walshTerm g₁ b y - walshTerm g₂ b y) := by
  simp only [walshTerm, indirectSum_append, FABL.f₂DotProduct_append]
  rw [indirectIdentity_add_characters]
  exact two_mul_bitSignInt_indirectIdentity
    (f₁ x + FABL.f₂DotProduct a x)
    (f₂ x + FABL.f₂DotProduct a x)
    (g₁ y + FABL.f₂DotProduct b y)
    (g₂ y + FABL.f₂DotProduct b y)

/-- Division-free form of Carlet Relation (66). -/
theorem two_mul_walshTransform_indirectSum
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    2 * walshTransform (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b) =
      walshTransform f₁ a * (walshTransform g₁ b + walshTransform g₂ b) +
        walshTransform f₂ a *
          (walshTransform g₁ b - walshTransform g₂ b) := by
  classical
  simp only [walshTransform]
  calc
    2 * ∑ z : FABL.F₂Cube (r + s),
        walshTerm (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b) z =
      2 * ∑ p : FABL.F₂Cube r × FABL.F₂Cube s,
        walshTerm (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b)
          (Fin.append p.1 p.2) := by
      congr 1
      exact (Fintype.sum_equiv (Fin.appendEquiv r s)
        (fun p ↦ walshTerm (indirectSum f₁ f₂ g₁ g₂)
          (Fin.append a b) (Fin.append p.1 p.2))
        (fun z ↦ walshTerm (indirectSum f₁ f₂ g₁ g₂)
          (Fin.append a b) z)
        (fun _ ↦ rfl)).symm
    _ = ∑ x : FABL.F₂Cube r, ∑ y : FABL.F₂Cube s,
        2 * walshTerm (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b)
          (Fin.append x y) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = ∑ x : FABL.F₂Cube r, ∑ y : FABL.F₂Cube s,
        (walshTerm f₁ a x * (walshTerm g₁ b y + walshTerm g₂ b y) +
          walshTerm f₂ a x *
            (walshTerm g₁ b y - walshTerm g₂ b y)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact two_mul_walshTerm_indirectSum_append f₁ f₂ g₁ g₂ a b x y
    _ = (∑ x : FABL.F₂Cube r, walshTerm f₁ a x) *
          ((∑ y : FABL.F₂Cube s, walshTerm g₁ b y) +
            ∑ y : FABL.F₂Cube s, walshTerm g₂ b y) +
        (∑ x : FABL.F₂Cube r, walshTerm f₂ a x) *
          ((∑ y : FABL.F₂Cube s, walshTerm g₁ b y) -
            ∑ y : FABL.F₂Cube s, walshTerm g₂ b y) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Carlet Relation (66) in the source's real-valued half-factor form. -/
theorem walshTransform_indirectSum_cast_eq_relation_66
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    (walshTransform (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b) : ℝ) =
      (1 / 2 : ℝ) * (walshTransform f₁ a : ℝ) *
          ((walshTransform g₁ b : ℝ) + walshTransform g₂ b) +
        (1 / 2 : ℝ) * (walshTransform f₂ a : ℝ) *
          ((walshTransform g₁ b : ℝ) - walshTransform g₂ b) := by
  have h := congrArg (fun z : ℤ ↦ (z : ℝ))
    (two_mul_walshTransform_indirectSum f₁ f₂ g₁ g₂ a b)
  push_cast at h
  linarith

/-- Carlet Theorem 14: the indirect sum of a `t`-resilient pair and an
`m`-resilient pair is `(t+m+1)`-resilient. -/
theorem isResilient_indirectSum
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (ht : t < r) (hm : m < s)
    (hf₁ : IsResilient t f₁) (hf₂ : IsResilient t f₂)
    (hg₁ : IsResilient m g₁) (hg₂ : IsResilient m g₂) :
    IsResilient (t + m + 1) (indirectSum f₁ f₂ g₁ g₂) := by
  have hr : 0 < r := by omega
  have hs : 0 < s := by omega
  have hrs : 0 < r + s := by omega
  have horder : t + m + 1 < r + s := by omega
  have hf₁Walsh := theorem_3_resilient_iff_walshTransform_eq_zero
    t f₁ hr ht |>.mp hf₁
  have hf₂Walsh := theorem_3_resilient_iff_walshTransform_eq_zero
    t f₂ hr ht |>.mp hf₂
  have hg₁Walsh := theorem_3_resilient_iff_walshTransform_eq_zero
    m g₁ hs hm |>.mp hg₁
  have hg₂Walsh := theorem_3_resilient_iff_walshTransform_eq_zero
    m g₂ hs hm |>.mp hg₂
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (t + m + 1) (indirectSum f₁ f₂ g₁ g₂) hrs horder]
  intro u huweight
  let p := (Fin.appendEquiv r s).symm u
  have hu : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  have hpweight :
      (FABL.f₂Support p.1).card + (FABL.f₂Support p.2).card ≤
        t + m + 1 := by
    rw [← card_f₂Support_append]
    simpa only [hu] using huweight
  have hrelation :=
    two_mul_walshTransform_indirectSum f₁ f₂ g₁ g₂ p.1 p.2
  rw [hu] at hrelation
  by_cases hleft : (FABL.f₂Support p.1).card ≤ t
  · rw [hf₁Walsh p.1 hleft, hf₂Walsh p.1 hleft] at hrelation
    omega
  · have hright : (FABL.f₂Support p.2).card ≤ m := by omega
    rw [hg₁Walsh p.2 hright, hg₂Walsh p.2 hright] at hrelation
    omega

private theorem two_mul_natAbs_walshTransform_indirectSum_of_disjointAt
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s)
    (hf : walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (hg : walshTransform g₁ b = 0 ∨ walshTransform g₂ b = 0) :
    2 * (walshTransform (indirectSum f₁ f₂ g₁ g₂)
        (Fin.append a b)).natAbs =
      max (walshTransform f₁ a).natAbs (walshTransform f₂ a).natAbs *
        max (walshTransform g₁ b).natAbs (walshTransform g₂ b).natAbs := by
  have hrelation :=
    two_mul_walshTransform_indirectSum f₁ f₂ g₁ g₂ a b
  rcases hf with hf₁ | hf₂ <;> rcases hg with hg₁ | hg₂
  all_goals
    simp_all
    have habs := congrArg Int.natAbs hrelation
    simpa [Int.natAbs_mul] using habs

private theorem exists_pointwise_max_walshPair
    (f g : BooleanFunction r) :
  ∃ a : FABL.F₂Cube r,
      max (walshTransform f a).natAbs (walshTransform g a).natAbs =
        max (maxWalshMagnitude f) (maxWalshMagnitude g) := by
  rcases le_total (maxWalshMagnitude f) (maxWalshMagnitude g) with hfg | hgf
  · obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube r)))
      Finset.univ_nonempty
      (fun u ↦ (walshTransform g u).natAbs)
    have hgMax : (walshTransform g a).natAbs = maxWalshMagnitude g := by
      unfold maxWalshMagnitude
      exact hmax.symm
    refine ⟨a, ?_⟩
    rw [Nat.max_eq_right hfg, hgMax]
    exact Nat.max_eq_right ((walshTransform_natAbs_le_maxWalshMagnitude f a).trans hfg)
  · obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube r)))
      Finset.univ_nonempty
      (fun u ↦ (walshTransform f u).natAbs)
    have hfMax : (walshTransform f a).natAbs = maxWalshMagnitude f := by
      unfold maxWalshMagnitude
      exact hmax.symm
    refine ⟨a, ?_⟩
    rw [Nat.max_eq_left hgf, hfMax]
    exact Nat.max_eq_left ((walshTransform_natAbs_le_maxWalshMagnitude g a).trans hgf)

/-- Under disjoint spectra in each pair, twice the maximum Walsh magnitude
of the indirect sum is the product of the two pairwise maximum magnitudes. -/
theorem two_mul_maxWalshMagnitude_indirectSum_of_disjointWalshSupport
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hf : ∀ a : FABL.F₂Cube r,
      walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (hg : ∀ b : FABL.F₂Cube s,
      walshTransform g₁ b = 0 ∨ walshTransform g₂ b = 0) :
    2 * maxWalshMagnitude (indirectSum f₁ f₂ g₁ g₂) =
      max (maxWalshMagnitude f₁) (maxWalshMagnitude f₂) *
        max (maxWalshMagnitude g₁) (maxWalshMagnitude g₂) := by
  apply le_antisymm
  · unfold maxWalshMagnitude
    obtain ⟨u, _hu, hmax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube (r + s))))
      Finset.univ_nonempty
      (fun z ↦
        (walshTransform (indirectSum f₁ f₂ g₁ g₂) z).natAbs)
    let p := (Fin.appendEquiv r s).symm u
    have hu : Fin.append p.1 p.2 = u :=
      (Fin.appendEquiv r s).apply_symm_apply u
    rw [hmax, ← hu,
      two_mul_natAbs_walshTransform_indirectSum_of_disjointAt
        f₁ f₂ g₁ g₂ p.1 p.2 (hf p.1) (hg p.2)]
    exact Nat.mul_le_mul
      (Nat.max_le.mpr ⟨
        (walshTransform_natAbs_le_maxWalshMagnitude f₁ p.1).trans
          (Nat.le_max_left _ _),
        (walshTransform_natAbs_le_maxWalshMagnitude f₂ p.1).trans
          (Nat.le_max_right _ _)⟩)
      (Nat.max_le.mpr ⟨
        (walshTransform_natAbs_le_maxWalshMagnitude g₁ p.2).trans
          (Nat.le_max_left _ _),
        (walshTransform_natAbs_le_maxWalshMagnitude g₂ p.2).trans
          (Nat.le_max_right _ _)⟩)
  · obtain ⟨a, ha⟩ := exists_pointwise_max_walshPair f₁ f₂
    obtain ⟨b, hb⟩ := exists_pointwise_max_walshPair g₁ g₂
    rw [← ha, ← hb,
      ← two_mul_natAbs_walshTransform_indirectSum_of_disjointAt
        f₁ f₂ g₁ g₂ a b (hf a) (hg b)]
    exact Nat.mul_le_mul_left 2
      (walshTransform_natAbs_le_maxWalshMagnitude
        (indirectSum f₁ f₂ g₁ g₂) (Fin.append a b))

/-- Relation (67) in a normalization-independent spectral form. -/
theorem nonlinearity_indirectSum_cast_eq_relation_67_spectral
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hf : ∀ a : FABL.F₂Cube r,
      walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (hg : ∀ b : FABL.F₂Cube s,
      walshTransform g₁ b = 0 ∨ walshTransform g₂ b = 0) :
    (nonlinearity (indirectSum f₁ f₂ g₁ g₂) : ℝ) =
      (2 : ℝ) ^ (r + s) / 2 -
        ((max (maxWalshMagnitude f₁) (maxWalshMagnitude f₂) : ℕ) : ℝ) *
          ((max (maxWalshMagnitude g₁) (maxWalshMagnitude g₂) : ℕ) : ℝ) /
          4 := by
  rw [nonlinearity_cast_eq_relation_35]
  have hmaxNat :=
    two_mul_maxWalshMagnitude_indirectSum_of_disjointWalshSupport
      f₁ f₂ g₁ g₂ hf hg
  have hmax :
      2 * (maxWalshMagnitude (indirectSum f₁ f₂ g₁ g₂) : ℝ) =
        ((max (maxWalshMagnitude f₁) (maxWalshMagnitude f₂) : ℕ) : ℝ) *
          ((max (maxWalshMagnitude g₁) (maxWalshMagnitude g₂) : ℕ) : ℝ) := by
    exact_mod_cast hmaxNat
  nlinarith

/-- Relation (67), simplified from the minimum over four pairs to the
minimum nonlinearity in each disjoint spectral pair. -/
theorem nonlinearity_indirectSum_cast_eq_relation_67
    (f₁ f₂ : BooleanFunction r) (g₁ g₂ : BooleanFunction s)
    (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ a : FABL.F₂Cube r,
      walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (hg : ∀ b : FABL.F₂Cube s,
      walshTransform g₁ b = 0 ∨ walshTransform g₂ b = 0) :
    (nonlinearity (indirectSum f₁ f₂ g₁ g₂) : ℝ) =
      (2 : ℝ) ^ (r + s - 2) +
        (2 : ℝ) ^ (r - 1) *
          (min (nonlinearity g₁) (nonlinearity g₂) : ℕ) +
        (2 : ℝ) ^ (s - 1) *
          (min (nonlinearity f₁) (nonlinearity f₂) : ℕ) -
        (min (nonlinearity f₁) (nonlinearity f₂) : ℕ) *
          (min (nonlinearity g₁) (nonlinearity g₂) : ℕ) := by
  rw [nonlinearity_indirectSum_cast_eq_relation_67_spectral
    f₁ f₂ g₁ g₂ hf hg]
  have hf₁Relation := two_mul_nonlinearity_add_maxWalshMagnitude f₁
  have hf₂Relation := two_mul_nonlinearity_add_maxWalshMagnitude f₂
  have hg₁Relation := two_mul_nonlinearity_add_maxWalshMagnitude g₁
  have hg₂Relation := two_mul_nonlinearity_add_maxWalshMagnitude g₂
  have hF :
      ((max (maxWalshMagnitude f₁) (maxWalshMagnitude f₂) : ℕ) : ℝ) =
        (2 : ℝ) ^ r -
          2 * (min (nonlinearity f₁) (nonlinearity f₂) : ℕ) := by
    rcases le_total (nonlinearity f₁) (nonlinearity f₂) with hle | hle
    · have hMagnitude : maxWalshMagnitude f₂ ≤ maxWalshMagnitude f₁ := by
        omega
      rw [Nat.max_eq_left hMagnitude, Nat.min_eq_left hle]
      have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hf₁Relation
      push_cast at hcast
      linarith
    · have hMagnitude : maxWalshMagnitude f₁ ≤ maxWalshMagnitude f₂ := by
        omega
      rw [Nat.max_eq_right hMagnitude, Nat.min_eq_right hle]
      have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hf₂Relation
      push_cast at hcast
      linarith
  have hG :
      ((max (maxWalshMagnitude g₁) (maxWalshMagnitude g₂) : ℕ) : ℝ) =
        (2 : ℝ) ^ s -
          2 * (min (nonlinearity g₁) (nonlinearity g₂) : ℕ) := by
    rcases le_total (nonlinearity g₁) (nonlinearity g₂) with hle | hle
    · have hMagnitude : maxWalshMagnitude g₂ ≤ maxWalshMagnitude g₁ := by
        omega
      rw [Nat.max_eq_left hMagnitude, Nat.min_eq_left hle]
      have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hg₁Relation
      push_cast at hcast
      linarith
    · have hMagnitude : maxWalshMagnitude g₁ ≤ maxWalshMagnitude g₂ := by
        omega
      rw [Nat.max_eq_right hMagnitude, Nat.min_eq_right hle]
      have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hg₂Relation
      push_cast at hcast
      linarith
  have hpowR : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    ring
  have hpowS : (2 : ℝ) ^ s = 2 * (2 : ℝ) ^ (s - 1) := by
    conv_lhs => rw [show s = (s - 1) + 1 by omega, pow_succ]
    ring
  have hpowRS : (2 : ℝ) ^ (r + s) = 4 * (2 : ℝ) ^ (r + s - 2) := by
    conv_lhs => rw [show r + s = (r + s - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hpowProduct :
      (2 : ℝ) ^ (r - 1) * (2 : ℝ) ^ (s - 1) =
        (2 : ℝ) ^ (r + s - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hF, hG, hpowR, hpowS, hpowRS]
  nlinarith [hpowProduct]

end CryptBoolean
