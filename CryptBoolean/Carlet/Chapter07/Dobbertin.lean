/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.FlatSwitching
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Dobbertin's balanced modification of normal bent functions

Carlet Proposition 33 and Relation (64): switching a normal bent function
along its zero flat by a balanced Boolean function.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m k : ℕ}

/-- Dobbertin's modification replaces the zero-second-block restriction of
`f` by `g`. -/
def dobbertinConstruction
    (f : BooleanFunction (m + m)) (g : BooleanFunction m) :
    BooleanFunction (m + m) :=
  fun z ↦
    let blocks := cubeSplitLinearEquiv m m z
    f z + if blocks.2 = 0 then g blocks.1 else 0

@[simp] private theorem cubeSplitLinearEquiv_append
    (x y : FABL.F₂Cube m) :
    cubeSplitLinearEquiv m m (Fin.append x y) = (x, y) := by
  change (Fin.appendEquiv m m).symm (Fin.append x y) = (x, y)
  exact (Fin.appendEquiv m m).symm_apply_apply (x, y)

/-- Evaluation of Dobbertin's construction on the two coordinate blocks. -/
@[simp] theorem dobbertinConstruction_append
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (x y : FABL.F₂Cube m) :
    dobbertinConstruction f g (Fin.append x y) =
      f (Fin.append x y) + if y = 0 then g x else 0 := by
  simp [dobbertinConstruction]

private theorem walshTerm_dobbertinConstruction_sub
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (u v x y : FABL.F₂Cube m) :
    walshTerm (dobbertinConstruction f g) (Fin.append u v)
          (Fin.append x y) -
        walshTerm f (Fin.append u v) (Fin.append x y) =
      if y = 0 then
        walshTerm g u x - walshTerm (0 : BooleanFunction m) u x
      else 0 := by
  by_cases hy : y = 0
  · subst y
    have hvzero :
        FABL.f₂DotProduct v (0 : FABL.F₂Cube m) = 0 := by
      simp [FABL.f₂DotProduct, dotProduct_zero]
    simp [walshTerm, hflat, FABL.f₂DotProduct_append, hvzero]
  · simp [walshTerm, hy, FABL.f₂DotProduct_append]

/-- Before using bentness and balancedness, the exact spectral correction is
the source Walsh coefficient plus the mask coefficient minus the zero-flat
character sum. -/
theorem walshTransform_dobbertinConstruction_general
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (u v : FABL.F₂Cube m) :
    walshTransform (dobbertinConstruction f g) (Fin.append u v) =
      walshTransform f (Fin.append u v) + walshTransform g u -
        walshTransform (0 : BooleanFunction m) u := by
  classical
  have hdelta :
      walshTransform (dobbertinConstruction f g) (Fin.append u v) -
          walshTransform f (Fin.append u v) =
        walshTransform g u - walshTransform (0 : BooleanFunction m) u := by
    rw [walshTransform, walshTransform, walshTransform, walshTransform,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    calc
      (∑ z : FABL.F₂Cube (m + m),
          (walshTerm (dobbertinConstruction f g) (Fin.append u v) z -
            walshTerm f (Fin.append u v) z)) =
          ∑ p : FABL.F₂Cube m × FABL.F₂Cube m,
            (walshTerm (dobbertinConstruction f g) (Fin.append u v)
                (Fin.append p.1 p.2) -
              walshTerm f (Fin.append u v) (Fin.append p.1 p.2)) := by
        exact (Fintype.sum_equiv (Fin.appendEquiv m m)
          (fun p ↦
            walshTerm (dobbertinConstruction f g) (Fin.append u v)
                (Fin.append p.1 p.2) -
              walshTerm f (Fin.append u v) (Fin.append p.1 p.2))
          (fun z ↦
            walshTerm (dobbertinConstruction f g) (Fin.append u v) z -
              walshTerm f (Fin.append u v) z)
          (fun _ ↦ rfl)).symm
      _ = ∑ x : FABL.F₂Cube m, ∑ y : FABL.F₂Cube m,
          (walshTerm (dobbertinConstruction f g) (Fin.append u v)
              (Fin.append x y) -
            walshTerm f (Fin.append u v) (Fin.append x y)) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : FABL.F₂Cube m,
          (walshTerm g u x - walshTerm (0 : BooleanFunction m) u x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.sum_eq_single 0]
        · simpa using
            walshTerm_dobbertinConstruction_sub f g hflat u v x 0
        · intro y _hy hy
          rw [walshTerm_dobbertinConstruction_sub f g hflat]
          simp [hy]
        · simp
  omega

private theorem walshTransform_zero
    (u : FABL.F₂Cube m) :
    walshTransform (0 : BooleanFunction m) u =
      if u = 0 then (2 : ℤ) ^ m else 0 := by
  have hzero :
      (0 : BooleanFunction m) = FABL.affineFunction 0 0 := by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct]
  rw [hzero, walshTransform_affineFunction]
  simp [bitSignInt]

/-- The exact correction formula with the zero-flat character sum evaluated. -/
theorem walshTransform_dobbertinConstruction
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (u v : FABL.F₂Cube m) :
    walshTransform (dobbertinConstruction f g) (Fin.append u v) =
      walshTransform f (Fin.append u v) + walshTransform g u -
        if u = 0 then (2 : ℤ) ^ m else 0 := by
  rw [walshTransform_dobbertinConstruction_general f g hflat,
    walshTransform_zero]

private theorem sum_walshTerm_zeroFirstBlock
    (f : BooleanFunction (m + m)) (x y : FABL.F₂Cube m) :
    (∑ v : FABL.F₂Cube m,
        walshTerm f (Fin.append 0 v) (Fin.append x y)) =
      if y = 0 then
        (2 : ℤ) ^ m * bitSignInt (f (Fin.append x 0))
      else 0 := by
  calc
    (∑ v : FABL.F₂Cube m,
        walshTerm f (Fin.append 0 v) (Fin.append x y)) =
        bitSignInt (f (Fin.append x y)) *
          walshTransform (0 : BooleanFunction m) y := by
      rw [walshTransform, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [walshTerm, walshTerm, FABL.f₂DotProduct_append,
        bitSignInt_add]
      have hzero :
          FABL.f₂DotProduct (0 : FABL.F₂Cube m) x = 0 := by
        simp [FABL.f₂DotProduct]
      rw [hzero, zero_add]
      rw [Pi.zero_apply, zero_add]
      congr 1
      exact congrArg bitSignInt (dotProduct_comm v y)
    _ = if y = 0 then
          (2 : ℤ) ^ m * bitSignInt (f (Fin.append x 0))
        else 0 := by
      rw [walshTransform_zero]
      by_cases hy : y = 0
      · subst y
        simp [mul_comm]
      · simp [hy]

private theorem sum_walshTransform_zeroFirstBlock
    (f : BooleanFunction (m + m))
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0) :
    (∑ v : FABL.F₂Cube m,
        walshTransform f (Fin.append 0 v)) =
      ((2 : ℤ) ^ m) ^ 2 := by
  classical
  simp only [walshTransform]
  calc
    (∑ v : FABL.F₂Cube m,
        ∑ z : FABL.F₂Cube (m + m),
          walshTerm f (Fin.append 0 v) z) =
        ∑ v : FABL.F₂Cube m,
          ∑ p : FABL.F₂Cube m × FABL.F₂Cube m,
            walshTerm f (Fin.append 0 v) (Fin.append p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact (Fintype.sum_equiv (Fin.appendEquiv m m)
        (fun p ↦ walshTerm f (Fin.append 0 v) (Fin.append p.1 p.2))
        (fun z ↦ walshTerm f (Fin.append 0 v) z)
        (fun _ ↦ rfl)).symm
    _ = ∑ x : FABL.F₂Cube m, ∑ y : FABL.F₂Cube m,
        ∑ v : FABL.F₂Cube m,
          walshTerm f (Fin.append 0 v) (Fin.append x y) := by
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ x : FABL.F₂Cube m, ∑ y : FABL.F₂Cube m,
        if y = 0 then
          (2 : ℤ) ^ m * bitSignInt (f (Fin.append x 0))
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact sum_walshTerm_zeroFirstBlock f x y
    _ = ((2 : ℤ) ^ m) ^ 2 := by
      have hinner (x : FABL.F₂Cube m) :
          (∑ y : FABL.F₂Cube m,
            if y = 0 then
              (2 : ℤ) ^ m * bitSignInt (f (Fin.append x 0))
            else 0) = (2 : ℤ) ^ m := by
        rw [Finset.sum_eq_single 0]
        · simp [hflat, bitSignInt]
        · intro y _hy hy
          simp [hy]
        · simp
      simp_rw [hinner]
      rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
        nsmul_eq_mul]
      norm_num [pow_two]

/-- A bent function that vanishes on the zero second-block flat has positive
Walsh coefficient `2^m` on every frequency perpendicular to that flat. -/
theorem walshTransform_zeroFirstBlock_eq_two_pow_of_isBent
    (f : BooleanFunction (m + m)) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (v : FABL.F₂Cube m) :
    walshTransform f (Fin.append 0 v) = (2 : ℤ) ^ m := by
  classical
  have hmagnitude (w : FABL.F₂Cube m) :
      (walshTransform f (Fin.append 0 w)).natAbs = 2 ^ m := by
    have h := natAbs_walshTransform_eq_two_pow_half_of_isBent
      f hf (Fin.append 0 w)
    have hhalf : (m + m) / 2 = m := by omega
    rw [hhalf] at h
    exact h
  have hle (w : FABL.F₂Cube m) :
      walshTransform f (Fin.append 0 w) ≤ (2 : ℤ) ^ m := by
    calc
      walshTransform f (Fin.append 0 w) ≤
          ((walshTransform f (Fin.append 0 w)).natAbs : ℤ) :=
        Int.le_natAbs
      _ = (2 : ℤ) ^ m := by
        rw [hmagnitude]
        norm_num
  apply le_antisymm (hle v)
  by_contra hnot
  have hvlt :
      walshTransform f (Fin.append 0 v) < (2 : ℤ) ^ m :=
    lt_of_not_ge hnot
  have hsumlt :
      (∑ w : FABL.F₂Cube m,
          walshTransform f (Fin.append 0 w)) <
        ∑ _w : FABL.F₂Cube m, (2 : ℤ) ^ m := by
    exact Finset.sum_lt_sum (fun w _hw ↦ hle w)
      ⟨v, Finset.mem_univ v, hvlt⟩
  rw [sum_walshTransform_zeroFirstBlock f hflat,
    Finset.sum_const, Finset.card_univ, card_f₂Cube,
    nsmul_eq_mul] at hsumlt
  rw [pow_two] at hsumlt
  exact (lt_irrefl _ hsumlt)

/-- Carlet Proposition 33 and Relation (64): the modified spectrum vanishes
when the first frequency block is zero and otherwise is the sum of the bent
and mask spectra. -/
theorem walshTransform_dobbertinConstruction_of_isBent_of_isBalanced
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g)
    (u v : FABL.F₂Cube m) :
    walshTransform (dobbertinConstruction f g) (Fin.append u v) =
      if u = 0 then 0 else
        walshTransform f (Fin.append u v) + walshTransform g u := by
  rw [walshTransform_dobbertinConstruction f g hflat]
  by_cases hu : u = 0
  · subst u
    rw [if_pos rfl,
      walshTransform_zeroFirstBlock_eq_two_pow_of_isBent f hf hflat,
      (isBalanced_iff_walshTransform_zero_eq_zero g).1 hg]
    simp
  · simp [hu]

/-- Zero-first-block branch of Dobbertin's Walsh spectrum. -/
theorem walshTransform_dobbertinConstruction_zeroFirstBlock
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g)
    (v : FABL.F₂Cube m) :
    walshTransform (dobbertinConstruction f g) (Fin.append 0 v) = 0 := by
  rw [walshTransform_dobbertinConstruction_of_isBent_of_isBalanced
    f g hf hflat hg]
  simp

/-- Nonzero-first-block branch of Dobbertin's Walsh spectrum. -/
theorem walshTransform_dobbertinConstruction_ne_zeroFirstBlock
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g)
    (u v : FABL.F₂Cube m) (hu : u ≠ 0) :
    walshTransform (dobbertinConstruction f g) (Fin.append u v) =
      walshTransform f (Fin.append u v) + walshTransform g u := by
  rw [walshTransform_dobbertinConstruction_of_isBent_of_isBalanced
    f g hf hflat hg, if_neg hu]

/-- Dobbertin's modification is balanced. -/
theorem isBalanced_dobbertinConstruction
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) :
    IsBalanced (dobbertinConstruction f g) := by
  apply (isBalanced_iff_walshTransform_zero_eq_zero _).2
  have hzero :
      (0 : FABL.F₂Cube (m + m)) =
        Fin.append (0 : FABL.F₂Cube m) 0 := by
    apply (cubeSplitLinearEquiv m m).injective
    simp
    rfl
  rw [hzero,
    walshTransform_dobbertinConstruction_zeroFirstBlock
      f g hf hflat hg]

/-- The spectral triangle inequality behind Dobbertin's nonlinearity bound. -/
theorem maxWalshMagnitude_dobbertinConstruction_le
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) :
    maxWalshMagnitude (dobbertinConstruction f g) ≤
      2 ^ m + maxWalshMagnitude g := by
  unfold maxWalshMagnitude
  apply Finset.sup'_le
  intro a _ha
  let p := cubeSplitLinearEquiv m m a
  have ha : Fin.append p.1 p.2 = a := by
    exact (Fin.appendEquiv m m).apply_symm_apply a
  rw [← ha,
    walshTransform_dobbertinConstruction_of_isBent_of_isBalanced
      f g hf hflat hg]
  by_cases hp : p.1 = 0
  · simp [hp]
  · rw [if_neg hp]
    calc
      (walshTransform f (Fin.append p.1 p.2) +
          walshTransform g p.1).natAbs ≤
          (walshTransform f (Fin.append p.1 p.2)).natAbs +
            (walshTransform g p.1).natAbs :=
        Int.natAbs_add_le _ _
      _ = 2 ^ m + (walshTransform g p.1).natAbs := by
        have hhalf : (m + m) / 2 = m := by omega
        rw [natAbs_walshTransform_eq_two_pow_half_of_isBent f hf,
          hhalf]
      _ ≤ 2 ^ m + maxWalshMagnitude g :=
        Nat.add_le_add_left
          (walshTransform_natAbs_le_maxWalshMagnitude g p.1) _

/-- Additive form of Dobbertin's nonlinearity bound. -/
theorem nonlinearity_dobbertinConstruction_add_le
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hm : 0 < m) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) :
    nonlinearity f + nonlinearity g ≤
      nonlinearity (dobbertinConstruction f g) + 2 ^ (m - 1) := by
  have hhRelation := two_mul_nonlinearity_add_maxWalshMagnitude
    (dobbertinConstruction f g)
  have hfRelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hgRelation := two_mul_nonlinearity_add_maxWalshMagnitude g
  have hhMax := maxWalshMagnitude_dobbertinConstruction_le
    f g hf hflat hg
  have hfMax := maxWalshMagnitude_eq_two_pow_half_of_isBent f hf
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf] at hfMax
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  omega

/-- Dobbertin's nonlinearity lower bound in Carlet's subtraction form. -/
theorem nonlinearity_dobbertinConstruction_lowerBound
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hm : 0 < m) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) :
    nonlinearity f + nonlinearity g - 2 ^ (m - 1) ≤
      nonlinearity (dobbertinConstruction f g) := by
  have hbound := nonlinearity_dobbertinConstruction_add_le
    f g hm hf hflat hg
  omega

/-- For a bent source, Carlet's two forms of the Dobbertin lower-bound term
agree. -/
theorem nonlinearity_dobbertinConstruction_boundTerm_eq
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hm : 0 < m) (hf : IsBent f) :
    nonlinearity f + nonlinearity g - 2 ^ (m - 1) =
      2 ^ (m + m - 1) - 2 ^ m + nonlinearity g := by
  have hfNonlinearity :=
    nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent
      f hf (by omega)
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf] at hfNonlinearity
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  have hlarge : 2 ^ m ≤ 2 ^ (m + m - 1) := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  omega

/-- Source-normalized form of Dobbertin's nonlinearity lower bound. -/
theorem nonlinearity_dobbertinConstruction_lowerBound_source
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hm : 0 < m) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) :
    2 ^ (m + m - 1) - 2 ^ m + nonlinearity g ≤
      nonlinearity (dobbertinConstruction f g) := by
  rw [← nonlinearity_dobbertinConstruction_boundTerm_eq f g hm hf]
  exact nonlinearity_dobbertinConstruction_lowerBound
    f g hm hf hflat hg

private theorem eq_of_two_fullMagnitude_walshCoefficients
    (g : BooleanFunction m) (a b : FABL.F₂Cube m)
    (ha : (walshTransform g a).natAbs = 2 ^ m)
    (hb : (walshTransform g b).natAbs = 2 ^ m) :
    a = b := by
  classical
  by_contra hab
  have haCast := congrArg (fun q : ℕ ↦ (q : ℝ)) ha
  have haAbs :
      |(walshTransform g a : ℝ)| = (2 : ℝ) ^ m := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
      Nat.cast_ofNat] using haCast
  have haSquare :
      (walshTransform g a : ℝ) ^ 2 = ((2 : ℝ) ^ m) ^ 2 := by
    rw [← sq_abs, haAbs]
  have hparseval := sum_walshTransform_sq_eq_two_pow_sq g
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset (FABL.F₂Cube m))
    (fun u ↦ (walshTransform g u : ℝ) ^ 2)
    (Finset.mem_univ a)
  have herase :
      (∑ u ∈ (Finset.univ : Finset (FABL.F₂Cube m)).erase a,
        (walshTransform g u : ℝ) ^ 2) = 0 := by
    nlinarith
  have hbmem :
      b ∈ (Finset.univ : Finset (FABL.F₂Cube m)).erase a := by
    simp [Ne.symm hab]
  have hbSquare :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _hu ↦ sq_nonneg (walshTransform g u : ℝ))).mp
      herase b hbmem
  have hbCast : (walshTransform g b : ℝ) = 0 := by
    nlinarith
  have hbZero : walshTransform g b = 0 := by
    exact_mod_cast hbCast
  rw [hbZero] at hb
  have hpositive : 0 < 2 ^ m := by positivity
  omega

/-- In ambient dimension at least four, Dobbertin's construction is not
resilient of any positive order. -/
theorem not_isResilient_dobbertinConstruction_of_pos
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (hm : 2 ≤ m) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) (hk : 0 < k) :
    ¬ IsResilient k (dobbertinConstruction f g) := by
  intro hresilient
  have hresilientOne :
      IsResilient 1 (dobbertinConstruction f g) := by
    refine ⟨?_, hresilient.2⟩
    intro J z hcard
    exact hresilient.1 J z (by omega)
  have hwalshZero :=
    (theorem_3_resilient_iff_walshTransform_eq_zero
      1 (dobbertinConstruction f g) (by omega) (by omega)).1
      hresilientOne
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let a : FABL.F₂Cube m := Pi.single i₀ 1
  let b : FABL.F₂Cube m := Pi.single i₁ 1
  have hi : i₀ ≠ i₁ := by
    intro h
    have hval := congrArg Fin.val h
    simp [i₀, i₁] at hval
  have haNe : a ≠ 0 := by
    intro h
    have hvalue := congrFun h i₀
    simp [a] at hvalue
  have hbNe : b ≠ 0 := by
    intro h
    have hvalue := congrFun h i₁
    simp [b] at hvalue
  have hab : a ≠ b := by
    intro h
    have hvalue := congrFun h i₀
    simp [a, b, hi] at hvalue
  have haCard : #(FABL.f₂Support a) = 1 := by
    rw [show FABL.f₂Support a = {i₀} by
      ext j
      simp [FABL.f₂Support, a, Pi.single_apply]]
    simp
  have hbCard : #(FABL.f₂Support b) = 1 := by
    rw [show FABL.f₂Support b = {i₁} by
      ext j
      simp [FABL.f₂Support, b, Pi.single_apply]]
    simp
  have hmaskMagnitude
      (u : FABL.F₂Cube m) (huNe : u ≠ 0)
      (huCard : #(FABL.f₂Support u) = 1) :
      (walshTransform g u).natAbs = 2 ^ m := by
    have hfrequencyCard :
        #(FABL.f₂Support
          (Fin.append u (0 : FABL.F₂Cube m))) ≤ 1 := by
      rw [card_f₂Support_append, huCard]
      simp [FABL.f₂Support]
    have hzero := hwalshZero
      (Fin.append u (0 : FABL.F₂Cube m)) hfrequencyCard
    have hspectrum :=
      walshTransform_dobbertinConstruction_ne_zeroFirstBlock
        f g hf hflat hg u 0 huNe
    have hsum :
        walshTransform f (Fin.append u 0) + walshTransform g u = 0 :=
      hspectrum.symm.trans hzero
    have hmask :
        walshTransform g u =
          -walshTransform f (Fin.append u 0) :=
      eq_neg_of_add_eq_zero_right hsum
    rw [hmask, Int.natAbs_neg,
      natAbs_walshTransform_eq_two_pow_half_of_isBent f hf]
    congr 1
    omega
  have haMagnitude := hmaskMagnitude a haNe haCard
  have hbMagnitude := hmaskMagnitude b hbNe hbCard
  exact hab
    (eq_of_two_fullMagnitude_walshCoefficients
      g a b haMagnitude hbMagnitude)

end CryptBoolean
