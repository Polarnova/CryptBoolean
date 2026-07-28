/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.SpectralSupport

import Mathlib.Algebra.Order.Chebyshev

/-!
# Fourier uncertainty for pseudo-Boolean functions

Carlet Proposition 27: a nonzero pseudo-Boolean function and its raw Fourier
transform cannot both have small support.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

/-- The finite support of a pseudo-Boolean function. -/
noncomputable def pseudoBooleanSupport (φ : PseudoBooleanFunction n) :
    Finset (FABL.F₂Cube n) :=
  Finset.univ.filter fun x ↦ φ x ≠ 0

@[simp] theorem mem_pseudoBooleanSupport (φ : PseudoBooleanFunction n)
    (x : FABL.F₂Cube n) :
    x ∈ pseudoBooleanSupport φ ↔ φ x ≠ 0 := by
  classical
  simp [pseudoBooleanSupport]

private theorem sum_pseudoBooleanSupport_pow_eq_sum
    (φ : PseudoBooleanFunction n) (k : ℕ) (hk : k ≠ 0) :
    (∑ x ∈ pseudoBooleanSupport φ, φ x ^ k) = ∑ x, φ x ^ k := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _hx hnot
  have hzero : φ x = 0 := by
    exact not_ne_iff.mp (by simpa only [mem_pseudoBooleanSupport] using hnot)
  simp [hzero, hk]

private theorem sum_rawFourierSupport_pow_eq_sum
    (φ : PseudoBooleanFunction n) (k : ℕ) (hk : k ≠ 0) :
    (∑ u ∈ rawFourierSupport φ, rawFourierTransform φ u ^ k) =
      ∑ u, rawFourierTransform φ u ^ k := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _hu hnot
  have hzero : rawFourierTransform φ u = 0 := by
    exact not_ne_iff.mp (by simpa only [mem_rawFourierSupport] using hnot)
  simp [hzero, hk]

private theorem sum_sq_pos_of_pseudoBoolean_ne_zero
    (φ : PseudoBooleanFunction n) (hφ : φ ≠ 0) :
    0 < ∑ x, φ x ^ 2 := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hφ
  exact Finset.sum_pos'
    (fun y _hy ↦ sq_nonneg (φ y))
    ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩

private theorem rawFourierTransform_sq_le_card_support_mul_sum_sq
    (φ : PseudoBooleanFunction n) (u : FABL.F₂Cube n) :
    rawFourierTransform φ u ^ 2 ≤
      ((pseudoBooleanSupport φ).card : ℝ) * ∑ x, φ x ^ 2 := by
  classical
  have hsum :
      (∑ x ∈ pseudoBooleanSupport φ,
          φ x * FABL.vectorWalshCharacter u x) =
        ∑ x, φ x * FABL.vectorWalshCharacter u x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _hx hnot
    have hzero : φ x = 0 := by
      exact not_ne_iff.mp (by simpa only [mem_pseudoBooleanSupport] using hnot)
    simp [hzero]
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := pseudoBooleanSupport φ)
    (f := fun x ↦ φ x * FABL.vectorWalshCharacter u x)
  calc
    rawFourierTransform φ u ^ 2 =
        (∑ x ∈ pseudoBooleanSupport φ,
          φ x * FABL.vectorWalshCharacter u x) ^ 2 := by
      rw [rawFourierTransform, hsum]
    _ ≤ ((pseudoBooleanSupport φ).card : ℝ) *
          ∑ x ∈ pseudoBooleanSupport φ,
            (φ x * FABL.vectorWalshCharacter u x) ^ 2 := hcauchy
    _ = ((pseudoBooleanSupport φ).card : ℝ) *
          ∑ x ∈ pseudoBooleanSupport φ, φ x ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      rw [mul_pow]
      have hcharacter : FABL.vectorWalshCharacter u x ^ 2 = 1 := by
        rw [← sq_abs, FABL.abs_vectorWalshCharacter, one_pow]
      rw [hcharacter, mul_one]
    _ = ((pseudoBooleanSupport φ).card : ℝ) * ∑ x, φ x ^ 2 := by
      rw [sum_pseudoBooleanSupport_pow_eq_sum φ 2 (by norm_num)]

private theorem eq_on_of_sq_sum_eq_card_mul_sum_sq
    {α : Type*} (s : Finset α) (q : α → ℝ)
    (hs : s.Nonempty)
    (heq : (∑ x ∈ s, q x) ^ 2 = (s.card : ℝ) * ∑ x ∈ s, q x ^ 2) :
    ∀ x ∈ s, ∀ y ∈ s, q x = q y := by
  classical
  let mean : ℝ := (∑ x ∈ s, q x) / (s.card : ℝ)
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hs
  have hvariance : ∑ x ∈ s, (q x - mean) ^ 2 = 0 := by
    have hpoint (x : α) :
        (q x - mean) ^ 2 = q x ^ 2 - 2 * mean * q x + mean ^ 2 := by
      ring
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hmiddle :
        (∑ x ∈ s, 2 * mean * q x) = 2 * mean * ∑ x ∈ s, q x := by
      rw [Finset.mul_sum]
    rw [hmiddle]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [mean]
    field_simp [hcard]
    nlinarith [heq]
  have hterm (x : α) (hx : x ∈ s) : q x = mean := by
    have hxzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _hy ↦ sq_nonneg (q y - mean))).mp hvariance x hx
    nlinarith [sq_nonneg (q x - mean)]
  intro x hx y hy
  rw [hterm x hx, hterm y hy]

private theorem rawFourierTransform_sq_eq_card_support_mul_sum_sq_of_eq
    (φ : PseudoBooleanFunction n)
    (hproduct :
      (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card = 2 ^ n)
    (u : FABL.F₂Cube n) (hu : u ∈ rawFourierSupport φ) :
    rawFourierTransform φ u ^ 2 =
      ((pseudoBooleanSupport φ).card : ℝ) * ∑ x, φ x ^ 2 := by
  classical
  let energy : ℝ := ∑ x, φ x ^ 2
  have hproductReal :
      (((pseudoBooleanSupport φ).card * (rawFourierSupport φ).card : ℕ) : ℝ) =
        (2 : ℝ) ^ n := by
    exact_mod_cast hproduct
  have hparseval :
      ∑ v, rawFourierTransform φ v ^ 2 = (2 : ℝ) ^ n * energy := by
    simpa only [pow_two, energy] using sum_rawFourierTransform_mul φ φ
  have hsums :
      (∑ v ∈ rawFourierSupport φ, rawFourierTransform φ v ^ 2) =
        ∑ _v ∈ rawFourierSupport φ,
          ((pseudoBooleanSupport φ).card : ℝ) * energy := by
    calc
      (∑ v ∈ rawFourierSupport φ, rawFourierTransform φ v ^ 2) =
          ∑ v, rawFourierTransform φ v ^ 2 :=
        sum_rawFourierSupport_pow_eq_sum φ 2 (by norm_num)
      _ = (2 : ℝ) ^ n * energy := hparseval
      _ = (((pseudoBooleanSupport φ).card *
            (rawFourierSupport φ).card : ℕ) : ℝ) * energy := by
        rw [hproductReal]
      _ = ∑ _v ∈ rawFourierSupport φ,
          ((pseudoBooleanSupport φ).card : ℝ) * energy := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
        ring
  exact (Finset.sum_eq_sum_iff_of_le
    (fun v _hv ↦ rawFourierTransform_sq_le_card_support_mul_sum_sq φ v)).mp
      hsums u hu

private theorem support_modulated_value_eq_of_uncertainty_eq
    (φ : PseudoBooleanFunction n) (hφ : φ ≠ 0)
    (hproduct :
      (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card = 2 ^ n)
    (u x y : FABL.F₂Cube n)
    (hu : u ∈ rawFourierSupport φ)
    (hx : x ∈ pseudoBooleanSupport φ)
    (hy : y ∈ pseudoBooleanSupport φ) :
    φ x * FABL.vectorWalshCharacter u x =
      φ y * FABL.vectorWalshCharacter u y := by
  classical
  let q : FABL.F₂Cube n → ℝ := fun z ↦
    φ z * FABL.vectorWalshCharacter u z
  have hsupportNonempty : (pseudoBooleanSupport φ).Nonempty := by
    obtain ⟨z, hz⟩ := Function.ne_iff.mp hφ
    exact ⟨z, (mem_pseudoBooleanSupport φ z).mpr hz⟩
  have hsum :
      (∑ z ∈ pseudoBooleanSupport φ, q z) = rawFourierTransform φ u := by
    dsimp [q]
    rw [rawFourierTransform]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _hz hnot
    have hzero : φ z = 0 := by
      exact not_ne_iff.mp (by simpa only [mem_pseudoBooleanSupport] using hnot)
    simp [hzero]
  have hsumSq :
      (∑ z ∈ pseudoBooleanSupport φ, q z ^ 2) = ∑ z, φ z ^ 2 := by
    calc
      (∑ z ∈ pseudoBooleanSupport φ, q z ^ 2) =
          ∑ z ∈ pseudoBooleanSupport φ, φ z ^ 2 := by
        apply Finset.sum_congr rfl
        intro z _hz
        dsimp [q]
        rw [mul_pow]
        have hcharacter : FABL.vectorWalshCharacter u z ^ 2 = 1 := by
          rw [← sq_abs, FABL.abs_vectorWalshCharacter, one_pow]
        rw [hcharacter, mul_one]
      _ = ∑ z, φ z ^ 2 :=
        sum_pseudoBooleanSupport_pow_eq_sum φ 2 (by norm_num)
  apply eq_on_of_sq_sum_eq_card_mul_sum_sq
    (pseudoBooleanSupport φ) q hsupportNonempty
  · rw [hsum, hsumSq]
    exact rawFourierTransform_sq_eq_card_support_mul_sum_sq_of_eq
      φ hproduct u hu
  · exact hx
  · exact hy

/-- Carlet Proposition 27's uncertainty inequality: for every nonzero
pseudo-Boolean function, the product of its value-support size and raw
Fourier-support size is at least the size of the binary cube. -/
theorem two_pow_le_card_pseudoBooleanSupport_mul_card_rawFourierSupport
    (φ : PseudoBooleanFunction n) (hφ : φ ≠ 0) :
    2 ^ n ≤ (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card := by
  classical
  let energy : ℝ := ∑ x, φ x ^ 2
  have henergy : 0 < energy :=
    sum_sq_pos_of_pseudoBoolean_ne_zero φ hφ
  have hparseval :
      ∑ u, rawFourierTransform φ u ^ 2 = (2 : ℝ) ^ n * energy := by
    simpa only [pow_two, energy] using
      sum_rawFourierTransform_mul φ φ
  have hscaled :
      (2 : ℝ) ^ n * energy ≤
        (((pseudoBooleanSupport φ).card * (rawFourierSupport φ).card : ℕ) : ℝ) *
          energy := by
    calc
      (2 : ℝ) ^ n * energy =
          ∑ u, rawFourierTransform φ u ^ 2 := hparseval.symm
      _ = ∑ u ∈ rawFourierSupport φ, rawFourierTransform φ u ^ 2 := by
        rw [sum_rawFourierSupport_pow_eq_sum φ 2 (by norm_num)]
      _ ≤ ∑ _u ∈ rawFourierSupport φ,
          ((pseudoBooleanSupport φ).card : ℝ) * energy := by
        apply Finset.sum_le_sum
        intro u _hu
        exact rawFourierTransform_sq_le_card_support_mul_sum_sq φ u
      _ = (((pseudoBooleanSupport φ).card *
            (rawFourierSupport φ).card : ℕ) : ℝ) * energy := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
        ring
  have hcast :
      (2 ^ n : ℝ) ≤
        (((pseudoBooleanSupport φ).card * (rawFourierSupport φ).card : ℕ) : ℝ) :=
    le_of_mul_le_mul_right hscaled henergy
  exact_mod_cast hcast

/-- A pseudo-Boolean function is a modulated affine-flat indicator when it is
a nonzero real multiple of one Walsh character on an affine flat and vanishes
off that flat. -/
def IsModulatedAffineFlatIndicator (φ : PseudoBooleanFunction n) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧
    ∃ H : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      ∃ a u : FABL.F₂Cube n,
        φ = fun x ↦ c * FABL.vectorWalshCharacter u x *
          FABL.setIndicator
            (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x

private theorem card_pseudoBooleanSupport_le_card_submodule_of_affineFlatIndicator
    (φ : PseudoBooleanFunction n) (c : ℝ)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a u : FABL.F₂Cube n)
    (hφ : φ = fun x ↦ c * FABL.vectorWalshCharacter u x *
      FABL.setIndicator
        (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x) :
    (pseudoBooleanSupport φ).card ≤ Nat.card H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have support_mem_flat (x : pseudoBooleanSupport φ) :
      x.1 ∈ FABL.binaryAffineSubspace H a := by
    by_contra hx
    have hzero :
        FABL.setIndicator
          (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x.1 = 0 := by
      simp [FABL.setIndicator, hx]
    have hxne : φ x.1 ≠ 0 := (mem_pseudoBooleanSupport φ x.1).mp x.2
    have hφx := congrFun hφ x.1
    rw [hφx, hzero, mul_zero] at hxne
    exact hxne rfl
  let toDirection : pseudoBooleanSupport φ → H := fun x ↦
    ⟨x.1 + a,
      (FABL.mem_binaryAffineSubspace_iff_add_mem H a x.1).mp
        (support_mem_flat x)⟩
  have hinjective : Function.Injective toDirection := by
    intro x y hxy
    apply Subtype.ext
    have hvalue := congrArg Subtype.val hxy
    exact add_right_cancel hvalue
  have hcard :
      Fintype.card (pseudoBooleanSupport φ) ≤ Fintype.card H :=
    Fintype.card_le_of_injective toDirection hinjective
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard

private theorem card_rawFourierSupport_le_card_perpendicular_of_affineFlatIndicator
    (φ : PseudoBooleanFunction n) (c : ℝ)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a u : FABL.F₂Cube n)
    (hφ : φ = fun x ↦ c * FABL.vectorWalshCharacter u x *
      FABL.setIndicator
        (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x) :
    (rawFourierSupport φ).card ≤
      Nat.card (FABL.perpendicularSubspace H) := by
  classical
  letI : Fintype (FABL.perpendicularSubspace H) := Fintype.ofFinite _
  have support_shift_mem (v : rawFourierSupport φ) :
      u + v.1 ∈ FABL.perpendicularSubspace H := by
    have hv : FABL.vectorFourierCoeff φ v.1 ≠ 0 :=
      (mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero φ v.1).mp v.2
    have hcoefficient :
        FABL.vectorFourierCoeff φ v.1 =
          c * FABL.vectorFourierCoeff
            (FABL.setIndicator
              (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)))
            (u + v.1) := by
      calc
        FABL.vectorFourierCoeff φ v.1 =
            FABL.vectorFourierCoeff
              (fun x ↦ c * FABL.vectorWalshCharacter u x *
                FABL.setIndicator
                  (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x)
              v.1 := congrArg (fun ψ : PseudoBooleanFunction n ↦
                FABL.vectorFourierCoeff ψ v.1) hφ
        _ = FABL.vectorFourierCoeff
            (fun x ↦ c *
              (FABL.vectorWalshCharacter u x *
                FABL.setIndicator
                  (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x)) v.1 := by
          congr 1
          funext x
          ring
        _ = _ := by
          rw [FABL.vectorFourierCoeff_const_mul,
            vectorFourierCoeff_mul_vectorWalshCharacter]
    rw [hcoefficient] at hv
    have hindicator :
        FABL.vectorFourierCoeff
          (FABL.setIndicator
            (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)))
          (u + v.1) ≠ 0 :=
      (mul_ne_zero_iff.mp hv).2
    exact (FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_ne_zero_iff
      H a (u + v.1)).mp hindicator
  let toPerpendicular : rawFourierSupport φ → FABL.perpendicularSubspace H :=
    fun v ↦ ⟨u + v.1, support_shift_mem v⟩
  have hinjective : Function.Injective toPerpendicular := by
    intro v w hvw
    apply Subtype.ext
    have hvalue := congrArg Subtype.val hvw
    exact add_left_cancel hvalue
  have hcard :
      Fintype.card (rawFourierSupport φ) ≤
        Fintype.card (FABL.perpendicularSubspace H) :=
    Fintype.card_le_of_injective toPerpendicular hinjective
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard

private theorem card_submodule_mul_card_perpendicular
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Nat.card H * Nat.card (FABL.perpendicularSubspace H) = 2 ^ n := by
  have hrank : Module.finrank FABL.𝔽₂ H ≤ n := by
    simpa using H.finrank_le
  rw [FABL.card_submodule_eq_two_pow_finrank,
    FABL.card_submodule_eq_two_pow_finrank,
    FABL.finrank_perpendicularSubspace, ← pow_add,
    Nat.add_sub_of_le hrank]

/-- Every nonzero modulated affine-flat indicator attains equality in the
Fourier uncertainty bound. -/
theorem IsModulatedAffineFlatIndicator.card_support_mul_card_rawFourierSupport_eq
    {φ : PseudoBooleanFunction n} (hφ : IsModulatedAffineFlatIndicator φ) :
    (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card = 2 ^ n := by
  rcases hφ with ⟨c, hc, H, a, u, hrepresentation⟩
  have hφne : φ ≠ 0 := by
    apply Function.ne_iff.mpr
    refine ⟨a, ?_⟩
    have ha : a ∈ FABL.binaryAffineSubspace H a := by
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
        ZModModule.add_self]
      exact H.zero_mem
    rw [hrepresentation]
    simp only [FABL.setIndicator, Set.indicator_of_mem ha, mul_one]
    apply mul_ne_zero hc
    rcases FABL.vectorWalshCharacter_eq_neg_one_or_one u a with h | h <;>
      simp [h]
  have hlower :=
    two_pow_le_card_pseudoBooleanSupport_mul_card_rawFourierSupport φ hφne
  have hvalueSupport :=
    card_pseudoBooleanSupport_le_card_submodule_of_affineFlatIndicator
      φ c H a u hrepresentation
  have hfrequencySupport :=
    card_rawFourierSupport_le_card_perpendicular_of_affineFlatIndicator
      φ c H a u hrepresentation
  have hupper :
      (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card ≤ 2 ^ n := by
    rw [← card_submodule_mul_card_perpendicular H]
    exact Nat.mul_le_mul hvalueSupport hfrequencySupport
  omega

/-- Equality in the Fourier uncertainty bound forces the value support to be
an affine flat and the function to be a nonzero scalar multiple of one Walsh
character on that flat. -/
theorem isModulatedAffineFlatIndicator_of_card_support_mul_card_rawFourierSupport_eq
    (φ : PseudoBooleanFunction n) (hφ : φ ≠ 0)
    (hproduct :
      (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card = 2 ^ n) :
    IsModulatedAffineFlatIndicator φ := by
  classical
  have hproductPos :
      0 < (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card := by
    rw [hproduct]
    positivity
  have hvalueSupportPos : 0 < (pseudoBooleanSupport φ).card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, zero_mul] at hproductPos
    exact (Nat.lt_irrefl 0 hproductPos).elim
  have hfrequencySupportPos : 0 < (rawFourierSupport φ).card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, mul_zero] at hproductPos
    exact (Nat.lt_irrefl 0 hproductPos).elim
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hvalueSupportPos
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hfrequencySupportPos
  let c : ℝ := φ a * FABL.vectorWalshCharacter u a
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero ((mem_pseudoBooleanSupport φ a).mp ha)
    rcases FABL.vectorWalshCharacter_eq_neg_one_or_one u a with h | h <;>
      simp [h]
  have hcharacterSq (v x : FABL.F₂Cube n) :
      FABL.vectorWalshCharacter v x ^ 2 = 1 := by
    rw [← sq_abs, FABL.abs_vectorWalshCharacter, one_pow]
  have hrepresentationOnSupport
      (x : FABL.F₂Cube n) (hx : x ∈ pseudoBooleanSupport φ) :
      φ x = c * FABL.vectorWalshCharacter u x := by
    have heq := support_modulated_value_eq_of_uncertainty_eq
      φ hφ hproduct u x a hu hx ha
    have hcharacterMul :
        FABL.vectorWalshCharacter u x * FABL.vectorWalshCharacter u x = 1 := by
      simpa [pow_two] using hcharacterSq u x
    calc
      φ x = φ x * 1 := by ring
      _ = φ x * (FABL.vectorWalshCharacter u x *
          FABL.vectorWalshCharacter u x) := by rw [hcharacterMul]
      _ = (φ x * FABL.vectorWalshCharacter u x) *
          FABL.vectorWalshCharacter u x := by ring
      _ = (φ a * FABL.vectorWalshCharacter u a) *
          FABL.vectorWalshCharacter u x := by rw [heq]
      _ = c * FABL.vectorWalshCharacter u x := rfl
  let H : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
    ⨅ v : rawFourierSupport φ,
      LinearMap.ker
        ((dotProductEquiv FABL.𝔽₂ (Fin n)) (u + v.1))
  have hsupportDifferenceMem
      (x : FABL.F₂Cube n) (hx : x ∈ pseudoBooleanSupport φ) :
      x + a ∈ H := by
    rw [show H = ⨅ v : rawFourierSupport φ,
      LinearMap.ker
        ((dotProductEquiv FABL.𝔽₂ (Fin n)) (u + v.1)) by rfl]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro v
    have hvEq := support_modulated_value_eq_of_uncertainty_eq
      φ hφ hproduct v.1 x a v.2 hx ha
    rw [hrepresentationOnSupport x hx,
      hrepresentationOnSupport a ha] at hvEq
    have hmulX := congrArg
      (fun χ : AddChar (FABL.F₂Cube n) ℝ ↦ χ x)
      (FABL.vectorWalshCharacter_mul u v.1)
    have hmulA := congrArg
      (fun χ : AddChar (FABL.F₂Cube n) ℝ ↦ χ a)
      (FABL.vectorWalshCharacter_mul u v.1)
    change FABL.vectorWalshCharacter u x *
        FABL.vectorWalshCharacter v.1 x =
      FABL.vectorWalshCharacter (u + v.1) x at hmulX
    change FABL.vectorWalshCharacter u a *
        FABL.vectorWalshCharacter v.1 a =
      FABL.vectorWalshCharacter (u + v.1) a at hmulA
    have hfrequency :
        FABL.vectorWalshCharacter (u + v.1) x =
          FABL.vectorWalshCharacter (u + v.1) a := by
      apply mul_left_cancel₀ hc
      calc
        c * FABL.vectorWalshCharacter (u + v.1) x =
            (c * FABL.vectorWalshCharacter u x) *
              FABL.vectorWalshCharacter v.1 x := by rw [← hmulX]; ring
        _ = (c * FABL.vectorWalshCharacter u a) *
              FABL.vectorWalshCharacter v.1 a := hvEq
        _ = c * FABL.vectorWalshCharacter (u + v.1) a := by rw [← hmulA]; ring
    have hcharacterOne :
        FABL.vectorWalshCharacter (u + v.1) (x + a) = 1 := by
      rw [AddChar.map_add_eq_mul, hfrequency]
      simpa [pow_two] using hcharacterSq (u + v.1) a
    have hdotZero : FABL.f₂DotProduct (u + v.1) (x + a) = 0 :=
      (FABL.binarySign_eq_one_iff _).mp (by
        rw [← FABL.vectorWalshCharacter_apply]
        exact hcharacterOne)
    rw [dotProductEquiv_apply_apply]
    simpa only [FABL.f₂DotProduct] using hdotZero
  let toDirection : pseudoBooleanSupport φ → H := fun x ↦
    ⟨x.1 + a, hsupportDifferenceMem x.1 x.2⟩
  have toDirection_injective : Function.Injective toDirection := by
    intro x y hxy
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val hxy)
  have hvalueSupport_le :
      (pseudoBooleanSupport φ).card ≤ Nat.card H := by
    letI : Fintype H := Fintype.ofFinite H
    have hcard :
        Fintype.card (pseudoBooleanSupport φ) ≤ Fintype.card H :=
      Fintype.card_le_of_injective toDirection toDirection_injective
    simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
  have hfrequencyShiftMem (v : rawFourierSupport φ) :
      u + v.1 ∈ FABL.perpendicularSubspace H := by
    rw [FABL.mem_perpendicularSubspace_iff]
    intro d hd
    rw [show H = ⨅ w : rawFourierSupport φ,
      LinearMap.ker
        ((dotProductEquiv FABL.𝔽₂ (Fin n)) (u + w.1)) by rfl] at hd
    have hd' : ∀ w : rawFourierSupport φ,
        ((dotProductEquiv FABL.𝔽₂ (Fin n)) (u + w.1)) d = 0 := by
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hd
    simpa [FABL.f₂DotProduct, dotProductEquiv_apply_apply] using hd' v
  let toPerpendicular : rawFourierSupport φ → FABL.perpendicularSubspace H :=
    fun v ↦ ⟨u + v.1, hfrequencyShiftMem v⟩
  have toPerpendicular_injective : Function.Injective toPerpendicular := by
    intro v w hvw
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hvw)
  have hfrequencySupport_le :
      (rawFourierSupport φ).card ≤
        Nat.card (FABL.perpendicularSubspace H) := by
    letI : Fintype (FABL.perpendicularSubspace H) := Fintype.ofFinite _
    have hcard :
        Fintype.card (rawFourierSupport φ) ≤
          Fintype.card (FABL.perpendicularSubspace H) :=
      Fintype.card_le_of_injective toPerpendicular toPerpendicular_injective
    simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard
  have hvalueSupportCard : (pseudoBooleanSupport φ).card = Nat.card H := by
    apply Nat.le_antisymm hvalueSupport_le
    by_contra hnot
    have hstrict : (pseudoBooleanSupport φ).card < Nat.card H :=
      Nat.lt_of_not_ge hnot
    have hperpendicularPos : 0 < Nat.card (FABL.perpendicularSubspace H) :=
      Nat.card_pos
    have hproductLe :
        (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card ≤
          (pseudoBooleanSupport φ).card *
            Nat.card (FABL.perpendicularSubspace H) :=
      Nat.mul_le_mul_left _ hfrequencySupport_le
    have hproductLt :
        (pseudoBooleanSupport φ).card *
            Nat.card (FABL.perpendicularSubspace H) <
          Nat.card H * Nat.card (FABL.perpendicularSubspace H) :=
      Nat.mul_lt_mul_of_pos_right hstrict hperpendicularPos
    have := hproductLe.trans_lt hproductLt
    rw [hproduct, card_submodule_mul_card_perpendicular H] at this
    exact (Nat.lt_irrefl _ this).elim
  letI : Fintype H := Fintype.ofFinite H
  have htoDirectionCard :
      Fintype.card (pseudoBooleanSupport φ) = Fintype.card H := by
    simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using
      hvalueSupportCard
  have toDirection_surjective : Function.Surjective toDirection :=
    ((Fintype.bijective_iff_injective_and_card toDirection).mpr
      ⟨toDirection_injective, htoDirectionCard⟩).2
  have hflat_iff_support (x : FABL.F₂Cube n) :
      x ∈ FABL.binaryAffineSubspace H a ↔ x ∈ pseudoBooleanSupport φ := by
    constructor
    · intro hx
      have hxa : x + a ∈ H :=
        (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).mp hx
      obtain ⟨y, hy⟩ := toDirection_surjective ⟨x + a, hxa⟩
      have hyValue := congrArg Subtype.val hy
      have hyx : y.1 = x := add_right_cancel hyValue
      simpa [hyx] using y.2
    · intro hx
      exact (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).mpr
        (hsupportDifferenceMem x hx)
  refine ⟨c, hc, H, a, u, ?_⟩
  funext x
  by_cases hx : x ∈ pseudoBooleanSupport φ
  · have hxflat := (hflat_iff_support x).mpr hx
    rw [hrepresentationOnSupport x hx]
    simp [FABL.setIndicator, hxflat]
  · have hxzero : φ x = 0 := by
      exact not_ne_iff.mp (by simpa only [mem_pseudoBooleanSupport] using hx)
    have hxflat : x ∉ FABL.binaryAffineSubspace H a := by
      exact fun h ↦ hx ((hflat_iff_support x).mp h)
    rw [hxzero]
    simp [FABL.setIndicator, hxflat]

/-- Carlet Proposition 27's equality classification. The coefficient is
explicitly nonzero, as forced by the theorem's nonzero-function hypothesis. -/
theorem card_support_mul_card_rawFourierSupport_eq_two_pow_iff
    (φ : PseudoBooleanFunction n) (hφ : φ ≠ 0) :
    (pseudoBooleanSupport φ).card * (rawFourierSupport φ).card = 2 ^ n ↔
      IsModulatedAffineFlatIndicator φ := by
  constructor
  · exact isModulatedAffineFlatIndicator_of_card_support_mul_card_rawFourierSupport_eq
      φ hφ
  · exact IsModulatedAffineFlatIndicator.card_support_mul_card_rawFourierSupport_eq

end CryptBoolean
