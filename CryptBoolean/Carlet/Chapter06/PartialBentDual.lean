/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.PartialBent
public import CryptBoolean.Carlet.Chapter05.CoveringSequences

/-!
# Duality and Fourier types of partial bent functions

The punctured two-level Fourier definition, its involutive duality, and the
corrected Parseval dichotomy for the two Fourier types.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The integral raw Fourier transform of a Boolean function's zero-one embedding. -/
def partialBentIntegerFourier
    (f : BooleanFunction n) (u : FABL.F₂Cube n) : ℤ :=
  integerWalshTransform (fun x ↦ bitValueInt (f x)) u

/-- The integral partial-bent transform casts to the raw real Fourier transform. -/
theorem partialBentIntegerFourier_cast
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (partialBentIntegerFourier f u : ℝ) =
      rawFourierTransform (FABL.booleanRealEmbedding f) u := by
  rw [partialBentIntegerFourier,
    integerWalshTransform_cast_eq_rawFourierTransform]
  congr 2
  funext x
  by_cases hx : f x = 1 <;>
    simp [bitValueInt, FABL.booleanRealEmbedding, hx]

private theorem sum_bitSignInt_dotProduct_eq_zero
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    ∑ x, bitSignInt (FABL.f₂DotProduct x u) = 0 := by
  have hzero :
      integerWalshTransform (fun _ : FABL.F₂Cube n ↦ (1 : ℤ)) u = 0 := by
    apply Int.cast_injective (α := ℝ)
    norm_num only [Int.cast_zero]
    calc
      (integerWalshTransform (fun _ : FABL.F₂Cube n ↦ (1 : ℤ)) u : ℝ) =
          rawFourierTransform (fun _ : FABL.F₂Cube n ↦ (1 : ℝ)) u := by
        simpa using integerWalshTransform_cast_eq_rawFourierTransform
          (fun _ : FABL.F₂Cube n ↦ (1 : ℤ)) u
      _ = 0 := by rw [rawFourierTransform_one, if_neg hu]
  simpa [integerWalshTransform] using hzero

private theorem partialBentIntegerFourier_eq_of_constant_punctured
    (f : BooleanFunction n) (b : FABL.𝔽₂)
    (hconstant : ∀ x ≠ 0, f x = b)
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    partialBentIntegerFourier f u =
      bitValueInt (f 0) - bitValueInt b := by
  rw [partialBentIntegerFourier, integerWalshTransform]
  have hsum := sum_bitSignInt_dotProduct_eq_zero u hu
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : FABL.F₂Cube n))] at hsum ⊢
  have hrest :
      ∑ x ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          bitValueInt (f x) * bitSignInt (FABL.f₂DotProduct x u) =
        bitValueInt b *
          ∑ x ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
            bitSignInt (FABL.f₂DotProduct x u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa using (Finset.mem_erase.mp hx).1
    rw [hconstant x hx0]
  rw [hrest]
  simp [FABL.f₂DotProduct, bitSignInt] at hsum ⊢
  linear_combination bitValueInt b * hsum

private theorem exists_punctured_zero_and_one_of_partialBentLevels
    (f : BooleanFunction n) (level : ℤ)
    (hlevels : HasPartialBentFourierLevels f level) :
    (∃ x ≠ 0, f x = 0) ∧ (∃ x ≠ 0, f x = 1) := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ (n / 2) := by positivity
  have hdistinct :
      (level : ℝ) ≠ (level : ℝ) + (2 : ℝ) ^ (n / 2) := by
    linarith
  have hexistsLevel :
      ∃ u : {u : FABL.F₂Cube n // u ≠ 0},
        rawFourierTransform (FABL.booleanRealEmbedding f) u.1 = (level : ℝ) := by
    have hmem : (level : ℝ) ∈
        ({(level : ℝ), (level : ℝ) + (2 : ℝ) ^ (n / 2)} : Set ℝ) := by
      simp
    rw [← hlevels] at hmem
    exact hmem
  have hexistsUpper :
      ∃ u : {u : FABL.F₂Cube n // u ≠ 0},
        rawFourierTransform (FABL.booleanRealEmbedding f) u.1 =
          (level : ℝ) + (2 : ℝ) ^ (n / 2) := by
    have hmem : (level : ℝ) + (2 : ℝ) ^ (n / 2) ∈
        ({(level : ℝ), (level : ℝ) + (2 : ℝ) ^ (n / 2)} : Set ℝ) := by
      simp
    rw [← hlevels] at hmem
    exact hmem
  obtain ⟨u, hu⟩ := hexistsLevel
  obtain ⟨v, hv⟩ := hexistsUpper
  constructor
  · by_contra hzero
    push Not at hzero
    have hconstant : ∀ x ≠ 0, f x = 1 := by
      intro x hx
      exact Fin.eq_one_of_ne_zero _ (hzero x hx)
    have heu := partialBentIntegerFourier_eq_of_constant_punctured
      f 1 hconstant u.1 u.2
    have hev := partialBentIntegerFourier_eq_of_constant_punctured
      f 1 hconstant v.1 v.2
    have hucast := partialBentIntegerFourier_cast f u.1
    have hvcast := partialBentIntegerFourier_cast f v.1
    rw [heu, hu] at hucast
    rw [hev, hv] at hvcast
    linarith
  · by_contra hone
    push Not at hone
    have hconstant : ∀ x ≠ 0, f x = 0 := by
      intro x hx
      by_contra hzero
      exact hone x hx (Fin.eq_one_of_ne_zero _ hzero)
    have heu := partialBentIntegerFourier_eq_of_constant_punctured
      f 0 hconstant u.1 u.2
    have hev := partialBentIntegerFourier_eq_of_constant_punctured
      f 0 hconstant v.1 v.2
    have hucast := partialBentIntegerFourier_cast f u.1
    have hvcast := partialBentIntegerFourier_cast f v.1
    rw [heu, hu] at hucast
    rw [hev, hv] at hvcast
    linarith

private theorem partialBentIntegerFourier_eq_level_or
    (f : BooleanFunction n) (level : ℤ)
    (hlevels : HasPartialBentFourierLevels f level)
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    partialBentIntegerFourier f u = level ∨
      partialBentIntegerFourier f u = level + (2 : ℤ) ^ (n / 2) := by
  have hmem :
      rawFourierTransform (FABL.booleanRealEmbedding f) u ∈
        Set.range (fun v : {v : FABL.F₂Cube n // v ≠ 0} ↦
          rawFourierTransform (FABL.booleanRealEmbedding f) v.1) :=
    ⟨⟨u, hu⟩, rfl⟩
  rw [hlevels] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hcast := partialBentIntegerFourier_cast f u
  rcases hmem with h | h
  · left
    exact_mod_cast hcast.trans h
  · right
    have hpow : (((2 : ℤ) ^ (n / 2) : ℤ) : ℝ) =
        (2 : ℝ) ^ (n / 2) := by norm_num
    exact_mod_cast hcast.trans h

/-- The dual of a partial bent function, with the source's punctured-spectrum
convention completed at zero by `f(0)`. -/
def partialBentDual
    (f : BooleanFunction n) (level : ℤ) : BooleanFunction n :=
  fun u ↦
    if u = 0 then f 0
    else if partialBentIntegerFourier f u = level then 0 else 1

@[simp] theorem partialBentDual_zero
    (f : BooleanFunction n) (level : ℤ) :
    partialBentDual f level 0 = f 0 := by
  simp [partialBentDual]

private theorem bitValueInt_partialBentDual_of_ne_zero
    (f : BooleanFunction n) (level : ℤ)
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    bitValueInt (partialBentDual f level u) =
      if partialBentIntegerFourier f u = level then 0 else 1 := by
  by_cases hvalue : partialBentIntegerFourier f u = level <;>
    simp [partialBentDual, hu, hvalue, bitValueInt]

private theorem partialBentIntegerFourier_decomposition
    (f : BooleanFunction n) (level : ℤ)
    (hlevels : HasPartialBentFourierLevels f level)
    (u : FABL.F₂Cube n) :
    partialBentIntegerFourier f u =
      level + (2 : ℤ) ^ (n / 2) *
          bitValueInt (partialBentDual f level u) +
        if u = 0 then
          partialBentIntegerFourier f 0 - level -
            (2 : ℤ) ^ (n / 2) * bitValueInt (f 0)
        else 0 := by
  by_cases hu : u = 0
  · subst u
    simp [partialBentDual]
  · rcases partialBentIntegerFourier_eq_level_or f level hlevels u hu with
      hvalue | hvalue
    · rw [if_neg hu,
        bitValueInt_partialBentDual_of_ne_zero f level u hu,
        if_pos hvalue]
      omega
    · have hne : partialBentIntegerFourier f u ≠ level := by
        intro heq
        have hpositive : (0 : ℤ) < (2 : ℤ) ^ (n / 2) := by positivity
        omega
      rw [if_neg hu,
        bitValueInt_partialBentDual_of_ne_zero f level u hu,
        if_neg hne, hvalue]
      omega

private theorem partialBentDual_transform_relation
    (f : BooleanFunction n) (level : ℤ)
    (hlevels : HasPartialBentFourierLevels f level)
    (x : FABL.F₂Cube n) (hx : x ≠ 0) :
    (2 : ℤ) ^ (n / 2) *
        partialBentIntegerFourier (partialBentDual f level) x =
      (2 : ℤ) ^ n * bitValueInt (f x) -
        (partialBentIntegerFourier f 0 - level -
          (2 : ℤ) ^ (n / 2) * bitValueInt (f 0)) := by
  let q : ℤ := (2 : ℤ) ^ (n / 2)
  let correction : ℤ :=
    partialBentIntegerFourier f 0 - level - q * bitValueInt (f 0)
  have hinvolution :=
    integerWalshTransform_involution
      (fun y ↦ bitValueInt (f y)) x
  change integerWalshTransform (partialBentIntegerFourier f) x =
      (2 : ℤ) ^ n * bitValueInt (f x) at hinvolution
  rw [integerWalshTransform] at hinvolution
  have hconstant := sum_bitSignInt_dotProduct_eq_zero x hx
  have horigin :
      ∑ u : FABL.F₂Cube n,
          (if u = 0 then correction else 0) *
            bitSignInt (FABL.f₂DotProduct u x) = correction := by
    rw [Fintype.sum_eq_single 0]
    · simp [FABL.f₂DotProduct, bitSignInt]
    · intro u hu
      simp [hu]
  have hdual :
      ∑ u : FABL.F₂Cube n,
          (q * bitValueInt (partialBentDual f level u)) *
            bitSignInt (FABL.f₂DotProduct u x) =
        q * partialBentIntegerFourier (partialBentDual f level) x := by
    rw [partialBentIntegerFourier, integerWalshTransform, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    ring
  have hdecomposition (u : FABL.F₂Cube n) :
      partialBentIntegerFourier f u =
        level + q * bitValueInt (partialBentDual f level u) +
          if u = 0 then correction else 0 := by
    exact partialBentIntegerFourier_decomposition f level hlevels u
  simp_rw [hdecomposition] at hinvolution
  have hconstantScaled :
      ∑ u : FABL.F₂Cube n,
          level * bitSignInt (FABL.f₂DotProduct u x) = 0 := by
    rw [← Finset.mul_sum, hconstant, mul_zero]
  rw [show
      (∑ u : FABL.F₂Cube n,
        (level + q * bitValueInt (partialBentDual f level u) +
            if u = 0 then correction else 0) *
          bitSignInt (FABL.f₂DotProduct u x)) =
        (∑ u : FABL.F₂Cube n,
          level * bitSignInt (FABL.f₂DotProduct u x)) +
        (∑ u : FABL.F₂Cube n,
          (q * bitValueInt (partialBentDual f level u)) *
            bitSignInt (FABL.f₂DotProduct u x)) +
        (∑ u : FABL.F₂Cube n,
          (if u = 0 then correction else 0) *
            bitSignInt (FABL.f₂DotProduct u x)) by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _hu
      ring] at hinvolution
  rw [hconstantScaled, zero_add, hdual, horigin] at hinvolution
  dsimp [q, correction] at hinvolution ⊢
  omega

/-- The punctured Fourier transform of the partial-bent dual again has two
levels, and its level choice records the values of the original function. -/
theorem exists_partialBentDual_fourierLevels
    (f : BooleanFunction n) (level : ℤ)
    (hn : Even n)
    (hlevels : HasPartialBentFourierLevels f level) :
    ∃ dualLevel : ℤ,
      HasPartialBentFourierLevels (partialBentDual f level) dualLevel ∧
        ∀ x ≠ 0,
          partialBentIntegerFourier (partialBentDual f level) x =
            dualLevel + (2 : ℤ) ^ (n / 2) * bitValueInt (f x) := by
  obtain ⟨⟨x₀, hx₀, hfx₀⟩, ⟨x₁, hx₁, hfx₁⟩⟩ :=
    exists_punctured_zero_and_one_of_partialBentLevels f level hlevels
  let g := partialBentDual f level
  let dualLevel := partialBentIntegerFourier g x₀
  refine ⟨dualLevel, ?_, ?_⟩
  · rw [HasPartialBentFourierLevels]
    ext value
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      have hrelationX :=
        partialBentDual_transform_relation f level hlevels x hx
      have hrelationZero :=
        partialBentDual_transform_relation f level hlevels x₀ hx₀
      have hq : (2 : ℤ) ^ (n / 2) ≠ 0 := by positivity
      have hpow : (2 : ℤ) ^ n =
          (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) := by
        rcases hn with ⟨m, rfl⟩
        have hhalf : (m + m) / 2 = m := by omega
        rw [hhalf, ← pow_add]
      rw [hpow] at hrelationX hrelationZero
      have hbitZero : bitValueInt (f x₀) = 0 := by
        simp [hfx₀, bitValueInt]
      rw [hbitZero, mul_zero] at hrelationZero
      have hvalue :
          partialBentIntegerFourier g x =
            dualLevel + (2 : ℤ) ^ (n / 2) * bitValueInt (f x) := by
        dsimp [g, dualLevel]
        apply mul_left_cancel₀ hq
        linear_combination hrelationX - hrelationZero
      have hcast := partialBentIntegerFourier_cast g x
      rw [hvalue] at hcast
      by_cases hfx : f x = 0
      · left
        rw [hfx] at hcast
        simpa [bitValueInt] using hcast.symm
      · right
        have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
        rw [hfxOne] at hcast
        norm_num [bitValueInt] at hcast ⊢
        exact hcast.symm
    · intro hvalue
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalue
      rcases hvalue with hvalue | hvalue
      · refine ⟨⟨x₀, hx₀⟩, ?_⟩
        have hcast := partialBentIntegerFourier_cast g x₀
        dsimp [dualLevel]
        rw [hvalue]
        exact hcast.symm
      · refine ⟨⟨x₁, hx₁⟩, ?_⟩
        have hrelationOne :=
          partialBentDual_transform_relation f level hlevels x₁ hx₁
        have hrelationZero :=
          partialBentDual_transform_relation f level hlevels x₀ hx₀
        have hq : (2 : ℤ) ^ (n / 2) ≠ 0 := by positivity
        have hpow : (2 : ℤ) ^ n =
            (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) := by
          rcases hn with ⟨m, rfl⟩
          have hhalf : (m + m) / 2 = m := by omega
          rw [hhalf, ← pow_add]
        rw [hpow] at hrelationOne hrelationZero
        have hbitOne : bitValueInt (f x₁) = 1 := by
          simp [hfx₁, bitValueInt]
        have hbitZero : bitValueInt (f x₀) = 0 := by
          simp [hfx₀, bitValueInt]
        rw [hbitOne, mul_one] at hrelationOne
        rw [hbitZero, mul_zero] at hrelationZero
        have hinteger :
            partialBentIntegerFourier g x₁ =
              dualLevel + (2 : ℤ) ^ (n / 2) := by
          dsimp [dualLevel]
          apply mul_left_cancel₀ hq
          linear_combination hrelationOne - hrelationZero
        have hcast := partialBentIntegerFourier_cast g x₁
        rw [hinteger] at hcast
        rw [hvalue]
        norm_num at hcast ⊢
        simpa [g] using hcast.symm
  · intro x hx
    have hrelationX :=
      partialBentDual_transform_relation f level hlevels x hx
    have hrelationZero :=
      partialBentDual_transform_relation f level hlevels x₀ hx₀
    have hq : (2 : ℤ) ^ (n / 2) ≠ 0 := by positivity
    have hpow : (2 : ℤ) ^ n =
        (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) := by
      rcases hn with ⟨m, rfl⟩
      have hhalf : (m + m) / 2 = m := by omega
      rw [hhalf, ← pow_add]
    rw [hpow] at hrelationX hrelationZero
    have hbitZero : bitValueInt (f x₀) = 0 := by
      simp [hfx₀, bitValueInt]
    rw [hbitZero, mul_zero] at hrelationZero
    dsimp [g, dualLevel]
    apply mul_left_cancel₀ hq
    linear_combination hrelationX - hrelationZero

/-- Taking the partial-bent dual twice, with the Fourier levels supplied by
the first duality theorem, returns the original function. -/
theorem partialBentDual_involution
    (f : BooleanFunction n) (level dualLevel : ℤ)
    (hdual : ∀ x ≠ 0,
      partialBentIntegerFourier (partialBentDual f level) x =
        dualLevel + (2 : ℤ) ^ (n / 2) * bitValueInt (f x)) :
    partialBentDual (partialBentDual f level) dualLevel = f := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp
  · rw [partialBentDual]
    simp only [hx, if_false]
    rw [hdual x hx]
    by_cases hfx : f x = 0
    · simp [hfx, bitValueInt]
    · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
      rw [hfxOne]
      simp [bitValueInt]

/-- A partial-bent dual is partial bent, and its dual is the original function. -/
theorem exists_isPartialBent_partialBentDual_and_involution
    (f : BooleanFunction n) (level : ℤ)
    (hn : Even n)
    (hlevels : HasPartialBentFourierLevels f level) :
    ∃ dualLevel : ℤ,
      IsPartialBent (partialBentDual f level) ∧
        HasPartialBentFourierLevels (partialBentDual f level) dualLevel ∧
          partialBentDual (partialBentDual f level) dualLevel = f := by
  obtain ⟨dualLevel, hdualLevels, htransform⟩ :=
    exists_partialBentDual_fourierLevels f level hn hlevels
  exact ⟨dualLevel, ⟨hn, dualLevel, hdualLevels⟩, hdualLevels,
    partialBentDual_involution f level dualLevel htransform⟩

private theorem sum_partialBentIntegerFourier
    (f : BooleanFunction n) :
    ∑ u, partialBentIntegerFourier f u =
      (2 : ℤ) ^ n * bitValueInt (f 0) := by
  have hinvolution := integerWalshTransform_involution
    (fun x ↦ bitValueInt (f x)) (0 : FABL.F₂Cube n)
  change integerWalshTransform (partialBentIntegerFourier f) 0 =
    (2 : ℤ) ^ n * bitValueInt (f 0) at hinvolution
  simpa using hinvolution

private theorem sum_partialBentIntegerFourier_sq
    (f : BooleanFunction n) :
    ∑ u, (partialBentIntegerFourier f u) ^ 2 =
      (2 : ℤ) ^ n * partialBentIntegerFourier f 0 := by
  apply Int.cast_injective (α := ℝ)
  norm_num only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat, Int.cast_mul]
  simp_rw [partialBentIntegerFourier_cast]
  rw [show
      (∑ u : FABL.F₂Cube n,
        rawFourierTransform (FABL.booleanRealEmbedding f) u ^ 2) =
        ∑ u : FABL.F₂Cube n,
          rawFourierTransform (FABL.booleanRealEmbedding f) u *
            rawFourierTransform (FABL.booleanRealEmbedding f) u by
      apply Finset.sum_congr rfl
      intro u _hu
      ring,
    sum_rawFourierTransform_mul]
  have hsum :
      ∑ x : FABL.F₂Cube n,
          FABL.booleanRealEmbedding f x * FABL.booleanRealEmbedding f x =
        rawFourierTransform (FABL.booleanRealEmbedding f) 0 := by
    calc
      ∑ x : FABL.F₂Cube n,
          FABL.booleanRealEmbedding f x * FABL.booleanRealEmbedding f x =
          ∑ x : FABL.F₂Cube n, FABL.booleanRealEmbedding f x := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hfx : f x = 1 <;>
          simp [FABL.booleanRealEmbedding, hfx]
      _ = rawFourierTransform (FABL.booleanRealEmbedding f) 0 := by
        simp [rawFourierTransform]
  rw [hsum]

/-- Parseval gives the two mutually exclusive partial-bent Fourier types.
The second factor has the corrected sign, and both factors retain the origin
value required by the punctured-spectrum convention. -/
theorem partialBent_fourier_level_types
    (f : BooleanFunction n) (level : ℤ)
    (hnEven : Even n) (hn : 0 < n)
    (hlevels : HasPartialBentFourierLevels f level) :
    Xor
      (partialBentIntegerFourier f 0 - bitValueInt (f 0) =
        -(level - bitValueInt (f 0)) *
          ((2 : ℤ) ^ (n / 2) - 1))
      (partialBentIntegerFourier f 0 - bitValueInt (f 0) =
        ((2 : ℤ) ^ (n / 2) + level - bitValueInt (f 0)) *
          ((2 : ℤ) ^ (n / 2) + 1)) := by
  let q : ℤ := (2 : ℤ) ^ (n / 2)
  let total : ℤ := (2 : ℤ) ^ n
  let weight : ℤ := partialBentIntegerFourier f 0
  let origin : ℤ := bitValueInt (f 0)
  have hqPositive : 0 < q := by
    dsimp [q]
    positivity
  have hhalfPositive : 0 < n / 2 := by
    rcases hnEven with ⟨m, hm⟩
    subst n
    omega
  have hqEven : Even q := by
    refine ⟨(2 : ℤ) ^ (n / 2 - 1), ?_⟩
    dsimp [q]
    have hindex : n / 2 = n / 2 - 1 + 1 := by omega
    calc
      (2 : ℤ) ^ (n / 2) = (2 : ℤ) ^ (n / 2 - 1 + 1) :=
        congrArg (fun k : ℕ ↦ (2 : ℤ) ^ k) hindex
      _ = (2 : ℤ) ^ (n / 2 - 1) * 2 := by rw [pow_succ]
      _ = (2 : ℤ) ^ (n / 2 - 1) + (2 : ℤ) ^ (n / 2 - 1) := by ring
  have hsum := sum_partialBentIntegerFourier f
  have hsquares := sum_partialBentIntegerFourier_sq f
  change (∑ u, partialBentIntegerFourier f u) = total * origin at hsum
  change (∑ u, (partialBentIntegerFourier f u) ^ 2) = total * weight at hsquares
  have hquad (u : FABL.F₂Cube n) (hu : u ≠ 0) :
      (partialBentIntegerFourier f u - level) *
          (partialBentIntegerFourier f u - level - q) = 0 := by
    rcases partialBentIntegerFourier_eq_level_or f level hlevels u hu with
      hvalue | hvalue
    · rw [hvalue]
      ring
    · change partialBentIntegerFourier f u = level + q at hvalue
      rw [hvalue]
      ring
  have hsumQuad :
      ∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          ((partialBentIntegerFourier f u - level) *
            (partialBentIntegerFourier f u - level - q)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact hquad u (Finset.mem_erase.mp hu).1
  have hsumErase :
      ∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          partialBentIntegerFourier f u = total * origin - weight := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      (f := fun u ↦ partialBentIntegerFourier f u)
      (Finset.mem_univ (0 : FABL.F₂Cube n))
    rw [hsum] at hsplit
    change
      (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
        partialBentIntegerFourier f u) + weight = total * origin at hsplit
    linear_combination hsplit
  have hsquaresErase :
      ∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          (partialBentIntegerFourier f u) ^ 2 =
        total * weight - weight ^ 2 := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      (f := fun u ↦ (partialBentIntegerFourier f u) ^ 2)
      (Finset.mem_univ (0 : FABL.F₂Cube n))
    rw [hsquares] at hsplit
    change
      (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
        (partialBentIntegerFourier f u) ^ 2) + weight ^ 2 =
          total * weight at hsplit
    linear_combination hsplit
  have hcardErase :
      (Finset.univ.erase (0 : FABL.F₂Cube n)).card = (2 ^ n : ℕ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_f₂Cube]
  have htotal : total = q * q := by
    rcases hnEven with ⟨m, hm⟩
    subst n
    have hhalf : (m + m) / 2 = m := by omega
    dsimp [total, q]
    rw [hhalf, ← pow_add]
  have horiginSq : origin ^ 2 = origin := by
    dsimp [origin]
    by_cases hvalue : f 0 = 1 <;>
      simp [bitValueInt, hvalue]
  have hfactor :
      (weight - origin + (level - origin) * (q - 1)) *
        (weight - origin - (q + level - origin) * (q + 1)) = 0 := by
    have hcardCast :
        ((Finset.univ.erase (0 : FABL.F₂Cube n)).card : ℤ) = total - 1 := by
      rw [hcardErase]
      dsimp [total]
      norm_num
    have hexpand :
        (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          ((partialBentIntegerFourier f u - level) *
            (partialBentIntegerFourier f u - level - q))) =
          (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
            (partialBentIntegerFourier f u) ^ 2) -
          (2 * level + q) *
            (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
              partialBentIntegerFourier f u) +
          ((Finset.univ.erase (0 : FABL.F₂Cube n)).card : ℤ) *
            (level * (level + q)) := by
      calc
        (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
          ((partialBentIntegerFourier f u - level) *
            (partialBentIntegerFourier f u - level - q))) =
            ∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
              ((partialBentIntegerFourier f u) ^ 2 -
                (2 * level + q) * partialBentIntegerFourier f u +
                level * (level + q)) := by
          apply Finset.sum_congr rfl
          intro u _hu
          ring
        _ =
          (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
            (partialBentIntegerFourier f u) ^ 2) -
          (2 * level + q) *
            (∑ u ∈ (Finset.univ.erase (0 : FABL.F₂Cube n)),
              partialBentIntegerFourier f u) +
          ((Finset.univ.erase (0 : FABL.F₂Cube n)).card : ℤ) *
            (level * (level + q)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
          simp
    rw [hexpand, hsquaresErase, hsumErase, hcardCast] at hsumQuad
    rw [htotal] at hsumQuad
    nlinarith [horiginSq]
  change Xor
    (weight - origin = -(level - origin) * (q - 1))
    (weight - origin = (q + level - origin) * (q + 1))
  rcases mul_eq_zero.mp hfactor with hfirst | hsecond
  · refine Or.inl ⟨?_, ?_⟩
    · linarith
    · intro hsecondEq
      change weight - origin =
        (q + level - origin) * (q + 1) at hsecondEq
      have hrootEq :
          -(level - origin) * (q - 1) =
            (q + level - origin) * (q + 1) := by
        linarith
      obtain ⟨r, hr⟩ := hqEven
      have hproduct : q * (q + 1 + 2 * (level - origin)) = 0 := by
        calc
          q * (q + 1 + 2 * (level - origin)) =
              (q + level - origin) * (q + 1) -
                (-(level - origin) * (q - 1)) := by ring
          _ = 0 := by rw [hrootEq]; ring
      have hlinear : q + 1 + 2 * (level - origin) = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hqPositive)
      omega
  · refine Or.inr ⟨?_, ?_⟩
    · linarith
    · intro hfirstEq
      change weight - origin =
        -(level - origin) * (q - 1) at hfirstEq
      have hrootEq :
          -(level - origin) * (q - 1) =
            (q + level - origin) * (q + 1) := by
        linarith
      obtain ⟨r, hr⟩ := hqEven
      have hproduct : q * (q + 1 + 2 * (level - origin)) = 0 := by
        calc
          q * (q + 1 + 2 * (level - origin)) =
              (q + level - origin) * (q + 1) -
                (-(level - origin) * (q - 1)) := by ring
          _ = 0 := by rw [hrootEq]; ring
      have hlinear : q + 1 + 2 * (level - origin) = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hqPositive)
      omega

end CryptBoolean
