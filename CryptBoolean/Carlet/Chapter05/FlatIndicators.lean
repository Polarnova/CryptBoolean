/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
public import CryptBoolean.Carlet.Chapter04.Nonlinearity

/-!
# Carlet Chapter 5 affine-flat indicators

Exact raw Walsh spectra and nonlinearities of affine-flat indicators.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance affineFlatIndicatorMembershipDecidable
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    DecidablePred (fun x ↦ x ∈ FABL.perpendicularSubspace H) :=
  Classical.decPred _

/-- The sign view of an affine-flat indicator is one minus twice its real
set indicator. -/
theorem realSignView_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a x : FABL.F₂Cube n) :
    realSignView (affineFlatIndicator H a) x =
      1 - 2 * FABL.setIndicator
        (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x := by
  by_cases hx : x ∈ FABL.binaryAffineSubspace H a
  · simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, affineFlatIndicator, FABL.setIndicator, hx]
    norm_num
  · simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, affineFlatIndicator, FABL.setIndicator, hx]

/-- Carlet Section 5.3: the affine-flat indicator has a three-case raw Walsh
spectrum, supported on the perpendicular direction. -/
theorem walshTransform_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a u : FABL.F₂Cube n) :
    walshTransform (affineFlatIndicator H a) u =
      if u = 0 then
        (2 ^ n : ℤ) - 2 * (Nat.card H : ℤ)
      else if u ∈ FABL.perpendicularSubspace H then
        -2 * bitSignInt (FABL.f₂DotProduct u a) * (Nat.card H : ℤ)
      else 0 := by
  classical
  by_cases hu : u = 0
  · subst u
    rw [if_pos rfl, walshTransform_zero_eq_two_pow_sub_two_weight,
      hammingWeight_affineFlatIndicator,
      ← FABL.card_submodule_eq_two_pow_finrank H]
  · rw [if_neg hu]
    apply Int.cast_injective (α := ℝ)
    rw [walshTransform_cast_eq_sum_realSignView_mul_character]
    simp_rw [realSignView_affineFlatIndicator]
    have hcharacter : ∑ x, FABL.vectorWalshCharacter u x = 0 := by
      have h := FABL.expect_vectorWalshCharacter u
      rw [if_neg hu, Fintype.expect_eq_sum_div_card] at h
      exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
    calc
      ∑ x, (1 - 2 * FABL.setIndicator
            (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) x) *
          FABL.vectorWalshCharacter u x =
          (∑ x, FABL.vectorWalshCharacter u x) -
            2 * rawFourierTransform
              (FABL.setIndicator
                (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n))) u := by
        rw [rawFourierTransform, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = -2 * rawFourierTransform
              (FABL.setIndicator
                (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n))) u := by
        rw [hcharacter]
        ring
      _ = ((if u ∈ FABL.perpendicularSubspace H then
            -2 * bitSignInt (FABL.f₂DotProduct u a) * (Nat.card H : ℤ)
          else 0 : ℤ) : ℝ) := by
        rw [rawFourierTransform_setIndicator_binaryAffineSubspace]
        by_cases huH : u ∈ FABL.perpendicularSubspace H
        · rw [if_pos huH, if_pos huH]
          rw [FABL.vectorWalshCharacter_apply, ← bitSignInt_cast]
          push_cast
          ring
        · rw [if_neg huH, if_neg huH]
          norm_num

private theorem four_mul_card_le_two_pow_of_two_le_codimension
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcodim : 2 ≤ FABL.f₂Codimension H) :
    4 * Nat.card H ≤ 2 ^ n := by
  have hrankTwo : Module.finrank FABL.𝔽₂ H + 2 ≤ n := by
    have hrankLe : Module.finrank FABL.𝔽₂ H ≤ n := by
      simpa using H.finrank_le
    rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace] at hcodim
    omega
  calc
    4 * Nat.card H = 2 ^ (Module.finrank FABL.𝔽₂ H + 2) := by
      rw [FABL.card_submodule_eq_two_pow_finrank, pow_add]
      norm_num
      omega
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hrankTwo

/-- In codimension at least two, the zero-frequency coefficient is the
largest absolute Walsh coefficient of an affine-flat indicator. -/
theorem maxWalshMagnitude_affineFlatIndicator_of_two_le_codimension
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hcodim : 2 ≤ FABL.f₂Codimension H) :
    maxWalshMagnitude (affineFlatIndicator H a) =
      2 ^ n - 2 * Nat.card H := by
  classical
  have hfour :=
    four_mul_card_le_two_pow_of_two_le_codimension H hcodim
  have htwo : 2 * Nat.card H ≤ 2 ^ n := by omega
  have hside : 2 * Nat.card H ≤ 2 ^ n - 2 * Nat.card H := by omega
  have hzeroAbs :
      ((2 ^ n : ℤ) - 2 * (Nat.card H : ℤ)).natAbs =
        2 ^ n - 2 * Nat.card H := by
    simpa using Int.natAbs_natCast_sub_natCast_of_ge htwo
  unfold maxWalshMagnitude
  apply Nat.le_antisymm
  · apply Finset.sup'_le
    intro u _hu
    rw [walshTransform_affineFlatIndicator]
    by_cases huzero : u = 0
    · rw [if_pos huzero]
      rw [hzeroAbs]
    · rw [if_neg huzero]
      by_cases huH : u ∈ FABL.perpendicularSubspace H
      · rw [if_pos huH]
        have hsign :
            (bitSignInt (FABL.f₂DotProduct u a)).natAbs = 1 := by
          simp [bitSignInt]
        rw [Int.natAbs_mul, Int.natAbs_mul, hsign]
        norm_num
        simpa [Nat.card_eq_fintype_card] using hside
      · rw [if_neg huH]
        simp
  · apply Finset.le_sup'_of_le
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      (f := fun u ↦ (walshTransform (affineFlatIndicator H a) u).natAbs)
      (Finset.mem_univ (0 : FABL.F₂Cube n))
    rw [walshTransform_affineFlatIndicator, if_pos rfl, hzeroAbs]

/-- Carlet Section 5.3: an affine-flat indicator of codimension at least two
has nonlinearity equal to the cardinality of its flat. -/
theorem nonlinearity_affineFlatIndicator_of_two_le_codimension
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hcodim : 2 ≤ FABL.f₂Codimension H) :
    nonlinearity (affineFlatIndicator H a) = Nat.card H := by
  have hrelation :=
    two_mul_nonlinearity_add_maxWalshMagnitude (affineFlatIndicator H a)
  rw [maxWalshMagnitude_affineFlatIndicator_of_two_le_codimension H a hcodim]
    at hrelation
  have hcardLe : 2 * Nat.card H ≤ 2 ^ n := by
    have hfour :=
      four_mul_card_le_two_pow_of_two_le_codimension H hcodim
    omega
  omega

/-- An affine-flat indicator of codimension at most one is affine and hence
has zero nonlinearity. -/
theorem nonlinearity_affineFlatIndicator_of_codimension_le_one
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hcodim : FABL.f₂Codimension H ≤ 1) :
    nonlinearity (affineFlatIndicator H a) = 0 := by
  have hdegree :
      FABL.functionAlgebraicDegree (affineFlatIndicator H a) ≤ 1 := by
    rw [functionAlgebraicDegree_affineFlatIndicator]
    exact hcodim
  obtain ⟨b, u, hfunction⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (affineFlatIndicator H a) hdegree
  unfold nonlinearity
  apply Nat.eq_zero_of_le_zero
  calc
    (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
        Finset.univ_nonempty
        (fun p ↦ hammingDistance (affineFlatIndicator H a)
          (FABL.affineFunction p.1 p.2)) ≤
        hammingDistance (affineFlatIndicator H a)
          (FABL.affineFunction b u) :=
      Finset.inf'_le _ (Finset.mem_univ (b, u))
    _ = hammingDistance (FABL.affineFunction b u)
        (FABL.affineFunction b u) := by rw [hfunction]
    _ = 0 := hammingDist_self _

/-- Carlet Section 5.3 with the codimension-one exception made explicit: an
affine-flat indicator has zero nonlinearity in codimension zero or one and
otherwise has nonlinearity equal to the flat cardinality. -/
theorem nonlinearity_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    nonlinearity (affineFlatIndicator H a) =
      if FABL.f₂Codimension H ≤ 1 then 0 else Nat.card H := by
  by_cases hcodim : FABL.f₂Codimension H ≤ 1
  · rw [if_pos hcodim,
      nonlinearity_affineFlatIndicator_of_codimension_le_one H a hcodim]
  · have htwo : 2 ≤ FABL.f₂Codimension H := by omega
    rw [if_neg hcodim,
      nonlinearity_affineFlatIndicator_of_two_le_codimension H a htwo]

/-- The codimension-one case printed implicitly in Carlet's spectrum formula
has zero nonlinearity. -/
theorem nonlinearity_affineFlatIndicator_of_codimension_one
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hcodim : FABL.f₂Codimension H = 1) :
    nonlinearity (affineFlatIndicator H a) = 0 :=
  nonlinearity_affineFlatIndicator_of_codimension_le_one H a (by omega)

/-- Dimension form of the complete affine-flat-indicator nonlinearity
formula. -/
theorem nonlinearity_affineFlatIndicator_of_finrank_eq
    (r : ℕ) (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hrn : r ≤ n) (hfinrank : Module.finrank FABL.𝔽₂ H = n - r) :
    nonlinearity (affineFlatIndicator H a) =
      if r ≤ 1 then 0 else 2 ^ (n - r) := by
  have hcodim : FABL.f₂Codimension H = r := by
    rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace, hfinrank]
    omega
  rw [nonlinearity_affineFlatIndicator, hcodim,
    FABL.card_submodule_eq_two_pow_finrank, hfinrank]

end CryptBoolean
