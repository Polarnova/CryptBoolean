/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AffineSubspaceRestrictions
public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter04.IndicatorSpectralBounds
public import CryptBoolean.Carlet.Chapter04.OtherComplexity
public import CryptBoolean.Carlet.Chapter05.Affine

import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Nonlinearity of affine-flat restrictions

Carlet Relation (42) and its affine-restriction consequence.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

noncomputable local instance restrictionSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

/-- A binary coordinate model of a subspace cannot have dimension larger
than the ambient cube. -/
theorem coordinateAffineSubspaceDimension_le
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    k ≤ n := by
  have hdim : Module.finrank FABL.𝔽₂ E = k := by
    have heq := LinearEquiv.finrank_eq e
    rw [Module.finrank_fintype_fun_eq_card] at heq
    simpa using heq.symm
  calc
    k = Module.finrank FABL.𝔽₂ E := hdim.symm
    _ ≤ n := by simpa using E.finrank_le

/-- Adding an affine Boolean function preserves maximum raw Walsh magnitude. -/
theorem maxWalshMagnitude_add_affineFunction
    (f : BooleanFunction n) (b : FABL.𝔽₂)
    (a : FABL.F₂Cube n) :
    maxWalshMagnitude (f + FABL.affineFunction b a) =
      maxWalshMagnitude f := by
  classical
  apply le_antisymm
  · unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro u _hu
    rw [walshTransform_add_affineFunction_natAbs]
    exact Finset.le_sup'
      (fun v : FABL.F₂Cube n ↦ (walshTransform f v).natAbs)
      (Finset.mem_univ (u + a))
  · unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro u _hu
    have hle := Finset.le_sup'
      (fun v : FABL.F₂Cube n ↦
        (walshTransform (f + FABL.affineFunction b a) v).natAbs)
      (Finset.mem_univ (u + a))
    rw [walshTransform_add_affineFunction_natAbs] at hle
    simpa [add_assoc, ZModModule.add_self] using hle

/-- A Walsh character indexed outside a subspace sums to zero over the
perpendicular subspace. -/
theorem sum_vectorWalshCharacter_perpendicular_eq_zero_of_not_mem
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x : FABL.F₂Cube n) (hx : x ∉ E) :
    (∑ u : FABL.perpendicularSubspace E,
      FABL.vectorWalshCharacter x u.1) = 0 := by
  classical
  have hxPerpendicular :
      x ∉ FABL.perpendicularSubspace (FABL.perpendicularSubspace E) := by
    simpa [FABL.perpendicularSubspace_perpendicularSubspace] using hx
  have hsum := FABL.subspaceCharacterSum_eq_zero_of_not_mem
    (FABL.perpendicularSubspace E) x hxPerpendicular
  change
    (∑ u : FABL.perpendicularSubspace E,
      FABL.vectorWalshCharacter u.1 x) = 0 at hsum
  calc
    (∑ u : FABL.perpendicularSubspace E,
        FABL.vectorWalshCharacter x u.1) =
        ∑ u : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter u.1 x := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [FABL.vectorWalshCharacter_apply,
        FABL.vectorWalshCharacter_apply]
      congr 1
      exact dotProduct_comm x u.1
    _ = 0 := hsum

/-- Every binary frequency on coordinates of a subspace extends to an
ambient dot-product frequency. -/
theorem exists_ambientFrequency_restricts_to_subspace
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube k) :
    ∃ b : FABL.F₂Cube n, ∀ y : FABL.F₂Cube k,
      FABL.f₂DotProduct b (e y).1 = FABL.f₂DotProduct c y := by
  let localFrequency : Module.Dual FABL.𝔽₂ E :=
    ((dotProductEquiv FABL.𝔽₂ (Fin k)) c).comp e.symm.toLinearMap
  obtain ⟨ambientFrequency, hextend⟩ :=
    LinearMap.exists_extend localFrequency
  let b : FABL.F₂Cube n :=
    (dotProductEquiv FABL.𝔽₂ (Fin n)).symm ambientFrequency
  refine ⟨b, ?_⟩
  intro y
  calc
    FABL.f₂DotProduct b (e y).1 =
      (dotProductEquiv FABL.𝔽₂ (Fin n) b) (e y).1 :=
      (dotProductEquiv_apply_apply FABL.𝔽₂ (Fin n) b (e y).1).symm
    _ = ambientFrequency (e y).1 := by
      rw [show dotProductEquiv FABL.𝔽₂ (Fin n) b = ambientFrequency by
        exact (dotProductEquiv FABL.𝔽₂ (Fin n)).apply_symm_apply _]
    _ = localFrequency (e y) := by
      exact DFunLike.congr_fun hextend (e y)
    _ = (dotProductEquiv FABL.𝔽₂ (Fin k) c) y := by
      change (dotProductEquiv FABL.𝔽₂ (Fin k) c) (e.symm (e y)) = _
      rw [e.symm_apply_apply]
    _ = FABL.f₂DotProduct c y :=
      dotProductEquiv_apply_apply FABL.𝔽₂ (Fin k) c y

/-- Poisson summation expresses a Walsh coefficient of a coset restriction
as the signed mean of an ambient Walsh coset. -/
theorem sum_walshTransform_perpendicularCoset_eq_restriction
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube k)
    (b : FABL.F₂Cube n)
    (hb : ∀ y : FABL.F₂Cube k,
      FABL.f₂DotProduct b (e y).1 = FABL.f₂DotProduct c y) :
    (∑ u : FABL.perpendicularSubspace E,
        FABL.vectorWalshCharacter a (b + u.1) *
          (walshTransform f (b + u.1) : ℝ)) =
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        (walshTransform
          (coordinateAffineSubspaceRestriction f E a e) c : ℝ) := by
  classical
  let h := coordinateAffineSubspaceRestriction f E a e
  have htransform (u : FABL.F₂Cube n) :
      rawFourierTransform (realSignView f) u =
        (walshTransform f u : ℝ) :=
    (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm
  have hcharacter (y : FABL.F₂Cube k) :
      FABL.vectorWalshCharacter b (e y).1 =
        FABL.vectorWalshCharacter c y := by
    rw [FABL.vectorWalshCharacter_apply,
      FABL.vectorWalshCharacter_apply, hb y]
  have hlocal :
      (∑ x : E,
          FABL.vectorWalshCharacter b (a + x.1) *
            realSignView f (a + x.1)) =
        FABL.vectorWalshCharacter b a * (walshTransform h c : ℝ) := by
    rw [← Fintype.sum_equiv e.toEquiv
      (fun y : FABL.F₂Cube k ↦
        FABL.vectorWalshCharacter b (a + (e y).1) *
          realSignView f (a + (e y).1))
      (fun x : E ↦ FABL.vectorWalshCharacter b (a + x.1) *
        realSignView f (a + x.1))
      (fun _ ↦ rfl)]
    rw [walshTransform_cast_eq_sum_realSignView_mul_character,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [AddChar.map_add_eq_mul, hcharacter]
    change
      (FABL.vectorWalshCharacter b a * FABL.vectorWalshCharacter c y) *
          realSignView f (a + (e y).1) =
        FABL.vectorWalshCharacter b a *
          (realSignView h y * FABL.vectorWalshCharacter c y)
    rw [show realSignView h y = realSignView f (a + (e y).1) by
      simp only [h, realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, coordinateAffineSubspaceRestriction_apply,
        add_comm]]
    ring
  have hsymm :
      FABL.vectorWalshCharacter b a =
        FABL.vectorWalshCharacter a b := by
    rw [FABL.vectorWalshCharacter_apply,
      FABL.vectorWalshCharacter_apply]
    congr 1
    exact dotProduct_comm b a
  have hsquare :
      FABL.vectorWalshCharacter a b *
        FABL.vectorWalshCharacter b a = 1 := by
    rw [hsymm, ← AddChar.map_add_eq_mul, ZModModule.add_self,
      AddChar.map_zero_eq_one]
  have hpoisson := rawPoissonSummationFormula
    (realSignView f) (FABL.perpendicularSubspace E) b a
  rw [FABL.perpendicularSubspace_perpendicularSubspace] at hpoisson
  simp_rw [htransform] at hpoisson
  rw [hlocal] at hpoisson
  calc
    (∑ u : FABL.perpendicularSubspace E,
        FABL.vectorWalshCharacter a (b + u.1) *
          (walshTransform f (b + u.1) : ℝ)) =
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          FABL.vectorWalshCharacter a b *
            (FABL.vectorWalshCharacter b a *
              (walshTransform h c : ℝ)) := hpoisson
    _ = (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        (walshTransform h c : ℝ) := by
      calc
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
            FABL.vectorWalshCharacter a b *
              (FABL.vectorWalshCharacter b a *
                (walshTransform h c : ℝ)) =
            (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
              (FABL.vectorWalshCharacter a b *
                FABL.vectorWalshCharacter b a) *
                  (walshTransform h c : ℝ) := by ring
        _ = _ := by rw [hsquare, mul_one]

/-- Every Walsh magnitude of an affine-flat restriction is bounded by the
ambient maximum Walsh magnitude. -/
theorem abs_walshTransform_coordinateAffineSubspaceRestriction_le
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube k) :
    |(walshTransform
      (coordinateAffineSubspaceRestriction f E a e) c : ℝ)| ≤
        (maxWalshMagnitude f : ℝ) := by
  classical
  obtain ⟨b, hb⟩ :=
    exists_ambientFrequency_restricts_to_subspace E e c
  let q : FABL.perpendicularSubspace E → ℝ := fun u ↦
    FABL.vectorWalshCharacter a (b + u.1) *
      (walshTransform f (b + u.1) : ℝ)
  have hsum :
      (∑ u : FABL.perpendicularSubspace E, q u) =
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          (walshTransform
            (coordinateAffineSubspaceRestriction f E a e) c : ℝ) := by
    exact sum_walshTransform_perpendicularCoset_eq_restriction
      f E a e c b hb
  have htriangle :
      |∑ u : FABL.perpendicularSubspace E, q u| ≤
        ∑ u : FABL.perpendicularSubspace E, |q u| := by
    simpa using Finset.abs_sum_le_sum_abs q Finset.univ
  have hterms :
      (∑ u : FABL.perpendicularSubspace E, |q u|) ≤
        ∑ _u : FABL.perpendicularSubspace E,
          (maxWalshMagnitude f : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    change
      |FABL.vectorWalshCharacter a (b + u.1) *
          (walshTransform f (b + u.1) : ℝ)| ≤
        (maxWalshMagnitude f : ℝ)
    rw [abs_mul, FABL.abs_vectorWalshCharacter, one_mul]
    exact abs_walshTransform_le_maxWalshMagnitude f (b + u.1)
  have hscaled :
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          |(walshTransform
            (coordinateAffineSubspaceRestriction f E a e) c : ℝ)| ≤
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          (maxWalshMagnitude f : ℝ) := by
    have hcardNonnegative :
        0 ≤ (Nat.card (FABL.perpendicularSubspace E) : ℝ) := by
      positivity
    calc
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          |(walshTransform
            (coordinateAffineSubspaceRestriction f E a e) c : ℝ)| =
          |(Nat.card (FABL.perpendicularSubspace E) : ℝ) *
            (walshTransform
              (coordinateAffineSubspaceRestriction f E a e) c : ℝ)| := by
        rw [abs_mul, abs_of_nonneg hcardNonnegative]
      _ = |∑ u : FABL.perpendicularSubspace E, q u| := by rw [hsum]
      _ ≤ ∑ u : FABL.perpendicularSubspace E, |q u| := htriangle
      _ ≤ ∑ _u : FABL.perpendicularSubspace E,
          (maxWalshMagnitude f : ℝ) := hterms
      _ = (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          (maxWalshMagnitude f : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]
  have hcardPositive :
      0 < (Nat.card (FABL.perpendicularSubspace E) : ℝ) := by
    exact_mod_cast Nat.card_pos
  exact le_of_mul_le_mul_left hscaled hcardPositive

/-- Passing to an affine-flat restriction cannot increase the maximum raw
Walsh magnitude. -/
theorem maxWalshMagnitude_coordinateAffineSubspaceRestriction_le
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    maxWalshMagnitude (coordinateAffineSubspaceRestriction f E a e) ≤
      maxWalshMagnitude f := by
  classical
  unfold maxWalshMagnitude
  apply Finset.sup'_le
  intro c _
  have hreal :=
    abs_walshTransform_coordinateAffineSubspaceRestriction_le
      f E a e c
  have hcast :
      ((walshTransform
        (coordinateAffineSubspaceRestriction f E a e) c).natAbs : ℝ) ≤
          (maxWalshMagnitude f : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal
  exact_mod_cast hcast

/-- The division-free, all-dimensions form of Carlet Relation (42). -/
theorem two_mul_nonlinearity_add_two_pow_le_restriction
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    2 * nonlinearity f + 2 ^ k ≤
      2 ^ n +
        2 * nonlinearity (coordinateAffineSubspaceRestriction f E a e) := by
  have hmax :=
    maxWalshMagnitude_coordinateAffineSubspaceRestriction_le f E a e
  have hambient := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hrestriction := two_mul_nonlinearity_add_maxWalshMagnitude
    (coordinateAffineSubspaceRestriction f E a e)
  omega

/-- Carlet Relation (42), written over the reals so the half-cardinality
terms remain total in dimensions zero and one. -/
theorem nonlinearity_cast_le_restriction_relation_42
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    (nonlinearity f : ℝ) ≤
      (2 ^ n : ℝ) / 2 - (2 ^ k : ℝ) / 2 +
        nonlinearity (coordinateAffineSubspaceRestriction f E a e) := by
  have hmax :
      (maxWalshMagnitude
        (coordinateAffineSubspaceRestriction f E a e) : ℝ) ≤
          (maxWalshMagnitude f : ℝ) := by
    exact_mod_cast
      maxWalshMagnitude_coordinateAffineSubspaceRestriction_le f E a e
  rw [nonlinearity_cast_eq_relation_35 f,
    nonlinearity_cast_eq_relation_35
      (coordinateAffineSubspaceRestriction f E a e)]
  linarith

/-- The natural-number exponent form of Relation (42) in positive flat
dimension. -/
theorem nonlinearity_le_restriction_relation_42
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hk : 1 ≤ k) :
    nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (k - 1) +
        nonlinearity (coordinateAffineSubspaceRestriction f E a e) := by
  have hkn : k ≤ n := coordinateAffineSubspaceDimension_le E e
  have hn : 1 ≤ n := hk.trans hkn
  have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    exact (mul_pow_sub_one (by omega : k ≠ 0) 2).symm
  have hnpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    exact (mul_pow_sub_one (by omega : n ≠ 0) 2).symm
  have hpowle : 2 ^ (k - 1) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdivisionFree :=
    two_mul_nonlinearity_add_two_pow_le_restriction f E a e
  rw [hkpow, hnpow] at hdivisionFree
  omega

/-- Relation (42) in Carlet's complementary-subspace parameterization. -/
theorem nonlinearity_le_restriction_relation_42_of_isCompl
    (f : BooleanFunction n)
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (_hcompl : IsCompl E E')
    (a : E')
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hk : 1 ≤ k) :
    nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (k - 1) +
        nonlinearity
          (coordinateAffineSubspaceRestriction f E a.1 e) :=
  nonlinearity_le_restriction_relation_42 f E a.1 e hk

/-- An affine restriction on an ambient flat becomes an affine Boolean
function in any binary coordinate model of its direction space. -/
theorem exists_affineFunction_eq_coordinateAffineSubspaceRestriction_of_isAffineOnAffineFlat
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hflat : IsAffineOnAffineFlat f E a) :
    ∃ b : FABL.𝔽₂, ∃ c : FABL.F₂Cube k,
      coordinateAffineSubspaceRestriction f E a e =
        FABL.affineFunction b c := by
  obtain ⟨b, c, hbc⟩ := hflat
  refine ⟨FABL.affineFunction b c a,
    coordinateRestrictedAffineFrequency E e c, ?_⟩
  funext y
  have hyMem : (e y).1 + a ∈ FABL.binaryAffineSubspace E a := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    rw [add_assoc, ZModModule.add_self, add_zero]
    exact (e y).2
  calc
    coordinateAffineSubspaceRestriction f E a e y =
        FABL.affineFunction b c ((e y).1 + a) := hbc _ hyMem
    _ = FABL.affineFunction (FABL.affineFunction b c a)
        (coordinateRestrictedAffineFrequency E e c) y := by
      simpa [add_comm] using
        affineFunction_coordinateAffineSubspaceRestriction E e a c b y

/-- An affine affine-flat restriction has zero nonlinearity in subspace
coordinates. -/
theorem nonlinearity_coordinateAffineSubspaceRestriction_eq_zero_of_isAffineOnAffineFlat
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hflat : IsAffineOnAffineFlat f E a) :
    nonlinearity (coordinateAffineSubspaceRestriction f E a e) = 0 := by
  obtain ⟨b, c, hrestriction⟩ :=
    exists_affineFunction_eq_coordinateAffineSubspaceRestriction_of_isAffineOnAffineFlat
      f E a e hflat
  rw [hrestriction]
  unfold nonlinearity
  apply Nat.eq_zero_of_le_zero
  have hle := Finset.inf'_le
    (fun p : FABL.𝔽₂ × FABL.F₂Cube k ↦
      hammingDistance (FABL.affineFunction b c)
        (FABL.affineFunction p.1 p.2))
    (Finset.mem_univ (b, c))
  simpa using hle

/-- If a Boolean function is affine on a positive-dimensional affine flat,
its nonlinearity satisfies Carlet's affine-flat bound. -/
theorem nonlinearity_le_of_isAffineOnAffineFlat
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hk : 1 ≤ k)
    (hflat : IsAffineOnAffineFlat f E a) :
    nonlinearity f ≤ 2 ^ (n - 1) - 2 ^ (k - 1) := by
  have hrelation :=
    nonlinearity_le_restriction_relation_42 f E a e hk
  rw [nonlinearity_coordinateAffineSubspaceRestriction_eq_zero_of_isAffineOnAffineFlat
    f E a e hflat, add_zero] at hrelation
  exact hrelation

/-- Equality in the affine-flat nonlinearity bound forces the sum with any
ambient affine extension to be balanced on every other coset. -/
theorem isBalanced_coordinateAffineSubspaceRestriction_add_affineFunction_of_eq_bound
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hk : 1 ≤ k)
    (b : FABL.𝔽₂) (c : FABL.F₂Cube n)
    (hextension : ∀ x ∈ FABL.binaryAffineSubspace E a,
      f x = FABL.affineFunction b c x)
    (hequality : nonlinearity f =
      2 ^ (n - 1) - 2 ^ (k - 1))
    (z : FABL.F₂Cube n) (hz : z + a ∉ E) :
    IsBalanced
      (coordinateAffineSubspaceRestriction
        (f + FABL.affineFunction b c) E z e) := by
  classical
  let g : BooleanFunction n := f + FABL.affineFunction b c
  have hkn : k ≤ n := coordinateAffineSubspaceDimension_le E e
  have hn : 1 ≤ n := hk.trans hkn
  have hkpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    exact (mul_pow_sub_one (by omega : k ≠ 0) 2).symm
  have hnpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    exact (mul_pow_sub_one (by omega : n ≠ 0) 2).symm
  have hpowle : 2 ^ (k - 1) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmaxf : maxWalshMagnitude f = 2 ^ k := by
    have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
    rw [hequality, hnpow] at hrelation
    omega
  have hmaxg : maxWalshMagnitude g = 2 ^ k := by
    dsimp [g]
    rw [maxWalshMagnitude_add_affineFunction, hmaxf]
  have hrestrictionZero :
      coordinateAffineSubspaceRestriction g E a e = 0 := by
    funext y
    have hyMem : (e y).1 + a ∈ FABL.binaryAffineSubspace E a := by
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
      rw [add_assoc, ZModModule.add_self, add_zero]
      exact (e y).2
    change f ((e y).1 + a) +
      FABL.affineFunction b c ((e y).1 + a) = 0
    rw [hextension _ hyMem, CharTwo.add_self_eq_zero]
  have hlocalWalsh :
      walshTransform (coordinateAffineSubspaceRestriction g E a e) 0 =
        (2 ^ k : ℤ) := by
    rw [hrestrictionZero, walshTransform_zero_eq_two_pow_sub_two_weight]
    simp
  let q : FABL.perpendicularSubspace E → ℝ := fun u ↦
    FABL.vectorWalshCharacter a u.1 * (walshTransform g u.1 : ℝ)
  have hpoissonA :=
    sum_walshTransform_perpendicularCoset_eq_restriction
      g E a e 0 0 (by
        intro y
        simp [FABL.f₂DotProduct])
  have hsumA :
      (∑ u : FABL.perpendicularSubspace E, q u) =
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          (2 ^ k : ℝ) := by
    simpa [q, hlocalWalsh] using hpoissonA
  have hqLe (u : FABL.perpendicularSubspace E) :
      q u ≤ (2 ^ k : ℝ) := by
    have habs := abs_walshTransform_le_maxWalshMagnitude g u.1
    rw [hmaxg] at habs
    calc
      q u ≤ |q u| := le_abs_self _
      _ = |(walshTransform g u.1 : ℝ)| := by
        dsimp [q]
        rw [abs_mul, FABL.abs_vectorWalshCharacter, one_mul]
      _ ≤ (2 ^ k : ℝ) := by simpa using habs
  have hsumConst :
      (∑ u : FABL.perpendicularSubspace E, q u) =
        ∑ _u : FABL.perpendicularSubspace E, (2 ^ k : ℝ) := by
    rw [hsumA, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
  have hqEq (u : FABL.perpendicularSubspace E) :
      q u = (2 ^ k : ℝ) := by
    exact (Finset.sum_eq_sum_iff_of_le
      (fun v _hv ↦ hqLe v)).mp hsumConst u (Finset.mem_univ u)
  have hwalshg (u : FABL.perpendicularSubspace E) :
      (walshTransform g u.1 : ℝ) =
        FABL.vectorWalshCharacter a u.1 * (2 ^ k : ℝ) := by
    have hterm := hqEq u
    dsimp [q] at hterm
    have hsquare :
        FABL.vectorWalshCharacter a u.1 *
            FABL.vectorWalshCharacter a u.1 = 1 := by
      rw [← AddChar.map_add_eq_mul, ZModModule.add_self,
        AddChar.map_zero_eq_one]
    calc
      (walshTransform g u.1 : ℝ) =
          1 * (walshTransform g u.1 : ℝ) := by ring
      _ = (FABL.vectorWalshCharacter a u.1 *
            FABL.vectorWalshCharacter a u.1) *
              (walshTransform g u.1 : ℝ) := by rw [hsquare]
      _ = FABL.vectorWalshCharacter a u.1 *
          (FABL.vectorWalshCharacter a u.1 *
            (walshTransform g u.1 : ℝ)) := by ring
      _ = FABL.vectorWalshCharacter a u.1 * (2 ^ k : ℝ) := by
        rw [hterm]
  have hsumZ :
      (∑ u : FABL.perpendicularSubspace E,
        FABL.vectorWalshCharacter z u.1 *
          (walshTransform g u.1 : ℝ)) = 0 := by
    calc
      (∑ u : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter z u.1 *
            (walshTransform g u.1 : ℝ)) =
          ∑ u : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter z u.1 *
              (FABL.vectorWalshCharacter a u.1 * (2 ^ k : ℝ)) := by
        apply Finset.sum_congr rfl
        intro u _hu
        rw [hwalshg u]
      _ = (2 ^ k : ℝ) *
          ∑ u : FABL.perpendicularSubspace E,
            FABL.vectorWalshCharacter (z + a) u.1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        have hmul := DFunLike.congr_fun
          (FABL.vectorWalshCharacter_mul z a) u.1
        change FABL.vectorWalshCharacter z u.1 *
          FABL.vectorWalshCharacter a u.1 =
            FABL.vectorWalshCharacter (z + a) u.1 at hmul
        rw [← hmul]
        ring
      _ = 0 := by
        rw [sum_vectorWalshCharacter_perpendicular_eq_zero_of_not_mem
          E (z + a) hz, mul_zero]
  have hpoissonZ :=
    sum_walshTransform_perpendicularCoset_eq_restriction
      g E z e 0 0 (by
        intro y
        simp [FABL.f₂DotProduct])
  have hzeroProduct :
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        (walshTransform
          (coordinateAffineSubspaceRestriction g E z e) 0 : ℝ) = 0 := by
    rw [← hpoissonZ]
    simpa using hsumZ
  have hcardNe :
      (Nat.card (FABL.perpendicularSubspace E) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card
      (FABL.perpendicularSubspace E) ≠ 0)
  have hwalshZeroReal :
      (walshTransform
        (coordinateAffineSubspaceRestriction g E z e) 0 : ℝ) = 0 :=
    (mul_eq_zero.mp hzeroProduct).resolve_left hcardNe
  have hwalshZero :
      walshTransform
        (coordinateAffineSubspaceRestriction g E z e) 0 = 0 := by
    exact_mod_cast hwalshZeroReal
  change IsBalanced (coordinateAffineSubspaceRestriction g E z e)
  exact (isBalanced_iff_walshTransform_zero_eq_zero _).2 hwalshZero

end CryptBoolean
