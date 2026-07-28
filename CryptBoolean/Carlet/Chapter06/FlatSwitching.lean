/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.RestrictionSquareIdentity
public import CryptBoolean.Carlet.Chapter02.WalshDivisibility
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
public import CryptBoolean.Carlet.Chapter04.KthNonhomomorphicity
public import CryptBoolean.Carlet.Chapter04.OtherComplexity
public import CryptBoolean.Carlet.Chapter05.FlatIndicators
public import CryptBoolean.Carlet.Chapter05.RestrictionNonlinearity
public import CryptBoolean.Carlet.Chapter06.Bentness
public import CryptBoolean.Carlet.Chapter06.DegreeBounds
public import CryptBoolean.Carlet.Chapter06.DualIsometry
public import CryptBoolean.Carlet.Chapter06.DualPoisson
public import CryptBoolean.Carlet.Chapter06.WalshCongruence

/-!
# Switching a bent function on an affine flat

Carlet Chapter 6, Theorem 9.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

noncomputable local instance flatSwitchingSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

noncomputable local instance flatSwitchingMembershipDecidable
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    DecidablePred (fun x ↦ x ∈ S) :=
  Classical.decPred _

/-- The Boolean function obtained by complementing `f` on the affine flat
`b + E`. -/
noncomputable def flatSwitch
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) : BooleanFunction n :=
  f + affineFlatIndicator E b

/-- Balancedness of the restriction of a Boolean function to an affine flat,
expressed without choosing coordinates on its direction subspace. -/
def IsBalancedOnAffineFlat
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) : Prop :=
  affineSubspaceRestrictionImbalance f E b = 0

/-- A Boolean function is constant or balanced on an affine flat exactly
when its signed restriction sum is extremal or zero. -/
def IsConstantOrBalancedOnAffineFlat
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) : Prop :=
  IsBalancedOnAffineFlat f E b ∨
    |affineSubspaceRestrictionImbalance f E b| = Nat.card E

/-- The signed Walsh sum of `f` over the affine flat `b + E`. -/
noncomputable def affineFlatWalshSum
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a : FABL.F₂Cube n) : ℤ :=
  ∑ x : E, walshTerm f a (x.1 + b)

private noncomputable def affineFlatSubtypeEquiv
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) :
    E ≃ {x : FABL.F₂Cube n // x ∈ FABL.binaryAffineSubspace E b} where
  toFun x := ⟨x.1 + b, by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem, add_assoc,
      ZModModule.add_self, add_zero]
    exact x.2⟩
  invFun x := ⟨x.1 + b,
    (FABL.mem_binaryAffineSubspace_iff_add_mem E b x.1).1 x.2⟩
  left_inv x := by
    ext i
    simp [add_assoc, ZModModule.add_self]
  right_inv x := by
    ext i
    simp [add_assoc, ZModModule.add_self]

private theorem sum_mul_setIndicator_affineFlat
    (φ : FABL.F₂Cube n → ℝ)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) :
    (∑ x, φ x * FABL.setIndicator
      (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) =
      ∑ x : E, φ (x.1 + b) := by
  classical
  calc
    (∑ x, φ x * FABL.setIndicator
        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) =
        ∑ x ∈ (Finset.univ.filter fun x : FABL.F₂Cube n ↦
          x ∈ FABL.binaryAffineSubspace E b), φ x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxb : x ∈ FABL.binaryAffineSubspace E b <;>
        simp [FABL.setIndicator, hxb]
    _ = ∑ x : {x : FABL.F₂Cube n //
          x ∈ FABL.binaryAffineSubspace E b}, φ x.1 := by
      simpa using
        (Finset.sum_subtype
          (p := fun x : FABL.F₂Cube n ↦
            x ∈ FABL.binaryAffineSubspace E b)
          (Finset.univ.filter fun x : FABL.F₂Cube n ↦
            x ∈ FABL.binaryAffineSubspace E b)
          (by simp) φ)
    _ = ∑ x : E, φ (x.1 + b) := by
      simpa [affineFlatSubtypeEquiv] using
        (Equiv.sum_comp (affineFlatSubtypeEquiv E b)
          (fun x : {x : FABL.F₂Cube n //
            x ∈ FABL.binaryAffineSubspace E b} ↦ φ x.1)).symm

private theorem setIndicator_affineFlat_mul_translate_eq_zero
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a x : FABL.F₂Cube n) (ha : a ∉ E) :
    FABL.setIndicator
        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x *
      FABL.setIndicator
        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) (x + a) = 0 := by
  classical
  by_cases hx : x ∈ FABL.binaryAffineSubspace E b
  · have hxa : x + a ∉ FABL.binaryAffineSubspace E b := by
      intro hxa
      have hxE := (FABL.mem_binaryAffineSubspace_iff_add_mem E b x).1 hx
      have hxaE :=
        (FABL.mem_binaryAffineSubspace_iff_add_mem E b (x + a)).1 hxa
      apply ha
      have hsum := E.add_mem hxE hxaE
      have heq : (x + b) + (x + a + b) = a := by
        calc
          (x + b) + (x + a + b) = (x + x) + (b + b) + a := by abel
          _ = a := by
            rw [ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]
      simpa only [heq] using hsum
    simp [FABL.setIndicator, hx, hxa]
  · simp [FABL.setIndicator, hx]

private theorem sum_derivativeSign_mul_setIndicator_translate
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a : FABL.F₂Cube n) :
    (∑ x, realSignView (FABL.booleanDerivative f a) x *
      FABL.setIndicator
        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) (x + a)) =
      affineSubspaceRestrictionImbalance
        (FABL.booleanDerivative f a) E b := by
  classical
  calc
    (∑ x, realSignView (FABL.booleanDerivative f a) x *
        FABL.setIndicator
          (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) (x + a)) =
        ∑ x, realSignView (FABL.booleanDerivative f a) (x + a) *
          FABL.setIndicator
            (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x := by
      simpa [add_assoc, ZModModule.add_self] using
        (Equiv.sum_comp (Equiv.addRight a)
          (fun x : FABL.F₂Cube n ↦
            realSignView (FABL.booleanDerivative f a) x *
              FABL.setIndicator
                (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                (x + a))).symm
    _ = ∑ x, realSignView (FABL.booleanDerivative f a) x *
          FABL.setIndicator
            (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [realSignView_booleanDerivative,
        realSignView_booleanDerivative]
      simp only [add_assoc, ZModModule.add_self, add_zero]
      ring
    _ = affineSubspaceRestrictionImbalance
          (FABL.booleanDerivative f a) E b := by
      rw [sum_mul_setIndicator_affineFlat]
      rfl

/-- Complementing on an affine flat changes a Walsh coefficient by twice
the signed Walsh sum over that flat. -/
theorem walshTransform_sub_flatSwitch
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a : FABL.F₂Cube n) :
    walshTransform f a - walshTransform (flatSwitch f E b) a =
      2 * affineFlatWalshSum f E b a := by
  classical
  rw [walshTransform, walshTransform, ← Finset.sum_sub_distrib]
  calc
    (∑ x, (walshTerm f a x - walshTerm (flatSwitch f E b) a x)) =
        ∑ x ∈ (Finset.univ.filter fun x : FABL.F₂Cube n ↦
          x ∈ FABL.binaryAffineSubspace E b), 2 * walshTerm f a x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxb : x ∈ FABL.binaryAffineSubspace E b
      · simp only [if_pos hxb, flatSwitch, Pi.add_apply,
          affineFlatIndicator, walshTerm]
        have hflip :
            bitSignInt ((f x + FABL.f₂DotProduct a x) + 1) =
              -bitSignInt (f x + FABL.f₂DotProduct a x) := by
          rw [bitSignInt_add]
          norm_num [bitSignInt]
        rw [show f x + 1 + FABL.f₂DotProduct a x =
          (f x + FABL.f₂DotProduct a x) + 1 by abel,
          hflip]
        ring
      · simp only [if_neg hxb, flatSwitch, Pi.add_apply,
          affineFlatIndicator, walshTerm, add_zero, sub_self]
    _ = ∑ x : {x : FABL.F₂Cube n //
          x ∈ FABL.binaryAffineSubspace E b}, 2 * walshTerm f a x.1 := by
      simpa using
        (Finset.sum_subtype
          (p := fun x : FABL.F₂Cube n ↦
            x ∈ FABL.binaryAffineSubspace E b)
          (Finset.univ.filter fun x : FABL.F₂Cube n ↦
            x ∈ FABL.binaryAffineSubspace E b)
          (by simp) (fun x ↦ 2 * walshTerm f a x))
    _ = ∑ x : E, 2 * walshTerm f a (x.1 + b) := by
      simpa [affineFlatSubtypeEquiv] using
        (Equiv.sum_comp (affineFlatSubtypeEquiv E b)
          (fun x : {x : FABL.F₂Cube n //
            x ∈ FABL.binaryAffineSubspace E b} ↦
              2 * walshTerm f a x.1)).symm
    _ = 2 * affineFlatWalshSum f E b a := by
      rw [affineFlatWalshSum, Finset.mul_sum]

/-- In coordinates on `E`, the signed Walsh sum on `b + E` is the local
Walsh coefficient, up to the sign contributed by the translate. -/
theorem affineFlatWalshSum_eq_bitSignInt_mul_walshTransform_restriction
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube k)
    (ha : ∀ y : FABL.F₂Cube k,
      FABL.f₂DotProduct a (e y).1 = FABL.f₂DotProduct c y) :
    affineFlatWalshSum f E b a =
      bitSignInt (FABL.f₂DotProduct a b) *
        walshTransform (coordinateAffineSubspaceRestriction f E b e) c := by
  classical
  rw [affineFlatWalshSum,
    ← Fintype.sum_equiv e.toEquiv
      (fun y : FABL.F₂Cube k ↦ walshTerm f a ((e y).1 + b))
      (fun x : E ↦ walshTerm f a (x.1 + b))
      (fun _ ↦ rfl), walshTransform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [walshTerm, walshTerm, coordinateAffineSubspaceRestriction_apply]
  change
    bitSignInt (f ((e y).1 + b) +
      (a ⬝ᵥ ((e y).1 + b))) =
      bitSignInt (a ⬝ᵥ b) *
        bitSignInt (f ((e y).1 + b) + c ⬝ᵥ y)
  rw [dotProduct_add]
  change
    bitSignInt (f ((e y).1 + b) +
      ((a ⬝ᵥ (e y).1) + a ⬝ᵥ b)) =
      bitSignInt (a ⬝ᵥ b) *
        bitSignInt (f ((e y).1 + b) + c ⬝ᵥ y)
  rw [show a ⬝ᵥ (e y).1 = c ⬝ᵥ y from ha y]
  simp_rw [bitSignInt_add]
  ring

/-- Poisson summation identifies the imbalance of the dual-plus-linear
restriction on `a + Eᵖ` with the signed Walsh sum of `f` on `b + E`. -/
theorem affineSubspaceRestrictionImbalance_bentDual_add_linear
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a b : FABL.F₂Cube n) :
    affineSubspaceRestrictionImbalance
        (bentDual f + FABL.affineFunction 0 b)
        (FABL.perpendicularSubspace E) a =
      ((2 : ℝ) ^ (n / 2))⁻¹ *
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        FABL.vectorWalshCharacter b a *
          (affineFlatWalshSum f E b a : ℝ) := by
  classical
  have hpoisson := bentDual_poissonSummationFormula f hf
    (FABL.perpendicularSubspace E) a b
  rw [FABL.perpendicularSubspace_perpendicularSubspace] at hpoisson
  calc
    affineSubspaceRestrictionImbalance
        (bentDual f + FABL.affineFunction 0 b)
        (FABL.perpendicularSubspace E) a =
        ∑ u : FABL.perpendicularSubspace E,
          realSignView (bentDual f) (a + u.1) *
            FABL.vectorWalshCharacter b (a + u.1) := by
      unfold affineSubspaceRestrictionImbalance
      apply Finset.sum_congr rfl
      intro u _hu
      rw [FABL.affineSubspaceRestriction_apply, add_comm u.1 a,
        realSignView_add, realSignView_affineFunction]
      simp
    _ = ((2 : ℝ) ^ (n / 2))⁻¹ *
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        FABL.vectorWalshCharacter b a *
          ∑ x : E, realSignView f (b + x.1) *
            FABL.vectorWalshCharacter a (b + x.1) := hpoisson
    _ = ((2 : ℝ) ^ (n / 2))⁻¹ *
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
        FABL.vectorWalshCharacter b a *
          (affineFlatWalshSum f E b a : ℝ) := by
      congr 1
      rw [affineFlatWalshSum, Int.cast_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [walshTerm_cast_eq_realSignView_mul_character, add_comm x.1 b]

/-- Absolute-value form of the dual Poisson identity used in Carlet
Theorem 9, Condition 2. -/
theorem abs_affineSubspaceRestrictionImbalance_bentDual_add_linear
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a b : FABL.F₂Cube n) :
    |affineSubspaceRestrictionImbalance
        (bentDual f + FABL.affineFunction 0 b)
        (FABL.perpendicularSubspace E) a| =
      ((2 : ℝ) ^ (n / 2))⁻¹ *
        (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
          |(affineFlatWalshSum f E b a : ℝ)| := by
  have hcard :
      0 ≤ (Nat.card (FABL.perpendicularSubspace E) : ℝ) := by positivity
  rw [affineSubspaceRestrictionImbalance_bentDual_add_linear f hf E a b]
  rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_pow,
    abs_of_nonneg hcard, FABL.abs_vectorWalshCharacter]
  norm_num

private theorem flatWalshSum_eq_zero_or_abs_eq_two_pow_half
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n)
    (hswitch : IsBent (flatSwitch f E b))
    (a : FABL.F₂Cube n) :
    affineFlatWalshSum f E b a = 0 ∨
      |(affineFlatWalshSum f E b a : ℝ)| = (2 : ℝ) ^ (n / 2) := by
  have hdifference := walshTransform_sub_flatSwitch f E b a
  rw [walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      (flatSwitch f E b) hswitch a] at hdifference
  rw [bitSignInt_eq_if_one, bitSignInt_eq_if_one] at hdifference
  by_cases hs : bentDual f a = 1
  · by_cases ht : bentDual (flatSwitch f E b) a = 1
    · left
      simp only [if_pos hs, if_pos ht] at hdifference
      nlinarith
    · right
      simp only [if_pos hs, if_neg ht] at hdifference
      have hsum : affineFlatWalshSum f E b a = -((2 : ℤ) ^ (n / 2)) := by
        nlinarith
      rw [hsum]
      norm_num
  · by_cases ht : bentDual (flatSwitch f E b) a = 1
    · right
      simp only [if_neg hs, if_pos ht] at hdifference
      have hsum : affineFlatWalshSum f E b a = (2 : ℤ) ^ (n / 2) := by
        nlinarith
      rw [hsum]
      norm_num
    · left
      simp only [if_neg hs, if_neg ht] at hdifference
      nlinarith

/-- The autocorrelation change under affine-flat switching. In directions
outside `E`, the correction is four times the imbalance of the restricted
derivative. -/
theorem autocorrelation_flatSwitch
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b a : FABL.F₂Cube n) :
    autocorrelation (flatSwitch f E b) a =
      if a ∈ E then autocorrelation f a
      else autocorrelation f a -
        4 * affineSubspaceRestrictionImbalance
          (FABL.booleanDerivative f a) E b := by
  classical
  by_cases ha : a ∈ E
  · rw [if_pos ha, autocorrelation, autocorrelation]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [flatSwitch, booleanDerivative_add, realSignView_add]
    have hindicator :
        FABL.booleanDerivative (affineFlatIndicator E b) a x = 0 := by
      rw [FABL.booleanDerivative]
      have hmem :
          x ∈ FABL.binaryAffineSubspace E b ↔
            x + a ∈ FABL.binaryAffineSubspace E b := by
        rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
          FABL.mem_binaryAffineSubspace_iff_add_mem]
        constructor
        · intro hxE
          simpa [add_assoc, add_comm a b] using E.add_mem hxE ha
        · intro hxaE
          have := E.add_mem hxaE ha
          simpa [add_assoc, add_comm a b, ZModModule.add_self] using this
      by_cases hx : x ∈ FABL.binaryAffineSubspace E b
      · have hxa := hmem.mp hx
        simp [affineFlatIndicator, hx, hxa]
      · have hxa : x + a ∉ FABL.binaryAffineSubspace E b :=
          fun h ↦ hx (hmem.mpr h)
        simp [affineFlatIndicator, hx, hxa]
    have hsign :
        realSignView (FABL.booleanDerivative (affineFlatIndicator E b) a) x =
          1 := by
      simp only [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, hindicator]
      norm_num
    rw [hsign, mul_one]
  · rw [if_neg ha, autocorrelation, autocorrelation]
    have hfirst :
        (∑ x, realSignView (FABL.booleanDerivative f a) x *
          FABL.setIndicator
            (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) =
          affineSubspaceRestrictionImbalance
            (FABL.booleanDerivative f a) E b :=
      sum_mul_setIndicator_affineFlat
        (realSignView (FABL.booleanDerivative f a)) E b
    have hsecond := sum_derivativeSign_mul_setIndicator_translate f E b a
    calc
      (∑ x, realSignView
          (FABL.booleanDerivative (flatSwitch f E b) a) x) =
          ∑ x, realSignView (FABL.booleanDerivative f a) x *
            ((1 - 2 * FABL.setIndicator
                (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) *
              (1 - 2 * FABL.setIndicator
                (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                  (x + a))) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [flatSwitch, booleanDerivative_add, realSignView_add,
          realSignView_booleanDerivative f a x,
          realSignView_booleanDerivative (affineFlatIndicator E b) a x,
          realSignView_affineFlatIndicator,
          realSignView_affineFlatIndicator]
      _ = (∑ x, realSignView (FABL.booleanDerivative f a) x) -
          2 * (∑ x, realSignView (FABL.booleanDerivative f a) x *
            FABL.setIndicator
              (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) -
          2 * (∑ x, realSignView (FABL.booleanDerivative f a) x *
            FABL.setIndicator
              (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                (x + a)) := by
        calc
          (∑ x, realSignView (FABL.booleanDerivative f a) x *
              ((1 - 2 * FABL.setIndicator
                  (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) *
                (1 - 2 * FABL.setIndicator
                  (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                    (x + a)))) =
              ∑ x, (realSignView (FABL.booleanDerivative f a) x -
                2 * (realSignView (FABL.booleanDerivative f a) x *
                  FABL.setIndicator
                    (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) -
                2 * (realSignView (FABL.booleanDerivative f a) x *
                  FABL.setIndicator
                    (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                      (x + a))) := by
            apply Finset.sum_congr rfl
            intro x _hx
            have hzero :=
              setIndicator_affineFlat_mul_translate_eq_zero E b a x ha
            calc
              realSignView (FABL.booleanDerivative f a) x *
                    ((1 - 2 * FABL.setIndicator
                        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) *
                      (1 - 2 * FABL.setIndicator
                        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                          (x + a))) =
                  (realSignView (FABL.booleanDerivative f a) x -
                    2 * (realSignView (FABL.booleanDerivative f a) x *
                      FABL.setIndicator
                        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x) -
                    2 * (realSignView (FABL.booleanDerivative f a) x *
                      FABL.setIndicator
                        (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                          (x + a))) +
                    4 * realSignView (FABL.booleanDerivative f a) x *
                      (FABL.setIndicator
                          (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n)) x *
                        FABL.setIndicator
                          (FABL.binaryAffineSubspace E b : Set (FABL.F₂Cube n))
                            (x + a)) := by ring
              _ = _ := by rw [hzero]; ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ x, realSignView (FABL.booleanDerivative f a) x) -
          4 * affineSubspaceRestrictionImbalance
            (FABL.booleanDerivative f a) E b := by
        rw [hfirst, hsecond]
        ring

/-- Carlet Theorem 9, Condition 1: switching a bent function on `b + E`
is bent exactly when every derivative in a direction outside `E` is balanced
on that flat. -/
theorem isBent_flatSwitch_iff_derivative_balanced_on_affineFlat
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) :
    IsBent (flatSwitch f E b) ↔
      ∀ a : FABL.F₂Cube n, a ∉ E →
        IsBalancedOnAffineFlat (FABL.booleanDerivative f a) E b := by
  constructor
  · intro hswitch a ha
    have haNe : a ≠ 0 := by
      intro haZero
      apply ha
      subst a
      exact E.zero_mem
    have hfAuto : autocorrelation f a = 0 :=
      (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).1
        ((isBent_iff_forall_nonzero_derivative_isBalanced f).1 hf a haNe)
    have hswitchAuto : autocorrelation (flatSwitch f E b) a = 0 :=
      (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
        (flatSwitch f E b) a).1
        ((isBent_iff_forall_nonzero_derivative_isBalanced
          (flatSwitch f E b)).1 hswitch a haNe)
    rw [autocorrelation_flatSwitch, if_neg ha, hfAuto] at hswitchAuto
    change affineSubspaceRestrictionImbalance
      (FABL.booleanDerivative f a) E b = 0
    linarith
  · intro hcondition
    apply (isBent_iff_forall_nonzero_derivative_isBalanced
      (flatSwitch f E b)).2
    intro a haNe
    apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
      (flatSwitch f E b) a).2
    have hfAuto : autocorrelation f a = 0 :=
      (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).1
        ((isBent_iff_forall_nonzero_derivative_isBalanced f).1 hf a haNe)
    by_cases ha : a ∈ E
    · rw [autocorrelation_flatSwitch, if_pos ha, hfAuto]
    · have hflat := hcondition a ha
      change affineSubspaceRestrictionImbalance
        (FABL.booleanDerivative f a) E b = 0 at hflat
      rw [autocorrelation_flatSwitch, if_neg ha, hfAuto, hflat]
      norm_num

/-- Carlet Theorem 9, Condition 2: switching a bent function on `b + E`
is bent exactly when `bentDual f + b · x` is constant or balanced on every
coset of `Eᵖ`. -/
theorem isBent_flatSwitch_iff_bentDual_add_linear_constant_or_balanced
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) :
    IsBent (flatSwitch f E b) ↔
      ∀ a : FABL.F₂Cube n,
        IsConstantOrBalancedOnAffineFlat
          (bentDual f + FABL.affineFunction 0 b)
          (FABL.perpendicularSubspace E) a := by
  constructor
  · intro hswitch a
    rw [IsConstantOrBalancedOnAffineFlat]
    rcases flatWalshSum_eq_zero_or_abs_eq_two_pow_half
      f hf E b hswitch a with hzero | habs
    · left
      rw [IsBalancedOnAffineFlat,
        affineSubspaceRestrictionImbalance_bentDual_add_linear
          f hf E a b, hzero]
      norm_num
    · right
      rw [abs_affineSubspaceRestrictionImbalance_bentDual_add_linear
        f hf E a b, habs]
      have hp : (2 : ℝ) ^ (n / 2) ≠ 0 := by positivity
      calc
        ((2 : ℝ) ^ (n / 2))⁻¹ *
              (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
                (2 : ℝ) ^ (n / 2) =
            (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
              (((2 : ℝ) ^ (n / 2))⁻¹ * (2 : ℝ) ^ (n / 2)) := by ring
        _ = Nat.card (FABL.perpendicularSubspace E) := by
          rw [inv_mul_cancel₀ hp, mul_one]
  · intro hcondition
    have hnEven := even_of_isBent f hf
    by_cases hnTwo : 2 ≤ n
    · apply (isBent_iff_forall_walshTransform_modeq
        (flatSwitch f E b) hnEven hnTwo).2
      intro a
      have hflat : affineFlatWalshSum f E b a = 0 ∨
          |(affineFlatWalshSum f E b a : ℝ)| = (2 : ℝ) ^ (n / 2) := by
        rcases hcondition a with hbalanced | hextremal
        · left
          rw [IsBalancedOnAffineFlat] at hbalanced
          have hrelation :=
            affineSubspaceRestrictionImbalance_bentDual_add_linear
              f hf E a b
          rw [hbalanced] at hrelation
          have hpInv : ((2 : ℝ) ^ (n / 2))⁻¹ ≠ 0 := by positivity
          have hcard :
              (Nat.card (FABL.perpendicularSubspace E) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.card_pos.ne' :
              Nat.card (FABL.perpendicularSubspace E) ≠ 0)
          have hcharacter : FABL.vectorWalshCharacter b a ≠ 0 := by
            intro hzero
            have habs := FABL.abs_vectorWalshCharacter b a
            rw [hzero, abs_zero] at habs
            norm_num at habs
          have hcoefficient :
              ((2 : ℝ) ^ (n / 2))⁻¹ *
                  (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
                    FABL.vectorWalshCharacter b a ≠ 0 :=
            mul_ne_zero (mul_ne_zero hpInv hcard) hcharacter
          have hcast : (affineFlatWalshSum f E b a : ℝ) = 0 :=
            (mul_eq_zero.mp hrelation.symm).resolve_left hcoefficient
          exact_mod_cast hcast
        · right
          have habsRelation :=
            abs_affineSubspaceRestrictionImbalance_bentDual_add_linear
              f hf E a b
          rw [hextremal] at habsRelation
          have hp : (2 : ℝ) ^ (n / 2) ≠ 0 := by positivity
          have hcard :
              (Nat.card (FABL.perpendicularSubspace E) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.card_pos.ne' :
              Nat.card (FABL.perpendicularSubspace E) ≠ 0)
          have hcancel :
              1 = ((2 : ℝ) ^ (n / 2))⁻¹ *
                |(affineFlatWalshSum f E b a : ℝ)| := by
            apply mul_left_cancel₀ hcard
            calc
              (Nat.card (FABL.perpendicularSubspace E) : ℝ) * 1 =
                  Nat.card (FABL.perpendicularSubspace E) := by ring
              _ = ((2 : ℝ) ^ (n / 2))⁻¹ *
                    (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
                      |(affineFlatWalshSum f E b a : ℝ)| := habsRelation
              _ = (Nat.card (FABL.perpendicularSubspace E) : ℝ) *
                    (((2 : ℝ) ^ (n / 2))⁻¹ *
                      |(affineFlatWalshSum f E b a : ℝ)|) := by ring
          calc
            |(affineFlatWalshSum f E b a : ℝ)| =
                (2 : ℝ) ^ (n / 2) *
                  (((2 : ℝ) ^ (n / 2))⁻¹ *
                    |(affineFlatWalshSum f E b a : ℝ)|) := by
              rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
            _ = (2 : ℝ) ^ (n / 2) * 1 := by rw [← hcancel]
            _ = (2 : ℝ) ^ (n / 2) := by ring
      have hdifference := walshTransform_sub_flatSwitch f E b a
      have hdiv : (2 : ℤ) ^ (n / 2 + 1) ∣
          walshTransform f a - walshTransform (flatSwitch f E b) a := by
        rcases hflat with hzero | habs
        · rw [hdifference, hzero]
          exact dvd_zero _
        · rcases eq_or_eq_neg_of_abs_eq habs with hpositive | hnegative
          · have hpositiveInt :
                affineFlatWalshSum f E b a = (2 : ℤ) ^ (n / 2) := by
              exact_mod_cast hpositive
            refine ⟨1, ?_⟩
            rw [hdifference, hpositiveInt, pow_succ, mul_one]
            ring
          · have hnegativeInt :
                affineFlatWalshSum f E b a = -((2 : ℤ) ^ (n / 2)) := by
              exact_mod_cast hnegative
            refine ⟨-1, ?_⟩
            rw [hdifference, hnegativeInt, pow_succ]
            ring
      have hswitchMod :
          Int.ModEq (2 ^ (n / 2 + 1))
            (walshTransform (flatSwitch f E b) a) (walshTransform f a) :=
        Int.modEq_iff_dvd.mpr hdiv
      exact hswitchMod.trans
        (((isBent_iff_forall_walshTransform_modeq f hnEven hnTwo).1 hf) a)
    · apply (isBent_flatSwitch_iff_derivative_balanced_on_affineFlat
        f hf E b).2
      intro a ha
      exfalso
      apply ha
      have hnZero : n = 0 := by
        rcases hnEven with ⟨m, hm⟩
        omega
      subst n
      have haZero : a = 0 := Subsingleton.elim _ _
      simpa [haZero] using E.zero_mem

/-- The two criteria in Carlet Theorem 9 are equivalent. -/
theorem derivative_balanced_on_affineFlat_iff_bentDual_add_linear_constant_or_balanced
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n) :
    (∀ a : FABL.F₂Cube n, a ∉ E →
        IsBalancedOnAffineFlat (FABL.booleanDerivative f a) E b) ↔
      ∀ a : FABL.F₂Cube n,
        IsConstantOrBalancedOnAffineFlat
          (bentDual f + FABL.affineFunction 0 b)
          (FABL.perpendicularSubspace E) a :=
  (isBent_flatSwitch_iff_derivative_balanced_on_affineFlat f hf E b).symm.trans
    (isBent_flatSwitch_iff_bentDual_add_linear_constant_or_balanced f hf E b)

private theorem bitSignInt_mul_self_flatSwitching (z : FABL.𝔽₂) :
    bitSignInt z * bitSignInt z = 1 := by
  fin_cases z <;> rfl

private theorem exists_bitSignInt_sub_eq_two_mul
    (s t : FABL.𝔽₂) :
    ∃ z : ℤ, bitSignInt s - bitSignInt t = 2 * z := by
  fin_cases s <;> fin_cases t <;>
    first | exact ⟨0, by rfl⟩ | exact ⟨1, by rfl⟩ | exact ⟨-1, by rfl⟩

/-- If both the original function and its affine-flat switch are bent, every
Walsh coefficient of the restriction to the switched flat is divisible by
`2^(n/2)`. -/
theorem two_pow_half_dvd_walshTransform_affineFlatRestriction
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n)
    (hswitch : IsBent (flatSwitch f E b))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (c : FABL.F₂Cube k) :
    (2 : ℤ) ^ (n / 2) ∣
      walshTransform (coordinateAffineSubspaceRestriction f E b e) c := by
  obtain ⟨a, ha⟩ := exists_ambientFrequency_restricts_to_subspace E e c
  have hdifference := walshTransform_sub_flatSwitch f E b a
  rw [affineFlatWalshSum_eq_bitSignInt_mul_walshTransform_restriction
    f E b a e c ha,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      (flatSwitch f E b) hswitch a] at hdifference
  obtain ⟨z, hz⟩ := exists_bitSignInt_sub_eq_two_mul
    (bentDual f a) (bentDual (flatSwitch f E b) a)
  have hcancel :
      (2 : ℤ) ^ (n / 2) * z =
        bitSignInt (FABL.f₂DotProduct a b) *
          walshTransform (coordinateAffineSubspaceRestriction f E b e) c := by
    rw [← mul_sub, hz] at hdifference
    nlinarith
  refine ⟨bitSignInt (FABL.f₂DotProduct a b) * z, ?_⟩
  calc
    walshTransform (coordinateAffineSubspaceRestriction f E b e) c =
        (bitSignInt (FABL.f₂DotProduct a b) *
          bitSignInt (FABL.f₂DotProduct a b)) *
            walshTransform (coordinateAffineSubspaceRestriction f E b e) c := by
      rw [bitSignInt_mul_self_flatSwitching, one_mul]
    _ = bitSignInt (FABL.f₂DotProduct a b) *
          (bitSignInt (FABL.f₂DotProduct a b) *
            walshTransform (coordinateAffineSubspaceRestriction f E b e) c) := by
      ring
    _ = bitSignInt (FABL.f₂DotProduct a b) *
          ((2 : ℤ) ^ (n / 2) * z) := by rw [← hcancel]
    _ = (2 : ℤ) ^ (n / 2) *
          (bitSignInt (FABL.f₂DotProduct a b) * z) := by ring

/-- Carlet Theorem 9: if a bent function remains bent after switching on
`b + E`, then `E` has dimension at least `n/2`. -/
theorem half_dimension_le_finrank_of_isBent_flatSwitch
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n)
    (hswitch : IsBent (flatSwitch f E b)) :
    n / 2 ≤ Module.finrank FABL.𝔽₂ E := by
  let e : FABL.F₂Cube (Module.finrank FABL.𝔽₂ E) ≃ₗ[FABL.𝔽₂] E :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp)
  let h := coordinateAffineSubspaceRestriction f E b e
  obtain ⟨c, hc⟩ := exists_walshTransform_ne_zero h
  have hdiv : (2 : ℤ) ^ (n / 2) ∣ walshTransform h c := by
    exact two_pow_half_dvd_walshTransform_affineFlatRestriction
      f hf E b hswitch e c
  obtain ⟨z, hz⟩ := hdiv
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply hc
    rw [hz, hzZero, mul_zero]
  have hzAbs : 1 ≤ z.natAbs := by
    exact Int.natAbs_pos.mpr hzNe
  have hlower :
      2 ^ (n / 2) ≤ (walshTransform h c).natAbs := by
    rw [hz, Int.natAbs_mul]
    norm_num
    exact hzAbs
  have hboundReal := abs_walshTransform_le_two_pow h c
  have hbound :
      (walshTransform h c).natAbs ≤
        2 ^ Module.finrank FABL.𝔽₂ E := by
    have hcast :
        ((walshTransform h c).natAbs : ℝ) ≤
          (2 ^ Module.finrank FABL.𝔽₂ E : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
        Nat.cast_ofNat] using hboundReal
    exact_mod_cast hcast
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < (2 : ℕ))).mp
    (hlower.trans hbound)

/-- Carlet Theorem 9: when the switch is bent, the algebraic degree of the
restriction to `b + E` is at most `dim(E) - n/2 + 1`. -/
theorem functionAlgebraicDegree_affineFlatRestriction_le_of_isBent_flatSwitch
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n)
    (hswitch : IsBent (flatSwitch f E b))
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    FABL.functionAlgebraicDegree
        (coordinateAffineSubspaceRestriction f E b e) ≤
      k - n / 2 + 1 := by
  have hdim : Module.finrank FABL.𝔽₂ E = k := by
    have heq := LinearEquiv.finrank_eq e
    rw [Module.finrank_fintype_fun_eq_card] at heq
    simpa using heq.symm
  have hhalf : n / 2 ≤ k := by
    rw [← hdim]
    exact half_dimension_le_finrank_of_isBent_flatSwitch f hf E b hswitch
  by_cases hhalfZero : n / 2 = 0
  · exact (FABL.functionAlgebraicDegree_le_dimension
      (coordinateAffineSubspaceRestriction f E b e)).trans (by omega)
  have hhalfPos : 1 ≤ n / 2 := by omega
  by_cases hkTwo : 2 ≤ k
  · exact functionAlgebraicDegree_le_of_two_pow_dvd_walshTransform
      (coordinateAffineSubspaceRestriction f E b e) (n / 2)
      hkTwo hhalfPos hhalf
      (two_pow_half_dvd_walshTransform_affineFlatRestriction
        f hf E b hswitch e)
  · exact (FABL.functionAlgebraicDegree_le_dimension
      (coordinateAffineSubspaceRestriction f E b e)).trans (by omega)

/-- Carlet Theorem 9, converse: if `E` has dimension `n/2` and the
restriction of a bent function to `b + E` is affine, switching on that flat
is bent. -/
theorem isBent_flatSwitch_of_half_dimension_of_restriction_degree_le_one
    (f : BooleanFunction n) (hf : IsBent f)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (b : FABL.F₂Cube n)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (hk : k = n / 2)
    (hdegree : FABL.functionAlgebraicDegree
      (coordinateAffineSubspaceRestriction f E b e) ≤ 1) :
    IsBent (flatSwitch f E b) := by
  have hnEven := even_of_isBent f hf
  by_cases hnTwo : 2 ≤ n
  · obtain ⟨d, u, hrestriction⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
        (coordinateAffineSubspaceRestriction f E b e) hdegree
    apply (isBent_iff_forall_walshTransform_modeq
      (flatSwitch f E b) hnEven hnTwo).2
    intro a
    let c := coordinateRestrictedAffineFrequency E e a
    have hfrequency : ∀ y : FABL.F₂Cube k,
        FABL.f₂DotProduct a (e y).1 = FABL.f₂DotProduct c y := by
      intro y
      exact (f₂DotProduct_coordinateRestrictedAffineFrequency E e a y).symm
    have hdifference := walshTransform_sub_flatSwitch f E b a
    rw [affineFlatWalshSum_eq_bitSignInt_mul_walshTransform_restriction
      f E b a e c hfrequency, hrestriction,
      walshTransform_affineFunction] at hdifference
    have hdiffDiv :
        (2 : ℤ) ^ (n / 2 + 1) ∣
          walshTransform f a - walshTransform (flatSwitch f E b) a := by
      by_cases hcu : c = u
      · rw [if_pos hcu, hk] at hdifference
        refine ⟨bitSignInt (FABL.f₂DotProduct a b) * bitSignInt d, ?_⟩
        calc
          walshTransform f a - walshTransform (flatSwitch f E b) a =
              2 * (bitSignInt (FABL.f₂DotProduct a b) *
                (bitSignInt d * (2 ^ (n / 2) : ℤ))) := by
            rw [hdifference]
          _ = (2 : ℤ) ^ (n / 2 + 1) *
              (bitSignInt (FABL.f₂DotProduct a b) * bitSignInt d) := by
            rw [pow_succ]
            ring
      · rw [if_neg hcu] at hdifference
        refine ⟨0, ?_⟩
        rw [mul_zero]
        linarith
    have hswitchMod :
        Int.ModEq (2 ^ (n / 2 + 1))
          (walshTransform (flatSwitch f E b) a) (walshTransform f a) :=
      Int.modEq_iff_dvd.mpr hdiffDiv
    exact hswitchMod.trans
      (((isBent_iff_forall_walshTransform_modeq f hnEven hnTwo).1 hf) a)
  · apply (isBent_flatSwitch_iff_derivative_balanced_on_affineFlat
      f hf E b).2
    intro a ha
    exfalso
    apply ha
    have hnZero : n = 0 := by
      rcases hnEven with ⟨m, hm⟩
      omega
    subst n
    have haZero : a = 0 := Subsingleton.elim _ _
    simpa [haZero] using E.zero_mem

end CryptBoolean
