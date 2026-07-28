/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.QuadraticPolar
public import CryptBoolean.Carlet.Chapter04.LinearStructures

/-!
# Carlet Chapter 5 quadratic Boolean functions

The symplectic polar form, its identification with the linear kernel, and
Carlet's quadratic kernel-sum identity.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance quadraticLinearKernelFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

/-- For a quadratic Boolean function, the radical of the polar form is its
linear kernel. -/
theorem quadraticRadical_eq_linearKernel
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    quadraticRadical f hdegree = linearKernel f := by
  ext a
  constructor
  · intro ha
    rw [mem_linearKernel]
    refine ⟨f a + f 0, ?_⟩
    intro x
    exact congrFun
      (booleanDerivative_eq_const_of_mem_quadraticRadical
        f hdegree a ha) x
  · intro ha
    obtain ⟨ε, hε⟩ := (mem_linearKernel f a).mp ha
    rw [mem_quadraticRadical_iff]
    intro b
    simp only [quadraticPolarKernel, hε b, hε 0,
      ZModModule.add_self]

/-- Carlet Relation (41), first in the real character form supplied by
autocorrelation orthogonality. -/
theorem walshTransform_zero_sq_eq_two_pow_mul_sum_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (walshTransform f 0 : ℝ) ^ 2 =
      (2 ^ n : ℝ) *
        ∑ a : quadraticRadical f hdegree,
          FABL.binarySign (FABL.booleanDerivative f a.1 0) := by
  rw [← sum_autocorrelation_eq_walshTransform_zero_sq,
    sum_autocorrelation_eq_card_mul_sum_quadraticRadicalSignCharacter
      f hdegree]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [quadraticRadicalSignCharacter, FABL.booleanDerivative,
    add_zero, add_comm]
  rfl

/-- Carlet Relation (41) with the source's integer raw Walsh transform and
linear kernel. -/
theorem walshTransform_zero_sq_eq_two_pow_mul_sum_linearKernel
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    walshTransform f 0 ^ 2 =
      (2 ^ n : ℤ) *
        ∑ a : linearKernel f,
          bitSignInt (FABL.booleanDerivative f a.1 0) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [← quadraticRadical_eq_linearKernel f hdegree]
  rw [walshTransform_zero_sq_eq_two_pow_mul_sum_quadraticRadical
    f hdegree]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact (bitSignInt_cast (FABL.booleanDerivative f a.1 0)).symm

/-- The quadratic radical sign character is trivial exactly when the
quadratic function is constant on its radical. -/
theorem quadraticRadicalSignCharacter_eq_zero_iff
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    quadraticRadicalSignCharacter f hdegree = 0 ↔
      ∀ a : quadraticRadical f hdegree, f a.1 = f 0 := by
  constructor
  · intro hcharacter a
    have hvalue := congrArg
      (fun ψ : AddChar (quadraticRadical f hdegree) ℝ ↦ ψ a)
      hcharacter
    change FABL.binarySign (f a.1 + f 0) = 1 at hvalue
    have hsumZero :=
      (FABL.binarySign_eq_one_iff (f a.1 + f 0)).mp hvalue
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hsumZero
    exact hsumZero
  · intro hconstant
    apply AddChar.ext
    intro a
    change FABL.binarySign (f a.1 + f 0) = 1
    apply (FABL.binarySign_eq_one_iff _).mpr
    rw [hconstant a, ZModModule.add_self]

/-- Relation (41) is the radical's cardinality term precisely when the
restriction is constant, and vanishes otherwise. -/
theorem walshTransform_zero_sq_eq_if_constant_on_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (walshTransform f 0 : ℝ) ^ 2 =
      if (∀ a : quadraticRadical f hdegree, f a.1 = f 0) then
        (2 ^ n : ℝ) * Fintype.card (quadraticRadical f hdegree)
      else 0 := by
  rw [← sum_autocorrelation_eq_walshTransform_zero_sq,
    sum_autocorrelation_eq_card_mul_sum_quadraticRadicalSignCharacter
      f hdegree]
  by_cases hconstant :
      ∀ a : quadraticRadical f hdegree, f a.1 = f 0
  · rw [if_pos hconstant, AddChar.sum_eq_ite,
      if_pos ((quadraticRadicalSignCharacter_eq_zero_iff
        f hdegree).mpr hconstant)]
  · have hcharacter : quadraticRadicalSignCharacter f hdegree ≠ 0 :=
      fun hzero ↦ hconstant
        ((quadraticRadicalSignCharacter_eq_zero_iff
          f hdegree).mp hzero)
    rw [if_neg hconstant, AddChar.sum_eq_ite,
      if_neg hcharacter, mul_zero]

/-- Relation (41)'s constant/nonconstant alternative on Carlet's linear
kernel. -/
theorem walshTransform_zero_sq_eq_if_constant_on_linearKernel
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (walshTransform f 0 : ℝ) ^ 2 =
      if (∀ a : linearKernel f, f a.1 = f 0) then
        (2 ^ n : ℝ) * Fintype.card (linearKernel f)
      else 0 := by
  rw [← quadraticRadical_eq_linearKernel f hdegree]
  exact walshTransform_zero_sq_eq_if_constant_on_quadraticRadical
    f hdegree

/-- A quadratic function is balanced exactly when its radical character is
nontrivial. -/
theorem isBalanced_iff_quadraticRadicalSignCharacter_ne_zero
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsBalanced f ↔ quadraticRadicalSignCharacter f hdegree ≠ 0 := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  have hcast :
      walshTransform f 0 = 0 ↔ (walshTransform f 0 : ℝ) ^ 2 = 0 := by
    rw [sq_eq_zero_iff, Int.cast_eq_zero]
  rw [hcast, ← sum_autocorrelation_eq_walshTransform_zero_sq,
    sum_autocorrelation_eq_card_mul_sum_quadraticRadicalSignCharacter
      f hdegree,
    mul_eq_zero]
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [or_iff_right hpow]
  exact AddChar.sum_eq_zero_iff_ne_zero
    (ψ := quadraticRadicalSignCharacter f hdegree)

/-- The balancedness part of Carlet Theorem 4: a quadratic function is
balanced exactly when its restriction to the linear kernel is nonconstant. -/
theorem isBalanced_iff_not_constant_on_linearKernel_of_degree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsBalanced f ↔ ¬ ∀ a : linearKernel f, f a.1 = f 0 := by
  rw [← quadraticRadical_eq_linearKernel f hdegree,
    isBalanced_iff_quadraticRadicalSignCharacter_ne_zero f hdegree]
  exact not_congr
    (quadraticRadicalSignCharacter_eq_zero_iff f hdegree)

/-- The radical character is nontrivial exactly when some directional
derivative is the constant-one function. -/
theorem quadraticRadicalSignCharacter_ne_zero_iff_exists_derivative_one
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    quadraticRadicalSignCharacter f hdegree ≠ 0 ↔
      ∃ a : FABL.F₂Cube n, FABL.booleanDerivative f a = 1 := by
  constructor
  · intro hcharacter
    by_contra hexists
    apply hcharacter
    apply AddChar.ext
    intro a
    change FABL.binarySign (f a.1 + f 0) = 1
    apply (FABL.binarySign_eq_one_iff _).mpr
    by_contra hvalue
    have hone : f a.1 + f 0 = 1 :=
      Fin.eq_one_of_ne_zero _ hvalue
    apply hexists
    refine ⟨a.1, ?_⟩
    rw [booleanDerivative_eq_const_of_mem_quadraticRadical
      f hdegree a.1 a.2, hone]
    rfl
  · rintro ⟨a, hderivative⟩ hcharacter
    have haLinear : a ∈ linearKernel f := by
      rw [mem_linearKernel]
      exact ⟨1, fun x ↦ congrFun hderivative x⟩
    have haRadical : a ∈ quadraticRadical f hdegree := by
      rw [quadraticRadical_eq_linearKernel f hdegree]
      exact haLinear
    have hvalue := congrArg
      (fun ψ : AddChar (quadraticRadical f hdegree) ℝ ↦
        ψ (⟨a, haRadical⟩ : quadraticRadical f hdegree))
      hcharacter
    change FABL.binarySign (f a + f 0) = 1 at hvalue
    have hconstant :=
      booleanDerivative_eq_const_of_mem_quadraticRadical
        f hdegree a haRadical
    rw [hderivative] at hconstant
    have hone : f a + f 0 = 1 := by
      simpa using (congrFun hconstant 0).symm
    rw [hone] at hvalue
    exact one_ne_zero
      ((FABL.binarySign_eq_one_iff (1 : FABL.𝔽₂)).mp hvalue)

/-- A quadratic Boolean function is balanced exactly when one of its
directional derivatives is the constant-one function. -/
theorem isBalanced_iff_exists_booleanDerivative_eq_one_of_degree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsBalanced f ↔
      ∃ a : FABL.F₂Cube n, FABL.booleanDerivative f a = 1 := by
  rw [isBalanced_iff_quadraticRadicalSignCharacter_ne_zero f hdegree,
    quadraticRadicalSignCharacter_ne_zero_iff_exists_derivative_one
      f hdegree]

/-- A constant-one derivative direction lies in the linear kernel and changes
the value of the quadratic function from its value at zero. -/
theorem mem_linearKernel_and_ne_zero_value_of_booleanDerivative_eq_one
    (f : BooleanFunction n) (a : FABL.F₂Cube n)
    (hderivative : FABL.booleanDerivative f a = 1) :
    a ∈ linearKernel f ∧ f a ≠ f 0 := by
  constructor
  · rw [mem_linearKernel]
    exact ⟨1, fun x ↦ congrFun hderivative x⟩
  · intro hvalue
    have hzero := congrFun hderivative 0
    simp only [FABL.booleanDerivative, zero_add] at hzero
    rw [hvalue, ZModModule.add_self] at hzero
    exact zero_ne_one hzero

/-- For odd arity, a quadratic semi-bent function has the extremal
nonlinearity displayed in Carlet Section 5.2. -/
def IsQuadraticSemiBent (f : BooleanFunction n) : Prop :=
  Odd n ∧ FABL.functionAlgebraicDegree f ≤ 2 ∧
    nonlinearity f = 2 ^ (n - 1) - 2 ^ ((n - 1) / 2)

end CryptBoolean
