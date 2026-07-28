/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
public import FABL.Chapter06.FoolingF₂Polynomials.DirectionalDerivatives
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Polar forms and radicals of quadratic Boolean functions

The bilinear alternating polar form, its radical, and the autocorrelation
decomposition shared by quadratic Boolean-function arguments.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance quadraticPolarSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

def quadraticPolarKernel
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) : FABL.𝔽₂ :=
  FABL.booleanDerivative f a b + FABL.booleanDerivative f a 0

theorem quadraticPolarKernel_eq
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) :
    quadraticPolarKernel f a b =
      f (a + b) + f a + f b + f 0 := by
  simp only [quadraticPolarKernel, FABL.booleanDerivative]
  abel_nf

theorem quadraticPolarKernel_comm
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) :
    quadraticPolarKernel f a b = quadraticPolarKernel f b a := by
  rw [quadraticPolarKernel_eq, quadraticPolarKernel_eq, add_comm a b]
  abel

theorem quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
    (f : BooleanFunction n) (a b : FABL.F₂Cube n)
    (d : FABL.𝔽₂) (u : FABL.F₂Cube n)
    (hderivative : FABL.booleanDerivative f a =
      FABL.affineFunction d u) :
    quadraticPolarKernel f a b = FABL.f₂DotProduct u b := by
  simp only [quadraticPolarKernel, hderivative, FABL.affineFunction,
    FABL.f₂DotProduct, dotProduct_zero]
  calc
    (d + dotProduct u b) + (d + 0) =
        (d + d) + dotProduct u b := by abel
    _ = dotProduct u b := by
      rw [ZModModule.add_self, zero_add]

theorem quadraticPolarKernel_add_right
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a b c : FABL.F₂Cube n) :
    quadraticPolarKernel f a (b + c) =
      quadraticPolarKernel f a b + quadraticPolarKernel f a c := by
  have hderivative : FABL.functionAlgebraicDegree
      (FABL.booleanDerivative f a) ≤ 1 := by
    exact (FABL.functionAlgebraicDegree_booleanDerivative_le f a).trans
      (by omega)
  obtain ⟨d, u, hu⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (FABL.booleanDerivative f a) hderivative
  rw [quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a (b + c) d u hu,
    quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a b d u hu,
    quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a c d u hu]
  exact dotProduct_add u b c

theorem quadraticPolarKernel_smul_right
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a b : FABL.F₂Cube n) (c : FABL.𝔽₂) :
    quadraticPolarKernel f a (c • b) =
      c • quadraticPolarKernel f a b := by
  have hderivative : FABL.functionAlgebraicDegree
      (FABL.booleanDerivative f a) ≤ 1 := by
    exact (FABL.functionAlgebraicDegree_booleanDerivative_le f a).trans
      (by omega)
  obtain ⟨d, u, hu⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (FABL.booleanDerivative f a) hderivative
  rw [quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a (c • b) d u hu,
    quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a b d u hu]
  simp only [FABL.f₂DotProduct, dotProduct_smul]

theorem quadraticPolarKernel_add_left
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a b c : FABL.F₂Cube n) :
    quadraticPolarKernel f (a + b) c =
      quadraticPolarKernel f a c + quadraticPolarKernel f b c := by
  rw [quadraticPolarKernel_comm f (a + b) c,
    quadraticPolarKernel_add_right f hdegree,
    quadraticPolarKernel_comm f c a,
    quadraticPolarKernel_comm f c b]

theorem quadraticPolarKernel_smul_left
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a b : FABL.F₂Cube n) (c : FABL.𝔽₂) :
    quadraticPolarKernel f (c • a) b =
      c • quadraticPolarKernel f a b := by
  rw [quadraticPolarKernel_comm f (c • a) b,
    quadraticPolarKernel_smul_right f hdegree,
    quadraticPolarKernel_comm f b a]

noncomputable def quadraticPolar
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    LinearMap.BilinForm FABL.𝔽₂ (FABL.F₂Cube n) :=
  LinearMap.mk₂ FABL.𝔽₂
    (quadraticPolarKernel f)
    (quadraticPolarKernel_add_left f hdegree)
    (fun c a b ↦ quadraticPolarKernel_smul_left f hdegree a b c)
    (quadraticPolarKernel_add_right f hdegree)
    (fun c a b ↦ quadraticPolarKernel_smul_right f hdegree a b c)

@[simp] theorem quadraticPolar_apply
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a b : FABL.F₂Cube n) :
    quadraticPolar f hdegree a b = quadraticPolarKernel f a b :=
  rfl

theorem quadraticPolar_isSymm
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (quadraticPolar f hdegree).IsSymm := by
  constructor
  exact quadraticPolarKernel_comm f

theorem quadraticPolar_isAlt
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    (quadraticPolar f hdegree).IsAlt := by
  intro a
  rw [quadraticPolar_apply]
  simp only [quadraticPolarKernel, FABL.booleanDerivative,
    ZModModule.add_self, zero_add]
  calc
    (f a + f 0) + (f 0 + f a) =
        (f a + f a) + (f 0 + f 0) := by abel
    _ = 0 := by
      rw [ZModModule.add_self, ZModModule.add_self, add_zero]

/-- The radical of the polar form of a quadratic Boolean function. -/
noncomputable def quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  LinearMap.ker (quadraticPolar f hdegree)

@[simp] theorem mem_quadraticRadical_iff
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n) :
    a ∈ quadraticRadical f hdegree ↔
      ∀ b, quadraticPolarKernel f a b = 0 := by
  rw [quadraticRadical, LinearMap.mem_ker]
  constructor
  · intro ha b
    exact DFunLike.congr_fun ha b
  · intro ha
    apply LinearMap.ext
    intro b
    exact ha b

theorem booleanDerivative_eq_const_of_mem_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n)
    (ha : a ∈ quadraticRadical f hdegree) :
    FABL.booleanDerivative f a = fun _ ↦ f a + f 0 := by
  funext b
  have hpolar := (mem_quadraticRadical_iff f hdegree a).mp ha b
  rw [quadraticPolarKernel_eq] at hpolar
  simp only [FABL.booleanDerivative]
  rw [add_comm b a]
  apply eq_of_sub_eq_zero
  rw [sub_eq_add_neg, ZModModule.neg_eq_self]
  calc
    f b + f (a + b) + (f a + f 0) =
        f (a + b) + f a + f b + f 0 := by abel
    _ = 0 := hpolar

theorem isBalanced_booleanDerivative_of_not_mem_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n)
    (ha : a ∉ quadraticRadical f hdegree) :
    IsBalanced (FABL.booleanDerivative f a) := by
  have hderivativeDegree : FABL.functionAlgebraicDegree
      (FABL.booleanDerivative f a) ≤ 1 := by
    exact (FABL.functionAlgebraicDegree_booleanDerivative_le f a).trans
      (by omega)
  obtain ⟨d, u, hu⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (FABL.booleanDerivative f a) hderivativeDegree
  rw [hu]
  apply isBalanced_affineFunction_of_ne_zero
  intro huZero
  apply ha
  rw [mem_quadraticRadical_iff]
  intro b
  rw [quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f a b d u hu, huZero]
  rw [FABL.f₂DotProduct, dotProduct_comm, dotProduct_zero]

theorem autocorrelation_eq_zero_of_not_mem_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n)
    (ha : a ∉ quadraticRadical f hdegree) :
    autocorrelation f a = 0 := by
  rw [autocorrelation_eq_walshTransform_booleanDerivative_zero]
  norm_cast
  exact (isBalanced_iff_walshTransform_zero_eq_zero
    (FABL.booleanDerivative f a)).mp
      (isBalanced_booleanDerivative_of_not_mem_quadraticRadical
        f hdegree a ha)

theorem autocorrelation_eq_card_mul_sign_of_mem_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n)
    (ha : a ∈ quadraticRadical f hdegree) :
    autocorrelation f a =
      (2 ^ n : ℝ) * FABL.binarySign (f a + f 0) := by
  rw [autocorrelation,
    booleanDerivative_eq_const_of_mem_quadraticRadical f hdegree a ha]
  simp only [realSignView, FABL.realSignEncodedFunction,
    FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_f₂Cube]
  norm_cast

/-- On the radical, the translated quadratic function is an additive
character after applying the binary sign. -/
noncomputable def quadraticRadicalSignCharacter
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    AddChar (quadraticRadical f hdegree) ℝ where
  toFun a := FABL.binarySign (f a.1 + f 0)
  map_zero_eq_one' := by
    rw [Submodule.coe_zero, ZModModule.add_self,
      AddChar.map_zero_eq_one]
  map_add_eq_mul' := by
    intro a b
    rw [Submodule.coe_add, ← AddChar.map_add_eq_mul FABL.binarySign]
    congr 1
    have hpolar :=
      (mem_quadraticRadical_iff f hdegree a.1).mp a.2 b.1
    rw [quadraticPolarKernel_eq] at hpolar
    apply eq_of_sub_eq_zero
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
    calc
      f (a.1 + b.1) + f 0 +
          ((f a.1 + f 0) + (f b.1 + f 0)) =
          (f (a.1 + b.1) + f a.1 + f b.1 + f 0) +
            (f 0 + f 0) := by abel
      _ = f (a.1 + b.1) + f a.1 + f b.1 + f 0 := by
        rw [ZModModule.add_self, add_zero]
      _ = 0 := hpolar

theorem sum_autocorrelation_eq_card_mul_sum_quadraticRadicalSignCharacter
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∑ a, autocorrelation f a =
      (2 ^ n : ℝ) *
        ∑ a : quadraticRadical f hdegree,
          quadraticRadicalSignCharacter f hdegree a := by
  classical
  let R := quadraticRadical f hdegree
  have hpoint (a : FABL.F₂Cube n) :
      autocorrelation f a =
        if a ∈ R then
          (2 ^ n : ℝ) * FABL.binarySign (f a + f 0)
        else 0 := by
    by_cases ha : a ∈ R
    · rw [if_pos ha]
      exact autocorrelation_eq_card_mul_sign_of_mem_quadraticRadical
        f hdegree a ha
    · rw [if_neg ha]
      exact autocorrelation_eq_zero_of_not_mem_quadraticRadical
        f hdegree a ha
  calc
    ∑ a, autocorrelation f a =
        ∑ a, if a ∈ R then
          (2 ^ n : ℝ) * FABL.binarySign (f a + f 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a
    _ = ∑ a with a ∈ R,
          (2 ^ n : ℝ) * FABL.binarySign (f a + f 0) := by
      rw [Finset.sum_filter]
    _ = ∑ a : R,
          (2 ^ n : ℝ) * FABL.binarySign (f a.1 + f 0) := by
      exact Finset.sum_subtype
        (Finset.univ.filter fun a ↦ a ∈ R)
        (by simp) _
    _ = (2 ^ n : ℝ) *
        ∑ a : R, FABL.binarySign (f a.1 + f 0) := by
      rw [Finset.mul_sum]
    _ = (2 ^ n : ℝ) *
        ∑ a : quadraticRadical f hdegree,
          quadraticRadicalSignCharacter f hdegree a := by
      rfl

end CryptBoolean
