/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightTwelve
public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightAffineSpan
public import FABL.Chapter06.FoolingF₂Polynomials.DirectionalDerivatives
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The corrected weight-twelve affine-flat classification

The five-variable quadratic core of the Kasami--Tokura classification and
the exact twenty-element fiber of ordered affine-flat decompositions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightTwelveQuadraticRadicalFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

noncomputable local instance weightTwelveQuotientDecidableEq
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    DecidableEq (FABL.F₂Cube n ⧸ S) :=
  Classical.decEq _

noncomputable local instance weightTwelveClassificationAffineSubspaceDecidableEq :
    DecidableEq (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

theorem goodWeightTwelveFlatTriple_geometry
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 ∧
      p.2.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.1.direction = 3 ∧
      p.2.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.2.direction = 3 ∧
      p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
      p.2.1.direction ⊓ p.2.2.direction = p.1.direction := by
  classical
  have hpGood := Finset.mem_filter.mp hp
  have hpTriple := Finset.mem_filter.mp hpGood.1
  have hpProduct := Finset.mem_product.mp hpTriple.1
  have hpThree := Finset.mem_product.mp hpProduct.2
  have hline : p.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.1.direction = 1 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpProduct.1
  have hfirst : p.2.1 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.2.1.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpThree.1
  have hsecond : p.2.2 ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂ p.2.2.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hpThree.2
  exact ⟨hline.1, hline.2, hfirst.1, hfirst.2,
    hsecond.1, hsecond.2, hpTriple.2.1, hpTriple.2.2, hpGood.2⟩

theorem binaryAffineFlatIndicator_add_period_of_mem_direction
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) (ha : a ∈ A.direction)
    (x : FABL.F₂Cube n) :
    binaryAffineFlatIndicator A (x + a) =
      binaryAffineFlatIndicator A x := by
  classical
  have hmem : x + a ∈ A ↔ x ∈ A := by
    simpa only [vadd_eq_add, add_comm] using
      (AffineSubspace.vadd_mem_iff_mem_of_mem_direction ha (p := x))
  simp only [binaryAffineFlatIndicator]
  by_cases hx : x ∈ A
  · rw [if_pos hx, if_pos (hmem.mpr hx)]
  · rw [if_neg hx, if_neg (fun h ↦ hx (hmem.mp h))]

theorem weightTwelveRepresentationWord_add_period_of_mem_line_direction
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (a : FABL.F₂Cube n) (ha : a ∈ p.1.direction)
    (x : FABL.F₂Cube n) :
    weightTwelveRepresentationWord p (x + a) =
      weightTwelveRepresentationWord p x := by
  have hdata := goodWeightTwelveFlatTriple_geometry hp
  have haFirst : a ∈ p.2.1.direction :=
    (AffineSubspace.direction_le hdata.2.2.2.2.2.2.1) ha
  have haSecond : a ∈ p.2.2.direction :=
    (AffineSubspace.direction_le hdata.2.2.2.2.2.2.2.1) ha
  simp only [weightTwelveRepresentationWord, Pi.add_apply]
  rw [binaryAffineFlatIndicator_add_period_of_mem_direction
      p.2.1 a haFirst x,
    binaryAffineFlatIndicator_add_period_of_mem_direction
      p.2.2 a haSecond x]

def quadraticPolarKernel
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) : FABL.𝔽₂ :=
  FABL.booleanDerivative f a b + FABL.booleanDerivative f a 0

theorem quadraticPolarKernel_eq
    (f : BooleanFunction n) (a b : FABL.F₂Cube n) :
    quadraticPolarKernel f a b =
      f (a + b) + f a + f b + f 0 := by
  simp only [quadraticPolarKernel, FABL.booleanDerivative]
  abel

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

theorem sum_quadraticRadicalSignCharacter_eq_two_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    ∑ a : quadraticRadical f hdegree,
        quadraticRadicalSignCharacter f hdegree a = 2 := by
  have hsum := sum_autocorrelation_eq_walshTransform_zero_sq f
  rw [sum_autocorrelation_eq_card_mul_sum_quadraticRadicalSignCharacter
      f hdegree,
    walshTransform_zero_eq_two_pow_sub_two_weight, hweight] at hsum
  norm_num at hsum ⊢
  linarith

theorem quadraticRadicalSignCharacter_eq_zero_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    quadraticRadicalSignCharacter f hdegree = 0 := by
  classical
  by_contra hnonzero
  have horthogonality :=
    AddChar.sum_eq_ite (quadraticRadicalSignCharacter f hdegree)
  rw [if_neg hnonzero,
    sum_quadraticRadicalSignCharacter_eq_two_of_weight_eq_twelve
      f hdegree hweight] at horthogonality
  norm_num at horthogonality

theorem natCard_quadraticRadical_eq_two_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    Nat.card (quadraticRadical f hdegree) = 2 := by
  classical
  have horthogonality :=
    AddChar.sum_eq_ite (quadraticRadicalSignCharacter f hdegree)
  rw [if_pos
      (quadraticRadicalSignCharacter_eq_zero_of_weight_eq_twelve
        f hdegree hweight),
    sum_quadraticRadicalSignCharacter_eq_two_of_weight_eq_twelve
      f hdegree hweight] at horthogonality
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast horthogonality.symm

theorem finrank_quadraticRadical_eq_one_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    Module.finrank FABL.𝔽₂ (quadraticRadical f hdegree) = 1 := by
  have hcard := FABL.card_submodule_eq_two_pow_finrank
    (quadraticRadical f hdegree)
  rw [natCard_quadraticRadical_eq_two_of_weight_eq_twelve
      f hdegree hweight] at hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    (by simpa using hcard.symm)

theorem mem_quadraticRadical_of_add_period
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a : FABL.F₂Cube n)
    (hperiod : ∀ x, f (x + a) = f x) :
    a ∈ quadraticRadical f hdegree := by
  rw [mem_quadraticRadical_iff]
  intro b
  rw [quadraticPolarKernel_eq]
  have hba : f (b + a) = f b := hperiod b
  have ha : f a = f 0 := by
    simpa only [zero_add] using hperiod 0
  rw [show f (a + b) = f b by simpa only [add_comm] using hba, ha]
  calc
    f b + f 0 + f b + f 0 =
        (f b + f b) + (f 0 + f 0) := by abel
    _ = 0 := by
      rw [ZModModule.add_self, ZModModule.add_self, add_zero]

theorem goodWeightTwelveFlatTriple_line_direction_le_quadraticRadical
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (hrepresentation : weightTwelveRepresentationWord p = f) :
    p.1.direction ≤ quadraticRadical f hdegree := by
  intro a ha
  apply mem_quadraticRadical_of_add_period f hdegree a
  intro x
  rw [← hrepresentation]
  exact weightTwelveRepresentationWord_add_period_of_mem_line_direction
    hp a ha x

theorem goodWeightTwelveFlatTriple_line_direction_eq_quadraticRadical_five
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    {p : WeightTwelveFlatTriple 5}
    (hp : p ∈ goodWeightTwelveFlatTriples 5)
    (hrepresentation : weightTwelveRepresentationWord p = f) :
    p.1.direction = quadraticRadical f hdegree := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact goodWeightTwelveFlatTriple_line_direction_le_quadraticRadical
      f hdegree hp hrepresentation
  · rw [(goodWeightTwelveFlatTriple_geometry hp).2.1,
      finrank_quadraticRadical_eq_one_of_weight_eq_twelve
        f hdegree hweight]

theorem goodWeightTwelveFlatTriple_line_value_eq_zero
    (f : BooleanFunction n)
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (hrepresentation : weightTwelveRepresentationWord p = f)
    (x : FABL.F₂Cube n) (hx : x ∈ p.1) :
    f x = 0 := by
  have hdata := goodWeightTwelveFlatTriple_geometry hp
  have hxFirst : x ∈ p.2.1 := hdata.2.2.2.2.2.2.1 hx
  have hxSecond : x ∈ p.2.2 := hdata.2.2.2.2.2.2.2.1 hx
  have happ := congrFun hrepresentation x
  simp only [weightTwelveRepresentationWord, Pi.add_apply,
    binaryAffineFlatIndicator] at happ
  rw [if_pos hxFirst, if_pos hxSecond,
    ZModModule.add_self] at happ
  exact happ.symm

theorem goodWeightTwelveFlatTriple_inf_eq_line
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    p.2.1 ⊓ p.2.2 = p.1 := by
  have hdata := goodWeightTwelveFlatTriple_geometry hp
  obtain ⟨u, hu⟩ :=
    (AffineSubspace.nonempty_iff_ne_bot p.1).2 hdata.1
  have huFirst : u ∈ p.2.1 := hdata.2.2.2.2.2.2.1 hu
  have huSecond : u ∈ p.2.2 := hdata.2.2.2.2.2.2.2.1 hu
  have huInf : u ∈ p.2.1 ⊓ p.2.2 :=
    (AffineSubspace.mem_inf_iff u p.2.1 p.2.2).2
      ⟨huFirst, huSecond⟩
  apply (AffineSubspace.eq_iff_direction_eq_of_mem huInf hu).2
  rw [AffineSubspace.direction_inf_of_mem_inf huInf]
  exact hdata.2.2.2.2.2.2.2.2

theorem mem_first_or_second_iff_representation_one_or_line
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (x : FABL.F₂Cube n) :
    x ∈ p.2.1 ∨ x ∈ p.2.2 ↔
      weightTwelveRepresentationWord p x = 1 ∨ x ∈ p.1 := by
  have hdata := goodWeightTwelveFlatTriple_geometry hp
  have hinf := goodWeightTwelveFlatTriple_inf_eq_line hp
  constructor
  · intro hx
    rcases hx with hxFirst | hxSecond
    · by_cases hxSecond : x ∈ p.2.2
      · right
        rw [← hinf, AffineSubspace.mem_inf_iff]
        exact ⟨hxFirst, hxSecond⟩
      · left
        simp [weightTwelveRepresentationWord, Pi.add_apply,
          binaryAffineFlatIndicator, hxFirst, hxSecond]
    · by_cases hxFirst : x ∈ p.2.1
      · right
        rw [← hinf, AffineSubspace.mem_inf_iff]
        exact ⟨hxFirst, hxSecond⟩
      · left
        simp [weightTwelveRepresentationWord, Pi.add_apply,
          binaryAffineFlatIndicator, hxFirst, hxSecond]
  · rintro (hword | hline)
    · by_cases hxFirst : x ∈ p.2.1
      · exact Or.inl hxFirst
      · by_cases hxSecond : x ∈ p.2.2
        · exact Or.inr hxSecond
        · simp [weightTwelveRepresentationWord, Pi.add_apply,
            binaryAffineFlatIndicator, hxFirst, hxSecond] at hword
    · exact Or.inl (hdata.2.2.2.2.2.2.1 hline)

theorem weightTwelveFlatPair_eq_or_swap_of_same_line
    (f : BooleanFunction n)
    {p q : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (hq : q ∈ goodWeightTwelveFlatTriples n)
    (hpRepresentation : weightTwelveRepresentationWord p = f)
    (hqRepresentation : weightTwelveRepresentationWord q = f)
    (hline : p.1 = q.1) :
    (p.2.1 = q.2.1 ∧ p.2.2 = q.2.2) ∨
      (p.2.1 = q.2.2 ∧ p.2.2 = q.2.1) := by
  have hpData := goodWeightTwelveFlatTriple_geometry hp
  have hqData := goodWeightTwelveFlatTriple_geometry hq
  obtain ⟨u, huPLine⟩ :=
    (AffineSubspace.nonempty_iff_ne_bot p.1).2 hpData.1
  have huQLine : u ∈ q.1 := by
    rw [← hline]
    exact huPLine
  have huPFirst : u ∈ p.2.1 := hpData.2.2.2.2.2.2.1 huPLine
  have huPSecond : u ∈ p.2.2 := hpData.2.2.2.2.2.2.2.1 huPLine
  have huQFirst : u ∈ q.2.1 := hqData.2.2.2.2.2.2.1 huQLine
  have huQSecond : u ∈ q.2.2 := hqData.2.2.2.2.2.2.2.1 huQLine
  have hunionAffine : ∀ x,
      x ∈ p.2.1 ∨ x ∈ p.2.2 ↔ x ∈ q.2.1 ∨ x ∈ q.2.2 := by
    intro x
    rw [mem_first_or_second_iff_representation_one_or_line hp,
      mem_first_or_second_iff_representation_one_or_line hq,
      hpRepresentation, hqRepresentation, hline]
  have hunionDirections : ∀ a,
      a ∈ p.2.1.direction ∨ a ∈ p.2.2.direction ↔
        a ∈ q.2.1.direction ∨ a ∈ q.2.2.direction := by
    intro a
    constructor
    · intro ha
      have hua : u + a ∈ p.2.1 ∨ u + a ∈ p.2.2 := by
        rcases ha with ha | ha
        · left
          have := AffineSubspace.vadd_mem_of_mem_direction ha huPFirst
          simpa only [vadd_eq_add, add_comm] using this
        · right
          have := AffineSubspace.vadd_mem_of_mem_direction ha huPSecond
          simpa only [vadd_eq_add, add_comm] using this
      rcases (hunionAffine (u + a)).mp hua with hua | hua
      · left
        apply (AffineSubspace.vadd_mem_iff_mem_direction a huQFirst).mp
        simpa only [vadd_eq_add, add_comm] using hua
      · right
        apply (AffineSubspace.vadd_mem_iff_mem_direction a huQSecond).mp
        simpa only [vadd_eq_add, add_comm] using hua
    · intro ha
      have hua : u + a ∈ q.2.1 ∨ u + a ∈ q.2.2 := by
        rcases ha with ha | ha
        · left
          have := AffineSubspace.vadd_mem_of_mem_direction ha huQFirst
          simpa only [vadd_eq_add, add_comm] using this
        · right
          have := AffineSubspace.vadd_mem_of_mem_direction ha huQSecond
          simpa only [vadd_eq_add, add_comm] using this
      rcases (hunionAffine (u + a)).mpr hua with hua | hua
      · left
        apply (AffineSubspace.vadd_mem_iff_mem_direction a huPFirst).mp
        simpa only [vadd_eq_add, add_comm] using hua
      · right
        apply (AffineSubspace.vadd_mem_iff_mem_direction a huPSecond).mp
        simpa only [vadd_eq_add, add_comm] using hua
  have hpDirectionsNe : p.2.1.direction ≠ p.2.2.direction := by
    intro heq
    have hintersection := hpData.2.2.2.2.2.2.2.2
    rw [heq, inf_idem] at hintersection
    have hrank := congrArg
      (fun S : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ↦
        Module.finrank FABL.𝔽₂ S) hintersection
    rw [hpData.2.2.2.2.2.1, hpData.2.1] at hrank
    omega
  have hdirections := unordered_submodule_pair_eq_of_union_eq
    p.2.1.direction p.2.2.direction q.2.1.direction q.2.2.direction
    (hpData.2.2.2.1.trans hqData.2.2.2.1.symm)
    (hpData.2.2.2.1.trans hqData.2.2.2.2.2.1.symm)
    (hpData.2.2.2.2.2.1.trans hqData.2.2.2.1.symm)
    (hpData.2.2.2.2.2.1.trans hqData.2.2.2.2.2.1.symm)
    hpDirectionsNe hunionDirections
  rcases hdirections with hsame | hswap
  · left
    exact ⟨(AffineSubspace.eq_iff_direction_eq_of_mem
        huPFirst huQFirst).2 hsame.1,
      (AffineSubspace.eq_iff_direction_eq_of_mem
        huPSecond huQSecond).2 hsame.2⟩
  · right
    exact ⟨(AffineSubspace.eq_iff_direction_eq_of_mem
        huPFirst huQSecond).2 hswap.1,
      (AffineSubspace.eq_iff_direction_eq_of_mem
        huPSecond huQFirst).2 hswap.2⟩

theorem goodWeightTwelveFlatTriple_line_eq_radicalCoset_five
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    {p : WeightTwelveFlatTriple 5}
    (hp : p ∈ goodWeightTwelveFlatTriples 5)
    (hrepresentation : weightTwelveRepresentationWord p = f)
    (u : FABL.F₂Cube 5) (hu : u ∈ p.1) :
    p.1 = FABL.binaryAffineSubspace (quadraticRadical f hdegree) u := by
  rw [← goodWeightTwelveFlatTriple_line_direction_eq_quadraticRadical_five
    f hdegree hweight hp hrepresentation]
  exact (AffineSubspace.mk'_eq hu).symm

theorem eq_zero_value_of_mem_quadraticRadical_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (a : FABL.F₂Cube 5)
    (ha : a ∈ quadraticRadical f hdegree) :
    f a = f 0 := by
  have hcharacter := congrArg
    (fun ψ : AddChar (quadraticRadical f hdegree) ℝ ↦
      ψ (⟨a, ha⟩ : quadraticRadical f hdegree))
    (quadraticRadicalSignCharacter_eq_zero_of_weight_eq_twelve
      f hdegree hweight)
  change FABL.binarySign (f a + f 0) = 1 at hcharacter
  have hsumZero := (FABL.binarySign_eq_one_iff (f a + f 0)).mp
    hcharacter
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hsumZero
  exact hsumZero

theorem add_mem_quadraticRadical_is_period_of_weight_eq_twelve
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (a : FABL.F₂Cube 5)
    (ha : a ∈ quadraticRadical f hdegree)
    (x : FABL.F₂Cube 5) :
    f (x + a) = f x := by
  have hpolar := (mem_quadraticRadical_iff f hdegree a).mp ha x
  rw [quadraticPolarKernel_eq, add_comm a x] at hpolar
  have haValue :=
    eq_zero_value_of_mem_quadraticRadical_of_weight_eq_twelve
      f hdegree hweight a ha
  rw [haValue] at hpolar
  apply eq_of_sub_eq_zero
  rw [sub_eq_add_neg, ZModModule.neg_eq_self]
  calc
    f (x + a) + f x =
        (f (x + a) + f x) + (f 0 + f 0) := by
      rw [ZModModule.add_self, add_zero]
    _ = f (x + a) + f 0 + f x + f 0 := by abel
    _ = 0 := hpolar

/-- A weight-twelve quadratic descends to the quotient by its one-dimensional
radical. -/
noncomputable def quadraticRadicalQuotientFunction
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree) → FABL.𝔽₂ :=
  fun q ↦ Quotient.liftOn' q f (by
    intro a b hab
    have hquotient :
        (quadraticRadical f hdegree).mkQ a =
          (quadraticRadical f hdegree).mkQ b :=
      Quotient.sound' hab
    have habRadical : a + b ∈ quadraticRadical f hdegree := by
      have hdifference :=
        (Submodule.Quotient.eq (quadraticRadical f hdegree)).mp
          hquotient
      simpa only [sub_eq_add_neg, ZModModule.neg_eq_self] using hdifference
    have hperiod :=
      add_mem_quadraticRadical_is_period_of_weight_eq_twelve
        f hdegree hweight (a + b) habRadical a
    simpa only [← add_assoc, ZModModule.add_self, zero_add] using hperiod.symm)

@[simp] theorem quadraticRadicalQuotientFunction_mkQ
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (x : FABL.F₂Cube 5) :
    quadraticRadicalQuotientFunction f hdegree hweight
        ((quadraticRadical f hdegree).mkQ x) = f x := by
  rfl

theorem card_submodule_mkQ_fiber
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (q : FABL.F₂Cube n ⧸ S) :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
      S.mkQ x = q).card = Nat.card S := by
  classical
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {x : FABL.F₂Cube n // S.mkQ x = q} =
        Fintype.card S.mkQ.toAddMonoidHom.ker := by
      apply Fintype.card_congr
      exact AddMonoidHom.fiberEquivKerOfSurjective
        (f := S.mkQ.toAddMonoidHom) S.mkQ_surjective q
    _ = Nat.card S := by
      rw [← Nat.card_eq_fintype_card]
      have hker : S.mkQ.toAddMonoidHom.ker = S.toAddSubgroup := by
        rw [← LinearMap.ker_toAddSubgroup, Submodule.ker_mkQ]
      rw [hker]
      congr

theorem card_filter_mkQ_eq_card_mul_card_filter
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (P : (FABL.F₂Cube n ⧸ S) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
      P (S.mkQ x)).card =
      Nat.card S *
        ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    (t := (Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P)
    (g := S.mkQ)
  rw [Finset.sum_const_nat] at hfiber
  · calc
      ((Finset.univ : Finset (FABL.F₂Cube n)).filter fun x ↦
          P (S.mkQ x)).card =
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card *
            Nat.card S := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          hfiber.symm
      _ = Nat.card S *
          ((Finset.univ : Finset (FABL.F₂Cube n ⧸ S)).filter P).card :=
        Nat.mul_comm _ _
  · intro q hq
    exact card_submodule_mkQ_fiber S q

theorem card_one_add_add_two_mul_card_one_inter
    {X : Type*} [Fintype X] (g h : X → FABL.𝔽₂) :
    ((Finset.univ : Finset X).filter fun x ↦ g x + h x = 1).card +
        2 * ((Finset.univ : Finset X).filter fun x ↦
          g x = 1 ∧ h x = 1).card =
      ((Finset.univ : Finset X).filter fun x ↦ g x = 1).card +
        ((Finset.univ : Finset X).filter fun x ↦ h x = 1).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hg : g x = 0
  · by_cases hh : h x = 0
    · norm_num [hg, hh]
    · have hhOne : h x = 1 := Fin.eq_one_of_ne_zero _ hh
      norm_num [hg, hhOne]
  · have hgOne : g x = 1 := Fin.eq_one_of_ne_zero _ hg
    by_cases hh : h x = 0
    · norm_num [hgOne, hh]
    · have hhOne : h x = 1 := Fin.eq_one_of_ne_zero _ hh
      norm_num [hgOne, hhOne]

theorem card_one_translate_add
    {X : Type*} [Fintype X] [AddGroup X]
    (g : X → FABL.𝔽₂) (a : X) :
    ((Finset.univ : Finset X).filter fun x ↦ g (x + a) = 1).card =
      ((Finset.univ : Finset X).filter fun x ↦ g x = 1).card := by
  classical
  apply Finset.card_equiv (Equiv.addRight a)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

noncomputable def binaryOneSupport
    {X : Type*} [Fintype X] (g : X → FABL.𝔽₂) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ g x = 1

noncomputable def binarySupportNeighbors
    {X : Type*} [Fintype X] [Add X]
    (g : X → FABL.𝔽₂) (x : X) : Finset X := by
  classical
  exact (binaryOneSupport g).filter fun y ↦ g (y + x) = 1

@[simp] theorem mem_binaryOneSupport
    {X : Type*} [Fintype X] (g : X → FABL.𝔽₂) (x : X) :
    x ∈ binaryOneSupport g ↔ g x = 1 := by
  classical
  simp [binaryOneSupport]

@[simp] theorem mem_binarySupportNeighbors
    {X : Type*} [Fintype X] [Add X]
    (g : X → FABL.𝔽₂) (x y : X) :
    y ∈ binarySupportNeighbors g x ↔
      g y = 1 ∧ g (y + x) = 1 := by
  classical
  simp [binarySupportNeighbors]

theorem exists_binarySupportNeighbor_pair
    {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0) (x : X) (hx : g x = 1)
    (hneighbors : (binarySupportNeighbors g x).card = 2) :
    ∃ y, g y = 1 ∧ g (x + y) = 1 ∧ y ≠ x ∧
      binarySupportNeighbors g x = {y, x + y} := by
  classical
  have hnonempty : (binarySupportNeighbors g x).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hneighbors
    norm_num at hneighbors
  obtain ⟨y, hyNeighbor⟩ := hnonempty
  have hyData := (mem_binarySupportNeighbors g x y).mp hyNeighbor
  have hxNonzero : x ≠ 0 := by
    intro hxZero
    rw [hxZero, hzero] at hx
    exact zero_ne_one hx
  have hyNeX : y ≠ x := by
    intro hyx
    subst y
    have := hyData.2
    rw [ZModModule.add_self, hzero] at this
    exact zero_ne_one this
  have hyNeSum : y ≠ x + y := by
    intro heq
    apply hxNonzero
    have h := congrArg (fun z ↦ z + y) heq
    simpa only [add_assoc, ZModModule.add_self, add_zero] using h.symm
  have hsumNeighbor : x + y ∈ binarySupportNeighbors g x := by
    rw [mem_binarySupportNeighbors]
    constructor
    · simpa only [add_comm] using hyData.2
    · have harg : (x + y) + x = y := by
        calc
          (x + y) + x = y + (x + x) := by abel
          _ = y := by rw [ZModModule.add_self, add_zero]
      rw [harg]
      exact hyData.1
  have hpairSubset : ({y, x + y} : Finset X) ⊆
      binarySupportNeighbors g x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun h ↦ h ▸ hyNeighbor) (fun h ↦ h ▸ hsumNeighbor)
  have hpairEq : ({y, x + y} : Finset X) =
      binarySupportNeighbors g x := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hneighbors, Finset.card_pair hyNeSum]
  exact ⟨y, hyData.1, by simpa only [add_comm] using hyData.2,
    hyNeX, hpairEq.symm⟩

theorem binarySupportNeighbors_eq_pair_of_mem
    {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0) (x y : X) (hx : g x = 1)
    (hyNeighbor : y ∈ binarySupportNeighbors g x)
    (hneighbors : (binarySupportNeighbors g x).card = 2) :
    binarySupportNeighbors g x = {y, x + y} := by
  have hyData := (mem_binarySupportNeighbors g x y).mp hyNeighbor
  have hxNonzero : x ≠ 0 := by
    intro hxZero
    rw [hxZero, hzero] at hx
    exact zero_ne_one hx
  have hyNeSum : y ≠ x + y := by
    intro heq
    apply hxNonzero
    have h := congrArg (fun z ↦ z + y) heq
    simpa only [add_assoc, ZModModule.add_self, add_zero] using h.symm
  have hsumNeighbor : x + y ∈ binarySupportNeighbors g x := by
    rw [mem_binarySupportNeighbors]
    constructor
    · simpa only [add_comm] using hyData.2
    · have harg : (x + y) + x = y := by
        calc
          (x + y) + x = y + (x + x) := by abel
          _ = y := by rw [ZModModule.add_self, add_zero]
      rw [harg]
      exact hyData.1
  have hpairSubset : ({y, x + y} : Finset X) ⊆
      binarySupportNeighbors g x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun h ↦ h ▸ hyNeighbor) (fun h ↦ h ▸ hsumNeighbor)
  symm
  apply Finset.eq_of_subset_of_card_le hpairSubset
  rw [hneighbors, Finset.card_pair hyNeSum]

noncomputable def binarySupportTriangle
    {X : Type*} [Fintype X] [Add X]
    (g : X → FABL.𝔽₂) (x : X) : Finset X := by
  classical
  exact insert x (binarySupportNeighbors g x)

@[simp] theorem mem_binarySupportTriangle
    {X : Type*} [Fintype X] [Add X]
    (g : X → FABL.𝔽₂) (x y : X) :
    y ∈ binarySupportTriangle g x ↔
      y = x ∨ (g y = 1 ∧ g (y + x) = 1) := by
  classical
  simp [binarySupportTriangle]

theorem card_binarySupportTriangle
    {X : Type*} [Fintype X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0) (x : X) (_hx : g x = 1)
    (hneighbors : (binarySupportNeighbors g x).card = 2) :
    (binarySupportTriangle g x).card = 3 := by
  classical
  rw [binarySupportTriangle, Finset.card_insert_of_notMem]
  · rw [hneighbors]
  · rw [mem_binarySupportNeighbors]
    intro hself
    rw [ZModModule.add_self, hzero] at hself
    exact zero_ne_one hself.2

theorem binarySupportTriangle_subset_oneSupport
    {X : Type*} [Fintype X] [Add X]
    (g : X → FABL.𝔽₂) (x : X) (hx : g x = 1) :
    binarySupportTriangle g x ⊆ binaryOneSupport g := by
  classical
  intro y hy
  rw [mem_binarySupportTriangle] at hy
  rw [mem_binaryOneSupport]
  exact hy.elim (fun h ↦ by simpa only [h] using hx) (fun h ↦ h.1)

theorem binarySupportTriangle_eq_of_mem
    {X : Type*} [Fintype X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0)
    (hneighbors : ∀ x, g x = 1 →
      (binarySupportNeighbors g x).card = 2)
    (x y : X) (hx : g x = 1) (hy : g y = 1)
    (hyTriangle : y ∈ binarySupportTriangle g x) :
    binarySupportTriangle g y = binarySupportTriangle g x := by
  classical
  rw [mem_binarySupportTriangle] at hyTriangle
  rcases hyTriangle with rfl | hyNeighbor
  · rfl
  · have hNx := binarySupportNeighbors_eq_pair_of_mem
      g hzero x y hx
      ((mem_binarySupportNeighbors g x y).mpr hyNeighbor)
      (hneighbors x hx)
    have hxNeighborY : x ∈ binarySupportNeighbors g y := by
      rw [mem_binarySupportNeighbors]
      exact ⟨hx, by simpa only [add_comm] using hyNeighbor.2⟩
    have hNy := binarySupportNeighbors_eq_pair_of_mem
      g hzero y x hy hxNeighborY (hneighbors y hy)
    rw [binarySupportTriangle, binarySupportTriangle, hNx, hNy]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [add_comm y x]
    tauto

theorem exists_disjoint_binarySupportTriangles
    {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0)
    (hsupport : (binaryOneSupport g).card = 6)
    (hneighbors : ∀ x, g x = 1 →
      (binarySupportNeighbors g x).card = 2) :
    ∃ x w : X,
      g x = 1 ∧ g w = 1 ∧
      Disjoint (binarySupportTriangle g x)
        (binarySupportTriangle g w) ∧
      binarySupportTriangle g x ∪ binarySupportTriangle g w =
        binaryOneSupport g := by
  classical
  have hsupportNonempty : (binaryOneSupport g).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hsupport
    norm_num at hsupport
  obtain ⟨x, hxSupport⟩ := hsupportNonempty
  have hx : g x = 1 := (mem_binaryOneSupport g x).mp hxSupport
  have htriangleXSubset :=
    binarySupportTriangle_subset_oneSupport g x hx
  have htriangleXCard : (binarySupportTriangle g x).card = 3 :=
    card_binarySupportTriangle g hzero x hx (hneighbors x hx)
  have htriangleXStrict :
      binarySupportTriangle g x ⊂ binaryOneSupport g := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨htriangleXSubset, ?_⟩
    intro heq
    rw [heq, hsupport] at htriangleXCard
    norm_num at htriangleXCard
  obtain ⟨w, hwSupport, hwNotTriangleX⟩ :=
    Finset.exists_of_ssubset htriangleXStrict
  have hw : g w = 1 := (mem_binaryOneSupport g w).mp hwSupport
  have htriangleWSubset :=
    binarySupportTriangle_subset_oneSupport g w hw
  have htriangleWCard : (binarySupportTriangle g w).card = 3 :=
    card_binarySupportTriangle g hzero w hw (hneighbors w hw)
  have hdisjoint : Disjoint (binarySupportTriangle g x)
      (binarySupportTriangle g w) := by
    rw [Finset.disjoint_left]
    intro z hzX hzW
    have hz : g z = 1 :=
      (mem_binaryOneSupport g z).mp (htriangleXSubset hzX)
    have htriangleZX := binarySupportTriangle_eq_of_mem
      g hzero hneighbors x z hx hz hzX
    have htriangleZW := binarySupportTriangle_eq_of_mem
      g hzero hneighbors w z hw hz hzW
    apply hwNotTriangleX
    rw [← htriangleZX, htriangleZW]
    simp only [mem_binarySupportTriangle]
    exact Or.inl trivial
  refine ⟨x, w, hx, hw, hdisjoint, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset htriangleXSubset htriangleWSubset
  · rw [hsupport, Finset.card_union_of_disjoint hdisjoint,
      htriangleXCard, htriangleWCard]

theorem mem_binarySpanPair_iff
    {X : Type*} [AddCommGroup X] [Module FABL.𝔽₂ X]
    (x y z : X) :
    z ∈ Submodule.span FABL.𝔽₂ ({x, y} : Set X) ↔
      z = 0 ∨ z = x ∨ z = y ∨ z = x + y := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        exact Or.inl (by simp)
      · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
        subst b
        exact Or.inr (Or.inr (Or.inl (by simp)))
    · have haOne : a = 1 := Fin.eq_one_of_ne_zero _ ha
      subst a
      by_cases hb : b = 0
      · subst b
        exact Or.inr (Or.inl (by simp))
      · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
        subst b
        exact Or.inr (Or.inr (Or.inr (by simp)))
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem mem_binarySpanSingleton_iff
    {X : Type*} [AddCommGroup X] [Module FABL.𝔽₂ X]
    (x z : X) :
    z ∈ FABL.𝔽₂ ∙ x ↔ z = 0 ∨ z = x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    by_cases ha : a = 0
    · subst a
      exact Or.inl (by simp)
    · have haOne : a = 1 := Fin.eq_one_of_ne_zero _ ha
      subst a
      exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

noncomputable def binarySpanPairNonzero
    {X : Type*} [Fintype X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (x y : X) : Finset X := by
  classical
  exact Finset.univ.filter fun z ↦
    z ≠ 0 ∧ z ∈ Submodule.span FABL.𝔽₂ ({x, y} : Set X)

@[simp] theorem mem_binarySpanPairNonzero
    {X : Type*} [Fintype X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (x y z : X) :
    z ∈ binarySpanPairNonzero x y ↔
      z ≠ 0 ∧ z ∈ Submodule.span FABL.𝔽₂ ({x, y} : Set X) := by
  classical
  simp [binarySpanPairNonzero]

theorem binarySupportTriangle_eq_binarySpanPairNonzero
    {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂) (hzero : g 0 = 0)
    (x y : X) (hx : g x = 1) (hy : g y = 1)
    (hxy : g (x + y) = 1)
    (hneighbors : binarySupportNeighbors g x = {y, x + y}) :
    binarySupportTriangle g x = binarySpanPairNonzero x y := by
  classical
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, hzero] at hx
    exact zero_ne_one hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, hzero] at hy
    exact zero_ne_one hy
  have hxy0 : x + y ≠ 0 := by
    intro h
    rw [h, hzero] at hxy
    exact zero_ne_one hxy
  rw [binarySupportTriangle, hneighbors]
  ext z
  rw [mem_binarySpanPairNonzero, mem_binarySpanPair_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    constructor
    · rcases hz with hz | hz | hz
      · simpa only [hz] using hx0
      · simpa only [hz] using hy0
      · simpa only [hz] using hxy0
    · exact Or.inr hz
  · rintro ⟨hz0, hz | hz⟩
    · exact (hz0 hz).elim
    · exact hz

theorem finrank_binarySpanPair_eq_two
    {X : Type*} [AddCommGroup X] [Module FABL.𝔽₂ X]
    [Module.Finite FABL.𝔽₂ X]
    (x y : X) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hyx : y ≠ x) :
    Module.finrank FABL.𝔽₂
      (Submodule.span FABL.𝔽₂ ({x, y} : Set X)) = 2 := by
  have hyNotSpan : y ∉ FABL.𝔽₂ ∙ x := by
    rw [mem_binarySpanSingleton_iff]
    tauto
  rw [Submodule.span_insert,
    Submodule.finrank_sup_span_singleton hyNotSpan,
    finrank_span_singleton hx0]

theorem finrank_comap_mkQ_eq_add
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (R : Submodule K X) (E : Submodule K (X ⧸ R)) :
    Module.finrank K (Submodule.comap R.mkQ E) =
      Module.finrank K R + Module.finrank K E := by
  let P := Submodule.comap R.mkQ E
  let φ : P →ₗ[K] E :=
    R.mkQ.restrict (fun x hx ↦ hx)
  have hRleP : R ≤ P := Submodule.le_comap_mkQ R E
  have hφSurjective : Function.Surjective φ := by
    intro q
    obtain ⟨x, hx⟩ := R.mkQ_surjective q
    have hxP : x ∈ P := by
      change R.mkQ x ∈ E
      rw [hx]
      exact q.2
    refine ⟨⟨x, hxP⟩, Subtype.ext ?_⟩
    exact hx
  have hφRange : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr hφSurjective
  have hφKer : LinearMap.ker φ =
      Submodule.comap P.subtype R := by
    ext z
    simp only [LinearMap.mem_ker, φ, LinearMap.coe_restrict_apply,
      Subtype.ext_iff,
      Submodule.mem_comap, Submodule.coe_subtype]
    rw [Submodule.mkQ_apply]
    change (Submodule.Quotient.mk (z : X) : X ⧸ R) = 0 ↔
      (z : X) ∈ R
    exact Submodule.Quotient.mk_eq_zero (p := R) (x := (z : X))
  have hφKerRank : Module.finrank K (LinearMap.ker φ) =
      Module.finrank K R := by
    rw [hφKer]
    exact (Submodule.comapSubtypeEquivOfLe hRleP).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφRange, finrank_top, hφKerRank] at hrank
  simpa only [P, add_comm] using hrank.symm

theorem exists_transverse_binaryPlanes_of_six_support
    {X : Type*} [Fintype X] [AddCommGroup X]
    [Module FABL.𝔽₂ X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0)
    (hsupport : (binaryOneSupport g).card = 6)
    (hneighbors : ∀ x, g x = 1 →
      (binarySupportNeighbors g x).card = 2) :
    ∃ E F : Submodule FABL.𝔽₂ X,
      Module.finrank FABL.𝔽₂ E = 2 ∧
      Module.finrank FABL.𝔽₂ F = 2 ∧
      E ⊓ F = ⊥ ∧
      ∀ z, g z = 1 ↔ z ≠ 0 ∧ (z ∈ E ∨ z ∈ F) := by
  classical
  obtain ⟨x, w, hx, hw, htrianglesDisjoint, htrianglesUnion⟩ :=
    exists_disjoint_binarySupportTriangles g hzero hsupport hneighbors
  obtain ⟨y, hy, hxy, hyx, hneighborsX⟩ :=
    exists_binarySupportNeighbor_pair
      g hzero x hx (hneighbors x hx)
  obtain ⟨v, hv, hwv, hvw, hneighborsW⟩ :=
    exists_binarySupportNeighbor_pair
      g hzero w hw (hneighbors w hw)
  let E := Submodule.span FABL.𝔽₂ ({x, y} : Set X)
  let F := Submodule.span FABL.𝔽₂ ({w, v} : Set X)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, hzero] at hx
    exact zero_ne_one hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, hzero] at hy
    exact zero_ne_one hy
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, hzero] at hw
    exact zero_ne_one hw
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, hzero] at hv
    exact zero_ne_one hv
  have htriangleX :
      binarySupportTriangle g x = binarySpanPairNonzero x y :=
    binarySupportTriangle_eq_binarySpanPairNonzero
      g hzero x y hx hy hxy hneighborsX
  have htriangleW :
      binarySupportTriangle g w = binarySpanPairNonzero w v :=
    binarySupportTriangle_eq_binarySpanPairNonzero
      g hzero w v hw hv hwv hneighborsW
  have hErank : Module.finrank FABL.𝔽₂ E = 2 := by
    exact finrank_binarySpanPair_eq_two x y hx0 hy0 hyx
  have hFrank : Module.finrank FABL.𝔽₂ F = 2 := by
    exact finrank_binarySpanPair_eq_two w v hw0 hv0 hvw
  have htransverse : E ⊓ F = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [Submodule.mem_bot]
      by_contra hz0
      have hzTriangleX : z ∈ binarySupportTriangle g x := by
        rw [htriangleX, mem_binarySpanPairNonzero]
        exact ⟨hz0, hz.1⟩
      have hzTriangleW : z ∈ binarySupportTriangle g w := by
        rw [htriangleW, mem_binarySpanPairNonzero]
        exact ⟨hz0, hz.2⟩
      exact (Finset.disjoint_left.mp htrianglesDisjoint)
        hzTriangleX hzTriangleW
    · exact bot_le
  refine ⟨E, F, hErank, hFrank, htransverse, ?_⟩
  intro z
  change g z = 1 ↔ z ≠ 0 ∧
    (z ∈ Submodule.span FABL.𝔽₂ ({x, y} : Set X) ∨
      z ∈ Submodule.span FABL.𝔽₂ ({w, v} : Set X))
  rw [← mem_binaryOneSupport, ← htrianglesUnion,
    Finset.mem_union, htriangleX, htriangleW,
    mem_binarySpanPairNonzero, mem_binarySpanPairNonzero]
  tauto

theorem card_binarySupportNeighbors_eq_two_of_six_support
    {X : Type*} [Fintype X] [AddCommGroup X]
    (g : X → FABL.𝔽₂)
    (hzero : g 0 = 0)
    (hsupport : (binaryOneSupport g).card = 6)
    (hderivative : ∀ a ≠ 0,
      ((Finset.univ : Finset X).filter fun x ↦
        g x + g (x + a) = 1).card = 8)
    (a : X) (ha : g a = 1) :
    (binarySupportNeighbors g a).card = 2 := by
  classical
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, hzero] at ha
    exact zero_ne_one ha
  have htranslated :
      ((Finset.univ : Finset X).filter fun x ↦
        g (x + a) = 1).card = 6 := by
    rw [card_one_translate_add]
    simpa only [binaryOneSupport] using hsupport
  have hidentity := card_one_add_add_two_mul_card_one_inter
    g (fun x ↦ g (x + a))
  have hsupport' :
      ((Finset.univ : Finset X).filter fun x ↦ g x = 1).card = 6 := by
    simpa only [binaryOneSupport] using hsupport
  rw [hderivative a ha0, hsupport', htranslated] at hidentity
  change
    ((binaryOneSupport g).filter fun x ↦ g (x + a) = 1).card = 2
  simpa only [binaryOneSupport, Finset.filter_filter,
    and_assoc] using (show
    ((Finset.univ : Finset X).filter fun x ↦
      g x = 1 ∧ g (x + a) = 1).card = 2 by omega)

/-- There are ten radical cosets on which a weight-twelve quadratic vanishes. -/
theorem card_zero_quadraticRadicalQuotientFunction
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    ((Finset.univ : Finset
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun q ↦
      quadraticRadicalQuotientFunction f hdegree hweight q = 0).card = 10 := by
  classical
  let R := quadraticRadical f hdegree
  let qf := quadraticRadicalQuotientFunction f hdegree hweight
  let zeroCosets : Set (FABL.F₂Cube 5 ⧸ R) := {q | qf q = 0}
  have hzeroPoints :
      ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
        f x = 0).card = 20 := by
    have hsupport :
        ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
          f x = 1).card = 12 := by
      simpa only [support, FABL.f₂OneSupport,
        hammingWeight_eq_card_support] using hweight
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (FABL.F₂Cube 5)))
      (p := fun x ↦ f x = 1)
    have hnotOne :
        ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
          ¬f x = 1).card =
        ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
          f x = 0).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hnotOne
        by_contra hnotZero
        exact hnotOne (Fin.eq_one_of_ne_zero _ hnotZero)
      · intro hzero hone
        rw [hzero] at hone
        norm_num at hone
    rw [hsupport, hnotOne, Finset.card_univ, card_f₂Cube] at hpartition
    norm_num at hpartition ⊢
    omega
  have hpreimageCard :
      Nat.card {x : FABL.F₂Cube 5 // R.mkQ x ∈ zeroCosets} = 20 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc
      ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
          R.mkQ x ∈ zeroCosets).card =
          ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
            f x = 0).card := by
        congr 1
      _ = 20 := hzeroPoints
  have hequiv :=
    QuotientAddGroup.preimageMkEquivAddSubgroupProdSet
      R.toAddSubgroup zeroCosets
  have hproductCard :
      Nat.card {x : FABL.F₂Cube 5 // R.mkQ x ∈ zeroCosets} =
        Nat.card R * Nat.card zeroCosets := by
    calc
      Nat.card {x : FABL.F₂Cube 5 // R.mkQ x ∈ zeroCosets} =
          Nat.card (R.toAddSubgroup × zeroCosets) :=
        Nat.card_congr hequiv
      _ = Nat.card R * Nat.card zeroCosets := by
        rw [Nat.card_prod]
        congr 1
  have hRCard : Nat.card R = 2 := by
    exact natCard_quadraticRadical_eq_two_of_weight_eq_twelve
      f hdegree hweight
  have hzeroCosetsCard : Nat.card zeroCosets = 10 := by
    rw [hpreimageCard, hRCard] at hproductCard
    omega
  simpa [zeroCosets, qf, Nat.card_eq_fintype_card,
    Fintype.card_subtype] using hzeroCosetsCard

theorem card_one_quadraticRadicalQuotientFunction
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    ((Finset.univ : Finset
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun q ↦
      quadraticRadicalQuotientFunction f hdegree hweight q = 1).card = 6 := by
  classical
  let R := quadraticRadical f hdegree
  let qf := quadraticRadicalQuotientFunction f hdegree hweight
  have hfactor := card_filter_mkQ_eq_card_mul_card_filter
    R (fun q ↦ qf q = 1)
  have hleft :
      ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
        qf (R.mkQ x) = 1).card = 12 := by
    simpa only [R, qf, quadraticRadicalQuotientFunction_mkQ,
      support, FABL.f₂OneSupport, hammingWeight_eq_card_support]
      using hweight
  have hRCard : Nat.card R = 2 :=
    natCard_quadraticRadical_eq_two_of_weight_eq_twelve
      f hdegree hweight
  rw [hleft, hRCard] at hfactor
  change 12 = 2 *
    ((Finset.univ : Finset
      (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun q ↦
        quadraticRadicalQuotientFunction f hdegree hweight q = 1).card at hfactor
  omega

theorem card_one_quadraticRadicalQuotientDerivative_of_ne_zero
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (a : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (ha : a ≠ 0) :
    ((Finset.univ : Finset
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun x ↦
      quadraticRadicalQuotientFunction f hdegree hweight x +
        quadraticRadicalQuotientFunction f hdegree hweight (x + a) = 1).card = 8 := by
  classical
  let R := quadraticRadical f hdegree
  let qf := quadraticRadicalQuotientFunction f hdegree hweight
  obtain ⟨v, rfl⟩ := R.mkQ_surjective a
  have hvNotRadical : v ∉ R := by
    intro hv
    apply ha
    have hvKer : v ∈ LinearMap.ker R.mkQ := by
      simpa only [Submodule.ker_mkQ] using hv
    exact LinearMap.mem_ker.mp hvKer
  have hbalanced :=
    isBalanced_booleanDerivative_of_not_mem_quadraticRadical
      f hdegree v hvNotRadical
  have hderivativeWeight :
      hammingWeight (FABL.booleanDerivative f v) = 16 := by
    change 2 * hammingWeight (FABL.booleanDerivative f v) = 2 ^ 5 at hbalanced
    norm_num at hbalanced ⊢
    omega
  have hfactor := card_filter_mkQ_eq_card_mul_card_filter
    R (fun x ↦ qf x + qf (x + R.mkQ v) = 1)
  have hleft :
      ((Finset.univ : Finset (FABL.F₂Cube 5)).filter fun x ↦
        qf (R.mkQ x) + qf (R.mkQ x + R.mkQ v) = 1).card = 16 := by
    simpa only [R, qf, ← map_add,
      quadraticRadicalQuotientFunction_mkQ,
      FABL.booleanDerivative, support, FABL.f₂OneSupport,
      hammingWeight_eq_card_support] using hderivativeWeight
  have hRCard : Nat.card R = 2 :=
    natCard_quadraticRadical_eq_two_of_weight_eq_twelve
      f hdegree hweight
  rw [hleft, hRCard] at hfactor
  change 16 = 2 *
    ((Finset.univ : Finset
      (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun x ↦
        quadraticRadicalQuotientFunction f hdegree hweight x +
          quadraticRadicalQuotientFunction f hdegree hweight
            (x + (quadraticRadical f hdegree).mkQ v) = 1).card at hfactor
  apply Eq.symm
  refine Nat.mul_left_cancel (n := 2) (by norm_num) ?_
  norm_num
  exact hfactor

theorem card_quadraticRadicalQuotient_support_neighbors
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (hzero : f 0 = 0)
    (a : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (ha : quadraticRadicalQuotientFunction f hdegree hweight a = 1) :
    ((Finset.univ : Finset
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)).filter fun x ↦
      quadraticRadicalQuotientFunction f hdegree hweight x = 1 ∧
        quadraticRadicalQuotientFunction f hdegree hweight (x + a) = 1).card = 2 := by
  classical
  let Q := FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree
  let qf : Q → FABL.𝔽₂ :=
    quadraticRadicalQuotientFunction f hdegree hweight
  have haNonzero : a ≠ 0 := by
    intro haZero
    subst a
    have hqzero : qf 0 = 0 := by
      change quadraticRadicalQuotientFunction f hdegree hweight
        ((quadraticRadical f hdegree).mkQ 0) = 0
      rw [quadraticRadicalQuotientFunction_mkQ]
      exact hzero
    exact zero_ne_one (hqzero.symm.trans ha)
  have hderivative :=
    card_one_quadraticRadicalQuotientDerivative_of_ne_zero
      f hdegree hweight a haNonzero
  have hsupport :=
    card_one_quadraticRadicalQuotientFunction f hdegree hweight
  have htranslated :
      ((Finset.univ : Finset Q).filter fun x ↦ qf (x + a) = 1).card = 6 := by
    rw [card_one_translate_add]
    simpa only [Q, qf] using hsupport
  have hidentity := card_one_add_add_two_mul_card_one_inter
    qf (fun x ↦ qf (x + a))
  change
    ((Finset.univ : Finset Q).filter fun x ↦
        qf x + qf (x + a) = 1).card = 8 at hderivative
  change ((Finset.univ : Finset Q).filter fun x ↦ qf x = 1).card = 6
    at hsupport
  rw [hderivative, hsupport, htranslated] at hidentity
  change
    ((Finset.univ : Finset Q).filter fun x ↦
      qf x = 1 ∧ qf (x + a) = 1).card = 2
  omega

theorem exists_transverse_quadraticRadicalQuotientPlanes
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (hzero : f 0 = 0) :
    ∃ E F : Submodule FABL.𝔽₂
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree),
      Module.finrank FABL.𝔽₂ E = 2 ∧
      Module.finrank FABL.𝔽₂ F = 2 ∧
      E ⊓ F = ⊥ ∧
      ∀ q,
        quadraticRadicalQuotientFunction f hdegree hweight q = 1 ↔
          q ≠ 0 ∧ (q ∈ E ∨ q ∈ F) := by
  classical
  let Q := FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree
  let qf : Q → FABL.𝔽₂ :=
    quadraticRadicalQuotientFunction f hdegree hweight
  have hqzero : qf 0 = 0 := by
    change quadraticRadicalQuotientFunction f hdegree hweight
      ((quadraticRadical f hdegree).mkQ 0) = 0
    rw [quadraticRadicalQuotientFunction_mkQ]
    exact hzero
  have hsupport : (binaryOneSupport qf).card = 6 := by
    simpa only [binaryOneSupport] using
      card_one_quadraticRadicalQuotientFunction f hdegree hweight
  have hneighbors : ∀ q, qf q = 1 →
      (binarySupportNeighbors qf q).card = 2 := by
    intro q hq
    have h := card_quadraticRadicalQuotient_support_neighbors
      f hdegree hweight hzero q hq
    simpa only [binarySupportNeighbors, binaryOneSupport,
      Finset.filter_filter, and_assoc] using h
  simpa only [Q, qf] using
    exists_transverse_binaryPlanes_of_six_support
      qf hqzero hsupport hneighbors

theorem exists_transverse_translated_quadraticRadicalQuotientPlanes
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (q₀ : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (hq₀ : quadraticRadicalQuotientFunction f hdegree hweight q₀ = 0) :
    ∃ E F : Submodule FABL.𝔽₂
        (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree),
      Module.finrank FABL.𝔽₂ E = 2 ∧
      Module.finrank FABL.𝔽₂ F = 2 ∧
      E ⊓ F = ⊥ ∧
      ∀ q,
        quadraticRadicalQuotientFunction f hdegree hweight (q + q₀) = 1 ↔
          q ≠ 0 ∧ (q ∈ E ∨ q ∈ F) := by
  classical
  let Q := FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree
  let qf : Q → FABL.𝔽₂ :=
    quadraticRadicalQuotientFunction f hdegree hweight
  let g : Q → FABL.𝔽₂ := fun q ↦ qf (q + q₀)
  have hgzero : g 0 = 0 := by
    simpa only [g, zero_add, qf] using hq₀
  have hqfSupport : (binaryOneSupport qf).card = 6 := by
    simpa only [binaryOneSupport, qf, Q] using
      card_one_quadraticRadicalQuotientFunction f hdegree hweight
  have hgSupport : (binaryOneSupport g).card = 6 := by
    have htranslate := card_one_translate_add qf q₀
    simpa only [binaryOneSupport, g] using htranslate.trans hqfSupport
  have hgDerivative : ∀ a ≠ 0,
      ((Finset.univ : Finset Q).filter fun x ↦
        g x + g (x + a) = 1).card = 8 := by
    intro a ha
    let d : Q → FABL.𝔽₂ := fun x ↦ qf x + qf (x + a)
    have hd := card_one_quadraticRadicalQuotientDerivative_of_ne_zero
      f hdegree hweight a ha
    have htranslate := card_one_translate_add d q₀
    have htranslatedDerivative :
        ((Finset.univ : Finset Q).filter fun x ↦
          d (x + q₀) = 1).card = 8 := by
      exact htranslate.trans hd
    simpa only [g, d, add_assoc, add_left_comm, add_comm] using
      htranslatedDerivative
  have hgNeighbors : ∀ a, g a = 1 →
      (binarySupportNeighbors g a).card = 2 := by
    exact fun a ha ↦ card_binarySupportNeighbors_eq_two_of_six_support
      g hgzero hgSupport hgDerivative a ha
  simpa only [Q, qf, g] using
    exists_transverse_binaryPlanes_of_six_support
      g hgzero hgSupport hgNeighbors

theorem exists_weightTwelveSubmodulePair_over_zeroCoset
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (q₀ : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (hq₀ : quadraticRadicalQuotientFunction f hdegree hweight q₀ = 0) :
    ∃ u : FABL.F₂Cube 5,
      ∃ H K : Submodule FABL.𝔽₂ (FABL.F₂Cube 5),
        (quadraticRadical f hdegree).mkQ u = q₀ ∧
        Module.finrank FABL.𝔽₂ H = 3 ∧
        Module.finrank FABL.𝔽₂ K = 3 ∧
        H ⊓ K = quadraticRadical f hdegree ∧
        f = binaryAffineFlatIndicator (FABL.binaryAffineSubspace H u) +
          binaryAffineFlatIndicator (FABL.binaryAffineSubspace K u) := by
  classical
  let R := quadraticRadical f hdegree
  obtain ⟨E, F, hErank, hFrank, hEF, hquotientSupport⟩ :=
    exists_transverse_translated_quadraticRadicalQuotientPlanes
      f hdegree hweight q₀ hq₀
  obtain ⟨u, hu⟩ := R.mkQ_surjective q₀
  let H := Submodule.comap R.mkQ E
  let K := Submodule.comap R.mkQ F
  have hRrank : Module.finrank FABL.𝔽₂ R = 1 :=
    finrank_quadraticRadical_eq_one_of_weight_eq_twelve
      f hdegree hweight
  have hHrank : Module.finrank FABL.𝔽₂ H = 3 := by
    change Module.finrank FABL.𝔽₂ (Submodule.comap R.mkQ E) = 3
    rw [finrank_comap_mkQ_eq_add R E, hRrank, hErank]
  have hKrank : Module.finrank FABL.𝔽₂ K = 3 := by
    change Module.finrank FABL.𝔽₂ (Submodule.comap R.mkQ F) = 3
    rw [finrank_comap_mkQ_eq_add R F, hRrank, hFrank]
  have hHK : H ⊓ K = R := by
    change Submodule.comap R.mkQ E ⊓ Submodule.comap R.mkQ F = R
    rw [← Submodule.comap_inf, hEF,
      Submodule.comap_bot, Submodule.ker_mkQ]
  refine ⟨u, H, K, hu, hHrank, hKrank, hHK, ?_⟩
  funext x
  let q : FABL.F₂Cube 5 ⧸ R := R.mkQ x + q₀
  have hsupportX := hquotientSupport q
  have hqarg : q + q₀ = R.mkQ x := by
    dsimp only [q]
    calc
      (R.mkQ x + q₀) + q₀ = R.mkQ x + (q₀ + q₀) := by abel
      _ = R.mkQ x := by rw [ZModModule.add_self, add_zero]
  rw [hqarg, quadraticRadicalQuotientFunction_mkQ] at hsupportX
  have hxH : x ∈ FABL.binaryAffineSubspace H u ↔ q ∈ E := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    change R.mkQ (x + u) ∈ E ↔ q ∈ E
    rw [map_add, hu]
  have hxK : x ∈ FABL.binaryAffineSubspace K u ↔ q ∈ F := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    change R.mkQ (x + u) ∈ F ↔ q ∈ F
    rw [map_add, hu]
  by_cases hxA : x ∈ FABL.binaryAffineSubspace H u
  · by_cases hxB : x ∈ FABL.binaryAffineSubspace K u
    · have hqInf : q ∈ E ⊓ F := ⟨hxH.mp hxA, hxK.mp hxB⟩
      have hqzero : q = 0 := by
        rw [hEF, Submodule.mem_bot] at hqInf
        exact hqInf
      have hfx : f x = 0 := by
        by_contra hfx0
        have hfx1 : f x = 1 := Fin.eq_one_of_ne_zero _ hfx0
        exact (hsupportX.mp hfx1).1 hqzero
      simp [Pi.add_apply, binaryAffineFlatIndicator, hxA, hxB, hfx]
    · have hqE : q ∈ E := hxH.mp hxA
      have hqzero : q ≠ 0 := by
        intro hq
        apply hxB
        apply hxK.mpr
        rw [hq]
        exact F.zero_mem
      have hfx : f x = 1 :=
        hsupportX.mpr ⟨hqzero, Or.inl hqE⟩
      simp [Pi.add_apply, binaryAffineFlatIndicator, hxA, hxB, hfx]
  · by_cases hxB : x ∈ FABL.binaryAffineSubspace K u
    · have hqF : q ∈ F := hxK.mp hxB
      have hqzero : q ≠ 0 := by
        intro hq
        apply hxA
        apply hxH.mpr
        rw [hq]
        exact E.zero_mem
      have hfx : f x = 1 :=
        hsupportX.mpr ⟨hqzero, Or.inr hqF⟩
      simp [Pi.add_apply, binaryAffineFlatIndicator, hxA, hxB, hfx]
    · have hfx : f x = 0 := by
        by_contra hfx0
        have hfx1 : f x = 1 := Fin.eq_one_of_ne_zero _ hfx0
        rcases (hsupportX.mp hfx1).2 with hqE | hqF
        · exact hxA (hxH.mpr hqE)
        · exact hxB (hxK.mpr hqF)
      simp [Pi.add_apply, binaryAffineFlatIndicator, hxA, hxB, hfx]

noncomputable def quadraticRadicalCosetRepresentative
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree) :
    FABL.F₂Cube 5 :=
  Classical.choose ((quadraticRadical f hdegree).mkQ_surjective q)

@[simp] theorem quadraticRadicalCosetRepresentative_mkQ
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree) :
    (quadraticRadical f hdegree).mkQ
        (quadraticRadicalCosetRepresentative f hdegree q) = q :=
  Classical.choose_spec ((quadraticRadical f hdegree).mkQ_surjective q)

noncomputable def quadraticRadicalCoset
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5) :=
  FABL.binaryAffineSubspace (quadraticRadical f hdegree)
    (quadraticRadicalCosetRepresentative f hdegree q)

@[simp] theorem mem_quadraticRadicalCoset_iff_mkQ_eq
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (x : FABL.F₂Cube 5) :
    x ∈ quadraticRadicalCoset f hdegree q ↔
      (quadraticRadical f hdegree).mkQ x = q := by
  let R := quadraticRadical f hdegree
  let u := quadraticRadicalCosetRepresentative f hdegree q
  have hu : R.mkQ u = q :=
    quadraticRadicalCosetRepresentative_mkQ f hdegree q
  rw [quadraticRadicalCoset,
    FABL.mem_binaryAffineSubspace_iff_add_mem]
  constructor
  · intro hx
    have hker : R.mkQ (x + u) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hx
    rw [map_add, hu, add_eq_zero_iff_eq_neg,
      ZModModule.neg_eq_self] at hker
    exact hker
  · intro hx
    have hker : R.mkQ (x + u) = 0 := by
      rw [map_add, hu, hx, ZModModule.add_self]
    have hmemKer : x + u ∈ LinearMap.ker R.mkQ :=
      LinearMap.mem_ker.mpr hker
    simpa only [Submodule.ker_mkQ] using hmemKer

theorem quadraticRadicalCoset_injective
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    Function.Injective (quadraticRadicalCoset f hdegree) := by
  intro q r hqr
  let u := quadraticRadicalCosetRepresentative f hdegree q
  have huQ : u ∈ quadraticRadicalCoset f hdegree q := by
    rw [mem_quadraticRadicalCoset_iff_mkQ_eq]
    exact quadraticRadicalCosetRepresentative_mkQ f hdegree q
  have huR : u ∈ quadraticRadicalCoset f hdegree r := by
    rw [← hqr]
    exact huQ
  have hmkQ := (mem_quadraticRadicalCoset_iff_mkQ_eq
    f hdegree r u).mp huR
  exact (quadraticRadicalCosetRepresentative_mkQ
    f hdegree q).symm.trans hmkQ

theorem quadraticRadicalCoset_eq_binaryAffineSubspace_of_mkQ_eq
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (u : FABL.F₂Cube 5)
    (hu : (quadraticRadical f hdegree).mkQ u = q) :
    quadraticRadicalCoset f hdegree q =
      FABL.binaryAffineSubspace (quadraticRadical f hdegree) u := by
  have huLeft : u ∈ quadraticRadicalCoset f hdegree q :=
    (mem_quadraticRadicalCoset_iff_mkQ_eq f hdegree q u).mpr hu
  have huRight : u ∈ FABL.binaryAffineSubspace
      (quadraticRadical f hdegree) u :=
    AffineSubspace.self_mem_mk' u (quadraticRadical f hdegree)
  apply (AffineSubspace.eq_iff_direction_eq_of_mem huLeft huRight).2
  rw [quadraticRadicalCoset, FABL.binaryAffineSubspace_direction,
    FABL.binaryAffineSubspace_direction]

noncomputable def zeroQuadraticRadicalCosets
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    Finset (FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree) := by
  classical
  exact Finset.univ.filter fun q ↦
    quadraticRadicalQuotientFunction f hdegree hweight q = 0

noncomputable def weightTwelveZeroRadicalLines
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)) := by
  classical
  exact (zeroQuadraticRadicalCosets f hdegree hweight).image
    (quadraticRadicalCoset f hdegree)

theorem card_weightTwelveZeroRadicalLines
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    (weightTwelveZeroRadicalLines f hdegree hweight).card = 10 := by
  classical
  rw [weightTwelveZeroRadicalLines,
    Finset.card_image_of_injective _
      (quadraticRadicalCoset_injective f hdegree)]
  simpa only [zeroQuadraticRadicalCosets] using
    card_zero_quadraticRadicalQuotientFunction f hdegree hweight

theorem weightTwelveRepresentation_line_mem_zeroRadicalLines
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    {p : WeightTwelveFlatTriple 5}
    (hp : p ∈ goodWeightTwelveFlatTriples 5)
    (hrepresentation : weightTwelveRepresentationWord p = f) :
    p.1 ∈ weightTwelveZeroRadicalLines f hdegree hweight := by
  classical
  have hdata := goodWeightTwelveFlatTriple_geometry hp
  obtain ⟨u, hu⟩ :=
    (AffineSubspace.nonempty_iff_ne_bot p.1).2 hdata.1
  let q := (quadraticRadical f hdegree).mkQ u
  have hqzero :
      quadraticRadicalQuotientFunction f hdegree hweight q = 0 := by
    change quadraticRadicalQuotientFunction f hdegree hweight
      ((quadraticRadical f hdegree).mkQ u) = 0
    rw [quadraticRadicalQuotientFunction_mkQ]
    exact goodWeightTwelveFlatTriple_line_value_eq_zero
      f hp hrepresentation u hu
  have huCoset : u ∈ quadraticRadicalCoset f hdegree q := by
    rw [mem_quadraticRadicalCoset_iff_mkQ_eq]
  have hlineEq : p.1 = quadraticRadicalCoset f hdegree q := by
    apply (AffineSubspace.eq_iff_direction_eq_of_mem hu huCoset).2
    rw [goodWeightTwelveFlatTriple_line_direction_eq_quadraticRadical_five
        f hdegree hweight hp hrepresentation,
      quadraticRadicalCoset, FABL.binaryAffineSubspace_direction]
  rw [weightTwelveZeroRadicalLines, Finset.mem_image]
  refine ⟨q, ?_, hlineEq.symm⟩
  simp only [zeroQuadraticRadicalCosets, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hqzero

theorem submodulePair_weightTwelveFlatTriple_mem_good
    (R H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (u : FABL.F₂Cube n)
    (hRrank : Module.finrank FABL.𝔽₂ R = 1)
    (hHrank : Module.finrank FABL.𝔽₂ H = 3)
    (hKrank : Module.finrank FABL.𝔽₂ K = 3)
    (hHK : H ⊓ K = R) :
    (FABL.binaryAffineSubspace R u,
        (FABL.binaryAffineSubspace H u,
          FABL.binaryAffineSubspace K u)) ∈
      goodWeightTwelveFlatTriples n := by
  classical
  have hLmem : FABL.binaryAffineSubspace R u ∈
      binaryAffineFlats 1 n :=
    binaryAffineSubspace_mem_binaryAffineFlats R u
      ((mem_binaryLinearSubspaces R).mpr hRrank)
  have hAmem : FABL.binaryAffineSubspace H u ∈
      binaryAffineFlats 3 n :=
    binaryAffineSubspace_mem_binaryAffineFlats H u
      ((mem_binaryLinearSubspaces H).mpr hHrank)
  have hBmem : FABL.binaryAffineSubspace K u ∈
      binaryAffineFlats 3 n :=
    binaryAffineSubspace_mem_binaryAffineFlats K u
      ((mem_binaryLinearSubspaces K).mpr hKrank)
  have hRleH : R ≤ H := by
    rw [← hHK]
    exact inf_le_left
  have hRleK : R ≤ K := by
    rw [← hHK]
    exact inf_le_right
  have hLA : FABL.binaryAffineSubspace R u ≤
      FABL.binaryAffineSubspace H u := by
    intro x hx
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hx ⊢
    exact hRleH hx
  have hLB : FABL.binaryAffineSubspace R u ≤
      FABL.binaryAffineSubspace K u := by
    intro x hx
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hx ⊢
    exact hRleK hx
  rw [show goodWeightTwelveFlatTriples n =
      (weightTwelveFlatTriples n).filter (fun p ↦
        p.2.1.direction ⊓ p.2.2.direction = p.1.direction) by rfl]
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · rw [show weightTwelveFlatTriples n =
        (((binaryAffineFlats 1 n).product
          ((binaryAffineFlats 3 n).product (binaryAffineFlats 3 n))).filter
            fun p ↦ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2) by rfl]
    refine Finset.mem_filter.mpr ⟨?_, ⟨hLA, hLB⟩⟩
    exact Finset.mem_product.mpr
      ⟨hLmem, Finset.mem_product.mpr ⟨hAmem, hBmem⟩⟩
  · simpa only [FABL.binaryAffineSubspace_direction] using hHK

theorem exists_exactly_two_weightTwelveRepresentations_over_zeroCoset
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (q : FABL.F₂Cube 5 ⧸ quadraticRadical f hdegree)
    (hq : quadraticRadicalQuotientFunction f hdegree hweight q = 0) :
    ∃ p₁ p₂ : WeightTwelveFlatTriple 5,
      p₁ ≠ p₂ ∧
      p₁ ∈ goodWeightTwelveFlatTriples 5 ∧
      weightTwelveRepresentationWord p₁ = f ∧
      p₁.1 = quadraticRadicalCoset f hdegree q ∧
      p₂ ∈ goodWeightTwelveFlatTriples 5 ∧
      weightTwelveRepresentationWord p₂ = f ∧
      p₂.1 = quadraticRadicalCoset f hdegree q ∧
      ∀ p : WeightTwelveFlatTriple 5,
        p ∈ goodWeightTwelveFlatTriples 5 →
        weightTwelveRepresentationWord p = f →
        p.1 = quadraticRadicalCoset f hdegree q →
        p = p₁ ∨ p = p₂ := by
  classical
  let R := quadraticRadical f hdegree
  obtain ⟨u, H, K, hu, hHrank, hKrank, hHK, hrepresentation⟩ :=
    exists_weightTwelveSubmodulePair_over_zeroCoset
      f hdegree hweight q hq
  let L := quadraticRadicalCoset f hdegree q
  let A := FABL.binaryAffineSubspace H u
  let B := FABL.binaryAffineSubspace K u
  let p₁ : WeightTwelveFlatTriple 5 := (L, (A, B))
  let p₂ : WeightTwelveFlatTriple 5 := (L, (B, A))
  have hRrank : Module.finrank FABL.𝔽₂ R = 1 :=
    finrank_quadraticRadical_eq_one_of_weight_eq_twelve
      f hdegree hweight
  have hline : L = FABL.binaryAffineSubspace R u :=
    quadraticRadicalCoset_eq_binaryAffineSubspace_of_mkQ_eq
      f hdegree q u hu
  have hKH : K ⊓ H = R := by
    rw [inf_comm, hHK]
  have hp₁Good : p₁ ∈ goodWeightTwelveFlatTriples 5 := by
    dsimp only [p₁, A, B]
    rw [hline]
    exact submodulePair_weightTwelveFlatTriple_mem_good
      R H K u hRrank hHrank hKrank hHK
  have hp₂Good : p₂ ∈ goodWeightTwelveFlatTriples 5 := by
    dsimp only [p₂, A, B]
    rw [hline]
    exact submodulePair_weightTwelveFlatTriple_mem_good
      R K H u hRrank hKrank hHrank hKH
  have hp₁Representation : weightTwelveRepresentationWord p₁ = f := by
    simpa only [p₁, A, B, weightTwelveRepresentationWord] using
      hrepresentation.symm
  have hp₂Representation : weightTwelveRepresentationWord p₂ = f := by
    simpa only [p₂, A, B, weightTwelveRepresentationWord, add_comm] using
      hrepresentation.symm
  have hHKne : H ≠ K := by
    intro heq
    have hintersection := hHK
    rw [heq, inf_idem] at hintersection
    have hrank := congrArg
      (fun S : Submodule FABL.𝔽₂ (FABL.F₂Cube 5) ↦
        Module.finrank FABL.𝔽₂ S) hintersection
    rw [hKrank, hRrank] at hrank
    omega
  have hABne : A ≠ B := by
    intro heq
    apply hHKne
    have hdirection := congrArg
      (fun C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5) ↦ C.direction) heq
    simpa only [A, B, FABL.binaryAffineSubspace_direction] using hdirection
  have hpne : p₁ ≠ p₂ := by
    intro heq
    apply hABne
    have hfirst := congrArg
      (fun p : WeightTwelveFlatTriple 5 ↦ p.2.1) heq
    simpa only [p₁, p₂] using hfirst
  refine ⟨p₁, p₂, hpne, hp₁Good, hp₁Representation,
    rfl, hp₂Good, hp₂Representation, rfl, ?_⟩
  intro p hpGood hpRepresentation hpLine
  have hpLine₁ : p.1 = p₁.1 := by
    simpa only [p₁, L] using hpLine
  rcases weightTwelveFlatPair_eq_or_swap_of_same_line
      f hpGood hp₁Good hpRepresentation hp₁Representation hpLine₁ with
    hsame | hswap
  · left
    apply Prod.ext
    · exact hpLine₁
    · exact Prod.ext hsame.1 hsame.2
  · right
    apply Prod.ext
    · simpa only [p₂, L] using hpLine
    · exact Prod.ext hswap.1 hswap.2

theorem card_weightTwelveRepresentations_over_zeroRadicalLine
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12)
    (L : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5))
    (hL : L ∈ weightTwelveZeroRadicalLines f hdegree hweight) :
    (((goodWeightTwelveFlatTriples 5).filter fun p ↦
        weightTwelveRepresentationWord p = f).filter fun
          p : WeightTwelveFlatTriple 5 ↦
          p.1 = L).card = 2 := by
  classical
  rw [weightTwelveZeroRadicalLines, Finset.mem_image] at hL
  obtain ⟨q, hqZero, hqLine⟩ := hL
  have hq : quadraticRadicalQuotientFunction f hdegree hweight q = 0 := by
    simpa only [zeroQuadraticRadicalCosets, Finset.mem_filter,
      Finset.mem_univ, true_and] using hqZero
  obtain ⟨p₁, p₂, hpne, hp₁Good, hp₁Representation, hp₁Line,
      hp₂Good, hp₂Representation, hp₂Line, hunique⟩ :=
    exists_exactly_two_weightTwelveRepresentations_over_zeroCoset
      f hdegree hweight q hq
  have hp₁LineL : p₁.1 = L := hp₁Line.trans hqLine
  have hp₂LineL : p₂.1 = L := hp₂Line.trans hqLine
  have hfiber :
      ((goodWeightTwelveFlatTriples 5).filter fun p ↦
        weightTwelveRepresentationWord p = f).filter (fun p ↦ p.1 = L) =
        {p₁, p₂} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hpGood, hpRepresentation⟩, hpLine⟩
      exact hunique p hpGood hpRepresentation
        (hpLine.trans hqLine.symm)
    · intro hp
      rcases hp with rfl | rfl
      · exact ⟨⟨hp₁Good, hp₁Representation⟩, hp₁LineL⟩
      · exact ⟨⟨hp₂Good, hp₂Representation⟩, hp₂LineL⟩
  rw [hfiber, Finset.card_pair hpne]

theorem card_weightTwelveRepresentationFiber_eq_twenty_five
    (f : BooleanFunction 5)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hweight : hammingWeight f = 12) :
    ((goodWeightTwelveFlatTriples 5).filter fun p ↦
      weightTwelveRepresentationWord p = f).card = 20 := by
  classical
  let representations := (goodWeightTwelveFlatTriples 5).filter fun p ↦
    weightTwelveRepresentationWord p = f
  let lines := weightTwelveZeroRadicalLines f hdegree hweight
  have hmaps : (representations : Set (WeightTwelveFlatTriple 5)).MapsTo
      (fun p ↦ p.1) lines := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact weightTwelveRepresentation_line_mem_zeroRadicalLines
      f hdegree hweight hpData.1 hpData.2
  calc
    representations.card =
        ∑ L ∈ lines,
          (representations.filter fun p ↦ p.1 = L).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = lines.card * 2 := by
      apply Finset.sum_const_nat
      intro L hL
      exact card_weightTwelveRepresentations_over_zeroRadicalLine
        f hdegree hweight L hL
    _ = 20 := by
      rw [card_weightTwelveZeroRadicalLines f hdegree hweight]

set_option maxRecDepth 2000 in
private theorem card_weightTwelveRepresentationFiber_eq_twenty_of_mem
    (f : BooleanFunction 5)
    (hf : f ∈ orderTwoWeightTwelveDualWords 5) :
    ((goodWeightTwelveFlatTriples 5).filter fun p ↦
      weightTwelveRepresentationWord p = f).card = 20 := by
  have hfData : f ∈ reedMuller 2 5 ∧ hammingWeight f = 12 := by
    simpa only [orderTwoWeightTwelveDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hf
  have hdegree : FABL.functionAlgebraicDegree f ≤ 2 := by
    simpa only [mem_reedMuller_iff] using hfData.1
  exact card_weightTwelveRepresentationFiber_eq_twenty_five
    f hdegree hfData.2

set_option maxRecDepth 2000 in
private theorem card_weightTwelveRepresentationFiber_eq_zero_of_not_mem
    {n : ℕ} (f : BooleanFunction n)
    (hf : f ∉ orderTwoWeightTwelveDualWords n) :
    ((goodWeightTwelveFlatTriples n).filter fun p ↦
      weightTwelveRepresentationWord p = f).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hpGood hpRepresentation
  apply hf
  exact hpRepresentation ▸
    weightTwelveRepresentationWord_mem_dualWords hpGood

set_option maxRecDepth 2000 in
theorem hasWeightTwelveFlatPairClassification_five :
    HasWeightTwelveFlatPairClassification 5 := by
  intro f
  by_cases hf : f ∈ orderTwoWeightTwelveDualWords 5
  · rw [if_pos hf]
    exact card_weightTwelveRepresentationFiber_eq_twenty_of_mem f hf
  · rw [if_neg hf]
    exact card_weightTwelveRepresentationFiber_eq_zero_of_not_mem f hf

theorem mem_goodWeightTwelveFlatTriples_iff_geometry
    (p : WeightTwelveFlatTriple n) :
    p ∈ goodWeightTwelveFlatTriples n ↔
      p.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.1.direction = 1 ∧
        p.2.1 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.1.direction = 3 ∧
        p.2.2 ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ p.2.2.direction = 3 ∧
        p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
        p.2.1.direction ⊓ p.2.2.direction = p.1.direction := by
  classical
  constructor
  · exact goodWeightTwelveFlatTriple_geometry
  · intro h
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · simp only [binaryAffineFlats, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨h.1, h.2.1⟩
        · apply Finset.mem_product.mpr
          constructor
          · simp only [binaryAffineFlats, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨h.2.2.1, h.2.2.2.1⟩
          · simp only [binaryAffineFlats, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩
      · exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩
    · exact h.2.2.2.2.2.2.2.2

private theorem exists_superSubmodule_finrank_eq
    {X : Type*} [AddCommGroup X] [Module FABL.𝔽₂ X]
    [FiniteDimensional FABL.𝔽₂ X]
    (E : Submodule FABL.𝔽₂ X) (k : ℕ)
    (hE : Module.finrank FABL.𝔽₂ E ≤ k)
    (hk : k ≤ Module.finrank FABL.𝔽₂ X) :
    ∃ H : Submodule FABL.𝔽₂ X,
      E ≤ H ∧ Module.finrank FABL.𝔽₂ H = k := by
  induction k generalizing E with
  | zero =>
      exact ⟨E, le_rfl, Nat.eq_zero_of_le_zero hE⟩
  | succ k ih =>
      by_cases hErank : Module.finrank FABL.𝔽₂ E = k + 1
      · exact ⟨E, le_rfl, hErank⟩
      · have hErankLe : Module.finrank FABL.𝔽₂ E ≤ k := by omega
        have hkLe : k ≤ Module.finrank FABL.𝔽₂ X := by omega
        obtain ⟨H, hEH, hHrank⟩ := ih E hErankLe hkLe
        have hHlt : Module.finrank FABL.𝔽₂ H <
            Module.finrank FABL.𝔽₂ X := by omega
        obtain ⟨v, hv⟩ := H.exists_of_finrank_lt hHlt
        have hvNotMem : v ∉ H := by
          intro hvMem
          exact hv 1 one_ne_zero (by simpa only [one_smul] using hvMem)
        refine ⟨H ⊔ FABL.𝔽₂ ∙ v, hEH.trans le_sup_left, ?_⟩
        rw [Submodule.finrank_sup_span_singleton hvNotMem, hHrank]

private noncomputable def weightTwelveFiveFlatLinearEmbedding
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) :
    FABL.F₂Cube 5 →ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
  H.subtype.comp e.toLinearMap

private theorem weightTwelveFiveFlatLinearEmbedding_injective
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) :
    Function.Injective (weightTwelveFiveFlatLinearEmbedding H e) :=
  Subtype.val_injective.comp e.injective

private noncomputable def weightTwelveFiveFlatEmbedding
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) :
    FABL.F₂Cube 5 →ᵃ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun x := u + weightTwelveFiveFlatLinearEmbedding H e x
  linear := weightTwelveFiveFlatLinearEmbedding H e
  map_vadd' x v := by
    change u + weightTwelveFiveFlatLinearEmbedding H e (v + x) =
      weightTwelveFiveFlatLinearEmbedding H e v +
        (u + weightTwelveFiveFlatLinearEmbedding H e x)
    rw [map_add]
    abel

private theorem weightTwelveFiveFlatEmbedding_injective
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) :
    Function.Injective (weightTwelveFiveFlatEmbedding u H e) := by
  intro x y hxy
  apply weightTwelveFiveFlatLinearEmbedding_injective H e
  exact add_left_cancel hxy

private noncomputable def weightTwelveFiveFlatProjection
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) :
    FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube 5 where
  toFun x := (weightTwelveFiveFlatLinearEmbedding H e).leftInverse (x + u)
  linear := (weightTwelveFiveFlatLinearEmbedding H e).leftInverse
  map_vadd' x v := by
    change (weightTwelveFiveFlatLinearEmbedding H e).leftInverse
        (v + x + u) =
      (weightTwelveFiveFlatLinearEmbedding H e).leftInverse v +
        (weightTwelveFiveFlatLinearEmbedding H e).leftInverse (x + u)
    rw [show v + x + u = v + (x + u) by abel, map_add]

private theorem weightTwelveFiveFlatProjection_embedding
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (x : FABL.F₂Cube 5) :
    weightTwelveFiveFlatProjection u H e
        (weightTwelveFiveFlatEmbedding u H e x) = x := by
  have hker : LinearMap.ker (weightTwelveFiveFlatLinearEmbedding H e) = ⊥ :=
    LinearMap.ker_eq_bot.mpr
      (weightTwelveFiveFlatLinearEmbedding_injective H e)
  change (weightTwelveFiveFlatLinearEmbedding H e).leftInverse
      ((u + weightTwelveFiveFlatLinearEmbedding H e x) + u) = x
  rw [show (u + weightTwelveFiveFlatLinearEmbedding H e x) + u =
    weightTwelveFiveFlatLinearEmbedding H e x by
      rw [add_assoc, add_comm
        (weightTwelveFiveFlatLinearEmbedding H e x) u,
        ← add_assoc, ZModModule.add_self, zero_add]]
  exact LinearMap.leftInverse_apply_of_inj hker x

private theorem weightTwelveFiveFlatEmbedding_projection_of_mem_range
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (x : FABL.F₂Cube n)
    (hx : x ∈ (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map
      (weightTwelveFiveFlatEmbedding u H e)) :
    weightTwelveFiveFlatEmbedding u H e
        (weightTwelveFiveFlatProjection u H e x) = x := by
  rw [AffineSubspace.mem_map] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  rw [weightTwelveFiveFlatProjection_embedding]

private theorem functionAlgebraicDegree_affineMap_coordinate_le_one_of_dims
    {m n : ℕ} (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m)
    (i : Fin m) :
    FABL.functionAlgebraicDegree (fun x ↦ L x i) ≤ 1 := by
  have hlinear : FABL.IsF₂Linear (fun x ↦ L.linear x i) := by
    intro x y
    exact congrArg (fun z ↦ z i) (L.linear.map_add x y)
  obtain ⟨a, ha⟩ := (FABL.isF₂Linear_iff_exists_dotProduct _).mp hlinear
  have hcoordinate : (fun x ↦ L x i) =
      FABL.affineFunction (L 0 i) a := by
    funext x
    have hdecomp : L x = L.linear x + L 0 := by
      simpa using congrFun (AffineMap.decomp L) x
    calc
      L x i = L.linear x i + L 0 i := by
        simpa using congrArg (fun z ↦ z i) hdecomp
      _ = FABL.f₂DotProduct a x + L 0 i := by rw [ha x]
      _ = L 0 i + FABL.f₂DotProduct a x := add_comm _ _
      _ = FABL.affineFunction (L 0 i) a x := rfl
  rw [hcoordinate]
  exact FABL.functionAlgebraicDegree_affineFunction_le_one (L 0 i) a

private theorem functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card_of_dims
    {m n : ℕ} (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m)
    (S : Finset (Fin m)) :
    FABL.functionAlgebraicDegree (fun x ↦ FABL.anfMonomial S (L x)) ≤
      S.card := by
  calc
    FABL.functionAlgebraicDegree
        (fun x ↦ FABL.anfMonomial S (L x)) ≤
        ∑ i ∈ S, FABL.functionAlgebraicDegree (fun x ↦ L x i) := by
      have hfunctions : (∏ i ∈ S, (fun x ↦ L x i)) =
          (fun x ↦ FABL.anfMonomial S (L x)) := by
        funext x
        simp [FABL.anfMonomial, Finset.prod_apply]
      rw [← hfunctions]
      exact FABL.functionAlgebraicDegree_finset_prod_le S
        (fun i x ↦ L x i)
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact functionAlgebraicDegree_affineMap_coordinate_le_one_of_dims L i
    _ = S.card := by simp

private theorem functionAlgebraicDegree_comp_affineMap_le_of_dims
    {m n : ℕ} (f : BooleanFunction m)
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m) :
    FABL.functionAlgebraicDegree (f ∘ L) ≤
      FABL.functionAlgebraicDegree f := by
  classical
  let term : Finset (Fin m) → BooleanFunction n :=
    fun S x ↦ FABL.anfCoeff f S * FABL.anfMonomial S (L x)
  have hsum : f ∘ L = ∑ S, term S := by
    funext x
    simp only [Function.comp_apply, Fintype.sum_apply, term]
    exact (congrFun (FABL.anfEval_anfCoeff f) (L x)).symm
  rw [hsum]
  exact FABL.functionAlgebraicDegree_finset_sum_le Finset.univ term
    (FABL.functionAlgebraicDegree f) (by
      intro S _
      by_cases hS : FABL.anfCoeff f S = 0
      · have hterm : term S = 0 := by
          funext x
          simp [term, hS]
        rw [hterm, FABL.functionAlgebraicDegree_zero]
        exact Nat.zero_le _
      · have hSone : FABL.anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
        have hterm : term S = fun x ↦ FABL.anfMonomial S (L x) := by
          funext x
          simp [term, hSone]
        rw [hterm]
        apply (functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card_of_dims
          L S).trans
        exact (FABL.algebraicDegree_le_iff (FABL.anfCoeff f)
          (FABL.functionAlgebraicDegree f)).mp (by rfl) S hS)

private noncomputable def weightTwelveFiveFlatRestriction
    (h : BooleanFunction n) (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H) : BooleanFunction 5 :=
  h ∘ weightTwelveFiveFlatEmbedding u H e

private noncomputable def weightTwelveFiveFlatSupportEquiv
    (h : BooleanFunction n) (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (hsupport : (support h : Set (FABL.F₂Cube n)) ⊆
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map
        (weightTwelveFiveFlatEmbedding u H e)) :
    {x // x ∈ support (weightTwelveFiveFlatRestriction h u H e)} ≃
      {x // x ∈ support h} where
  toFun x := ⟨weightTwelveFiveFlatEmbedding u H e x, by
    apply (mem_support h _).mpr
    exact (mem_support (weightTwelveFiveFlatRestriction h u H e) _).mp x.2⟩
  invFun x := ⟨weightTwelveFiveFlatProjection u H e x, by
    apply (mem_support (weightTwelveFiveFlatRestriction h u H e) _).mpr
    change h (weightTwelveFiveFlatEmbedding u H e
      (weightTwelveFiveFlatProjection u H e x)) = 1
    rw [weightTwelveFiveFlatEmbedding_projection_of_mem_range
      u H e x (hsupport x.2)]
    exact (mem_support h _).mp x.2⟩
  left_inv x := Subtype.ext
    (weightTwelveFiveFlatProjection_embedding u H e x)
  right_inv x := Subtype.ext
    (weightTwelveFiveFlatEmbedding_projection_of_mem_range
      u H e x (hsupport x.2))

private theorem hammingWeight_weightTwelveFiveFlatRestriction
    (h : BooleanFunction n) (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (hsupport : (support h : Set (FABL.F₂Cube n)) ⊆
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map
        (weightTwelveFiveFlatEmbedding u H e)) :
    hammingWeight (weightTwelveFiveFlatRestriction h u H e) =
      hammingWeight h := by
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (weightTwelveFiveFlatSupportEquiv h u H e hsupport)

private theorem booleanFunctionPairing_eq_sum_support
    (q h : BooleanFunction n) :
    booleanFunctionPairing n q h = ∑ x : {x // x ∈ support h}, q x := by
  rw [booleanFunctionPairing_apply]
  calc
    (∑ x : FABL.F₂Cube n, q x * h x) =
        ∑ x ∈ support h, q x := by
      rw [support, FABL.f₂OneSupport, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : h x = 0
      · simp [hx]
      · have hxOne : h x = 1 := Fin.eq_one_of_ne_zero _ hx
        simp [hxOne]
    _ = ∑ x : {x // x ∈ support h}, q x := by
      exact Finset.sum_subtype (support h) (fun x ↦ by simp) q

private theorem booleanFunctionPairing_fiveFlatRestriction
    (h : BooleanFunction n) (q : BooleanFunction 5)
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (hsupport : (support h : Set (FABL.F₂Cube n)) ⊆
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map
        (weightTwelveFiveFlatEmbedding u H e)) :
    booleanFunctionPairing 5 q
        (weightTwelveFiveFlatRestriction h u H e) =
      booleanFunctionPairing n
        (q ∘ weightTwelveFiveFlatProjection u H e) h := by
  rw [booleanFunctionPairing_eq_sum_support,
    booleanFunctionPairing_eq_sum_support]
  exact Fintype.sum_equiv
    (weightTwelveFiveFlatSupportEquiv h u H e hsupport)
    (fun x : {x // x ∈ support
      (weightTwelveFiveFlatRestriction h u H e)} ↦ q x)
    (fun x : {x // x ∈ support h} ↦
      (q ∘ weightTwelveFiveFlatProjection u H e) x)
    (fun x ↦ by
      change q x = q (weightTwelveFiveFlatProjection u H e
        ((weightTwelveFiveFlatSupportEquiv h u H e hsupport x).1))
      change q x = q (weightTwelveFiveFlatProjection u H e
        (weightTwelveFiveFlatEmbedding u H e x))
      rw [weightTwelveFiveFlatProjection_embedding])

private theorem weightTwelveFiveFlatRestriction_mem_reedMuller_two
    (h : BooleanFunction n) (hn : 5 ≤ n)
    (hmem : h ∈ reedMuller (n - 3) n)
    (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H)
    (hsupport : (support h : Set (FABL.F₂Cube n)) ⊆
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map
        (weightTwelveFiveFlatEmbedding u H e)) :
    weightTwelveFiveFlatRestriction h u H e ∈ reedMuller 2 5 := by
  have hdual : h ∈ reedMullerDual 2 n := by
    rw [reedMullerDual_eq (r := 2) (n := n) (by omega)]
    simpa only [show n - 2 - 1 = n - 3 by omega] using hmem
  have hlocalDual : weightTwelveFiveFlatRestriction h u H e ∈
      reedMullerDual 2 5 := by
    rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff]
    intro q hq
    let Q : BooleanFunction n :=
      q ∘ weightTwelveFiveFlatProjection u H e
    have hqDegree : FABL.functionAlgebraicDegree q ≤ 2 := by
      simpa only [mem_reedMuller_iff] using hq
    have hQDegree : FABL.functionAlgebraicDegree Q ≤ 2 := by
      exact (functionAlgebraicDegree_comp_affineMap_le_of_dims q
        (weightTwelveFiveFlatProjection u H e)).trans hqDegree
    have hQ : Q ∈ reedMuller 2 n := by
      simpa only [mem_reedMuller_iff] using hQDegree
    rw [booleanFunctionPairing_fiveFlatRestriction h q u H e hsupport]
    exact hdual Q hQ
  rw [reedMullerDual_eq (r := 2) (n := 5) (by omega)] at hlocalDual
  simpa only using hlocalDual

private def weightTwelveFlatTripleMap
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (p : WeightTwelveFlatTriple m) : WeightTwelveFlatTriple n :=
  (p.1.map L, (p.2.1.map L, p.2.2.map L))

private def weightTwelveFlatTripleComap
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (p : WeightTwelveFlatTriple n) : WeightTwelveFlatTriple m :=
  (p.1.comap L, (p.2.1.comap L, p.2.2.comap L))

private theorem affineSubspaceMap_injective
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hL : Function.Injective L) :
    Function.Injective (AffineSubspace.map L) := by
  intro A B hAB
  have hcomap := congrArg (AffineSubspace.comap L) hAB
  simpa only [AffineSubspace.comap_map_eq_of_injective hL] using hcomap

private theorem weightTwelveFlatTripleMap_injective
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hL : Function.Injective L) :
    Function.Injective (weightTwelveFlatTripleMap L) := by
  intro p q hpq
  apply Prod.ext
  · apply affineSubspaceMap_injective L hL
    exact congrArg Prod.fst hpq
  · apply Prod.ext
    · apply affineSubspaceMap_injective L hL
      exact congrArg (fun r ↦ r.2.1) hpq
    · apply affineSubspaceMap_injective L hL
      exact congrArg (fun r ↦ r.2.2) hpq

private theorem finrank_direction_map_eq_of_linear_injective
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hlinear : Function.Injective L.linear)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m)) :
    Module.finrank FABL.𝔽₂ (A.map L).direction =
      Module.finrank FABL.𝔽₂ A.direction := by
  rw [AffineSubspace.map_direction, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj
    (hlinear.comp Subtype.val_injective)

private theorem weightTwelveFlatTripleMap_mem_good_iff
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hL : Function.Injective L)
    (hlinear : Function.Injective L.linear)
    (p : WeightTwelveFlatTriple m) :
    weightTwelveFlatTripleMap L p ∈ goodWeightTwelveFlatTriples n ↔
      p ∈ goodWeightTwelveFlatTriples m := by
  constructor
  · intro hpMap
    have hmapData :=
      (mem_goodWeightTwelveFlatTriples_iff_geometry
        (weightTwelveFlatTripleMap L p)).mp hpMap
    have hlineNe : p.1 ≠ ⊥ := by
      intro hbot
      apply hmapData.1
      change p.1.map L = ⊥
      rw [hbot, AffineSubspace.map_bot]
    have hfirstNe : p.2.1 ≠ ⊥ := by
      intro hbot
      apply hmapData.2.2.1
      change p.2.1.map L = ⊥
      rw [hbot, AffineSubspace.map_bot]
    have hsecondNe : p.2.2 ≠ ⊥ := by
      intro hbot
      apply hmapData.2.2.2.2.1
      change p.2.2.map L = ⊥
      rw [hbot, AffineSubspace.map_bot]
    have hlineRank : Module.finrank FABL.𝔽₂ p.1.direction = 1 := by
      rw [← finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hmapData.2.1
    have hfirstRank : Module.finrank FABL.𝔽₂ p.2.1.direction = 3 := by
      rw [← finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hmapData.2.2.2.1
    have hsecondRank : Module.finrank FABL.𝔽₂ p.2.2.direction = 3 := by
      rw [← finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hmapData.2.2.2.2.2.1
    have hlineFirst : p.1 ≤ p.2.1 := by
      intro x hx
      have hxMap : L x ∈ p.1.map L :=
        AffineSubspace.mem_map_of_mem L hx
      have hxFirstMap : L x ∈ p.2.1.map L :=
        hmapData.2.2.2.2.2.2.1 hxMap
      exact (AffineSubspace.mem_map_iff_mem_of_injective hL).mp hxFirstMap
    have hlineSecond : p.1 ≤ p.2.2 := by
      intro x hx
      have hxMap : L x ∈ p.1.map L :=
        AffineSubspace.mem_map_of_mem L hx
      have hxSecondMap : L x ∈ p.2.2.map L :=
        hmapData.2.2.2.2.2.2.2.1 hxMap
      exact (AffineSubspace.mem_map_iff_mem_of_injective hL).mp hxSecondMap
    have hmapInf := goodWeightTwelveFlatTriple_inf_eq_line hpMap
    have hmapInf' : p.2.1.map L ⊓ p.2.2.map L = p.1.map L := by
      simpa only [weightTwelveFlatTripleMap] using hmapInf
    have hinf : p.2.1 ⊓ p.2.2 = p.1 := by
      apply affineSubspaceMap_injective L hL
      rw [AffineSubspace.map_inf_eq L hL, hmapInf']
    obtain ⟨x, hxLine⟩ :=
      (AffineSubspace.nonempty_iff_ne_bot p.1).2 hlineNe
    have hxInf : x ∈ p.2.1 ⊓ p.2.2 := by
      rw [hinf]
      exact hxLine
    have hdirection : p.2.1.direction ⊓ p.2.2.direction =
        p.1.direction := by
      calc
        p.2.1.direction ⊓ p.2.2.direction =
            (p.2.1 ⊓ p.2.2).direction :=
          (AffineSubspace.direction_inf_of_mem_inf hxInf).symm
        _ = p.1.direction := congrArg AffineSubspace.direction hinf
    exact (mem_goodWeightTwelveFlatTriples_iff_geometry p).mpr
      ⟨hlineNe, hlineRank, hfirstNe, hfirstRank,
        hsecondNe, hsecondRank, hlineFirst, hlineSecond, hdirection⟩
  · intro hp
    have hpData := (mem_goodWeightTwelveFlatTriples_iff_geometry p).mp hp
    have hlineNe : p.1.map L ≠ ⊥ := by
      intro hbot
      exact hpData.1 ((AffineSubspace.map_eq_bot_iff (f := L)).mp hbot)
    have hfirstNe : p.2.1.map L ≠ ⊥ := by
      intro hbot
      exact hpData.2.2.1
        ((AffineSubspace.map_eq_bot_iff (f := L)).mp hbot)
    have hsecondNe : p.2.2.map L ≠ ⊥ := by
      intro hbot
      exact hpData.2.2.2.2.1
        ((AffineSubspace.map_eq_bot_iff (f := L)).mp hbot)
    have hlineRank : Module.finrank FABL.𝔽₂ (p.1.map L).direction = 1 := by
      rw [finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hpData.2.1
    have hfirstRank : Module.finrank FABL.𝔽₂ (p.2.1.map L).direction = 3 := by
      rw [finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hpData.2.2.2.1
    have hsecondRank : Module.finrank FABL.𝔽₂ (p.2.2.map L).direction = 3 := by
      rw [finrank_direction_map_eq_of_linear_injective L hlinear]
      exact hpData.2.2.2.2.2.1
    have hlineFirst : p.1.map L ≤ p.2.1.map L :=
      AffineSubspace.map_mono L hpData.2.2.2.2.2.2.1
    have hlineSecond : p.1.map L ≤ p.2.2.map L :=
      AffineSubspace.map_mono L hpData.2.2.2.2.2.2.2.1
    have hsourceInf := goodWeightTwelveFlatTriple_inf_eq_line hp
    have htargetInf : p.2.1.map L ⊓ p.2.2.map L = p.1.map L := by
      rw [← AffineSubspace.map_inf_eq L hL, hsourceInf]
    obtain ⟨x, hxLine⟩ :=
      (AffineSubspace.nonempty_iff_ne_bot p.1).2 hpData.1
    have hxTargetInf : L x ∈ p.2.1.map L ⊓ p.2.2.map L := by
      rw [htargetInf]
      exact AffineSubspace.mem_map_of_mem L hxLine
    have hdirection : (p.2.1.map L).direction ⊓
        (p.2.2.map L).direction = (p.1.map L).direction := by
      calc
        (p.2.1.map L).direction ⊓ (p.2.2.map L).direction =
            (p.2.1.map L ⊓ p.2.2.map L).direction :=
          (AffineSubspace.direction_inf_of_mem_inf hxTargetInf).symm
        _ = (p.1.map L).direction :=
          congrArg AffineSubspace.direction htargetInf
    exact (mem_goodWeightTwelveFlatTriples_iff_geometry
      (weightTwelveFlatTripleMap L p)).mpr
        ⟨hlineNe, hlineRank, hfirstNe, hfirstRank,
          hsecondNe, hsecondRank, hlineFirst, hlineSecond, hdirection⟩

private theorem binaryAffineFlatIndicator_map_apply
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hL : Function.Injective L)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m))
    (x : FABL.F₂Cube m) :
    binaryAffineFlatIndicator (A.map L) (L x) =
      binaryAffineFlatIndicator A x := by
  classical
  simp only [binaryAffineFlatIndicator,
    AffineSubspace.mem_map_iff_mem_of_injective hL]

private theorem weightTwelveRepresentationWord_map_apply
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hL : Function.Injective L)
    (p : WeightTwelveFlatTriple m) (x : FABL.F₂Cube m) :
    weightTwelveRepresentationWord (weightTwelveFlatTripleMap L p) (L x) =
      weightTwelveRepresentationWord p x := by
  simp only [weightTwelveRepresentationWord, weightTwelveFlatTripleMap,
    Pi.add_apply]
  rw [binaryAffineFlatIndicator_map_apply L hL,
    binaryAffineFlatIndicator_map_apply L hL]

private theorem affineSubspace_map_comap_eq_of_le_range
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ≤ (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m)).map L) :
    (A.comap L).map L = A := by
  apply le_antisymm (AffineSubspace.map_comap_le L A)
  intro x hx
  have hxRange := hA hx
  rw [AffineSubspace.mem_map] at hxRange
  obtain ⟨y, _hy, rfl⟩ := hxRange
  exact AffineSubspace.mem_map_of_mem L
    (show y ∈ A.comap L from hx)

private theorem weightTwelveFlatTriple_map_comap_eq_of_le_range
    {m n : ℕ} (L : FABL.F₂Cube m →ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (p : WeightTwelveFlatTriple n)
    (hline : p.1 ≤
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m)).map L)
    (hfirst : p.2.1 ≤
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m)).map L)
    (hsecond : p.2.2 ≤
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube m)).map L) :
    weightTwelveFlatTripleMap L (weightTwelveFlatTripleComap L p) = p := by
  apply Prod.ext
  · exact affineSubspace_map_comap_eq_of_le_range L p.1 hline
  · apply Prod.ext
    · exact affineSubspace_map_comap_eq_of_le_range L p.2.1 hfirst
    · exact affineSubspace_map_comap_eq_of_le_range L p.2.2 hsecond

private theorem card_first_sdiff_line_eq_six
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    (binaryAffineFlatPoints p.2.1 \ binaryAffineFlatPoints p.1).card = 6 := by
  have hpData := goodWeightTwelveFlatTriple_geometry hp
  have hsubset : binaryAffineFlatPoints p.1 ⊆
      binaryAffineFlatPoints p.2.1 := by
    intro x hx
    exact (mem_binaryAffineFlatPoints p.2.1 x).mpr
      (hpData.2.2.2.2.2.2.1
        ((mem_binaryAffineFlatPoints p.1 x).mp hx))
  rw [Finset.card_sdiff_of_subset hsubset,
    card_binaryAffineFlatPoints p.2.1 hpData.2.2.1,
    card_binaryAffineFlatPoints p.1 hpData.1,
    hpData.2.2.2.1, hpData.2.1]
  norm_num

private theorem card_second_sdiff_line_eq_six
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n) :
    (binaryAffineFlatPoints p.2.2 \ binaryAffineFlatPoints p.1).card = 6 := by
  have hpData := goodWeightTwelveFlatTriple_geometry hp
  have hsubset : binaryAffineFlatPoints p.1 ⊆
      binaryAffineFlatPoints p.2.2 := by
    intro x hx
    exact (mem_binaryAffineFlatPoints p.2.2 x).mpr
      (hpData.2.2.2.2.2.2.2.1
        ((mem_binaryAffineFlatPoints p.1 x).mp hx))
  rw [Finset.card_sdiff_of_subset hsubset,
    card_binaryAffineFlatPoints p.2.2 hpData.2.2.2.2.1,
    card_binaryAffineFlatPoints p.1 hpData.1,
    hpData.2.2.2.2.2.1, hpData.2.1]
  norm_num

private theorem affineThreeFlat_le_of_six_points_subset
    (F A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (_hFne : F ≠ ⊥)
    (hFrank : Module.finrank FABL.𝔽₂ F.direction = 3)
    (s : Finset (FABL.F₂Cube n)) (hscard : s.card = 6)
    (hsF : ∀ x ∈ s, x ∈ F) (hsA : ∀ x ∈ s, x ∈ A) :
    F ≤ A := by
  have hsNonempty : s.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨x, hx⟩ := hsNonempty
  have hxInf : x ∈ F ⊓ A :=
    (AffineSubspace.mem_inf_iff x F A).mpr ⟨hsF x hx, hsA x hx⟩
  have hInfNe : F ⊓ A ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨x, hxInf⟩
  have hsInf : s ⊆ binaryAffineFlatPoints (F ⊓ A) := by
    intro y hy
    exact (mem_binaryAffineFlatPoints (F ⊓ A) y).mpr
      ((AffineSubspace.mem_inf_iff y F A).mpr ⟨hsF y hy, hsA y hy⟩)
  have hcardInf := card_binaryAffineFlatPoints (F ⊓ A) hInfNe
  have hlower : 6 ≤ 2 ^ Module.finrank FABL.𝔽₂ (F ⊓ A).direction := by
    rw [← hcardInf, ← hscard]
    exact Finset.card_mono hsInf
  have hdirectionLe : (F ⊓ A).direction ≤ F.direction :=
    AffineSubspace.direction_le inf_le_left
  have hrankUpper : Module.finrank FABL.𝔽₂ (F ⊓ A).direction ≤ 3 := by
    rw [← hFrank]
    exact Submodule.finrank_mono hdirectionLe
  have hrankInf : Module.finrank FABL.𝔽₂ (F ⊓ A).direction = 3 := by
    interval_cases h : Module.finrank FABL.𝔽₂ (F ⊓ A).direction
    all_goals norm_num [h] at hlower
    all_goals omega
  have hinfEq : F ⊓ A = F := by
    apply (AffineSubspace.eq_iff_direction_eq_of_mem hxInf (hsF x hx)).2
    apply Submodule.eq_of_le_of_finrank_eq hdirectionLe
    rw [hrankInf, hFrank]
  rw [← hinfEq]
  exact inf_le_right

private theorem goodWeightTwelveFlatTriple_components_le_of_support_subset
    (f : BooleanFunction n)
    {p : WeightTwelveFlatTriple n}
    (hp : p ∈ goodWeightTwelveFlatTriples n)
    (hrepresentation : weightTwelveRepresentationWord p = f)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hsupport : (support f : Set (FABL.F₂Cube n)) ⊆ A) :
    p.1 ≤ A ∧ p.2.1 ≤ A ∧ p.2.2 ≤ A := by
  have hpData := goodWeightTwelveFlatTriple_geometry hp
  let firstAway :=
    binaryAffineFlatPoints p.2.1 \ binaryAffineFlatPoints p.1
  let secondAway :=
    binaryAffineFlatPoints p.2.2 \ binaryAffineFlatPoints p.1
  have hfirstCard : firstAway.card = 6 :=
    card_first_sdiff_line_eq_six hp
  have hsecondCard : secondAway.card = 6 :=
    card_second_sdiff_line_eq_six hp
  have hfirstF : ∀ x ∈ firstAway, x ∈ p.2.1 := by
    intro x hx
    exact (mem_binaryAffineFlatPoints p.2.1 x).mp
      (Finset.mem_sdiff.mp hx).1
  have hsecondF : ∀ x ∈ secondAway, x ∈ p.2.2 := by
    intro x hx
    exact (mem_binaryAffineFlatPoints p.2.2 x).mp
      (Finset.mem_sdiff.mp hx).1
  have hfirstA : ∀ x ∈ firstAway, x ∈ A := by
    intro x hx
    have hxData := Finset.mem_sdiff.mp hx
    have hxFirst := (mem_binaryAffineFlatPoints p.2.1 x).mp hxData.1
    have hxNotLine : x ∉ p.1 := fun hxLine ↦ hxData.2
      ((mem_binaryAffineFlatPoints p.1 x).mpr hxLine)
    have hxWord : weightTwelveRepresentationWord p x = 1 :=
      ((mem_first_or_second_iff_representation_one_or_line hp x).mp
        (Or.inl hxFirst)).resolve_right hxNotLine
    apply hsupport
    apply (mem_support f x).mpr
    rw [← hrepresentation]
    exact hxWord
  have hsecondA : ∀ x ∈ secondAway, x ∈ A := by
    intro x hx
    have hxData := Finset.mem_sdiff.mp hx
    have hxSecond := (mem_binaryAffineFlatPoints p.2.2 x).mp hxData.1
    have hxNotLine : x ∉ p.1 := fun hxLine ↦ hxData.2
      ((mem_binaryAffineFlatPoints p.1 x).mpr hxLine)
    have hxWord : weightTwelveRepresentationWord p x = 1 :=
      ((mem_first_or_second_iff_representation_one_or_line hp x).mp
        (Or.inr hxSecond)).resolve_right hxNotLine
    apply hsupport
    apply (mem_support f x).mpr
    rw [← hrepresentation]
    exact hxWord
  have hfirstLe : p.2.1 ≤ A :=
    affineThreeFlat_le_of_six_points_subset p.2.1 A
      hpData.2.2.1 hpData.2.2.2.1 firstAway hfirstCard hfirstF hfirstA
  have hsecondLe : p.2.2 ≤ A :=
    affineThreeFlat_le_of_six_points_subset p.2.2 A
      hpData.2.2.2.2.1 hpData.2.2.2.2.2.1
      secondAway hsecondCard hsecondF hsecondA
  exact ⟨hpData.2.2.2.2.2.2.1.trans hfirstLe, hfirstLe, hsecondLe⟩

set_option maxRecDepth 2000 in
theorem card_weightTwelveRepresentationFiber_eq_twenty_of_five_le
    (n : ℕ) (hn : 5 ≤ n)
    (f : BooleanFunction n)
    (hf : f ∈ orderTwoWeightTwelveDualWords n) :
    ((goodWeightTwelveFlatTriples n).filter fun p ↦
      weightTwelveRepresentationWord p = f).card = 20 := by
  classical
  have hfData : f ∈ reedMuller (n - 3) n ∧ hammingWeight f = 12 := by
    simpa only [orderTwoWeightTwelveDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hf
  have hsupportCard : (support f).card = 12 := by
    simpa only [hammingWeight_eq_card_support] using hfData.2
  have hsupportNonempty : (support f).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hsupportNonempty
  let E := supportDifferenceSpan f u
  have hErank : Module.finrank FABL.𝔽₂ E ≤ 5 := by
    exact finrank_supportDifferenceSpan_le_five_of_weight_twelve
      f u hu (by omega) hfData.1 hfData.2
  have hambientRank : Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨H, hEH, hHrank⟩ := exists_superSubmodule_finrank_eq E 5
    hErank (by rw [hambientRank]; exact hn)
  let e : FABL.F₂Cube 5 ≃ₗ[FABL.𝔽₂] H :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card, hHrank]
      simp)
  let L := weightTwelveFiveFlatEmbedding u H e
  let g := weightTwelveFiveFlatRestriction f u H e
  let localFiber := (goodWeightTwelveFlatTriples 5).filter fun p ↦
    weightTwelveRepresentationWord p = g
  let ambientFiber := (goodWeightTwelveFlatTriples n).filter fun p ↦
    weightTwelveRepresentationWord p = f
  have hLinj : Function.Injective L := by
    exact weightTwelveFiveFlatEmbedding_injective u H e
  have hLlinear : Function.Injective L.linear := by
    change Function.Injective (weightTwelveFiveFlatLinearEmbedding H e)
    exact weightTwelveFiveFlatLinearEmbedding_injective H e
  have hsupportRange : (support f : Set (FABL.F₂Cube n)) ⊆
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L := by
    intro x hx
    have hxE := support_subset_binaryAffineSubspace_supportDifferenceSpan
      f u hx
    change x ∈ FABL.binaryAffineSubspace E u at hxE
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hxE
    change x ∈
      (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L
    rw [AffineSubspace.mem_map]
    let y : FABL.F₂Cube 5 := e.symm ⟨x + u, hEH hxE⟩
    refine ⟨y, by simp, ?_⟩
    change u + (e y : FABL.F₂Cube n) = x
    rw [show e y = (⟨x + u, hEH hxE⟩ : H) by
      exact e.apply_symm_apply _]
    change u + (x + u) = x
    calc
      u + (x + u) = (u + u) + x := by abel
      _ = x := by rw [ZModModule.add_self, zero_add]
  have hgMem : g ∈ reedMuller 2 5 := by
    exact weightTwelveFiveFlatRestriction_mem_reedMuller_two
      f hn hfData.1 u H e hsupportRange
  have hgWeight : hammingWeight g = 12 := by
    exact (hammingWeight_weightTwelveFiveFlatRestriction
      f u H e hsupportRange).trans hfData.2
  have hg : g ∈ orderTwoWeightTwelveDualWords 5 := by
    simp only [orderTwoWeightTwelveDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hgMem, hgWeight⟩
  have hlocalCard : localFiber.card = 20 := by
    exact card_weightTwelveRepresentationFiber_eq_twenty_of_mem g hg
  have hforward : (localFiber : Set (WeightTwelveFlatTriple 5)).MapsTo
      (weightTwelveFlatTripleMap L) ambientFiber := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · exact (weightTwelveFlatTripleMap_mem_good_iff
        L hLinj hLlinear p).mpr hpData.1
    · funext x
      by_cases hxRange : x ∈
          (⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L
      · rw [AffineSubspace.mem_map] at hxRange
        obtain ⟨y, _hy, rfl⟩ := hxRange
        rw [weightTwelveRepresentationWord_map_apply L hLinj,
          hpData.2]
        rfl
      · have hxFirst : x ∉ p.2.1.map L := by
          intro hx
          exact hxRange (AffineSubspace.map_mono L le_top hx)
        have hxSecond : x ∉ p.2.2.map L := by
          intro hx
          exact hxRange (AffineSubspace.map_mono L le_top hx)
        have hxZero : f x = 0 := by
          by_contra hxNe
          have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hxNe
          exact hxRange (hsupportRange ((mem_support f x).mpr hxOne))
        simp only [weightTwelveRepresentationWord,
          weightTwelveFlatTripleMap, Pi.add_apply,
          binaryAffineFlatIndicator, if_neg hxFirst, if_neg hxSecond,
          zero_add, hxZero]
  have hforwardInj : Set.InjOn (weightTwelveFlatTripleMap L)
      (localFiber : Set (WeightTwelveFlatTriple 5)) :=
    (weightTwelveFlatTripleMap_injective L hLinj).injOn
  have hlocalLeAmbient : localFiber.card ≤ ambientFiber.card :=
    Finset.card_le_card_of_injOn (weightTwelveFlatTripleMap L)
      hforward hforwardInj
  have hbackward : (ambientFiber : Set (WeightTwelveFlatTriple n)).MapsTo
      (weightTwelveFlatTripleComap L) localFiber := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    obtain ⟨hline, hfirst, hsecond⟩ :=
      goodWeightTwelveFlatTriple_components_le_of_support_subset
        f hpData.1 hpData.2
          ((⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L)
          hsupportRange
    let q := weightTwelveFlatTripleComap L p
    have hmapq : weightTwelveFlatTripleMap L q = p :=
      weightTwelveFlatTriple_map_comap_eq_of_le_range
        L p hline hfirst hsecond
    apply Finset.mem_filter.mpr
    constructor
    · apply (weightTwelveFlatTripleMap_mem_good_iff
        L hLinj hLlinear q).mp
      rw [hmapq]
      exact hpData.1
    · funext y
      rw [← weightTwelveRepresentationWord_map_apply L hLinj q y,
        hmapq, hpData.2]
      rfl
  have hbackwardInj : Set.InjOn (weightTwelveFlatTripleComap L)
      (ambientFiber : Set (WeightTwelveFlatTriple n)) := by
    intro p hp q hq hpq
    have hpData := Finset.mem_filter.mp hp
    have hqData := Finset.mem_filter.mp hq
    obtain ⟨hpLine, hpFirst, hpSecond⟩ :=
      goodWeightTwelveFlatTriple_components_le_of_support_subset
        f hpData.1 hpData.2
          ((⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L)
          hsupportRange
    obtain ⟨hqLine, hqFirst, hqSecond⟩ :=
      goodWeightTwelveFlatTriple_components_le_of_support_subset
        f hqData.1 hqData.2
          ((⊤ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube 5)).map L)
          hsupportRange
    have hpInverse := weightTwelveFlatTriple_map_comap_eq_of_le_range
      L p hpLine hpFirst hpSecond
    have hqInverse := weightTwelveFlatTriple_map_comap_eq_of_le_range
      L q hqLine hqFirst hqSecond
    rw [← hpInverse, ← hqInverse, hpq]
  have hambientLeLocal : ambientFiber.card ≤ localFiber.card :=
    Finset.card_le_card_of_injOn (weightTwelveFlatTripleComap L)
      hbackward hbackwardInj
  have hcard : ambientFiber.card = localFiber.card :=
    Nat.le_antisymm hambientLeLocal hlocalLeAmbient
  exact hcard.trans hlocalCard

theorem hasWeightTwelveFlatPairClassification
    (n : ℕ) (hn : 5 ≤ n) :
    HasWeightTwelveFlatPairClassification n := by
  intro f
  by_cases hf : f ∈ orderTwoWeightTwelveDualWords n
  · rw [if_pos hf]
    exact card_weightTwelveRepresentationFiber_eq_twenty_of_five_le
      n hn f hf
  · rw [if_neg hf]
    exact card_weightTwelveRepresentationFiber_eq_zero_of_not_mem f hf

end CryptBoolean
