/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.Affine
public import CryptBoolean.Carlet.Chapter05.Quadratic
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Ranks of quadratic Boolean polar forms
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance quadraticRankSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

/-- Adding an affine function changes every directional derivative by a constant. -/
theorem booleanDerivative_add_affineFunction
    (f : BooleanFunction n) (c : FABL.𝔽₂) (u a : FABL.F₂Cube n) :
    FABL.booleanDerivative
        (fun x ↦ f x + FABL.affineFunction c u x) a =
      fun x ↦ FABL.booleanDerivative f a x + FABL.f₂DotProduct u a := by
  funext x
  simp only [FABL.booleanDerivative, FABL.affineFunction]
  rw [show FABL.f₂DotProduct u (x + a) =
      FABL.f₂DotProduct u x + FABL.f₂DotProduct u a by
    exact dotProduct_add u x a]
  have htwo : (2 : FABL.𝔽₂) = 0 := ZMod.natCast_self 2
  ring_nf
  simp [htwo]

/-- Adding an affine function preserves the linear kernel. -/
theorem linearKernel_add_affineFunction
    (f : BooleanFunction n) (c : FABL.𝔽₂) (u : FABL.F₂Cube n) :
    linearKernel (fun x ↦ f x + FABL.affineFunction c u x) =
      linearKernel f := by
  ext a
  simp only [mem_linearKernel]
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε + FABL.f₂DotProduct u a, ?_⟩
    intro x
    have hx := hε x
    rw [booleanDerivative_add_affineFunction] at hx
    change FABL.booleanDerivative f a x + FABL.f₂DotProduct u a = ε at hx
    rw [← hx]
    have htwo : (2 : FABL.𝔽₂) = 0 := ZMod.natCast_self 2
    ring_nf
    rw [htwo, mul_zero, add_zero]
  · rintro ⟨ε, hε⟩
    refine ⟨ε + FABL.f₂DotProduct u a, ?_⟩
    intro x
    rw [booleanDerivative_add_affineFunction]
    change FABL.booleanDerivative f a x + FABL.f₂DotProduct u a =
      ε + FABL.f₂DotProduct u a
    rw [hε x]

/-- A linear modulation moves a raw Walsh coefficient to frequency zero. -/
theorem walshTransform_add_linearFunction_zero
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    walshTransform (fun x ↦ f x + FABL.affineFunction 0 u x) 0 =
      walshTransform f u := by
  change walshTransform (f + FABL.affineFunction 0 u) 0 =
    walshTransform f u
  simpa [bitSignInt, FABL.signEncode_zero] using
    walshTransform_add_affineFunction f 0 u 0

/-- If an integer square is a power of two, then its exponent is even. -/
theorem even_exponent_of_int_sq_eq_two_pow
    (z : ℤ) (e : ℕ) (h : z ^ 2 = (2 : ℤ) ^ e) : Even e := by
  have hnat : z.natAbs ^ 2 = 2 ^ e := by
    have habs := congrArg Int.natAbs h
    simpa using habs
  have hfactor := congrArg (fun m : ℕ ↦ m.factorization 2) hnat
  rw [Nat.factorization_pow, Nat.Prime.factorization_pow Nat.prime_two] at hfactor
  have hfactor' : 2 * z.natAbs.factorization 2 = e := by
    simpa using hfactor
  exact ⟨z.natAbs.factorization 2, by omega⟩

/-- The dimension plus the linear-kernel dimension of a quadratic function is even. -/
theorem even_dimension_add_finrank_linearKernel_of_degree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    Even (n + Module.finrank FABL.𝔽₂ (linearKernel f)) := by
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  let g : BooleanFunction n :=
    fun x ↦ f x + FABL.affineFunction 0 u x
  have hgdegree : FABL.functionAlgebraicDegree g ≤ 2 := by
    apply (FABL.functionAlgebraicDegree_add_le_max
      f (FABL.affineFunction 0 u)).trans
    exact max_le hdegree
      (FABL.functionAlgebraicDegree_affineFunction_le_one 0 u |>.trans (by omega))
  have hgWalsh : walshTransform g 0 ≠ 0 := by
    rw [show walshTransform g 0 = walshTransform f u by
      exact walshTransform_add_linearFunction_zero f u]
    exact hu
  have hconstant : ∀ a : linearKernel g, g a.1 = g 0 := by
    by_contra h
    have hrelation :=
      walshTransform_zero_sq_eq_if_constant_on_linearKernel g hgdegree
    rw [if_neg h] at hrelation
    have hcast : (walshTransform g 0 : ℝ) ≠ 0 := by exact_mod_cast hgWalsh
    exact (pow_ne_zero 2 hcast) hrelation
  have hrelation :=
    walshTransform_zero_sq_eq_if_constant_on_linearKernel g hgdegree
  rw [if_pos hconstant] at hrelation
  have hkernel : linearKernel g = linearKernel f := by
    exact linearKernel_add_affineFunction f 0 u
  have hcard : Fintype.card (linearKernel g) =
      2 ^ Module.finrank FABL.𝔽₂ (linearKernel f) := by
    rw [hkernel, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := FABL.𝔽₂)
        (V := linearKernel f), Nat.card_zmod]
  rw [hcard] at hrelation
  have hreal : (walshTransform g 0 : ℝ) ^ 2 =
      (2 : ℝ) ^ (n + Module.finrank FABL.𝔽₂ (linearKernel f)) := by
    calc
      (walshTransform g 0 : ℝ) ^ 2 =
          (2 ^ n : ℝ) *
            (2 ^ Module.finrank FABL.𝔽₂ (linearKernel f) : ℕ) := hrelation
      _ = (2 : ℝ) ^
          (n + Module.finrank FABL.𝔽₂ (linearKernel f)) := by
        norm_num [pow_add]
  have hint : walshTransform g 0 ^ 2 =
      (2 : ℤ) ^ (n + Module.finrank FABL.𝔽₂ (linearKernel f)) := by
    exact_mod_cast hreal
  exact even_exponent_of_int_sq_eq_two_pow (walshTransform g 0)
    (n + Module.finrank FABL.𝔽₂ (linearKernel f)) hint

/-- The linear kernel of a quadratic Boolean function has even codimension. -/
theorem even_codimension_linearKernel_of_degree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    Even (n - Module.finrank FABL.𝔽₂ (linearKernel f)) := by
  have hle : Module.finrank FABL.𝔽₂ (linearKernel f) ≤ n := by
    have h := Submodule.finrank_le (linearKernel f)
    simpa only [Module.finrank_pi, Fintype.card_fin] using h
  apply (Nat.even_sub hle).mpr
  exact (Nat.even_add.mp
    (even_dimension_add_finrank_linearKernel_of_degree_le_two f hdegree))

end CryptBoolean
