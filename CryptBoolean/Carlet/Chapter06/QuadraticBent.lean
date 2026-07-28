/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.Quadratic
public import CryptBoolean.Carlet.Chapter06.Bentness

/-!
# Carlet Chapter 6 quadratic bent functions

The radical and linear-kernel characterizations of quadratic bent functions.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A quadratic Boolean function is bent exactly when the radical of its polar
form is trivial. -/
theorem isBent_iff_quadraticRadical_eq_bot
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsBent f ↔ quadraticRadical f hdegree = ⊥ := by
  constructor
  · intro hf
    ext a
    constructor
    · intro ha
      have haZero : a = 0 := by
        by_contra haNe
        have hbalanced :=
          (isBent_iff_forall_nonzero_derivative_isBalanced f).mp hf a haNe
        have hzero :=
          (isBalanced_iff_walshTransform_zero_eq_zero
            (FABL.booleanDerivative f a)).mp hbalanced
        rw [booleanDerivative_eq_const_of_mem_quadraticRadical
          f hdegree a ha] at hzero
        have hconstant :
            (fun _ : FABL.F₂Cube n ↦ f a + f 0) =
              FABL.affineFunction (f a + f 0) 0 := by
          funext x
          simp [FABL.affineFunction, FABL.f₂DotProduct]
        rw [hconstant, walshTransform_affineFunction] at hzero
        simp only [if_pos] at hzero
        have hsign : bitSignInt (f a + f 0) ≠ 0 := by
          rw [bitSignInt_eq_if_one]
          split <;> norm_num
        have hpow : (2 ^ n : ℤ) ≠ 0 := pow_ne_zero n (by norm_num)
        exact (mul_ne_zero hsign hpow) hzero
      simp [haZero]
    · intro ha
      have haZero : a = 0 := by simpa using ha
      subst a
      exact Submodule.zero_mem _
  · intro hradical
    apply (isBent_iff_forall_nonzero_derivative_isBalanced f).mpr
    intro a ha
    apply isBalanced_booleanDerivative_of_not_mem_quadraticRadical
      f hdegree a
    intro hmem
    rw [hradical] at hmem
    exact ha (by simpa using hmem)

/-- A quadratic Boolean function is bent exactly when its linear kernel is
trivial. -/
theorem isBent_iff_linearKernel_eq_bot_of_degree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsBent f ↔ linearKernel f = ⊥ := by
  simpa only [quadraticRadical_eq_linearKernel f hdegree] using
    (isBent_iff_quadraticRadical_eq_bot f hdegree)

end CryptBoolean
