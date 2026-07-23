/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Derivatives

/-!
# Carlet Chapter 4 linear structures

Linear structures are the directions in which a binary derivative is constant. They form the
linear kernel of the function.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A direction is a linear structure when the corresponding binary derivative is constant. -/
def IsLinearStructure (f : BooleanFunction n) (e : FABL.F₂Cube n) : Prop :=
  ∃ ε : FABL.𝔽₂, ∀ x, FABL.booleanDerivative f e x = ε

/-- The zero direction is a linear structure of every Boolean function. -/
theorem isLinearStructure_zero (f : BooleanFunction n) :
    IsLinearStructure f 0 := by
  refine ⟨0, ?_⟩
  intro x
  rw [FABL.booleanDerivative, add_zero, ZModModule.add_self]

/-- The derivative in a sum of directions is the sum of two translated derivatives. -/
theorem booleanDerivative_add_direction
    (f : BooleanFunction n) (e d x : FABL.F₂Cube n) :
    FABL.booleanDerivative f (e + d) x =
      FABL.booleanDerivative f e (x + d) + FABL.booleanDerivative f d x := by
  rw [FABL.booleanDerivative, FABL.booleanDerivative, FABL.booleanDerivative]
  have harg : (x + d) + e = x + (e + d) := by
    abel
  rw [harg]
  symm
  calc
    (f (x + d) + f (x + (e + d))) + (f x + f (x + d)) =
        (f (x + d) + f (x + d)) + (f (x + (e + d)) + f x) := by
      abel
    _ = f (x + (e + d)) + f x := by
      rw [ZModModule.add_self, zero_add]
    _ = f x + f (x + (e + d)) := add_comm _ _

/-- The sum of two linear structures is a linear structure. -/
theorem IsLinearStructure.add {f : BooleanFunction n} {e d : FABL.F₂Cube n}
    (he : IsLinearStructure f e) (hd : IsLinearStructure f d) :
    IsLinearStructure f (e + d) := by
  obtain ⟨ε, hε⟩ := he
  obtain ⟨δ, hδ⟩ := hd
  refine ⟨ε + δ, ?_⟩
  intro x
  rw [booleanDerivative_add_direction, hε, hδ]

/-- Scalar multiples of linear structures are linear structures. -/
theorem IsLinearStructure.smul {f : BooleanFunction n} {e : FABL.F₂Cube n}
    (he : IsLinearStructure f e) (c : FABL.𝔽₂) :
    IsLinearStructure f (c • e) := by
  by_cases hc : c = 0
  · simpa [hc] using isLinearStructure_zero f
  · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
    simpa [hc_one] using he

/-- Carlet's linear kernel, consisting of all linear structures of a Boolean function. -/
def linearKernel (f : BooleanFunction n) : Submodule FABL.𝔽₂ (FABL.F₂Cube n) where
  carrier := {e | IsLinearStructure f e}
  zero_mem' := isLinearStructure_zero f
  add_mem' he hd := he.add hd
  smul_mem' c _ he := he.smul c

/-- Membership in the linear kernel is exactly the linear-structure condition. -/
@[simp] theorem mem_linearKernel (f : BooleanFunction n) (e : FABL.F₂Cube n) :
    e ∈ linearKernel f ↔ IsLinearStructure f e :=
  Iff.rfl

end CryptBoolean
