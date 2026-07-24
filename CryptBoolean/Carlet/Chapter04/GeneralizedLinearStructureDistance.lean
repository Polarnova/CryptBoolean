/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import CryptBoolean.Carlet.Chapter04.LinearStructures
public import CryptBoolean.Carlet.Chapter04.AutocorrelationIndicators

/-!
# Carlet Chapter 4 generalized linear-structure distance

The zero-derivative directions form a linear space.  Carlet's criterion is the
minimum Hamming distance to a function whose zero-derivative space has a
prescribed lower bound on its dimension.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A direction along which a Boolean function has identically zero derivative. -/
def IsZeroDerivativeDirection
    (f : BooleanFunction n) (e : FABL.F₂Cube n) : Prop :=
  ∀ x, FABL.booleanDerivative f e x = 0

/-- The directions along which a Boolean function has identically zero derivative. -/
def zeroDerivativeKernel
    (f : BooleanFunction n) : Submodule FABL.𝔽₂ (FABL.F₂Cube n) where
  carrier := {e | IsZeroDerivativeDirection f e}
  zero_mem' := by
    intro x
    rw [FABL.booleanDerivative, add_zero, ZModModule.add_self]
  add_mem' := by
    intro e d he hd x
    rw [booleanDerivative_add_direction, he, hd, zero_add]
  smul_mem' := by
    intro c e he
    by_cases hc : c = 0
    · subst c
      intro x
      rw [zero_smul, FABL.booleanDerivative, add_zero, ZModModule.add_self]
    · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
      simpa [hc_one] using he

/-- Membership in the zero-derivative kernel is the defining pointwise condition. -/
@[simp] theorem mem_zeroDerivativeKernel
    (f : BooleanFunction n) (e : FABL.F₂Cube n) :
    e ∈ zeroDerivativeKernel f ↔ IsZeroDerivativeDirection f e :=
  Iff.rfl

/-- The zero-derivative kernel is a subspace of Carlet's linear kernel. -/
theorem zeroDerivativeKernel_le_linearKernel (f : BooleanFunction n) :
    zeroDerivativeKernel f ≤ linearKernel f := by
  intro e he
  exact ⟨0, he⟩

/-- Affine input reindexing transports the zero-derivative kernel by its linear part. -/
def zeroDerivativeKernelAffineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    zeroDerivativeKernel (f ∘ L) ≃ₗ[FABL.𝔽₂] zeroDerivativeKernel f where
  toFun e := ⟨L.linear e, by
    intro y
    have he := e.property (L.symm y)
    rw [booleanDerivative_comp_affineEquiv, L.apply_symm_apply] at he
    exact he⟩
  invFun e := ⟨L.linear.symm e, by
    intro x
    rw [booleanDerivative_comp_affineEquiv, L.linear.apply_symm_apply]
    exact e.property (L x)⟩
  left_inv e := by
    ext i
    exact congrFun (L.linear.symm_apply_apply e.1) i
  right_inv e := by
    ext i
    exact congrFun (L.linear.apply_symm_apply e.1) i
  map_add' e d := by
    ext i
    exact congrFun (L.linear.map_add e.1 d.1) i
  map_smul' c e := by
    ext i
    exact congrFun (L.linear.map_smul c e.1) i

/-- Affine input reindexing preserves the zero-derivative dimension. -/
theorem finrank_zeroDerivativeKernel_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    Module.finrank FABL.𝔽₂ (zeroDerivativeKernel (f ∘ L)) =
      Module.finrank FABL.𝔽₂ (zeroDerivativeKernel f) :=
  (zeroDerivativeKernelAffineEquiv f L).finrank_eq

/-- The zero function has every direction in its zero-derivative kernel. -/
@[simp] theorem zeroDerivativeKernel_zero :
    zeroDerivativeKernel (0 : BooleanFunction n) = ⊤ := by
  ext e
  simp [zeroDerivativeKernel, IsZeroDerivativeDirection, FABL.booleanDerivative]

/-- The zero function's zero-derivative kernel has the full cube dimension. -/
@[simp] theorem finrank_zeroDerivativeKernel_zero :
    Module.finrank FABL.𝔽₂
      (zeroDerivativeKernel (0 : BooleanFunction n)) = n := by
  rw [zeroDerivativeKernel_zero, finrank_top,
    Module.finrank_fintype_fun_eq_card]
  simp

/-- Functions whose zero-derivative space has dimension at least `k`. -/
noncomputable def largeZeroDerivativeFunctions
    (k : ℕ) : Finset (BooleanFunction n) :=
  Finset.univ.filter fun g ↦
    k ≤ Module.finrank FABL.𝔽₂ (zeroDerivativeKernel g)

/-- The comparison class is nonempty throughout its meaningful range `k ≤ n`. -/
theorem largeZeroDerivativeFunctions_nonempty
    (k : ℕ) (hk : k ≤ n) :
    (largeZeroDerivativeFunctions (n := n) k).Nonempty := by
  refine ⟨0, ?_⟩
  simp [largeZeroDerivativeFunctions, hk]

/-- Carlet's generalized distance to functions with a zero-derivative space
of dimension at least `k`. -/
noncomputable def generalizedLinearStructureDistance
    (f : BooleanFunction n) (k : ℕ) (hk : k ≤ n) : ℕ :=
  (largeZeroDerivativeFunctions (n := n) k).inf'
    (largeZeroDerivativeFunctions_nonempty k hk)
    (hammingDistance f)

/-- Affine input reindexing preserves membership in the comparison class. -/
theorem mem_largeZeroDerivativeFunctions_comp_affineEquiv_iff
    (g : BooleanFunction n) (k : ℕ)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    g ∘ L ∈ largeZeroDerivativeFunctions (n := n) k ↔
      g ∈ largeZeroDerivativeFunctions (n := n) k := by
  simp only [largeZeroDerivativeFunctions, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [finrank_zeroDerivativeKernel_comp_affineEquiv]

/-- One half of affine invariance for the generalized distance. -/
theorem generalizedLinearStructureDistance_comp_affineEquiv_le
    (f : BooleanFunction n) (k : ℕ) (hk : k ≤ n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    generalizedLinearStructureDistance (f ∘ L) k hk ≤
      generalizedLinearStructureDistance f k hk := by
  classical
  unfold generalizedLinearStructureDistance
  obtain ⟨g, hg, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := largeZeroDerivativeFunctions (n := n) k)
    (largeZeroDerivativeFunctions_nonempty k hk)
    (hammingDistance f)
  calc
    (largeZeroDerivativeFunctions (n := n) k).inf'
        (largeZeroDerivativeFunctions_nonempty k hk)
        (hammingDistance (f ∘ L)) ≤
      hammingDistance (f ∘ L) (g ∘ L) :=
        Finset.inf'_le _
          ((mem_largeZeroDerivativeFunctions_comp_affineEquiv_iff g k L).2 hg)
    _ = hammingDistance f g := hammingDistance_comp_affineEquiv f g L
    _ = (largeZeroDerivativeFunctions (n := n) k).inf'
        (largeZeroDerivativeFunctions_nonempty k hk)
        (hammingDistance f) := hmin.symm

/-- Carlet's generalized linear-structure distance is affine invariant. -/
theorem generalizedLinearStructureDistance_comp_affineEquiv
    (f : BooleanFunction n) (k : ℕ) (hk : k ≤ n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    generalizedLinearStructureDistance (f ∘ L) k hk =
      generalizedLinearStructureDistance f k hk := by
  apply Nat.le_antisymm
    (generalizedLinearStructureDistance_comp_affineEquiv_le f k hk L)
  have h := generalizedLinearStructureDistance_comp_affineEquiv_le
    (f ∘ L) k hk L.symm
  simpa [Function.comp_def] using h

end CryptBoolean
