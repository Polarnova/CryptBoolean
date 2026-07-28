/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.SupportDualDistance
public import CryptBoolean.Carlet.Chapter05.Affine
public import CryptBoolean.Carlet.Chapter06.HyperBentPartialSpread
import Mathlib.Data.Fintype.Powerset

/-!
# Counting the `PS_ap` family

The partial-spread quotient construction is injectively parametrized by the
balanced Boolean functions on the middle field.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable local instance psapCountingFieldFintype {r : ℕ} :
    Fintype (BinaryGaloisField r) :=
  Fintype.ofFinite (BinaryGaloisField r)

/-- The balanced Boolean parameters of the `PS_ap` construction. -/
abbrev PSapParameters (m : ℕ) :=
  {g : BooleanFunction m // IsBalanced g}

noncomputable local instance psapParametersFintype (m : ℕ) :
    Fintype (PSapParameters m) :=
  Fintype.ofFinite (PSapParameters m)

private noncomputable def booleanFunctionSupportEquiv (m : ℕ) :
    BooleanFunction m ≃ Finset (FABL.F₂Cube m) where
  toFun := support
  invFun := fun S x ↦ if x ∈ S then 1 else 0
  left_inv := by
    intro f
    funext x
    by_cases hx : f x = 0
    · simp [mem_support, hx]
    · have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hx
      simp [mem_support, hxOne]
  right_inv := by
    intro S
    ext x
    simp [mem_support]

private noncomputable def balancedBooleanFunctionSupportEquiv
    (m : ℕ) (hm : 0 < m) :
    PSapParameters m ≃
      {S : Finset (FABL.F₂Cube m) // S.card = 2 ^ (m - 1)} :=
  (booleanFunctionSupportEquiv m).subtypeEquiv fun f ↦ by
    exact isBalanced_iff_support_card_eq_two_pow_pred f hm

/-- There are exactly `choose (2^m) (2^(m-1))` balanced Boolean parameters. -/
theorem card_psapParameters (m : ℕ) (hm : 0 < m) :
    Fintype.card (PSapParameters m) =
      Nat.choose (2 ^ m) (2 ^ (m - 1)) := by
  calc
    Fintype.card (PSapParameters m) =
        Fintype.card
          {S : Finset (FABL.F₂Cube m) // S.card = 2 ^ (m - 1)} :=
      Fintype.card_congr (balancedBooleanFunctionSupportEquiv m hm)
    _ = Nat.choose (Fintype.card (FABL.F₂Cube m)) (2 ^ (m - 1)) :=
      Fintype.card_finset_len (2 ^ (m - 1))
    _ = Nat.choose (2 ^ m) (2 ^ (m - 1)) := by
      rw [card_f₂Cube]

/-- The field-valued `PS_ap` function selected by a balanced Boolean
parameter and fixed quadratic-extension coordinates. -/
noncomputable def psapOfParameters {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (g : PSapParameters m) : FieldBooleanFunction (2 * m) :=
  psapFunction hm iota omega homega (g.1 ∘ theta.symm)

/-- Evaluation of a parametrized `PS_ap` function in quadratic-extension
coordinates. -/
@[simp] theorem psapOfParameters_coordinate {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (g : PSapParameters m) (y' y : BinaryGaloisField m) :
    psapOfParameters hm iota omega homega theta g
        (iota y' + omega * iota y) =
      g.1 (theta.symm (y' / y)) := by
  rw [psapOfParameters, psapFunction_coordinate]
  rfl

/-- Distinct balanced parameters give distinct `PS_ap` functions. -/
theorem psapOfParameters_injective {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    Function.Injective (psapOfParameters hm iota omega homega theta) := by
  intro g h heq
  apply Subtype.ext
  funext x
  have hvalue := congrFun heq
    (iota (theta x) + omega * iota (1 : BinaryGaloisField m))
  rw [psapOfParameters_coordinate, psapOfParameters_coordinate] at hvalue
  simpa using hvalue

/-- The finite `PS_ap` family in fixed quadratic-extension coordinates. -/
noncomputable def psapClass {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    Finset (FieldBooleanFunction (2 * m)) := by
  classical
  exact Finset.univ.image
    (psapOfParameters hm iota omega homega theta)

/-- Carlet's exact count for the `PS_ap` family. -/
theorem card_psapClass {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    (psapClass hm iota omega homega theta).card =
      Nat.choose (2 ^ m) (2 ^ (m - 1)) := by
  classical
  rw [psapClass, Finset.card_image_of_injective,
    Finset.card_univ, card_psapParameters m hm]
  exact psapOfParameters_injective hm iota omega homega theta

private theorem isBalanced_add_constant_one
    {m : ℕ} (f : BooleanFunction m) (hf : IsBalanced f) :
    IsBalanced (f + FABL.affineFunction 1 0) := by
  apply (isBalanced_iff_walshTransform_zero_eq_zero _).2
  rw [walshTransform_add_affineFunction]
  simp only [add_zero]
  rw [(isBalanced_iff_walshTransform_zero_eq_zero f).1 hf]
  simp

/-- Every balanced `PS_ap` parameter yields a bent function after any linear
choice of ambient binary coordinates. -/
theorem isBent_psapOfParameters_comp_linearEquiv {m : ℕ} (hm : 2 ≤ m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (Theta : FABL.F₂Cube (2 * m) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (g : PSapParameters m) :
    IsBent (psapOfParameters (by omega) iota omega homega theta g ∘ Theta) := by
  let gf : FieldBooleanFunction m := g.1 ∘ theta.symm
  have hgfBalanced : IsBalanced (gf ∘ theta) := by
    simpa [gf, Function.comp_def] using g.2
  by_cases hgfZero : gf 0 = 0
  · have hhyper := isHyperBent_psapFunction hm iota omega homega theta
      gf hgfBalanced hgfZero
    exact (isFieldBent_iff_isBent_comp_linearEquiv Theta _).1
      hhyper.isFieldBent
  · have hgfOne : gf 0 = 1 := Fin.eq_one_of_ne_zero _ hgfZero
    let gc : FieldBooleanFunction m := fun x ↦ gf x + 1
    have hgcZero : gc 0 = 0 := by
      simp [gc, hgfOne]
    have hgcCoordinate :
        gc ∘ theta =
          (gf ∘ theta) + FABL.affineFunction 1 0 := by
      funext x
      simp [gc, FABL.affineFunction, FABL.f₂DotProduct]
    have hgcBalanced : IsBalanced (gc ∘ theta) := by
      rw [hgcCoordinate]
      exact isBalanced_add_constant_one (gf ∘ theta) hgfBalanced
    have hhyper := isHyperBent_psapFunction hm iota omega homega theta
      gc hgcBalanced hgcZero
    have hgcBent :
        IsBent (psapFunction (by omega) iota omega homega gc ∘ Theta) :=
      (isFieldBent_iff_isBent_comp_linearEquiv Theta _).1
        hhyper.isFieldBent
    have hcomplement :
        psapFunction (by omega) iota omega homega gf ∘ Theta =
          (psapFunction (by omega) iota omega homega gc ∘ Theta) +
            FABL.affineFunction 1 0 := by
      funext x
      simp only [Function.comp_apply, Pi.add_apply, FABL.affineFunction,
        FABL.f₂DotProduct, zero_dotProduct, add_zero]
      unfold psapFunction
      dsimp [gc]
      rw [add_assoc, show (1 : FABL.𝔽₂) + 1 = 0 by decide,
        add_zero]
    change IsBent (psapFunction (by omega) iota omega homega gf ∘ Theta)
    rw [hcomplement]
    exact (isBent_add_affineFunction_iff
      (psapFunction (by omega) iota omega homega gc ∘ Theta) 1 0).2
        hgcBent

end CryptBoolean
