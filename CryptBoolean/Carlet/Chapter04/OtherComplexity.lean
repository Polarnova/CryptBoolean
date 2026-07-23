/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import CryptBoolean.Carlet.Chapter02.SpectralSupport

/-!
# Carlet Chapter 4 auxiliary cryptographic complexity measures

Algebraic thickness, normality, weak normality, and spectral complexity.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance affineEquivFintype :
    Fintype (FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :=
  Fintype.ofInjective AffineEquiv.toEquiv AffineEquiv.toEquiv_injective

/-- Carlet's algebraic thickness: the least number of nonzero ANF terms in the affine orbit. -/
noncomputable def algebraicThickness (f : BooleanFunction n) : ℕ :=
  (Finset.univ : Finset (FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)).inf'
    (by simp)
    (fun L ↦ (FABL.anfSupport (FABL.anfCoeff (f ∘ L))).card)

/-- Algebraic thickness is attained by an affine reindexing. -/
theorem exists_affineEquiv_anfSupport_card_eq_algebraicThickness
    (f : BooleanFunction n) :
    ∃ L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n,
      (FABL.anfSupport (FABL.anfCoeff (f ∘ L))).card =
        algebraicThickness f := by
  classical
  obtain ⟨L, _hL, hcard⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ :
      Finset (FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)))
    (by simp)
    (fun L ↦ (FABL.anfSupport (FABL.anfCoeff (f ∘ L))).card)
  exact ⟨L, hcard.symm⟩

/-- A Boolean function is constant on the affine flat `a + H`. -/
def IsConstantOnAffineFlat
    (f : BooleanFunction n) (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : Prop :=
  ∃ b : FABL.𝔽₂, ∀ x ∈ FABL.binaryAffineSubspace H a, f x = b

/-- A Boolean function restricts to an affine function on the affine flat `a + H`. -/
def IsAffineOnAffineFlat
    (f : BooleanFunction n) (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : Prop :=
  ∃ b : FABL.𝔽₂, ∃ c : FABL.F₂Cube n,
    ∀ x ∈ FABL.binaryAffineSubspace H a, f x = FABL.affineFunction b c x

/-- A constant affine-flat restriction is an affine affine-flat restriction. -/
theorem IsConstantOnAffineFlat.isAffineOnAffineFlat
    {f : BooleanFunction n} {H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    {a : FABL.F₂Cube n} (h : IsConstantOnAffineFlat f H a) :
    IsAffineOnAffineFlat f H a := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, 0, ?_⟩
  intro x hx
  rw [hb x hx]
  simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]

/-- Carlet's normality parameter: the largest dimension of an affine flat on which `f` is
constant. -/
noncomputable def normality (f : BooleanFunction n) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset
        (Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n)).filter
        (fun p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n ↦
          IsConstantOnAffineFlat f p.1 p.2)).sup
      (fun p ↦ Module.finrank FABL.𝔽₂ p.1)

/-- Carlet's weak normality parameter: the largest dimension of an affine flat on which `f`
restricts to an affine function. -/
noncomputable def weakNormality (f : BooleanFunction n) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset
        (Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n)).filter
        (fun p : Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n ↦
          IsAffineOnAffineFlat f p.1 p.2)).sup
      (fun p ↦ Module.finrank FABL.𝔽₂ p.1)

/-- Every normal affine flat is weakly normal, so normality is bounded by weak normality. -/
theorem normality_le_weakNormality (f : BooleanFunction n) :
    normality f ≤ weakNormality f := by
  classical
  rw [normality, weakNormality]
  apply Finset.sup_le
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpweak : p ∈
      ((Finset.univ : Finset
        (Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n)).filter
        (fun q : Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n ↦
          IsAffineOnAffineFlat f q.1 q.2)) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ p, hp.2.isAffineOnAffineFlat⟩
  exact Finset.le_sup (f := fun q ↦ Module.finrank FABL.𝔽₂ q.1) hpweak

/-- Carlet's spectral complexity: the number of nonzero raw Walsh coefficients. -/
noncomputable def spectralComplexity (f : BooleanFunction n) : ℕ :=
  (rawFourierSupport (realSignView f)).card

end CryptBoolean
