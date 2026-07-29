/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.CodeGeneratorResiliency
public import CryptBoolean.Carlet.Chapter05.Affine

/-!
# Linear pullback construction

The coordinate-free form of Carlet's row-space-coset construction for
resilient functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

noncomputable local instance submoduleFintypeForLinearPullback
    (C : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype C :=
  Fintype.ofFinite C

/-- The minimum Hamming weight in the translate `t + C` of a binary
subspace. -/
noncomputable def binaryCosetMinimumWeight
    (t : FABL.F₂Cube n)
    (C : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : ℕ :=
  (Finset.univ : Finset C).inf' Finset.univ_nonempty
    fun c ↦ (FABL.f₂Support (t + c.1)).card

/-- The minimum weight of a coset is bounded by the weight of each of its
members. -/
theorem binaryCosetMinimumWeight_le
    (t : FABL.F₂Cube n)
    (C : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (c : FABL.F₂Cube n) (hc : c ∈ C) :
    binaryCosetMinimumWeight t C ≤
      (FABL.f₂Support (t + c)).card := by
  unfold binaryCosetMinimumWeight
  exact Finset.inf'_le
    (f := fun z : C ↦ (FABL.f₂Support (t + z.1)).card)
    (Finset.mem_univ ⟨c, hc⟩)

/-- A binary coset minimum weight never exceeds the ambient dimension. -/
theorem binaryCosetMinimumWeight_le_dimension
    (t : FABL.F₂Cube n)
    (C : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryCosetMinimumWeight t C ≤ n := by
  calc
    binaryCosetMinimumWeight t C ≤
        (FABL.f₂Support (t + (0 : FABL.F₂Cube n))).card :=
      binaryCosetMinimumWeight_le t C 0 C.zero_mem
    _ ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-- Pull a Boolean function back through a linear map and add the parity at
frequency `t`. -/
def linearPullbackWithFrequency
    (L : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube k)
    (g : BooleanFunction k) (t : FABL.F₂Cube n) :
    BooleanFunction n :=
  fun x ↦ g (L x) + FABL.f₂DotProduct t x

private theorem linearPullbackWithFrequency_eq_add_affineFunction
    (L : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube k)
    (g : BooleanFunction k) (t : FABL.F₂Cube n) :
    linearPullbackWithFrequency L g t =
      (fun x ↦ g (L x)) + FABL.affineFunction 0 t := by
  funext x
  simp [linearPullbackWithFrequency, FABL.affineFunction]

/-- Adding the outer frequency translates the Walsh spectrum of a linear
pullback. -/
theorem walshTransform_linearPullbackWithFrequency
    (L : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube k)
    (g : BooleanFunction k) (t u : FABL.F₂Cube n) :
    walshTransform (linearPullbackWithFrequency L g t) u =
      walshTransform (fun x ↦ g (L x)) (u + t) := by
  rw [linearPullbackWithFrequency_eq_add_affineFunction,
    walshTransform_add_affineFunction]
  simp [bitSignInt_eq_if_one]

/-- If the frequency translate has positive distance from the Fourier
support subspace of a linear pullback, the resulting function is resilient
to one less than that distance. -/
theorem isResilient_linearPullbackWithFrequency
    (L : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube k)
    (g : BooleanFunction k) (t : FABL.F₂Cube n)
    (hd : 0 <
      binaryCosetMinimumWeight t
        (FABL.perpendicularSubspace (LinearMap.ker L))) :
    IsResilient
      (binaryCosetMinimumWeight t
        (FABL.perpendicularSubspace (LinearMap.ker L)) - 1)
      (linearPullbackWithFrequency L g t) := by
  let d :=
    binaryCosetMinimumWeight t
      (FABL.perpendicularSubspace (LinearMap.ker L))
  have hdn : d ≤ n :=
    binaryCosetMinimumWeight_le_dimension t
      (FABL.perpendicularSubspace (LinearMap.ker L))
  have hn : 0 < n := hd.trans_le hdn
  have horder : d - 1 < n := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (d - 1) (linearPullbackWithFrequency L g t) hn horder]
  intro u hu
  rw [walshTransform_linearPullbackWithFrequency]
  apply walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero _ _ |>.mpr
  change FABL.vectorFourierCoeff
      (fun x ↦ realSignView g (L x)) (u + t) = 0
  apply vectorFourierCoeff_comp_linearMap_eq_zero_of_not_mem_perpendicular_ker
  intro hmem
  have hminimum :
      d ≤ (FABL.f₂Support (t + (u + t))).card := by
    exact binaryCosetMinimumWeight_le t
      (FABL.perpendicularSubspace (LinearMap.ker L))
      (u + t) hmem
  have hcancel : t + (u + t) = u := by
    calc
      t + (u + t) = u + (t + t) := by abel
      _ = u := by rw [ZModModule.add_self, add_zero]
  rw [hcancel] at hminimum
  omega

end CryptBoolean
