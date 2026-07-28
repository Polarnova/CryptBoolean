/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.GeometricCharacterization

/-!
# Partial-spread bent functions

Carlet Section 6.4: sums of indicators of pairwise disjoint
half-dimensional subspaces.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A finite family of half-dimensional subspaces whose distinct members
intersect only at the origin. -/
def IsHalfDimensionalPartialSpread
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n))) : Prop :=
  (∀ E ∈ P, Module.finrank FABL.𝔽₂ E = n / 2) ∧
    ∀ E ∈ P, ∀ F ∈ P, E ≠ F → E ⊓ F = ⊥

/-- The two cardinalities used by Dillon's partial-spread classes. -/
def HasPartialSpreadBentCardinality
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n))) : Prop :=
  P.card = 2 ^ (n / 2 - 1) ∨ P.card = 2 ^ (n / 2 - 1) + 1

/-- The Boolean sum of the indicators of the members of a partial spread. -/
noncomputable def partialSpreadFunction
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n))) :
    BooleanFunction n := by
  classical
  exact ∑ E ∈ P, fun x ↦ if x ∈ E then 1 else 0

/-- The coefficient family selecting the members of a partial spread. -/
noncomputable def partialSpreadCoefficients
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n))) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ := by
  classical
  exact fun E ↦ if E ∈ P then 1 else 0

private theorem halfSubspaceCombination_partialSpreadCoefficients
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)))
    (hP : IsHalfDimensionalPartialSpread P)
    (x : FABL.F₂Cube n) :
    halfSubspaceCombination (partialSpreadCoefficients P) x =
      ∑ E ∈ P, linearSubspaceIndicatorInt E x := by
  classical
  unfold halfSubspaceCombination partialSpreadCoefficients
  let H := binaryLinearSubspaces (n / 2) n
  have hsubset : P ⊆ H := by
    intro E hE
    exact (mem_binaryLinearSubspaces E).mpr (hP.1 E hE)
  calc
    (∑ E ∈ H, (if E ∈ P then (1 : ℤ) else 0) *
        linearSubspaceIndicatorInt E x) =
        ∑ E ∈ H.filter fun E ↦ E ∈ P,
          linearSubspaceIndicatorInt E x := by
      simp [Finset.sum_filter]
    _ = ∑ E ∈ P, linearSubspaceIndicatorInt E x := by
      congr 1
      ext E
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hsubset h, h⟩

private theorem unique_partialSpread_member_of_ne_zero
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)))
    (hP : IsHalfDimensionalPartialSpread P)
    {x : FABL.F₂Cube n} (hx : x ≠ 0)
    {E F : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (hE : E ∈ P) (hxE : x ∈ E) (hF : F ∈ P) (hxF : x ∈ F) :
    E = F := by
  by_contra hne
  have hintersection := hP.2 E hE F hF hne
  have hxBot : x ∈ (⊥ : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
    rw [← hintersection]
    exact ⟨hxE, hxF⟩
  exact hx (by simpa using hxBot)

/-- Away from the origin, the Boolean indicator sum equals its ordinary
integer indicator sum. -/
theorem bitValueInt_partialSpreadFunction_of_ne_zero
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)))
    (hP : IsHalfDimensionalPartialSpread P)
    (x : FABL.F₂Cube n) (hx : x ≠ 0) :
    bitValueInt (partialSpreadFunction P x) =
      ∑ E ∈ P, linearSubspaceIndicatorInt E x := by
  classical
  by_cases hexists : ∃ E ∈ P, x ∈ E
  · obtain ⟨E, hE, hxE⟩ := hexists
    have hother (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
        (hF : F ∈ P) (hFE : F ≠ E) : x ∉ F := by
      intro hxF
      exact hFE (unique_partialSpread_member_of_ne_zero
        P hP hx hF hxF hE hxE)
    have hboolean : partialSpreadFunction P x = 1 := by
      unfold partialSpreadFunction
      simp_rw [Finset.sum_apply]
      rw [Finset.sum_eq_single E]
      · simp [hxE]
      · intro F hF hFE
        simp [hother F hF hFE]
      · exact fun h ↦ (h hE).elim
    rw [hboolean]
    simp only [bitValueInt]
    norm_num
    rw [Finset.sum_eq_single E]
    · simp [linearSubspaceIndicatorInt, hxE]
    · intro F hF hFE
      simp [linearSubspaceIndicatorInt, hother F hF hFE]
    · exact fun h ↦ (h hE).elim
  · have hnone (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
        (hE : E ∈ P) : x ∉ E := by
      exact fun hxE ↦ hexists ⟨E, hE, hxE⟩
    have hboolean : partialSpreadFunction P x = 0 := by
      unfold partialSpreadFunction
      simp_rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro E hE
      simp [hnone E hE]
    have hsum :
        (∑ E ∈ P, linearSubspaceIndicatorInt E x) = 0 := by
      apply Finset.sum_eq_zero
      intro E hE
      simp [linearSubspaceIndicatorInt, hnone E hE]
    rw [hboolean]
    rw [hsum]
    simp [bitValueInt]

/-- At the origin, a partial-spread function records the parity of the
number of selected subspaces. -/
theorem partialSpreadFunction_zero
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n))) :
    partialSpreadFunction P 0 = (P.card : FABL.𝔽₂) := by
  classical
  unfold partialSpreadFunction
  simp_rw [Finset.sum_apply]
  simp

/-- A partial spread of either Dillon cardinality gives the exact generalized
partial-spread expression. -/
theorem hasExactGPSRepresentation_partialSpreadFunction
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)))
    (hP : IsHalfDimensionalPartialSpread P)
    (hcard : HasPartialSpreadBentCardinality P)
    (hhalf : 2 ≤ n / 2) :
    HasExactGPSRepresentation (partialSpreadFunction P)
      (partialSpreadCoefficients P) := by
  intro x
  rw [geometricBentExpression,
    halfSubspaceCombination_partialSpreadCoefficients P hP x]
  by_cases hx : x = 0
  · subst x
    have hpowEven : Even (2 ^ (n / 2 - 1)) :=
      Even.pow_of_ne_zero (by norm_num : Even 2) (by omega)
    rw [partialSpreadFunction_zero]
    simp only [linearSubspaceIndicatorInt, Submodule.zero_mem, if_pos,
      originIndicatorInt]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rcases hcard with hcard | hcard
    · rw [hcard]
      have hcastZero : ((2 ^ (n / 2 - 1) : ℕ) : FABL.𝔽₂) = 0 := by
        exact ZMod.natCast_eq_zero_iff_even.mpr hpowEven
      rw [hcastZero]
      simp [bitValueInt]
    · rw [hcard]
      have hcastZero : ((2 ^ (n / 2 - 1) : ℕ) : FABL.𝔽₂) = 0 := by
        exact ZMod.natCast_eq_zero_iff_even.mpr hpowEven
      rw [Nat.cast_add, hcastZero]
      simp [bitValueInt]
  · rw [bitValueInt_partialSpreadFunction_of_ne_zero P hP x hx]
    simp [originIndicatorInt, hx]

/-- Dillon's partial-spread construction: selecting either
`2^(n/2-1)` or `2^(n/2-1)+1` pairwise disjoint half-dimensional subspaces
produces a bent function. -/
theorem isBent_partialSpreadFunction
    (P : Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)))
    (hP : IsHalfDimensionalPartialSpread P)
    (hcard : HasPartialSpreadBentCardinality P)
    (hnEven : Even n) (hhalf : 2 ≤ n / 2) :
    IsBent (partialSpreadFunction P) := by
  exact (isBent_and_bitValueInt_bentDual_of_exactGPSRepresentation
    (partialSpreadFunction P) (partialSpreadCoefficients P)
    hnEven (by omega)
    (hasExactGPSRepresentation_partialSpreadFunction P hP hcard hhalf)).1

end CryptBoolean
