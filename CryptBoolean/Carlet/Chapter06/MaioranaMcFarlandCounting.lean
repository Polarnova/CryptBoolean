/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.DegreeBounds
public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarland

/-!
# Counting Maiorana--McFarland and bent functions

The exact size of the original Maiorana--McFarland class and Carlet's naive
upper bound for the total number of bent functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m n : ℕ}

noncomputable local instance countingReedMullerFintype
    (r n : ℕ) : Fintype (reedMuller r n) :=
  Fintype.ofFinite (reedMuller r n)

/-- The permutation and Boolean offset parameters of the original
Maiorana--McFarland construction. -/
abbrev MaioranaMcFarlandParameters (m : ℕ) :=
  Equiv.Perm (FABL.F₂Cube m) × BooleanFunction m

/-- The Boolean function determined by a Maiorana--McFarland parameter
pair. -/
def booleanMaioranaMcFarlandOfParameters
    (p : MaioranaMcFarlandParameters m) : BooleanFunction (m + m) :=
  booleanMaioranaMcFarlandPermutation p.1 p.2

/-- The original Maiorana--McFarland parameterization is injective. -/
theorem booleanMaioranaMcFarlandOfParameters_injective :
    Function.Injective
      (booleanMaioranaMcFarlandOfParameters (m := m)) := by
  rintro ⟨π, g⟩ ⟨σ, h⟩ heq
  have hoffset : g = h := by
    funext y
    have hy := congrFun heq
      (FABL.joinF₂CubeBlocks (0 : FABL.F₂Cube m) y)
    simpa [booleanMaioranaMcFarlandOfParameters, FABL.f₂DotProduct,
      zero_dotProduct] using hy
  have hperm : π = σ := by
    apply Equiv.ext
    intro y
    funext i
    have hi := congrFun heq
      (FABL.joinF₂CubeBlocks
        (Pi.single i (1 : FABL.𝔽₂)) y)
    rw [booleanMaioranaMcFarlandOfParameters,
      booleanMaioranaMcFarlandOfParameters,
      booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks,
      booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks,
      hoffset] at hi
    simpa [FABL.f₂DotProduct, single_dotProduct] using
      (add_right_cancel hi)
  exact Prod.ext hperm hoffset

/-- The original parameter space has
`(2^m)! * 2^(2^m)` elements. -/
theorem card_maioranaMcFarlandParameters (m : ℕ) :
    Fintype.card (MaioranaMcFarlandParameters m) =
      (2 ^ m).factorial * 2 ^ (2 ^ m) := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun]
  norm_num [Fintype.card_pi, Fintype.card_fin, BooleanFunction]

/-- The finite set of distinct functions in the original
Maiorana--McFarland class. -/
noncomputable def originalMaioranaMcFarlandClass (m : ℕ) :
    Finset (BooleanFunction (m + m)) := by
  classical
  exact Finset.univ.image booleanMaioranaMcFarlandOfParameters

/-- The original Maiorana--McFarland class contains exactly
`(2^m)! * 2^(2^m)` distinct functions. -/
theorem card_originalMaioranaMcFarlandClass (m : ℕ) :
    (originalMaioranaMcFarlandClass m).card =
      (2 ^ m).factorial * 2 ^ (2 ^ m) := by
  classical
  rw [originalMaioranaMcFarlandClass,
    Finset.card_image_of_injective]
  · rw [Finset.card_univ, card_maioranaMcFarlandParameters]
  · exact booleanMaioranaMcFarlandOfParameters_injective

/-- The finite family of all `n`-variable bent Boolean functions. -/
noncomputable def bentFunctionFamily (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact Finset.univ.filter IsBent

@[simp] theorem mem_bentFunctionFamily_iff
    {f : BooleanFunction n} :
    f ∈ bentFunctionFamily n ↔ IsBent f := by
  classical
  simp [bentFunctionFamily]

/-- The original Maiorana--McFarland class is a family of bent functions. -/
theorem originalMaioranaMcFarlandClass_subset_bentFunctionFamily (m : ℕ) :
    originalMaioranaMcFarlandClass m ⊆ bentFunctionFamily (m + m) := by
  classical
  intro f hf
  rw [originalMaioranaMcFarlandClass, Finset.mem_image] at hf
  obtain ⟨p, _hp, rfl⟩ := hf
  rw [mem_bentFunctionFamily_iff]
  exact isBent_booleanMaioranaMcFarlandPermutation p.1 p.2

/-- Carlet's naive bound: in even dimension at least four, the number of
bent functions is at most the number of Boolean functions of degree at most
half the dimension. -/
theorem card_bentFunctionFamily_le_naiveBound
    (_hnEven : Even n) (hn : 4 ≤ n) :
    (bentFunctionFamily n).card ≤
      2 ^ (∑ i ∈ Finset.range (n / 2 + 1), Nat.choose n i) := by
  classical
  let lowDegreeFunctions : Finset (BooleanFunction n) :=
    (Finset.univ : Finset (reedMuller (n / 2) n)).image
      (fun f ↦ f.1)
  have hsubset : bentFunctionFamily n ⊆ lowDegreeFunctions := by
    intro f hf
    rw [mem_bentFunctionFamily_iff] at hf
    simp only [lowDegreeFunctions, Finset.mem_image]
    refine ⟨⟨f, ?_⟩, Finset.mem_univ _, rfl⟩
    exact functionAlgebraicDegree_le_half_of_isBent f hf hn
  calc
    (bentFunctionFamily n).card ≤ lowDegreeFunctions.card :=
      Finset.card_le_card hsubset
    _ = Nat.card (reedMuller (n / 2) n) := by
      simp only [lowDegreeFunctions]
      rw [Finset.card_image_of_injective]
      · rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      · exact Subtype.val_injective
    _ = 2 ^ (∑ i ∈ Finset.range (n / 2 + 1), Nat.choose n i) :=
      reedMuller_card

end CryptBoolean
