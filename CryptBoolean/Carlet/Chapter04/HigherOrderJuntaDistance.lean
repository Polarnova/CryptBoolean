/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity

/-!
# Carlet Chapter 4 distance to coordinate juntas

A Boolean function depending on `r` coordinates has algebraic degree at most
`r`, so it is a valid Reed--Muller approximant for order-`r` nonlinearity.
-/

open Finset Set
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Invariance under one binary coordinate forces every ANF coefficient
containing that coordinate to vanish. -/
theorem anfCoeff_eq_zero_of_coordinate_invariant
    (g : BooleanFunction n) (S : Finset (Fin n)) (i : Fin n)
    (hiS : i ∈ S)
    (hinvariant : ∀ x : FABL.F₂Cube n,
      g (Function.update x i 1) = g (Function.update x i 0)) :
    FABL.anfCoeff g S = 0 := by
  classical
  let R := S.erase i
  have hiR : i ∉ R := Finset.notMem_erase i S
  have hS : S = insert i R := (Finset.insert_erase hiS).symm
  have hdisjoint : Disjoint R.powerset (R.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]
    intro T hTR hTimage
    have hiT : i ∉ T :=
      Finset.notMem_of_mem_powerset_of_notMem hTR hiR
    obtain ⟨U, hUR, hUT⟩ := Finset.mem_image.mp hTimage
    subst T
    exact hiT (Finset.mem_insert_self i U)
  have hinjective : Set.InjOn (insert i)
      (R.powerset : Set (Finset (Fin n))) := by
    intro A hAR B hBR hAB
    have hiA : i ∉ A :=
      Finset.notMem_of_mem_powerset_of_notMem hAR hiR
    have hiB : i ∉ B :=
      Finset.notMem_of_mem_powerset_of_notMem hBR hiR
    have herase := congrArg (fun T : Finset (Fin n) ↦ T.erase i) hAB
    simpa [hiA, hiB] using herase
  have hpoint (T : Finset (Fin n)) (hTR : T ∈ R.powerset) :
      g (FABL.f₂CubeOfFinset (insert i T)) =
        g (FABL.f₂CubeOfFinset T) := by
    have hiT : i ∉ T :=
      Finset.notMem_of_mem_powerset_of_notMem hTR hiR
    have hone : Function.update (FABL.f₂CubeOfFinset T) i 1 =
        FABL.f₂CubeOfFinset (insert i T) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [FABL.f₂CubeOfFinset_apply]
      · simp [FABL.f₂CubeOfFinset_apply, hji]
    have hzero : Function.update (FABL.f₂CubeOfFinset T) i 0 =
        FABL.f₂CubeOfFinset T := by
      apply Function.update_eq_self_iff.mpr
      simp [FABL.f₂CubeOfFinset_apply, hiT]
    simpa [hone, hzero] using hinvariant (FABL.f₂CubeOfFinset T)
  rw [FABL.anfCoeff, hS, Finset.powerset_insert,
    Finset.sum_union hdisjoint, Finset.sum_image hinjective]
  have heq :
      (∑ T ∈ R.powerset,
          g (FABL.f₂CubeOfFinset (insert i T))) =
        ∑ T ∈ R.powerset, g (FABL.f₂CubeOfFinset T) := by
    apply Finset.sum_congr rfl
    intro T hTR
    exact hpoint T hTR
  rw [heq, CharTwo.add_self_eq_zero]

/-- A function depending only on `I` has no ANF coefficient supported
outside `I`. -/
theorem anfCoeff_eq_zero_of_dependsOn_of_not_subset
    (g : BooleanFunction n) {I S : Finset (Fin n)}
    (hdepends : DependsOn g (I : Set (Fin n))) (hS : ¬ S ⊆ I) :
    FABL.anfCoeff g S = 0 := by
  obtain ⟨i, hiS, hiI⟩ := Finset.not_subset.mp hS
  apply anfCoeff_eq_zero_of_coordinate_invariant g S i hiS
  intro x
  apply hdepends
  intro j hjI
  have hji : j ≠ i := by
    intro h
    subst j
    exact hiI hjI
  rw [Function.update_of_ne hji, Function.update_of_ne hji]

/-- A Boolean function depending only on `I` has algebraic degree at most
the cardinality of `I`. -/
theorem functionAlgebraicDegree_le_card_of_dependsOn
    (g : BooleanFunction n) (I : Finset (Fin n))
    (hdepends : DependsOn g (I : Set (Fin n))) :
    FABL.functionAlgebraicDegree g ≤ I.card := by
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hcard
  have hnotSubset : ¬ S ⊆ I := by
    intro hsubset
    exact hcard (Finset.card_le_card hsubset)
  exact hcoeff
    (anfCoeff_eq_zero_of_dependsOn_of_not_subset g hdepends hnotSubset)

/-- Carlet's coordinate-junta bound: every function depending on a set `I`
of `r` coordinates is an admissible order-`r` approximant. -/
theorem higherOrderNonlinearity_le_hammingDistance_of_dependsOn
    (r : ℕ) (f g : BooleanFunction n) (I : Finset (Fin n))
    (hI : I.card = r) (hdepends : DependsOn g (I : Set (Fin n))) :
    higherOrderNonlinearity r f ≤ hammingDistance f g := by
  apply higherOrderNonlinearity_le_hammingDistance r f g
  rw [mem_reedMuller_iff, ← hI]
  exact functionAlgebraicDegree_le_card_of_dependsOn g I hdepends

end CryptBoolean
