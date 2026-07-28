/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.DualAffine
public import CryptBoolean.Carlet.Chapter06.SecondaryClasses

/-!
# Further secondary constructions of bent functions

Carlet's Maiorana--McFarland bent-family extension and the four-block
construction obtained by switching between the original and class-`D₀`
families.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m k p q : ℕ}

/-- The extension of Maiorana--McFarland type indexed by a family of Boolean
functions on an additional coordinate block. -/
def maioranaMcFarlandBentFamilyExtension
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (h : FABL.F₂Cube m → BooleanFunction k) :
    BooleanFunction ((m + m) + k) :=
  fun u ↦
    let blocks := (Fin.appendEquiv (m + m) k).symm u
    let xy := FABL.f₂CubeBlockEquiv m blocks.1
    h xy.2 blocks.2 + booleanMaioranaMcFarlandPermutation π g blocks.1

/-- Evaluation of the Maiorana--McFarland bent-family extension on its three
coordinate blocks. -/
@[simp] theorem maioranaMcFarlandBentFamilyExtension_append
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (h : FABL.F₂Cube m → BooleanFunction k)
    (x y : FABL.F₂Cube m) (z : FABL.F₂Cube k) :
    maioranaMcFarlandBentFamilyExtension π g h
        (Fin.append (FABL.joinF₂CubeBlocks x y) z) =
      h y z + FABL.f₂DotProduct x (π y) + g y := by
  simp [maioranaMcFarlandBentFamilyExtension,
    booleanMaioranaMcFarlandPermutation]
  abel

private theorem firstBlockSlice_maioranaMcFarlandBentFamilyExtension
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (h : FABL.F₂Cube m → BooleanFunction k) (z : FABL.F₂Cube k) :
    firstBlockSlice (maioranaMcFarlandBentFamilyExtension π g h) z =
      booleanMaioranaMcFarlandPermutation π (fun y ↦ g y + h y z) := by
  funext u
  let xy := FABL.f₂CubeBlockEquiv m u
  have hu : FABL.joinF₂CubeBlocks xy.1 xy.2 = u :=
    (FABL.f₂CubeBlockEquiv m).symm_apply_apply u
  rw [← hu]
  simp [firstBlockSlice,
    booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks]
  abel

/-- If every member of the indexed family is bent, the corresponding
Maiorana--McFarland extension is bent. -/
theorem isBent_maioranaMcFarlandBentFamilyExtension
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (h : FABL.F₂Cube m → BooleanFunction k)
    (hk : Even k) (hh : ∀ y, IsBent (h y)) :
    IsBent (maioranaMcFarlandBentFamilyExtension π g h) := by
  let F := maioranaMcFarlandBentFamilyExtension π g h
  have hslices : ∀ z, IsBent (firstBlockSlice F z) := by
    intro z
    dsimp [F]
    rw [firstBlockSlice_maioranaMcFarlandBentFamilyExtension]
    exact isBent_booleanMaioranaMcFarlandPermutation π
      (fun y ↦ g y + h y z)
  apply (isBent_iff_forall_isBent_dualSliceFunction
    F ⟨m, by omega⟩ hk hslices).2
  intro s
  let ab := FABL.f₂CubeBlockEquiv m s
  let a := ab.1
  let b := ab.2
  have hs : FABL.joinF₂CubeBlocks a b = s :=
    (FABL.f₂CubeBlockEquiv m).symm_apply_apply s
  let c := FABL.f₂DotProduct b (π.symm a) + g (π.symm a)
  have hdual :
      dualSliceFunction F s =
        h (π.symm a) + FABL.affineFunction c 0 := by
    funext z
    rw [dualSliceFunction]
    dsimp [F]
    rw [firstBlockSlice_maioranaMcFarlandBentFamilyExtension, ← hs]
    have hformula := bentDual_maioranaMcFarlandPermutation
      (booleanMaioranaMcFarlandPermutation π (fun y ↦ g y + h y z))
      (fun y ↦ g y + h y z) π
      (fun x y ↦
        booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks
          π (fun y ↦ g y + h y z) x y)
      a b
    rw [hformula]
    simp [c, FABL.affineFunction, FABL.f₂DotProduct]
    abel
  rw [hdual]
  exact (isBent_add_affineFunction_iff (h (π.symm a)) c 0).2
    (hh (π.symm a))

/-- The four-block construction combining two permutation
Maiorana--McFarland terms with a class-`D₀` switch. -/
def classDZeroFourBlock
    (π : Equiv.Perm (FABL.F₂Cube p))
    (ρ : Equiv.Perm (FABL.F₂Cube q)) (h : BooleanFunction q) :
    BooleanFunction ((p + p) + (q + q)) :=
  fun u ↦
    let blocks := (Fin.appendEquiv (p + p) (q + q)).symm u
    let xy := FABL.f₂CubeBlockEquiv p blocks.1
    let zt := FABL.f₂CubeBlockEquiv q blocks.2
    FABL.f₂DotProduct xy.1 (π xy.2) +
      FABL.f₂DotProduct zt.1 (ρ zt.2) +
      FABL.f₂PointIndicator 0 xy.1 * h zt.2

/-- Evaluation of the four-block class-`D₀` construction. -/
@[simp] theorem classDZeroFourBlock_append
    (π : Equiv.Perm (FABL.F₂Cube p))
    (ρ : Equiv.Perm (FABL.F₂Cube q)) (h : BooleanFunction q)
    (x y : FABL.F₂Cube p) (z t : FABL.F₂Cube q) :
    classDZeroFourBlock π ρ h
        (Fin.append (FABL.joinF₂CubeBlocks x y)
          (FABL.joinF₂CubeBlocks z t)) =
      FABL.f₂DotProduct x (π y) + FABL.f₂DotProduct z (ρ t) +
        FABL.f₂PointIndicator 0 x * h t := by
  simp [classDZeroFourBlock]

private theorem firstBlockSlice_classDZeroFourBlock
    (π : Equiv.Perm (FABL.F₂Cube p))
    (ρ : Equiv.Perm (FABL.F₂Cube q)) (h : BooleanFunction q)
    (z t : FABL.F₂Cube q) :
    firstBlockSlice (classDZeroFourBlock π ρ h)
        (FABL.joinF₂CubeBlocks z t) =
      if h t = 0 then
        booleanMaioranaMcFarlandPermutation π 0 +
          FABL.affineFunction (FABL.f₂DotProduct z (ρ t)) 0
      else
        classDZero π +
          FABL.affineFunction (FABL.f₂DotProduct z (ρ t)) 0 := by
  funext u
  let xy := FABL.f₂CubeBlockEquiv p u
  have hu : FABL.joinF₂CubeBlocks xy.1 xy.2 = u :=
    (FABL.f₂CubeBlockEquiv p).symm_apply_apply u
  rw [← hu]
  by_cases ht : h t = 0
  · rw [if_pos ht]
    simp [firstBlockSlice, ht,
      booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks,
      FABL.affineFunction, FABL.f₂DotProduct]
  · have htOne : h t = 1 := Fin.eq_one_of_ne_zero _ ht
    rw [if_neg ht]
    simp only [Pi.add_apply]
    have hDZero :
        classDZero π (FABL.joinF₂CubeBlocks xy.1 xy.2) =
          FABL.f₂DotProduct xy.1 (π xy.2) +
            FABL.f₂PointIndicator 0 xy.1 := by
      change classDZero π (Fin.append xy.1 xy.2) = _
      exact classDZero_append π xy.1 xy.2
    rw [firstBlockSlice, classDZeroFourBlock_append, hDZero]
    rw [htOne, mul_one]
    simp [FABL.affineFunction, FABL.f₂DotProduct]
    abel

/-- Carlet's four-block construction is bent for arbitrary Boolean `h` and
arbitrary permutations on the two coordinate pairs. -/
theorem isBent_classDZeroFourBlock
    (π : Equiv.Perm (FABL.F₂Cube p))
    (ρ : Equiv.Perm (FABL.F₂Cube q)) (h : BooleanFunction q) :
    IsBent (classDZeroFourBlock π ρ h) := by
  let F := classDZeroFourBlock π ρ h
  have hslices : ∀ u, IsBent (firstBlockSlice F u) := by
    intro u
    let zt := FABL.f₂CubeBlockEquiv q u
    let z := zt.1
    let t := zt.2
    have hu : FABL.joinF₂CubeBlocks z t = u :=
      (FABL.f₂CubeBlockEquiv q).symm_apply_apply u
    rw [← hu]
    dsimp [F]
    rw [firstBlockSlice_classDZeroFourBlock]
    by_cases ht : h t = 0
    · rw [if_pos ht]
      exact (isBent_add_affineFunction_iff
        (booleanMaioranaMcFarlandPermutation π 0)
        (FABL.f₂DotProduct z (ρ t)) 0).2
          (isBent_booleanMaioranaMcFarlandPermutation π 0)
    · rw [if_neg ht]
      exact (isBent_add_affineFunction_iff
        (classDZero π) (FABL.f₂DotProduct z (ρ t)) 0).2
          (isBent_classDZero π)
  apply (isBent_iff_forall_isBent_dualSliceFunction
    F ⟨p, by omega⟩ ⟨q, by omega⟩ hslices).2
  intro s
  let ab := FABL.f₂CubeBlockEquiv p s
  let a := ab.1
  let b := ab.2
  have hs : FABL.joinF₂CubeBlocks a b = s :=
    (FABL.f₂CubeBlockEquiv p).symm_apply_apply s
  let offset : BooleanFunction q := fun t ↦
    FABL.f₂DotProduct b (π.symm a) +
      FABL.f₂PointIndicator 0 b * h t
  have hdual :
      dualSliceFunction F s =
        booleanMaioranaMcFarlandPermutation ρ offset := by
    funext u
    let zt := FABL.f₂CubeBlockEquiv q u
    let z := zt.1
    let t := zt.2
    have hu : FABL.joinF₂CubeBlocks z t = u :=
      (FABL.f₂CubeBlockEquiv q).symm_apply_apply u
    rw [← hu, dualSliceFunction, ← hs]
    dsimp [F]
    rw [firstBlockSlice_classDZeroFourBlock]
    by_cases ht : h t = 0
    · rw [if_pos ht,
        bentDual_add_constant
          (booleanMaioranaMcFarlandPermutation π 0)
          (isBent_booleanMaioranaMcFarlandPermutation π 0)]
      have hformula := bentDual_maioranaMcFarlandPermutation
        (booleanMaioranaMcFarlandPermutation π 0) 0 π
        (fun x y ↦
          booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks π 0 x y)
        a b
      rw [hformula]
      simp [offset, ht,
        booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks]
      abel
    · have htOne : h t = 1 := Fin.eq_one_of_ne_zero _ ht
      rw [if_neg ht,
        bentDual_add_constant (classDZero π) (isBent_classDZero π)]
      rw [show FABL.joinF₂CubeBlocks a b = Fin.append a b from rfl,
        bentDual_classDZero_append]
      simp [offset, htOne,
        booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks]
      abel
  rw [hdual]
  exact isBent_booleanMaioranaMcFarlandPermutation ρ offset

end CryptBoolean
