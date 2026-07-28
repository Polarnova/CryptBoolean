/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FiniteField
public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandGeneral

/-!
# Linear spaces of bent functions

Finite-field multiplication supplies the half-dimensional linear spaces of
bent functions noted after the Maiorana--McFarland construction.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

/-- Binary coordinates on a positive-dimensional binary Galois field. -/
noncomputable def binaryGaloisFieldCoordinateEquiv
    (m : ℕ) (hm : 0 < m) :
    FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      GaloisField.finrank 2 hm.ne'])

/-- Multiplication by a field element, transported to binary cube
coordinates. -/
noncomputable def fieldMultiplicationCubeMap {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (a : BinaryGaloisField m) :
    FABL.F₂Cube m → FABL.F₂Cube m :=
  fun y ↦ theta.symm (a * theta y)

/-- The Maiorana--McFarland function indexed linearly by a field element. -/
noncomputable def fieldMaioranaMcFarlandFunction {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (a : BinaryGaloisField m) : BooleanFunction (m + m) :=
  fun z ↦
    let p := FABL.f₂CubeBlockEquiv m z
    FABL.f₂DotProduct p.1 (fieldMultiplicationCubeMap theta a p.2)

@[simp] theorem fieldMaioranaMcFarlandFunction_joinF₂CubeBlocks {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (a : BinaryGaloisField m) (x y : FABL.F₂Cube m) :
    fieldMaioranaMcFarlandFunction theta a
        (FABL.joinF₂CubeBlocks x y) =
      FABL.f₂DotProduct x (fieldMultiplicationCubeMap theta a y) := by
  simp [fieldMaioranaMcFarlandFunction]

/-- The field-indexed Maiorana--McFarland family depends linearly on its
field parameter. -/
noncomputable def fieldMaioranaMcFarlandLinearMap {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    BinaryGaloisField m →ₗ[FABL.𝔽₂] BooleanFunction (m + m) where
  toFun := fieldMaioranaMcFarlandFunction theta
  map_add' a b := by
    funext z
    let p := FABL.f₂CubeBlockEquiv m z
    simp only [fieldMaioranaMcFarlandFunction, fieldMultiplicationCubeMap,
      Pi.add_apply, add_mul, map_add, FABL.f₂DotProduct, dotProduct_add]
  map_smul' c a := by
    funext z
    simp only [fieldMaioranaMcFarlandFunction, fieldMultiplicationCubeMap,
      Pi.smul_apply, RingHom.id_apply]
    rw [smul_mul_assoc, map_smul, FABL.f₂DotProduct, dotProduct_smul]
    rfl

/-- Multiplication by a nonzero field parameter is a permutation of the
binary coordinate cube. -/
theorem fieldMultiplicationCubeMap_bijective {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (a : BinaryGaloisField m) (ha : a ≠ 0) :
    Function.Bijective (fieldMultiplicationCubeMap theta a) := by
  constructor
  · intro y z hyz
    apply theta.injective
    apply mul_left_cancel₀ ha
    simpa [fieldMultiplicationCubeMap] using congrArg theta hyz
  · intro z
    refine ⟨theta.symm (a⁻¹ * theta z), ?_⟩
    simp [fieldMultiplicationCubeMap, ha]

/-- Every nonzero member of the field-indexed family is bent. -/
theorem isBent_fieldMaioranaMcFarlandFunction {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (a : BinaryGaloisField m) (ha : a ≠ 0) :
    IsBent (fieldMaioranaMcFarlandFunction theta a) := by
  apply (isBent_iff_bijective_maioranaMcFarland
    (fieldMaioranaMcFarlandFunction theta a)
    (fieldMultiplicationCubeMap theta a) 0 (by
      intro x y
      have hblocks : FABL.f₂CubeBlockEquiv m (Fin.append x y) = (x, y) := by
        apply Prod.ext
        · funext i
          exact Fin.append_left x y i
        · funext i
          exact Fin.append_right x y i
      simp [fieldMaioranaMcFarlandFunction, hblocks])).2
  exact fieldMultiplicationCubeMap_bijective theta a ha

/-- Distinct field parameters give distinct members of the linear family. -/
theorem fieldMaioranaMcFarlandLinearMap_injective {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    Function.Injective (fieldMaioranaMcFarlandLinearMap theta) := by
  intro a b hab
  apply theta.symm.injective
  funext i
  let x : FABL.F₂Cube m := Pi.single i 1
  let y : FABL.F₂Cube m := theta.symm 1
  have hvalue := congrFun hab (FABL.joinF₂CubeBlocks x y)
  simpa [fieldMaioranaMcFarlandLinearMap, fieldMultiplicationCubeMap,
    x, y, FABL.f₂DotProduct, single_dotProduct] using hvalue

/-- The half-dimensional linear space obtained as the range of the
field-indexed family. -/
noncomputable def maioranaMcFarlandBentSubspace {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    Submodule FABL.𝔽₂ (BooleanFunction (m + m)) :=
  LinearMap.range (fieldMaioranaMcFarlandLinearMap theta)

/-- The constructed bent-function space has dimension `m`. -/
theorem finrank_maioranaMcFarlandBentSubspace {m : ℕ} (hm : 0 < m)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m) :
    Module.finrank FABL.𝔽₂ (maioranaMcFarlandBentSubspace theta) = m := by
  change Module.finrank FABL.𝔽₂
    (LinearMap.range (fieldMaioranaMcFarlandLinearMap theta)) = m
  rw [LinearMap.finrank_range_of_inj
    (fieldMaioranaMcFarlandLinearMap_injective theta),
    GaloisField.finrank 2 hm.ne']

/-- Every nonzero function in the constructed subspace is bent. -/
theorem isBent_of_mem_maioranaMcFarlandBentSubspace {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (f : BooleanFunction (m + m))
    (hf : f ∈ maioranaMcFarlandBentSubspace theta) (hf0 : f ≠ 0) :
    IsBent f := by
  change f ∈ LinearMap.range (fieldMaioranaMcFarlandLinearMap theta) at hf
  obtain ⟨a, rfl⟩ := hf
  apply isBent_fieldMaioranaMcFarlandFunction
  intro ha
  subst a
  apply hf0
  funext z
  simp [fieldMaioranaMcFarlandLinearMap,
    fieldMaioranaMcFarlandFunction, fieldMultiplicationCubeMap,
    FABL.f₂DotProduct]

/-- In every positive even dimension `2m`, there is an `m`-dimensional
linear space of Boolean functions whose nonzero members are bent. -/
theorem exists_halfDimensionalBentSubspace (m : ℕ) (hm : 0 < m) :
    ∃ B : Submodule FABL.𝔽₂ (BooleanFunction (m + m)),
      Module.finrank FABL.𝔽₂ B = m ∧
        ∀ f : BooleanFunction (m + m), f ∈ B → f ≠ 0 → IsBent f := by
  let theta := binaryGaloisFieldCoordinateEquiv m hm
  exact ⟨maioranaMcFarlandBentSubspace theta,
    finrank_maioranaMcFarlandBentSubspace hm theta,
    isBent_of_mem_maioranaMcFarlandBentSubspace theta⟩

end CryptBoolean
