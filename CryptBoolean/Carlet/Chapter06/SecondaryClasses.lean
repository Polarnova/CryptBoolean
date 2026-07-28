/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.FlatSwitching
public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarland
public import CryptBoolean.Carlet.Chapter06.NestedBent
public import FABL.Chapter06.F₂Polynomials.Interpolation

/-!
# Secondary classes of bent functions

Carlet's classes `D₀`, `D`, and `C` derived from the permutation
Maiorana--McFarland construction and affine-flat switching.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {k m : ℕ}

noncomputable local instance secondaryClassesSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) : Fintype S :=
  Fintype.ofFinite S

private def firstBlockZeroLinearMap (m : ℕ) :
    FABL.F₂Cube m →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + m) where
  toFun y := Fin.append 0 y
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp only [Pi.add_apply, Fin.append_right]
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp
    · simp only [Pi.smul_apply, Fin.append_right, RingHom.id_apply]

private theorem firstBlockZeroLinearMap_injective :
    Function.Injective (firstBlockZeroLinearMap m) := by
  intro x y hxy
  funext i
  have h := congrFun hxy (Fin.addNat i m)
  simpa [firstBlockZeroLinearMap, ← Fin.natAdd_eq_addNat] using h

private def firstBlockZeroSubspace (m : ℕ) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube (m + m)) :=
  LinearMap.range (firstBlockZeroLinearMap m)

private noncomputable def firstBlockZeroLinearEquiv (m : ℕ) :
    FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] firstBlockZeroSubspace m :=
  LinearEquiv.ofInjective (firstBlockZeroLinearMap m)
    firstBlockZeroLinearMap_injective

@[simp] private theorem firstBlockZeroLinearEquiv_apply_coe
    (y : FABL.F₂Cube m) :
    (firstBlockZeroLinearEquiv m y).1 = Fin.append 0 y :=
  rfl

private theorem mem_firstBlockZeroSubspace_append_iff
    (x y : FABL.F₂Cube m) :
    Fin.append x y ∈ firstBlockZeroSubspace m ↔ x = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    funext i
    have h := congrFun hz (Fin.castAdd m i)
    simpa [firstBlockZeroLinearMap] using h.symm
  · rintro rfl
    exact ⟨y, rfl⟩

@[simp] private theorem cubeSplitLinearEquiv_append
    (x y : FABL.F₂Cube m) :
    cubeSplitLinearEquiv m m (Fin.append x y) = (x, y) := by
  apply Prod.ext
  · funext i
    exact Fin.append_left x y i
  · funext i
    exact Fin.append_right x y i

@[simp] private theorem joinF₂CubeBlocks_eq_append
    (x y : FABL.F₂Cube m) :
    FABL.joinF₂CubeBlocks x y = Fin.append x y :=
  rfl

@[simp] private theorem booleanMaioranaMcFarlandPermutation_append
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (x y : FABL.F₂Cube m) :
    booleanMaioranaMcFarlandPermutation π g (Fin.append x y) =
      FABL.f₂DotProduct x (π y) + g y := by
  rw [← joinF₂CubeBlocks_eq_append,
    booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks]

/-- Carlet's class `D₀`, obtained by switching the zero first-block flat
of the permutation Maiorana--McFarland construction. -/
def classDZero
    (π : Equiv.Perm (FABL.F₂Cube m)) : BooleanFunction (m + m) :=
  fun z ↦
    let p := cubeSplitLinearEquiv m m z
    FABL.f₂DotProduct p.1 (π p.2) + FABL.f₂PointIndicator 0 p.1

@[simp] theorem classDZero_append
    (π : Equiv.Perm (FABL.F₂Cube m))
    (x y : FABL.F₂Cube m) :
    classDZero π (Fin.append x y) =
      FABL.f₂DotProduct x (π y) + FABL.f₂PointIndicator 0 x := by
  rw [classDZero, cubeSplitLinearEquiv_append]

private theorem affineFlatIndicator_firstBlockZero_append
    (x y : FABL.F₂Cube m) :
    affineFlatIndicator (firstBlockZeroSubspace m) 0 (Fin.append x y) =
      FABL.f₂PointIndicator 0 x := by
  classical
  rw [FABL.f₂PointIndicator_eq_ite]
  by_cases hx : x = 0
  · rw [if_pos hx, affineFlatIndicator_apply_eq_one_iff]
    simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using
      (mem_firstBlockZeroSubspace_append_iff x y).2 hx
  · rw [if_neg hx]
    simp only [affineFlatIndicator]
    rw [if_neg]
    simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using
      (mem_firstBlockZeroSubspace_append_iff x y).not.mpr hx

private theorem classDZero_eq_flatSwitch
    (π : Equiv.Perm (FABL.F₂Cube m)) :
    classDZero π =
      flatSwitch (booleanMaioranaMcFarlandPermutation π 0)
        (firstBlockZeroSubspace m) 0 := by
  funext z
  let p := cubeSplitLinearEquiv m m z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv m m).apply_symm_apply z
  rw [← hz, classDZero_append, flatSwitch, Pi.add_apply,
    booleanMaioranaMcFarlandPermutation_append,
    affineFlatIndicator_firstBlockZero_append, Pi.zero_apply, add_zero]

private theorem affineFlatWalshSum_maioranaMcFarlandZero
    (π : Equiv.Perm (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m) :
    affineFlatWalshSum (booleanMaioranaMcFarlandPermutation π 0)
        (firstBlockZeroSubspace m) 0 (Fin.append a b) =
      if b = 0 then (2 ^ m : ℤ) else 0 := by
  let e := firstBlockZeroLinearEquiv m
  have hfrequency : ∀ y : FABL.F₂Cube m,
      FABL.f₂DotProduct (Fin.append a b) (e y).1 =
        FABL.f₂DotProduct b y := by
    intro y
    rw [show (e y).1 = Fin.append 0 y by rfl,
      FABL.f₂DotProduct_append]
    simp [FABL.f₂DotProduct, dotProduct_zero]
  rw [affineFlatWalshSum_eq_bitSignInt_mul_walshTransform_restriction
    (booleanMaioranaMcFarlandPermutation π 0) (firstBlockZeroSubspace m) 0
    (Fin.append a b) e b hfrequency]
  have hrestriction :
      coordinateAffineSubspaceRestriction (booleanMaioranaMcFarlandPermutation π 0)
          (firstBlockZeroSubspace m) 0 e =
        FABL.affineFunction 0 0 := by
    funext y
    simp [coordinateAffineSubspaceRestriction_apply, e,
      booleanMaioranaMcFarlandPermutation_append,
      FABL.affineFunction, FABL.f₂DotProduct]
  rw [hrestriction, walshTransform_affineFunction]
  simp [FABL.f₂DotProduct, dotProduct_zero, bitSignInt]

/-- The exact Walsh spectrum of Carlet's class `D₀`. -/
theorem walshTransform_classDZero
    (π : Equiv.Perm (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m) :
    walshTransform (classDZero π) (Fin.append a b) =
      bitSignInt
          (FABL.f₂DotProduct b (π.symm a) +
            FABL.f₂PointIndicator 0 b) *
        (2 ^ m : ℤ) := by
  have hdifference := walshTransform_sub_flatSwitch
    (booleanMaioranaMcFarlandPermutation π 0) (firstBlockZeroSubspace m) 0
    (Fin.append a b)
  rw [← classDZero_eq_flatSwitch π,
    affineFlatWalshSum_maioranaMcFarlandZero] at hdifference
  have hbase := walshTransform_maioranaMcFarlandPermutation
    (booleanMaioranaMcFarlandPermutation π 0) 0 π
    (by
      intro x y
      exact booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks π 0 x y) a b
  simp only [Pi.zero_apply, zero_add] at hbase
  change walshTransform (booleanMaioranaMcFarlandPermutation π 0)
    (Fin.append a b) = _ at hbase
  by_cases hb : b = 0
  · subst b
    rw [hbase] at hdifference
    simp [FABL.f₂PointIndicator_eq_ite, FABL.f₂DotProduct,
      bitSignInt] at hdifference ⊢
    linarith
  · rw [if_neg hb] at hdifference
    rw [hbase] at hdifference
    rw [FABL.f₂PointIndicator_eq_ite, if_neg hb, add_zero]
    linarith

/-- Every class-`D₀` function is bent. -/
theorem isBent_classDZero
    (π : Equiv.Perm (FABL.F₂Cube m)) :
    IsBent (classDZero π) := by
  apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half _).2
  intro u
  let p := cubeSplitLinearEquiv m m u
  have hu : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv m m).apply_symm_apply u
  rw [← hu, walshTransform_classDZero, Int.natAbs_mul]
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf]
  simp [bitSignInt]

/-- The dual of a class-`D₀` function has the inverse-permutation formula
recorded by Carlet. -/
theorem bentDual_classDZero_append
    (π : Equiv.Perm (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m) :
    bentDual (classDZero π) (Fin.append a b) =
      FABL.f₂DotProduct b (π.symm a) + FABL.f₂PointIndicator 0 b := by
  have hdual := walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
    (classDZero π) (isBent_classDZero π) (Fin.append a b)
  have hhalf : (m + m) / 2 = m := by omega
  rw [hhalf, walshTransform_classDZero] at hdual
  apply bitSignInt_injective
  exact mul_right_cancel₀ (by positivity : (2 ^ m : ℤ) ≠ 0)
    (by simpa [mul_comm] using hdual.symm)

private def submoduleProdLinearEquiv
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    (E₁ × E₂) ≃ₗ[FABL.𝔽₂] E₁.prod E₂ where
  toFun p := ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def blockProductSubspace
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube (m + m)) :=
  (E₁.prod E₂).map (cubeSplitLinearEquiv m m).symm.toLinearMap

private theorem mem_blockProductSubspace_iff
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (z : FABL.F₂Cube (m + m)) :
    z ∈ blockProductSubspace E₁ E₂ ↔
      (cubeSplitLinearEquiv m m z).1 ∈ E₁ ∧
        (cubeSplitLinearEquiv m m z).2 ∈ E₂ := by
  constructor
  · rintro ⟨p, hp, hpz⟩
    have hsplit := congrArg (cubeSplitLinearEquiv m m) hpz
    have hpEq : p = cubeSplitLinearEquiv m m z := by
      simpa using hsplit
    rw [← hpEq]
    exact hp
  · intro hz
    refine ⟨cubeSplitLinearEquiv m m z, hz, ?_⟩
    exact (cubeSplitLinearEquiv m m).symm_apply_apply z

private theorem mem_blockProductSubspace_append_iff
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (x y : FABL.F₂Cube m) :
    Fin.append x y ∈ blockProductSubspace E₁ E₂ ↔
      x ∈ E₁ ∧ y ∈ E₂ := by
  rw [mem_blockProductSubspace_iff, cubeSplitLinearEquiv_append]

private theorem finrank_blockProductSubspace
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    Module.finrank FABL.𝔽₂ (blockProductSubspace E₁ E₂) =
      Module.finrank FABL.𝔽₂ E₁ + Module.finrank FABL.𝔽₂ E₂ := by
  rw [blockProductSubspace, LinearEquiv.finrank_map_eq,
    ← (submoduleProdLinearEquiv E₁ E₂).finrank_eq,
    Module.finrank_prod]

private def permutationSubmoduleEquiv
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (hπ : ∀ y, y ∈ E₂ ↔ π y ∈ FABL.perpendicularSubspace E₁) :
    E₂ ≃ FABL.perpendicularSubspace E₁ where
  toFun y := ⟨π y.1, (hπ y.1).1 y.2⟩
  invFun z := ⟨π.symm z.1, (hπ (π.symm z.1)).2 (by
    rw [π.apply_symm_apply]
    exact z.2)⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

private theorem finrank_add_finrank_eq_of_permutation_image_perpendicular
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (hπ : ∀ y, y ∈ E₂ ↔ π y ∈ FABL.perpendicularSubspace E₁) :
    Module.finrank FABL.𝔽₂ E₁ + Module.finrank FABL.𝔽₂ E₂ = m := by
  have hcard : Nat.card E₂ = Nat.card (FABL.perpendicularSubspace E₁) :=
    Nat.card_congr (permutationSubmoduleEquiv π E₁ E₂ hπ)
  rw [FABL.card_submodule_eq_two_pow_finrank,
    FABL.card_submodule_eq_two_pow_finrank,
    FABL.finrank_perpendicularSubspace] at hcard
  have hrank : Module.finrank FABL.𝔽₂ E₂ =
      m - Module.finrank FABL.𝔽₂ E₁ :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcard
  have hle : Module.finrank FABL.𝔽₂ E₁ ≤ m := by
    simpa using E₁.finrank_le
  omega

private theorem affineFlatIndicator_blockProduct_append
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (x y : FABL.F₂Cube m) :
    affineFlatIndicator (blockProductSubspace E₁ E₂) 0
        (Fin.append x y) =
      affineFlatIndicator E₁ 0 x * affineFlatIndicator E₂ 0 y := by
  classical
  by_cases hx : x ∈ E₁ <;> by_cases hy : y ∈ E₂ <;>
    simp [affineFlatIndicator, FABL.mem_binaryAffineSubspace_iff_add_mem,
      mem_blockProductSubspace_append_iff, hx, hy]

/-- Carlet's class `D`, obtained by switching a permutation
Maiorana--McFarland function on a product of subspaces. -/
noncomputable def classD
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    BooleanFunction (m + m) :=
  fun z ↦
    let p := cubeSplitLinearEquiv m m z
    FABL.f₂DotProduct p.1 (π p.2) +
      affineFlatIndicator E₁ 0 p.1 * affineFlatIndicator E₂ 0 p.2

@[simp] theorem classD_append
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (x y : FABL.F₂Cube m) :
    classD π E₁ E₂ (Fin.append x y) =
      FABL.f₂DotProduct x (π y) +
        affineFlatIndicator E₁ 0 x * affineFlatIndicator E₂ 0 y := by
  rw [classD, cubeSplitLinearEquiv_append]

private theorem classD_eq_flatSwitch
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    classD π E₁ E₂ =
      flatSwitch (booleanMaioranaMcFarlandPermutation π 0)
        (blockProductSubspace E₁ E₂) 0 := by
  funext z
  let p := cubeSplitLinearEquiv m m z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv m m).apply_symm_apply z
  rw [← hz, classD_append, flatSwitch, Pi.add_apply,
    booleanMaioranaMcFarlandPermutation_append,
    affineFlatIndicator_blockProduct_append, Pi.zero_apply, add_zero]

/-- Carlet's class `D` is bent when the permutation sends the second
switching subspace onto the perpendicular of the first. -/
theorem isBent_classD
    (π : Equiv.Perm (FABL.F₂Cube m))
    (E₁ E₂ : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (hπ : ∀ y, y ∈ E₂ ↔ π y ∈ FABL.perpendicularSubspace E₁) :
    IsBent (classD π E₁ E₂) := by
  let E := blockProductSubspace E₁ E₂
  have hErank : Module.finrank FABL.𝔽₂ E = m := by
    change Module.finrank FABL.𝔽₂ (blockProductSubspace E₁ E₂) = m
    rw [finrank_blockProductSubspace]
    exact finrank_add_finrank_eq_of_permutation_image_perpendicular π E₁ E₂ hπ
  let e : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card]
      simpa using hErank.symm)
  have hbase : IsBent (booleanMaioranaMcFarlandPermutation π 0) :=
    isBent_booleanMaioranaMcFarlandPermutation π 0
  have hrestriction :
      coordinateAffineSubspaceRestriction
        (booleanMaioranaMcFarlandPermutation π 0) E 0 e = 0 := by
    funext z
    rw [coordinateAffineSubspaceRestriction_apply, add_zero]
    let p := cubeSplitLinearEquiv m m (e z).1
    have hp : p.1 ∈ E₁ ∧ p.2 ∈ E₂ := by
      exact (mem_blockProductSubspace_iff E₁ E₂ (e z).1).1 (e z).2
    have hperp : π p.2 ∈ FABL.perpendicularSubspace E₁ :=
      (hπ p.2).1 hp.2
    have hzero := (FABL.mem_perpendicularSubspace_iff E₁ (π p.2)).1
      hperp p.1 hp.1
    change FABL.f₂DotProduct p.1 (π p.2) + 0 = 0
    rw [add_zero]
    rw [show FABL.f₂DotProduct p.1 (π p.2) =
      FABL.f₂DotProduct (π p.2) p.1 by exact dotProduct_comm _ _]
    exact hzero
  have hdegree : FABL.functionAlgebraicDegree
      (coordinateAffineSubspaceRestriction
        (booleanMaioranaMcFarlandPermutation π 0) E 0 e) ≤ 1 := by
    rw [hrestriction, FABL.functionAlgebraicDegree_zero]
    omega
  have hswitch :=
    isBent_flatSwitch_of_half_dimension_of_restriction_degree_le_one
      (booleanMaioranaMcFarlandPermutation π 0) hbase E 0 e (by omega) hdegree
  rw [classD_eq_flatSwitch]
  simpa [E] using hswitch

private def leftBlockPerpendicularLinearMap
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    FABL.perpendicularSubspace L →ₗ[FABL.𝔽₂]
      FABL.perpendicularSubspace (blockProductSubspace L ⊤) where
  toFun u := ⟨Fin.append u.1 0, by
    rw [FABL.mem_perpendicularSubspace_iff]
    intro z hz
    let p := cubeSplitLinearEquiv m m z
    have hp : p.1 ∈ L :=
      (mem_blockProductSubspace_iff L ⊤ z).1 hz |>.1
    have hz' : Fin.append p.1 p.2 = z :=
      (Fin.appendEquiv m m).apply_symm_apply z
    rw [← hz', FABL.f₂DotProduct_append]
    have hzero := (FABL.mem_perpendicularSubspace_iff L u.1).1
      u.2 p.1 hp
    rw [hzero]
    simp [FABL.f₂DotProduct, zero_dotProduct]⟩
  map_add' u v := by
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Pi.add_apply, Fin.append_left, Submodule.coe_add]
    · simp only [Pi.add_apply, Fin.append_right, Submodule.coe_add]
      simp
  map_smul' c u := by
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Pi.smul_apply, Fin.append_left, SetLike.val_smul,
        RingHom.id_apply]
    · simp only [Pi.smul_apply, Fin.append_right, SetLike.val_smul,
        RingHom.id_apply]
      simp

private theorem leftBlockPerpendicularLinearMap_injective
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    Function.Injective (leftBlockPerpendicularLinearMap L) := by
  intro u v huv
  apply Subtype.ext
  funext i
  have h := congrArg
    (fun z : FABL.perpendicularSubspace (blockProductSubspace L ⊤) ↦
      z.1 (Fin.castAdd m i)) huv
  simpa [leftBlockPerpendicularLinearMap] using h

private theorem leftBlockPerpendicularLinearMap_surjective
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    Function.Surjective (leftBlockPerpendicularLinearMap L) := by
  intro γ
  let p := cubeSplitLinearEquiv m m γ.1
  have hsecond : p.2 = 0 := by
    funext i
    have hzmem : Fin.append 0 (Pi.single i 1) ∈
        blockProductSubspace L ⊤ := by
      rw [mem_blockProductSubspace_append_iff]
      simp
    have hdot :=
      (FABL.mem_perpendicularSubspace_iff (blockProductSubspace L ⊤) γ.1).1
        γ.2 (Fin.append 0 (Pi.single i 1)) hzmem
    have hγ : Fin.append p.1 p.2 = γ.1 :=
      (Fin.appendEquiv m m).apply_symm_apply γ.1
    rw [← hγ, FABL.f₂DotProduct_append] at hdot
    simpa [FABL.f₂DotProduct, dotProduct_zero, dotProduct_single] using hdot
  have hfirst : p.1 ∈ FABL.perpendicularSubspace L := by
    rw [FABL.mem_perpendicularSubspace_iff]
    intro x hx
    have hzmem : Fin.append x 0 ∈ blockProductSubspace L ⊤ := by
      rw [mem_blockProductSubspace_append_iff]
      simp [hx]
    have hdot :=
      (FABL.mem_perpendicularSubspace_iff (blockProductSubspace L ⊤) γ.1).1
        γ.2 (Fin.append x 0) hzmem
    have hγ : Fin.append p.1 p.2 = γ.1 :=
      (Fin.appendEquiv m m).apply_symm_apply γ.1
    rw [← hγ, FABL.f₂DotProduct_append] at hdot
    simpa [FABL.f₂DotProduct, dotProduct_zero] using hdot
  refine ⟨⟨p.1, hfirst⟩, ?_⟩
  apply Subtype.ext
  apply (cubeSplitLinearEquiv m m).injective
  have hγ : Fin.append p.1 p.2 = γ.1 :=
    (Fin.appendEquiv m m).apply_symm_apply γ.1
  rw [show (leftBlockPerpendicularLinearMap L ⟨p.1, hfirst⟩).1 =
    Fin.append p.1 0 by rfl, cubeSplitLinearEquiv_append,
    ← hγ, cubeSplitLinearEquiv_append, hsecond]

private noncomputable def leftBlockPerpendicularLinearEquiv
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    FABL.perpendicularSubspace L ≃ₗ[FABL.𝔽₂]
      FABL.perpendicularSubspace (blockProductSubspace L ⊤) :=
  LinearEquiv.ofBijective (leftBlockPerpendicularLinearMap L)
    ⟨leftBlockPerpendicularLinearMap_injective L,
      leftBlockPerpendicularLinearMap_surjective L⟩

@[simp] private theorem leftBlockPerpendicularLinearEquiv_apply_coe
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (u : FABL.perpendicularSubspace L) :
    (leftBlockPerpendicularLinearEquiv L u).1 = Fin.append u.1 0 :=
  rfl

@[simp] private theorem leftBlockPerpendicularLinearEquiv_symm_apply_coe
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (q : FABL.perpendicularSubspace (blockProductSubspace L ⊤)) :
    ((leftBlockPerpendicularLinearEquiv L).symm q).1 =
      (cubeSplitLinearEquiv m m q.1).1 := by
  have h := congrArg
    (fun z : FABL.perpendicularSubspace (blockProductSubspace L ⊤) ↦ z.1)
    ((leftBlockPerpendicularLinearEquiv L).apply_symm_apply q)
  rw [leftBlockPerpendicularLinearEquiv_apply_coe] at h
  have hfirst := congrArg (fun z ↦ (cubeSplitLinearEquiv m m z).1) h
  rw [cubeSplitLinearEquiv_append] at hfirst
  exact hfirst

private theorem affineSubspaceRestrictionImbalance_eq_walshTransform_zero_cast
    (f : BooleanFunction m)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a : FABL.F₂Cube m)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E) :
    affineSubspaceRestrictionImbalance f E a =
      (walshTransform (coordinateAffineSubspaceRestriction f E a e) 0 : ℝ) := by
  classical
  rw [affineSubspaceRestrictionImbalance,
    walshTransform_cast_eq_sum_realSignView_mul_character]
  calc
    (∑ x : E, FABL.affineSubspaceRestriction (realSignView f) E a x) =
        ∑ y : FABL.F₂Cube k,
          FABL.affineSubspaceRestriction (realSignView f) E a (e y) := by
      exact (Equiv.sum_comp e.toEquiv
        (fun x : E ↦ FABL.affineSubspaceRestriction (realSignView f) E a x)).symm
    _ = ∑ y : FABL.F₂Cube k,
        realSignView (coordinateAffineSubspaceRestriction f E a e) y *
          FABL.vectorWalshCharacter 0 y := by
      apply Finset.sum_congr rfl
      intro y _hy
      simp [coordinateAffineSubspaceRestriction, realSignView,
        FABL.realSignEncodedFunction, FABL.signEncodedFunction]

private theorem isConstantOrBalancedOnAffineFlat_of_coordinate_eq_affineFunction
    (f : BooleanFunction m)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a : FABL.F₂Cube m)
    (e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E)
    (d : FABL.𝔽₂) (u : FABL.F₂Cube k)
    (hrestriction : coordinateAffineSubspaceRestriction f E a e =
      FABL.affineFunction d u) :
    IsConstantOrBalancedOnAffineFlat f E a := by
  rw [IsConstantOrBalancedOnAffineFlat]
  have himbalance :=
    affineSubspaceRestrictionImbalance_eq_walshTransform_zero_cast f E a e
  have hcard : Nat.card E = 2 ^ k := by
    calc
      Nat.card E = Nat.card (FABL.F₂Cube k) :=
        Nat.card_congr e.symm.toEquiv
      _ = 2 ^ k := by
        rw [Nat.card_eq_fintype_card, card_f₂Cube]
  have hsign : |(bitSignInt d : ℝ)| = 1 := by
    have hmul : (bitSignInt d : ℝ) * (bitSignInt d : ℝ) = 1 := by
      exact_mod_cast bitSignInt_mul_self d
    have habsmul : |(bitSignInt d : ℝ)| * |(bitSignInt d : ℝ)| = 1 := by
      rw [← abs_mul, hmul, abs_one]
    nlinarith [abs_nonneg (bitSignInt d : ℝ)]
  by_cases hu : u = 0
  · right
    rw [himbalance, hrestriction, hu, walshTransform_affineFunction,
      if_pos rfl, hcard]
    push_cast
    rw [abs_mul, hsign]
    norm_num
  · left
    have hzero : (0 : FABL.F₂Cube k) ≠ u := fun h ↦ hu h.symm
    rw [IsBalancedOnAffineFlat, himbalance, hrestriction,
      walshTransform_affineFunction, if_neg hzero]
    norm_num

private theorem isConstantOrBalancedOnAffineFlat_affineFunction
    (d : FABL.𝔽₂) (u : FABL.F₂Cube m)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (b : FABL.F₂Cube m) :
    IsConstantOrBalancedOnAffineFlat (FABL.affineFunction d u) H b := by
  let e : FABL.F₂Cube (Module.finrank FABL.𝔽₂ H) ≃ₗ[FABL.𝔽₂] H :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp)
  let c := coordinateRestrictedAffineFrequency H e u
  apply isConstantOrBalancedOnAffineFlat_of_coordinate_eq_affineFunction
    (FABL.affineFunction d u) H b e (FABL.affineFunction d u b) c
  funext y
  rw [coordinateAffineSubspaceRestriction_apply]
  simpa only [add_comm] using
    affineFunction_coordinateAffineSubspaceRestriction H e b u d y

private def perpendicularCosetPreimageEquiv
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m)
    (hflat : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a ↔
        y ∈ FABL.binaryAffineSubspace H b) :
    FABL.perpendicularSubspace L ≃
      {y : FABL.F₂Cube m // y ∈ FABL.binaryAffineSubspace H b} where
  toFun v := ⟨π.symm (v.1 + a), (hflat _).1 (by
    rw [π.apply_symm_apply, FABL.mem_binaryAffineSubspace_iff_add_mem]
    rw [add_assoc, ZModModule.add_self, add_zero]
    exact v.2)⟩
  invFun y := ⟨π y.1 + a, by
    exact (FABL.mem_binaryAffineSubspace_iff_add_mem _ _ _).1
      ((hflat y.1).2 y.2)⟩
  left_inv v := by
    apply Subtype.ext
    change π (π.symm (v.1 + a)) + a = v.1
    rw [π.apply_symm_apply, add_assoc, ZModModule.add_self, add_zero]
  right_inv y := by
    apply Subtype.ext
    change π.symm (π y.1 + a + a) = y.1
    rw [add_assoc, ZModModule.add_self, add_zero, π.symm_apply_apply]

@[simp] private theorem perpendicularCosetPreimageEquiv_apply_coe
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m)
    (hflat : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a ↔
        y ∈ FABL.binaryAffineSubspace H b)
    (v : FABL.perpendicularSubspace L) :
    (perpendicularCosetPreimageEquiv π L H a b hflat v).1 =
      π.symm (v.1 + a) :=
  rfl


private noncomputable def classCCosetEquiv
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m)
    (hflat : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a ↔
        y ∈ FABL.binaryAffineSubspace H b) :
    FABL.perpendicularSubspace (blockProductSubspace L ⊤) ≃ H :=
  (leftBlockPerpendicularLinearEquiv L).symm.toEquiv |>.trans
    ((perpendicularCosetPreimageEquiv π L H a b hflat).trans
      (affineFlatSubtypeEquiv H b).symm)

private theorem classCCosetEquiv_apply_add
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a b : FABL.F₂Cube m)
    (hflat : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a ↔
        y ∈ FABL.binaryAffineSubspace H b)
    (q : FABL.perpendicularSubspace (blockProductSubspace L ⊤)) :
    (classCCosetEquiv π L H a b hflat q).1 + b =
      π.symm (((cubeSplitLinearEquiv m m q.1).1) + a) := by
  change
    (π.symm
      (((leftBlockPerpendicularLinearEquiv L).symm q).1 + a) + b) + b = _
  rw [add_assoc, ZModModule.add_self, add_zero,
    leftBlockPerpendicularLinearEquiv_symm_apply_coe]

private theorem bentDual_booleanMaioranaMcFarlandPermutation_append
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (a b : FABL.F₂Cube m) :
    bentDual (booleanMaioranaMcFarlandPermutation π g) (Fin.append a b) =
      FABL.f₂DotProduct b (π.symm a) + g (π.symm a) := by
  rw [← joinF₂CubeBlocks_eq_append]
  exact bentDual_maioranaMcFarlandPermutation
    (booleanMaioranaMcFarlandPermutation π g) g π
      (booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks π g) a b

private theorem affineSubspaceRestrictionImbalance_classC_dual
    (π : Equiv.Perm (FABL.F₂Cube m)) (g : BooleanFunction m)
    (L H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a₁ a₂ b : FABL.F₂Cube m) (d : FABL.𝔽₂) (u : FABL.F₂Cube m)
    (hflat : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a₁ ↔
        y ∈ FABL.binaryAffineSubspace H b)
    (hg : ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a₁ →
        g y = FABL.affineFunction d u y) :
    affineSubspaceRestrictionImbalance
        (bentDual (booleanMaioranaMcFarlandPermutation π g) +
          FABL.affineFunction 0 0)
        (FABL.perpendicularSubspace (blockProductSubspace L ⊤))
        (Fin.append a₁ a₂) =
      affineSubspaceRestrictionImbalance
        (FABL.affineFunction d (u + a₂)) H b := by
  classical
  let Eperp := FABL.perpendicularSubspace (blockProductSubspace L ⊤)
  let Q : Eperp ≃ H := classCCosetEquiv π L H a₁ b hflat
  rw [affineSubspaceRestrictionImbalance,
    affineSubspaceRestrictionImbalance]
  calc
    (∑ q : Eperp,
        FABL.affineSubspaceRestriction
          (realSignView
            (bentDual (booleanMaioranaMcFarlandPermutation π g) +
              FABL.affineFunction 0 0)) Eperp (Fin.append a₁ a₂) q) =
        ∑ q : Eperp,
          FABL.affineSubspaceRestriction
            (realSignView (FABL.affineFunction d (u + a₂))) H b (Q q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      let v := (leftBlockPerpendicularLinearEquiv L).symm q
      let y := π.symm (v.1 + a₁)
      have hqcoe : q.1 = Fin.append v.1 0 := by
        have h := congrArg
          (fun z : Eperp ↦ z.1)
          ((leftBlockPerpendicularLinearEquiv L).apply_symm_apply q)
        exact h.symm
      have hinput : q.1 + Fin.append a₁ a₂ =
          Fin.append (v.1 + a₁) a₂ := by
        calc
          q.1 + Fin.append a₁ a₂ =
              Fin.append v.1 0 + Fin.append a₁ a₂ := by rw [hqcoe]
          _ = Fin.append (v.1 + a₁) (0 + a₂) :=
            (finAppend_add v.1 a₁ 0 a₂).symm
          _ = Fin.append (v.1 + a₁) a₂ := by rw [zero_add]
      have hymem : π y ∈
          FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a₁ := by
        change π (π.symm (v.1 + a₁)) ∈
          FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a₁
        rw [π.apply_symm_apply, FABL.mem_binaryAffineSubspace_iff_add_mem]
        rw [add_assoc, ZModModule.add_self, add_zero]
        exact v.2
      have hvalue :
          ((bentDual (booleanMaioranaMcFarlandPermutation π g) :
              BooleanFunction (m + m)) +
              FABL.affineFunction 0 (0 : FABL.F₂Cube (m + m)))
              (q.1 + Fin.append a₁ a₂) =
            FABL.affineFunction d (u + a₂) ((Q q).1 + b) := by
        rw [hinput, Pi.add_apply,
          bentDual_booleanMaioranaMcFarlandPermutation_append,
          hg y hymem, classCCosetEquiv_apply_add]
        have hv : (cubeSplitLinearEquiv m m q.1).1 = v.1 := by
          exact (leftBlockPerpendicularLinearEquiv_symm_apply_coe L q).symm
        rw [hv]
        change
          FABL.f₂DotProduct a₂ y + FABL.affineFunction d u y +
              FABL.affineFunction 0 0 (Fin.append (v.1 + a₁) a₂) =
            FABL.affineFunction d (u + a₂) y
        simp only [FABL.affineFunction, FABL.f₂DotProduct,
          add_dotProduct, zero_dotProduct, add_zero]
        abel
      exact congrArg
        (fun c : FABL.𝔽₂ ↦ FABL.signValue (FABL.signEncode c)) hvalue
    _ = ∑ x : H,
          FABL.affineSubspaceRestriction
            (realSignView (FABL.affineFunction d (u + a₂))) H b x := by
      exact Equiv.sum_comp Q
        (fun x : H ↦ FABL.affineSubspaceRestriction
          (realSignView (FABL.affineFunction d (u + a₂))) H b x)

/-- Every inverse image under `π` of a coset of `Lᵖ` is an affine flat. -/
def HasAffinePerpendicularCosetPreimages
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) : Prop :=
  ∀ a, ∃ (H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (b : FABL.F₂Cube m), ∀ y,
      π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a ↔
        y ∈ FABL.binaryAffineSubspace H b

/-- The offset function restricts affinely to every inverse image under
`π` of a coset of `Lᵖ`. -/
def IsAffineOnPerpendicularCosetPreimages
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (g : BooleanFunction m) : Prop :=
  ∀ a, ∃ (d : FABL.𝔽₂) (u : FABL.F₂Cube m), ∀ y,
    π y ∈ FABL.binaryAffineSubspace (FABL.perpendicularSubspace L) a →
      g y = FABL.affineFunction d u y

/-- The zero offset is affine on every perpendicular-coset preimage. -/
theorem isAffineOnPerpendicularCosetPreimages_zero
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) :
    IsAffineOnPerpendicularCosetPreimages π L 0 := by
  intro a
  refine ⟨0, 0, fun y _hy ↦ ?_⟩
  simp [FABL.affineFunction, FABL.f₂DotProduct, zero_dotProduct]

/-- Carlet's class `C`, obtained by switching a permutation
Maiorana--McFarland function on `L × V_m`. -/
noncomputable def classC
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (g : BooleanFunction m) : BooleanFunction (m + m) :=
  fun z ↦
    let p := cubeSplitLinearEquiv m m z
    FABL.f₂DotProduct p.1 (π p.2) + g p.2 +
      affineFlatIndicator L 0 p.1

@[simp] theorem classC_append
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (g : BooleanFunction m)
    (x y : FABL.F₂Cube m) :
    classC π L g (Fin.append x y) =
      FABL.f₂DotProduct x (π y) + g y + affineFlatIndicator L 0 x := by
  rw [classC, cubeSplitLinearEquiv_append]

private theorem affineFlatIndicator_top_zero
    (y : FABL.F₂Cube m) :
    affineFlatIndicator (⊤ : Submodule FABL.𝔽₂ (FABL.F₂Cube m)) 0 y = 1 := by
  classical
  simp [affineFlatIndicator, FABL.mem_binaryAffineSubspace_iff_add_mem]

private theorem classC_eq_flatSwitch
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (g : BooleanFunction m) :
    classC π L g =
      flatSwitch (booleanMaioranaMcFarlandPermutation π g)
        (blockProductSubspace L ⊤) 0 := by
  funext z
  let p := cubeSplitLinearEquiv m m z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv m m).apply_symm_apply z
  rw [← hz, classC_append, flatSwitch, Pi.add_apply,
    booleanMaioranaMcFarlandPermutation_append,
    affineFlatIndicator_blockProduct_append,
    affineFlatIndicator_top_zero, mul_one]

/-- Carlet's class `C` is bent when perpendicular-coset preimages are
affine flats and the offset restricts affinely to each of them. -/
theorem isBent_classC
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (g : BooleanFunction m)
    (hpreimages : HasAffinePerpendicularCosetPreimages π L)
    (hoffset : IsAffineOnPerpendicularCosetPreimages π L g) :
    IsBent (classC π L g) := by
  rw [classC_eq_flatSwitch]
  let E := blockProductSubspace L ⊤
  have hbase := isBent_booleanMaioranaMcFarlandPermutation π g
  apply (isBent_flatSwitch_iff_bentDual_add_linear_constant_or_balanced
    (booleanMaioranaMcFarlandPermutation π g) hbase E 0).2
  intro a
  let p := cubeSplitLinearEquiv m m a
  have ha : Fin.append p.1 p.2 = a :=
    (Fin.appendEquiv m m).apply_symm_apply a
  rw [← ha]
  obtain ⟨H, b, hflat⟩ := hpreimages p.1
  obtain ⟨d, u, hg⟩ := hoffset p.1
  have himbalance := affineSubspaceRestrictionImbalance_classC_dual
    π g L H p.1 p.2 b d u hflat hg
  have haffine := isConstantOrBalancedOnAffineFlat_affineFunction
    d (u + p.2) H b
  have hcard :
      Nat.card (FABL.perpendicularSubspace (blockProductSubspace L ⊤)) =
        Nat.card H :=
    Nat.card_congr (classCCosetEquiv π L H p.1 b hflat)
  rw [IsConstantOrBalancedOnAffineFlat] at haffine ⊢
  rcases haffine with hbalanced | hconstant
  · left
    rw [IsBalancedOnAffineFlat] at hbalanced ⊢
    rw [himbalance]
    exact hbalanced
  · right
    rw [himbalance, hcard]
    exact hconstant

/-- The basic class-`C` construction with zero offset. -/
theorem isBent_classC_zero
    (π : Equiv.Perm (FABL.F₂Cube m))
    (L : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (hpreimages : HasAffinePerpendicularCosetPreimages π L) :
    IsBent (classC π L 0) :=
  isBent_classC π L 0 hpreimages
    (isAffineOnPerpendicularCosetPreimages_zero π L)

end CryptBoolean
