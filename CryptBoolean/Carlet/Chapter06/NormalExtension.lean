/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.Normality
public import CryptBoolean.Carlet.Chapter06.CompleteQuadratic
public import CryptBoolean.Carlet.Chapter06.DirectSum
public import CryptBoolean.Carlet.Chapter06.DualPoisson
public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarland
public import CryptBoolean.Carlet.Chapter06.NestedBent

import Mathlib.LinearAlgebra.Goursat
import Mathlib.LinearAlgebra.Projection

/-!
# Normal extensions of bent Boolean functions

Carlet Section 6.9, Definition 8 and Propositions 30--31.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {a b c k m n p r s t : ℕ}

noncomputable local instance normalExtensionSubmoduleFintype
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype S :=
  Fintype.ofFinite S

private def cubeTripleLinearEquiv (a b : ℕ) :
    FABL.F₂Cube (a + (b + b)) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube a × (FABL.F₂Cube b × FABL.F₂Cube b)) :=
  (cubeSplitLinearEquiv a (b + b)).trans
    ((LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube a)).prodCongr
      (cubeSplitLinearEquiv b b))

@[simp] private theorem append_zero_addNat
    (v : FABL.F₂Cube n) (i : Fin n) :
    Fin.append v 0 (i.addNat n) = 0 := by
  have hi : i.addNat n = Fin.natAdd n i := by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
  rw [hi, Fin.append_right]
  rfl

@[simp] private theorem zero_append_addNat
    (v : FABL.F₂Cube n) (i : Fin n) :
    Fin.append 0 v (i.addNat n) = v i := by
  have hi : i.addNat n = Fin.natAdd n i := by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
  rw [hi, Fin.append_right]

@[simp] private theorem append_addNat
    (v w : FABL.F₂Cube n) (i : Fin n) :
    Fin.append v w (i.addNat n) = w i := by
  have hi : i.addNat n = Fin.natAdd n i := by
    ext
    simp [Fin.addNat, Fin.natAdd, Nat.add_comm]
  rw [hi, Fin.append_right]

private def normalExtensionReassociationLinearEquiv (a b t : ℕ) :
    FABL.F₂Cube (a + ((b + t) + (b + t))) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube (a + (b + b)) ×
        (FABL.F₂Cube t × FABL.F₂Cube t)) where
  toFun x :=
    let q := cubeTripleLinearEquiv a (b + t) x
    let y := cubeSplitLinearEquiv b t q.2.1
    let z := cubeSplitLinearEquiv b t q.2.2
    ((cubeTripleLinearEquiv a b).symm (q.1, (y.1, z.1)), (y.2, z.2))
  invFun x :=
    let q := cubeTripleLinearEquiv a b x.1
    (cubeTripleLinearEquiv a (b + t)).symm
      (q.1,
        ((cubeSplitLinearEquiv b t).symm (q.2.1, x.2.1),
          (cubeSplitLinearEquiv b t).symm (q.2.2, x.2.2)))
  left_inv x := by
    simp [cubeTripleLinearEquiv]
  right_inv x := by
    simp [cubeTripleLinearEquiv]
  map_add' x y := by
    simpa [map_add] using
      (cubeTripleLinearEquiv a b).symm.map_add
        (((cubeTripleLinearEquiv a (b + t)) x).1,
          (((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) x).2.1).1,
           ((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) x).2.2).1))
        (((cubeTripleLinearEquiv a (b + t)) y).1,
          (((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) y).2.1).1,
           ((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) y).2.2).1))
  map_smul' c x := by
    simpa [map_smul] using
      (cubeTripleLinearEquiv a b).symm.map_smul c
        (((cubeTripleLinearEquiv a (b + t)) x).1,
          (((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) x).2.1).1,
           ((cubeSplitLinearEquiv b t)
            ((cubeTripleLinearEquiv a (b + t)) x).2.2).1))

private def normalExtensionTransLinearEquiv
    (L : FABL.F₂Cube (k + (r + r)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (M : FABL.F₂Cube (n + (s + s)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube p) :
    FABL.F₂Cube (k + ((r + s) + (r + s))) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube p :=
  (normalExtensionReassociationLinearEquiv k r s).trans
    ((L.prodCongr
      (LinearEquiv.refl FABL.𝔽₂
        (FABL.F₂Cube s × FABL.F₂Cube s))).trans
      ((cubeTripleLinearEquiv n s).symm.trans M))

private def normalExtensionAuxiliarySwapLinearEquiv (a b : ℕ) :
    FABL.F₂Cube (a + (b + b)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (a + (b + b)) :=
  (cubeTripleLinearEquiv a b).trans
    (((LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube a)).prodCongr
      (LinearEquiv.prodComm FABL.𝔽₂
        (FABL.F₂Cube b) (FABL.F₂Cube b))).trans
      (cubeTripleLinearEquiv a b).symm)

@[simp] private theorem normalExtensionAuxiliarySwapLinearEquiv_apply
    (u : FABL.F₂Cube a) (w z : FABL.F₂Cube b) :
    normalExtensionAuxiliarySwapLinearEquiv a b
        (Fin.append u (Fin.append w z)) =
      Fin.append u (Fin.append z w) := by
  apply (cubeTripleLinearEquiv a b).injective
  simp [normalExtensionAuxiliarySwapLinearEquiv, cubeTripleLinearEquiv,
    cubeSplitLinearEquiv]

private def normalExtensionHeadLinearMap (a b : ℕ) :
    FABL.F₂Cube (a + b) →ₗ[FABL.𝔽₂]
      FABL.F₂Cube (a + (b + b)) where
  toFun x :=
    let q := cubeSplitLinearEquiv a b x
    (cubeTripleLinearEquiv a b).symm (q.1, (q.2, 0))
  map_add' x y := by
    simpa [map_add] using (cubeTripleLinearEquiv a b).symm.map_add
      (((cubeSplitLinearEquiv a b) x).1,
        (((cubeSplitLinearEquiv a b) x).2, 0))
      (((cubeSplitLinearEquiv a b) y).1,
        (((cubeSplitLinearEquiv a b) y).2, 0))
  map_smul' c x := by
    simpa [map_smul] using (cubeTripleLinearEquiv a b).symm.map_smul c
      (((cubeSplitLinearEquiv a b) x).1,
        (((cubeSplitLinearEquiv a b) x).2, 0))

@[simp] private theorem normalExtensionHeadLinearMap_apply
    (u : FABL.F₂Cube a) (w : FABL.F₂Cube b) :
    normalExtensionHeadLinearMap a b (Fin.append u w) =
      Fin.append u (Fin.append w 0) := by
  apply (cubeTripleLinearEquiv a b).injective
  suffices (0 : FABL.F₂Cube b) = (fun _i : Fin b ↦ 0) by
    simpa [normalExtensionHeadLinearMap, cubeTripleLinearEquiv,
      cubeSplitLinearEquiv] using this
  funext i
  rfl

private theorem normalExtensionHeadLinearMap_injective :
    Function.Injective (normalExtensionHeadLinearMap a b) := by
  intro x y hxy
  have h := congrArg (cubeTripleLinearEquiv a b) hxy
  apply (cubeSplitLinearEquiv a b).injective
  apply Prod.ext
  · simpa [normalExtensionHeadLinearMap] using congrArg
      (fun q ↦ q.1) h
  · simpa [normalExtensionHeadLinearMap] using congrArg
      (fun q ↦ q.2.1) h

private def normalExtensionHeadSubspace (a b : ℕ) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube (a + (b + b))) :=
  LinearMap.range (normalExtensionHeadLinearMap a b)

private noncomputable def normalExtensionHeadSubspaceLinearEquiv (a b : ℕ) :
    FABL.F₂Cube (a + b) ≃ₗ[FABL.𝔽₂]
      normalExtensionHeadSubspace a b :=
  LinearEquiv.ofInjective (normalExtensionHeadLinearMap a b)
    normalExtensionHeadLinearMap_injective

@[simp] private theorem normalExtensionHeadSubspaceLinearEquiv_apply_coe
    (x : FABL.F₂Cube (a + b)) :
    (normalExtensionHeadSubspaceLinearEquiv a b x).1 =
      normalExtensionHeadLinearMap a b x :=
  rfl

private theorem normalExtensionHeadLinearMap_apply_split
    (x : FABL.F₂Cube (a + b)) :
    normalExtensionHeadLinearMap a b x =
      Fin.append (cubeSplitLinearEquiv a b x).1
        (Fin.append (cubeSplitLinearEquiv a b x).2 0) := by
  let q := cubeSplitLinearEquiv a b x
  have hx : Fin.append q.1 q.2 = x :=
    (Fin.appendEquiv a b).apply_symm_apply x
  rw [← hx, normalExtensionHeadLinearMap_apply]
  have hq : cubeSplitLinearEquiv a b (Fin.append q.1 q.2) = q := by
    simp [cubeSplitLinearEquiv]
  rw [hq]

private def normalExtensionPrefixLinearMap (a b : ℕ) :
    FABL.F₂Cube (a + (b + b)) →ₗ[FABL.𝔽₂]
      FABL.F₂Cube a where
  toFun x := (cubeTripleLinearEquiv a b x).1
  map_add' x y := by simp [map_add]
  map_smul' c x := by simp [map_smul]

@[simp] private theorem normalExtensionPrefixLinearMap_apply
    (u : FABL.F₂Cube a) (w z : FABL.F₂Cube b) :
    normalExtensionPrefixLinearMap a b
        (Fin.append u (Fin.append w z)) = u := by
  simp [normalExtensionPrefixLinearMap, cubeTripleLinearEquiv,
    cubeSplitLinearEquiv]

private theorem mem_normalExtensionHeadSubspace_iff_tail_eq_zero
    (x : FABL.F₂Cube (a + (b + b))) :
    x ∈ normalExtensionHeadSubspace a b ↔
      (cubeTripleLinearEquiv a b x).2.2 = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [normalExtensionHeadLinearMap_apply_split]
    suffices (fun _i : Fin b ↦ (0 : FABL.𝔽₂)) = 0 by
      simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv] using this
    funext i
    rfl
  · intro hx
    let q := cubeTripleLinearEquiv a b x
    have hq : q.2.2 = 0 := hx
    have hrecover :
        Fin.append q.1 (Fin.append q.2.1 q.2.2) = x := by
      exact (cubeTripleLinearEquiv a b).injective (by
        simp [q, cubeTripleLinearEquiv, cubeSplitLinearEquiv])
    refine ⟨Fin.append q.1 q.2.1, ?_⟩
    rw [normalExtensionHeadLinearMap_apply, ← hq]
    exact hrecover

private def normalExtensionProjectedIntersection
    (N : Submodule FABL.𝔽₂ (FABL.F₂Cube (a + (b + b)))) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube a) :=
  (N ⊓ normalExtensionHeadSubspace a b).map
    (normalExtensionPrefixLinearMap a b)

private theorem normalExtensionProjectedIntersection_mem_of_mem
    {N : Submodule FABL.𝔽₂ (FABL.F₂Cube (a + (b + b)))}
    {x : FABL.F₂Cube (a + (b + b))}
    (hxN : x ∈ N) (hxHead : x ∈ normalExtensionHeadSubspace a b) :
    normalExtensionPrefixLinearMap a b x ∈
      normalExtensionProjectedIntersection N :=
  ⟨x, ⟨hxN, hxHead⟩, rfl⟩

private theorem isConstantOn_projectedIntersection
    (beta : BooleanFunction a)
    (f : BooleanFunction (a + (b + b)))
    (N : Submodule FABL.𝔽₂ (FABL.F₂Cube (a + (b + b))))
    (c : FABL.𝔽₂)
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = beta u)
    (hconstant : ∀ x ∈ FABL.binaryAffineSubspace N 0, f x = c) :
    ∀ u ∈ normalExtensionProjectedIntersection N, beta u = c := by
  intro u hu
  obtain ⟨x, hx, hxu⟩ := hu
  obtain ⟨y, hy⟩ := hx.2
  let q := cubeSplitLinearEquiv a b y
  have hySplit : Fin.append q.1 q.2 = y :=
    (Fin.appendEquiv a b).apply_symm_apply y
  have hxSplit : x = Fin.append q.1 (Fin.append q.2 0) := by
    rw [← hy, ← hySplit, normalExtensionHeadLinearMap_apply]
  have huq : u = q.1 := by
    rw [← hxu, hxSplit, normalExtensionPrefixLinearMap_apply]
  rw [huq, ← hrestriction q.1 q.2, ← hxSplit]
  apply hconstant
  simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hx.1

private theorem normalExtensionHead_perpendicular_dot_eq_zero
    (γ : FABL.perpendicularSubspace (normalExtensionHeadSubspace a b))
    (u : FABL.F₂Cube a) (w : FABL.F₂Cube b) :
    FABL.f₂DotProduct γ.1 (Fin.append u (Fin.append w 0)) = 0 := by
  exact (FABL.mem_perpendicularSubspace_iff
    (normalExtensionHeadSubspace a b) γ.1).1 γ.2
      (Fin.append u (Fin.append w 0))
      ⟨Fin.append u w, normalExtensionHeadLinearMap_apply u w⟩

private theorem normalExtensionHead_perpendicular_prefix_eq_zero
    (γ : FABL.perpendicularSubspace (normalExtensionHeadSubspace a b)) :
    (cubeTripleLinearEquiv a b γ.1).1 = 0 ∧
      (cubeTripleLinearEquiv a b γ.1).2.1 = 0 := by
  constructor
  · funext i
    have h := normalExtensionHead_perpendicular_dot_eq_zero γ
      (Pi.single i 1) 0
    simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv,
      FABL.f₂DotProduct, dotProduct, Pi.single_apply,
      Fin.sum_univ_add] using h
  · funext i
    have h := normalExtensionHead_perpendicular_dot_eq_zero γ
      0 (Pi.single i 1)
    simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv,
      FABL.f₂DotProduct, dotProduct, Pi.single_apply,
      Fin.sum_univ_add] using h

private def normalExtensionTailPerpendicularLinearMap (a b : ℕ) :
    FABL.F₂Cube b →ₗ[FABL.𝔽₂]
      FABL.perpendicularSubspace (normalExtensionHeadSubspace a b) where
  toFun z := ⟨Fin.append 0 (Fin.append 0 z), by
    rw [FABL.mem_perpendicularSubspace_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    let q := cubeSplitLinearEquiv a b y
    rw [show y = Fin.append q.1 q.2 by
      exact (Fin.appendEquiv a b).apply_symm_apply y |>.symm,
      normalExtensionHeadLinearMap_apply,
      FABL.f₂DotProduct_append, FABL.f₂DotProduct_append]
    simp [FABL.f₂DotProduct, dotProduct]⟩
  map_add' x y := by
    apply Subtype.ext
    apply (cubeTripleLinearEquiv a b).injective
    have hcoordinates :
        (fun _i : Fin a ↦ (0 : FABL.𝔽₂)) = 0 ∧
          (fun _i : Fin b ↦ (0 : FABL.𝔽₂)) = 0 ∧
            (fun i : Fin b ↦ x i + y i) = x + y := by
      constructor
      · funext i
        rfl
      · constructor <;> funext i <;> rfl
    simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv, map_add] using
      hcoordinates
  map_smul' c x := by
    apply Subtype.ext
    apply (cubeTripleLinearEquiv a b).injective
    simp [cubeTripleLinearEquiv, cubeSplitLinearEquiv, map_smul,
      funext_iff]

@[simp] private theorem normalExtensionTailPerpendicularLinearMap_apply_coe
    (z : FABL.F₂Cube b) :
    (normalExtensionTailPerpendicularLinearMap a b z).1 =
      Fin.append 0 (Fin.append 0 z) :=
  rfl

private theorem normalExtensionTailPerpendicularLinearMap_injective :
    Function.Injective (normalExtensionTailPerpendicularLinearMap a b) := by
  intro x y hxy
  have h := congrArg
    (fun z : FABL.perpendicularSubspace
      (normalExtensionHeadSubspace a b) ↦ z.1) hxy
  have hsplit := congrArg (cubeTripleLinearEquiv a b) h
  simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv] using
    congrArg (fun q ↦ q.2.2) hsplit

private theorem normalExtensionTailPerpendicularLinearMap_surjective :
    Function.Surjective (normalExtensionTailPerpendicularLinearMap a b) := by
  intro γ
  let q := cubeTripleLinearEquiv a b γ.1
  refine ⟨q.2.2, ?_⟩
  have hprefix := normalExtensionHead_perpendicular_prefix_eq_zero γ
  apply Subtype.ext
  apply (cubeTripleLinearEquiv a b).injective
  have htail : cubeTripleLinearEquiv a b
      (Fin.append 0 (Fin.append 0 q.2.2)) = (0, (0, q.2.2)) := by
    have hcoordinates :
        (fun i : Fin a ↦ Fin.append 0 (Fin.append 0 q.2.2)
          (Fin.castAdd (b + b) i)) = 0 ∧
          (fun i : Fin b ↦ Fin.append 0 q.2.2
            (Fin.castAdd b i)) = 0 := by
      constructor <;> funext i
      · exact Fin.append_left 0 (Fin.append 0 q.2.2) i
      · exact Fin.append_left 0 q.2.2 i
    simpa [cubeTripleLinearEquiv, cubeSplitLinearEquiv] using hcoordinates
  rw [normalExtensionTailPerpendicularLinearMap_apply_coe, htail]
  exact Prod.ext hprefix.1.symm (Prod.ext hprefix.2.symm rfl)

private noncomputable def normalExtensionTailPerpendicularLinearEquiv
    (a b : ℕ) :
    FABL.F₂Cube b ≃ₗ[FABL.𝔽₂]
      FABL.perpendicularSubspace (normalExtensionHeadSubspace a b) :=
  LinearEquiv.ofBijective (normalExtensionTailPerpendicularLinearMap a b)
    ⟨normalExtensionTailPerpendicularLinearMap_injective,
      normalExtensionTailPerpendicularLinearMap_surjective⟩

@[simp] private theorem normalExtensionTailPerpendicularLinearEquiv_apply_coe
    (z : FABL.F₂Cube b) :
    (normalExtensionTailPerpendicularLinearEquiv a b z).1 =
      Fin.append 0 (Fin.append 0 z) :=
  rfl

@[simp] private theorem
    normalExtensionTailPerpendicularLinearEquiv_toEquiv_apply_coe
    (z : FABL.F₂Cube b) :
    ((normalExtensionTailPerpendicularLinearEquiv a b).toEquiv z).1 =
      Fin.append 0 (Fin.append 0 z) :=
  rfl

/-- The adjoint of a cube linear equivalence for the standard binary dot
pairings. -/
noncomputable def walshAdjointLinearEquiv
    (L : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s) :
    FABL.F₂Cube s ≃ₗ[FABL.𝔽₂] FABL.F₂Cube r :=
  (dotProductEquiv FABL.𝔽₂ (Fin s)).trans
    (L.dualMap.trans (dotProductEquiv FABL.𝔽₂ (Fin r)).symm)

private theorem f₂DotProduct_walshAdjointLinearEquiv
    (L : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (a : FABL.F₂Cube s) (x : FABL.F₂Cube r) :
    FABL.f₂DotProduct (walshAdjointLinearEquiv L a) x =
      FABL.f₂DotProduct a (L x) := by
  change dotProduct (walshAdjointLinearEquiv L a) x = dotProduct a (L x)
  calc
    dotProduct (walshAdjointLinearEquiv L a) x =
        (dotProductEquiv FABL.𝔽₂ (Fin r))
          (walshAdjointLinearEquiv L a) x :=
      (dotProductEquiv_apply_apply FABL.𝔽₂ (Fin r) _ _).symm
    _ = ((dotProductEquiv FABL.𝔽₂ (Fin s)) a).comp L.toLinearMap x := by
      exact DFunLike.congr_fun
        ((dotProductEquiv FABL.𝔽₂ (Fin r)).apply_symm_apply
          (((dotProductEquiv FABL.𝔽₂ (Fin s)) a).comp L.toLinearMap)) x
    _ = dotProduct a (L x) :=
      dotProductEquiv_apply_apply FABL.𝔽₂ (Fin s) _ _

/-- A linear change of input coordinates transports Walsh frequencies by
the inverse adjoint map. -/
theorem walshTransform_comp_linearEquiv
    (f : BooleanFunction s)
    (L : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (a : FABL.F₂Cube r) :
    walshTransform (f ∘ L) a =
      walshTransform f (walshAdjointLinearEquiv L.symm a) := by
  classical
  rw [walshTransform, walshTransform]
  apply Fintype.sum_equiv L.toEquiv
  intro x
  rw [walshTerm, walshTerm]
  change bitSignInt (f (L x) + FABL.f₂DotProduct a x) =
    bitSignInt (f (L x) +
      FABL.f₂DotProduct (walshAdjointLinearEquiv L.symm a) (L x))
  rw [f₂DotProduct_walshAdjointLinearEquiv, L.symm_apply_apply]

/-- Bent duals transform contragrediently under a linear change of input
coordinates. -/
theorem bentDual_comp_linearEquiv
    (f : BooleanFunction s)
    (L : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (a : FABL.F₂Cube r) :
    bentDual (f ∘ L) a =
      bentDual f (walshAdjointLinearEquiv L.symm a) := by
  rw [bentDual, bentDual, walshTransform_comp_linearEquiv]

private theorem sum_walshTransform_canonical_normalExtension
    (β : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = β u)
    (a : FABL.F₂Cube k) :
    (∑ z : FABL.F₂Cube r,
        (walshTransform f (Fin.append a (Fin.append 0 z)) : ℝ)) =
      (2 : ℝ) ^ r * ((2 : ℝ) ^ r * (walshTransform β a : ℝ)) := by
  classical
  let E := normalExtensionHeadSubspace k r
  let e := normalExtensionHeadSubspaceLinearEquiv k r
  let c : FABL.F₂Cube (k + r) := Fin.append a 0
  let d : FABL.F₂Cube (k + (r + r)) := Fin.append a (Fin.append 0 0)
  have hd : ∀ y : FABL.F₂Cube (k + r),
      FABL.f₂DotProduct d (e y).1 = FABL.f₂DotProduct c y := by
    intro y
    let q := cubeSplitLinearEquiv k r y
    have hy : Fin.append q.1 q.2 = y :=
      (Fin.appendEquiv k r).apply_symm_apply y
    rw [← hy]
    rw [normalExtensionHeadSubspaceLinearEquiv_apply_coe,
      normalExtensionHeadLinearMap_apply]
    change FABL.f₂DotProduct
        (Fin.append a (Fin.append 0 0))
        (Fin.append q.1 (Fin.append q.2 0)) =
      FABL.f₂DotProduct (Fin.append a 0) (Fin.append q.1 q.2)
    simp_rw [FABL.f₂DotProduct_append]
    simp [FABL.f₂DotProduct, dotProduct]
  have hpoisson := sum_walshTransform_perpendicularCoset_eq_restriction
    f E 0 e c d hd
  have hlocal :
      coordinateAffineSubspaceRestriction f E 0 e =
        booleanDirectSum β (0 : BooleanFunction r) := by
    funext y
    let q := cubeSplitLinearEquiv k r y
    rw [coordinateAffineSubspaceRestriction_apply]
    rw [add_zero]
    change f ((e y).1) = booleanDirectSum β (0 : BooleanFunction r) y
    rw [normalExtensionHeadSubspaceLinearEquiv_apply_coe,
      normalExtensionHeadLinearMap_apply_split, hrestriction]
    simp [booleanDirectSum, cubeSplitLinearEquiv]
  have hcard : Nat.card (FABL.perpendicularSubspace E) = 2 ^ r := by
    calc
      Nat.card (FABL.perpendicularSubspace E) =
          Nat.card (FABL.F₂Cube r) :=
        Nat.card_congr
          (normalExtensionTailPerpendicularLinearEquiv k r).symm.toEquiv
      _ = 2 ^ r := by
        rw [Nat.card_eq_fintype_card, card_f₂Cube]
  have hlhs :
      (∑ u : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter 0 (d + u.1) *
            (walshTransform f (d + u.1) : ℝ)) =
        ∑ z : FABL.F₂Cube r,
          (walshTransform f (Fin.append a (Fin.append 0 z)) : ℝ) := by
    rw [← Fintype.sum_equiv
      (normalExtensionTailPerpendicularLinearEquiv k r).toEquiv
      (fun z : FABL.F₂Cube r ↦
        (walshTransform f (Fin.append a (Fin.append 0 z)) : ℝ))
      (fun u : FABL.perpendicularSubspace E ↦
        FABL.vectorWalshCharacter 0 (d + u.1) *
          (walshTransform f (d + u.1) : ℝ))]
    intro z
    rw [normalExtensionTailPerpendicularLinearEquiv_toEquiv_apply_coe]
    have hadd :
        d + Fin.append 0 (Fin.append 0 z) =
          Fin.append a (Fin.append 0 z) := by
      apply (cubeTripleLinearEquiv k r).injective
      simp [d, cubeTripleLinearEquiv, cubeSplitLinearEquiv, map_add,
        funext_iff]
    rw [hadd]
    simp
  have hzeroWalsh :
      walshTransform (0 : BooleanFunction r) 0 = (2 : ℤ) ^ r := by
    rw [walshTransform]
    calc
      (∑ x : FABL.F₂Cube r, walshTerm (0 : BooleanFunction r) 0 x) =
          ∑ _x : FABL.F₂Cube r, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        norm_num [walshTerm, bitSignInt, FABL.f₂DotProduct, dotProduct]
      _ = (2 : ℤ) ^ r := by simp
  have hwalshLocal :
      walshTransform (coordinateAffineSubspaceRestriction f E 0 e) c =
        walshTransform β a * (2 : ℤ) ^ r := by
    rw [hlocal, show c = Fin.append a 0 by rfl,
      walshTransform_booleanDirectSum_append, hzeroWalsh]
  rw [hlhs, hcard, hwalshLocal] at hpoisson
  simpa [mul_assoc, mul_left_comm, mul_comm] using hpoisson

/-- In standard extension coordinates, duality exchanges the two equal
complementary blocks. -/
theorem bentDual_canonical_normalExtension
    (β : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hβ : IsBent β) (hf : IsBent f)
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = β u)
    (a : FABL.F₂Cube k) (z : FABL.F₂Cube r) :
    bentDual f (Fin.append a (Fin.append 0 z)) = bentDual β a := by
  classical
  have hhalf : (k + (r + r)) / 2 = k / 2 + r := by
    rcases even_of_isBent β hβ with ⟨q, hq⟩
    omega
  have hfWalsh (y : FABL.F₂Cube r) :
      (walshTransform f (Fin.append a (Fin.append 0 y)) : ℝ) =
        (2 : ℝ) ^ ((k + (r + r)) / 2) *
          (bitSignInt
            (bentDual f (Fin.append a (Fin.append 0 y))) : ℝ) := by
    exact_mod_cast
      walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
        f hf (Fin.append a (Fin.append 0 y))
  have hβWalsh :
      (walshTransform β a : ℝ) =
        (2 : ℝ) ^ (k / 2) * (bitSignInt (bentDual β a) : ℝ) := by
    exact_mod_cast
      walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual β hβ a
  have hsum := sum_walshTransform_canonical_normalExtension
    β f hrestriction a
  have hscaled :
      (2 : ℝ) ^ (k / 2 + r) *
          (∑ y : FABL.F₂Cube r,
            (bitSignInt
              (bentDual f (Fin.append a (Fin.append 0 y))) : ℝ)) =
        (2 : ℝ) ^ (k / 2 + r) *
          ((2 : ℝ) ^ r * (bitSignInt (bentDual β a) : ℝ)) := by
    calc
      (2 : ℝ) ^ (k / 2 + r) *
          (∑ y : FABL.F₂Cube r,
            (bitSignInt
              (bentDual f (Fin.append a (Fin.append 0 y))) : ℝ)) =
          ∑ y : FABL.F₂Cube r,
            (walshTransform f (Fin.append a (Fin.append 0 y)) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [hfWalsh, hhalf]
      _ = (2 : ℝ) ^ r *
          ((2 : ℝ) ^ r * (walshTransform β a : ℝ)) := hsum
      _ = (2 : ℝ) ^ (k / 2 + r) *
          ((2 : ℝ) ^ r * (bitSignInt (bentDual β a) : ℝ)) := by
        rw [hβWalsh, pow_add]
        ring
  have hsignSumReal :
      (∑ y : FABL.F₂Cube r,
        (bitSignInt
          (bentDual f (Fin.append a (Fin.append 0 y))) : ℝ)) =
        (2 : ℝ) ^ r * (bitSignInt (bentDual β a) : ℝ) :=
    mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (k / 2 + r) ≠ 0) hscaled
  have hsignSum :
      (∑ y : FABL.F₂Cube r,
        bitSignInt (bentDual f (Fin.append a (Fin.append 0 y)))) =
        (2 : ℤ) ^ r * bitSignInt (bentDual β a) := by
    exact_mod_cast hsignSumReal
  let mismatch : BooleanFunction r := fun y ↦
    bentDual f (Fin.append a (Fin.append 0 y)) + bentDual β a
  have hsignSelf :
      bitSignInt (bentDual β a) * bitSignInt (bentDual β a) = 1 := by
    by_cases ht : bentDual β a = 1
    · simp [bitSignInt_eq_if_one, ht]
    · have htZero : bentDual β a = 0 := by
        by_contra hzero
        exact ht (Fin.eq_one_of_ne_zero (bentDual β a) hzero)
      simp [bitSignInt_eq_if_one, htZero]
  have hmismatchWalsh : walshTransform mismatch 0 = (2 : ℤ) ^ r := by
    rw [walshTransform]
    calc
      (∑ y : FABL.F₂Cube r, walshTerm mismatch 0 y) =
          ∑ y : FABL.F₂Cube r,
            bitSignInt (bentDual β a) *
              bitSignInt
                (bentDual f (Fin.append a (Fin.append 0 y))) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [walshTerm]
        have hdot : FABL.f₂DotProduct 0 y = 0 := by
          simp [FABL.f₂DotProduct, dotProduct]
        rw [hdot, add_zero]
        change bitSignInt
            (bentDual f (Fin.append a (Fin.append 0 y)) + bentDual β a) =
          bitSignInt (bentDual β a) *
            bitSignInt (bentDual f (Fin.append a (Fin.append 0 y)))
        rw [bitSignInt_add]
        ring
      _ = bitSignInt (bentDual β a) *
          ∑ y : FABL.F₂Cube r,
            bitSignInt
              (bentDual f (Fin.append a (Fin.append 0 y))) := by
        rw [Finset.mul_sum]
      _ = bitSignInt (bentDual β a) *
          ((2 : ℤ) ^ r * bitSignInt (bentDual β a)) := by
        rw [hsignSum]
      _ = (2 : ℤ) ^ r := by
        calc
          bitSignInt (bentDual β a) *
              ((2 : ℤ) ^ r * bitSignInt (bentDual β a)) =
              (2 : ℤ) ^ r *
                (bitSignInt (bentDual β a) * bitSignInt (bentDual β a)) := by
            ring
          _ = (2 : ℤ) ^ r := by rw [hsignSelf, mul_one]
  have hmismatchWeight : hammingWeight mismatch = 0 := by
    have hweight := walshTransform_zero_eq_two_pow_sub_two_weight mismatch
    rw [hmismatchWalsh] at hweight
    omega
  have hmismatchZero : mismatch z = 0 := by
    rw [hammingWeight_eq_card_support] at hmismatchWeight
    by_contra hz
    have hzOne : mismatch z = 1 := Fin.eq_one_of_ne_zero (mismatch z) hz
    have hzMem : z ∈ support mismatch := (mem_support mismatch z).2 hzOne
    have hpositive : 0 < (support mismatch).card := Finset.card_pos.mpr ⟨z, hzMem⟩
    omega
  have h := congrArg (fun q : FABL.𝔽₂ ↦ q + bentDual β a) hmismatchZero
  simpa [mismatch, add_assoc, ZModModule.add_self] using h

/-- Replace the restriction on the distinguished `W₂ = 0` flat in
standard normal-extension coordinates. -/
def canonicalNormalExtensionReplacement
    (β' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r))) :
    BooleanFunction (k + (r + r)) := fun x ↦
  let p := (Fin.appendEquiv k (r + r)).symm x
  let q := (Fin.appendEquiv r r).symm p.2
  if q.2 = 0 then β' p.1 else f x

@[simp] theorem canonicalNormalExtensionReplacement_apply_append
    (β' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (u : FABL.F₂Cube k) (w z : FABL.F₂Cube r) :
    canonicalNormalExtensionReplacement β' f
        (Fin.append u (Fin.append w z)) =
      if z = 0 then β' u else f (Fin.append u (Fin.append w z)) := by
  simp [canonicalNormalExtensionReplacement]

private theorem canonicalNormalExtensionReplacement_eq_on_head
    (beta' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (x : FABL.F₂Cube (k + (r + r)))
    (hx : x ∈ normalExtensionHeadSubspace k r) :
    canonicalNormalExtensionReplacement beta' f x =
      beta' (normalExtensionPrefixLinearMap k r x) := by
  let q := cubeTripleLinearEquiv k r x
  have hq : q.2.2 = 0 :=
    (mem_normalExtensionHeadSubspace_iff_tail_eq_zero x).1 hx
  have hxSplit : Fin.append q.1 (Fin.append q.2.1 q.2.2) = x := by
    exact (cubeTripleLinearEquiv k r).injective (by
      simp [q, cubeTripleLinearEquiv, cubeSplitLinearEquiv])
  rw [← hxSplit, canonicalNormalExtensionReplacement_apply_append,
    if_pos hq, normalExtensionPrefixLinearMap_apply]

private theorem canonicalNormalExtensionReplacement_eq_off_head
    (beta' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (x : FABL.F₂Cube (k + (r + r)))
    (hx : x ∉ normalExtensionHeadSubspace k r) :
    canonicalNormalExtensionReplacement beta' f x = f x := by
  let q := cubeTripleLinearEquiv k r x
  have hq : q.2.2 ≠ 0 := by
    intro hzero
    exact hx ((mem_normalExtensionHeadSubspace_iff_tail_eq_zero x).2 hzero)
  have hxSplit : Fin.append q.1 (Fin.append q.2.1 q.2.2) = x := by
    exact (cubeTripleLinearEquiv k r).injective (by
      simp [q, cubeTripleLinearEquiv, cubeSplitLinearEquiv])
  rw [← hxSplit, canonicalNormalExtensionReplacement_apply_append,
    if_neg hq, hxSplit]

private theorem walshTerm_canonicalNormalExtensionReplacement_sub
    (β β' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = β u)
    (a u : FABL.F₂Cube k) (b z w c : FABL.F₂Cube r) :
    walshTerm (canonicalNormalExtensionReplacement β' f)
        (Fin.append a (Fin.append b z))
        (Fin.append u (Fin.append w c)) -
      walshTerm f (Fin.append a (Fin.append b z))
        (Fin.append u (Fin.append w c)) =
      if c = 0 then
        (bitSignInt (β' u + FABL.f₂DotProduct a u) -
          bitSignInt (β u + FABL.f₂DotProduct a u)) *
            bitSignInt (FABL.f₂DotProduct b w)
      else 0 := by
  by_cases hc : c = 0
  · subst c
    rw [if_pos rfl, walshTerm, walshTerm,
      canonicalNormalExtensionReplacement_apply_append, if_pos rfl,
      hrestriction, FABL.f₂DotProduct_append,
      FABL.f₂DotProduct_append]
    simp only [FABL.f₂DotProduct, dotProduct_zero, add_zero]
    simp_rw [bitSignInt_add]
    ring
  · rw [if_neg hc, walshTerm, walshTerm,
      canonicalNormalExtensionReplacement_apply_append, if_neg hc]
    ring

private theorem walshTransform_canonicalNormalExtensionReplacement_sub
    (β β' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = β u)
    (a : FABL.F₂Cube k) (b z : FABL.F₂Cube r) :
    walshTransform (canonicalNormalExtensionReplacement β' f)
        (Fin.append a (Fin.append b z)) -
      walshTransform f (Fin.append a (Fin.append b z)) =
      (walshTransform β' a - walshTransform β a) *
        walshTransform (0 : BooleanFunction r) b := by
  classical
  rw [walshTransform, walshTransform, ← Finset.sum_sub_distrib]
  calc
    (∑ x : FABL.F₂Cube (k + (r + r)),
        (walshTerm (canonicalNormalExtensionReplacement β' f)
          (Fin.append a (Fin.append b z)) x -
        walshTerm f (Fin.append a (Fin.append b z)) x)) =
        ∑ p : FABL.F₂Cube k × (FABL.F₂Cube r × FABL.F₂Cube r),
          (walshTerm (canonicalNormalExtensionReplacement β' f)
            (Fin.append a (Fin.append b z))
              (Fin.append p.1 (Fin.append p.2.1 p.2.2)) -
          walshTerm f (Fin.append a (Fin.append b z))
            (Fin.append p.1 (Fin.append p.2.1 p.2.2))) := by
      apply Fintype.sum_equiv (cubeTripleLinearEquiv k r).toEquiv
      intro x
      have hx :
          Fin.append ((cubeTripleLinearEquiv k r x).1)
              (Fin.append (cubeTripleLinearEquiv k r x).2.1
                (cubeTripleLinearEquiv k r x).2.2) = x := by
        apply (cubeTripleLinearEquiv k r).injective
        simp [cubeTripleLinearEquiv, cubeSplitLinearEquiv]
      exact (congrArg
        (fun y ↦
          walshTerm (canonicalNormalExtensionReplacement β' f)
              (Fin.append a (Fin.append b z)) y -
            walshTerm f (Fin.append a (Fin.append b z)) y) hx).symm
    _ = ∑ u : FABL.F₂Cube k,
        ∑ w : FABL.F₂Cube r,
          ∑ c : FABL.F₂Cube r,
            (walshTerm (canonicalNormalExtensionReplacement β' f)
              (Fin.append a (Fin.append b z))
                (Fin.append u (Fin.append w c)) -
            walshTerm f (Fin.append a (Fin.append b z))
              (Fin.append u (Fin.append w c))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Fintype.sum_prod_type]
    _ = ∑ u : FABL.F₂Cube k,
        ∑ w : FABL.F₂Cube r,
          (bitSignInt (β' u + FABL.f₂DotProduct a u) -
            bitSignInt (β u + FABL.f₂DotProduct a u)) *
              bitSignInt (FABL.f₂DotProduct b w) := by
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro w _hw
      simp_rw [walshTerm_canonicalNormalExtensionReplacement_sub
        β β' f hrestriction a u b z w]
      simp
    _ = (∑ u : FABL.F₂Cube k,
          (bitSignInt (β' u + FABL.f₂DotProduct a u) -
            bitSignInt (β u + FABL.f₂DotProduct a u))) *
        ∑ w : FABL.F₂Cube r,
          bitSignInt (FABL.f₂DotProduct b w) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
    _ = (walshTransform β' a - walshTransform β a) *
        walshTransform (0 : BooleanFunction r) b := by
      congr 1
      · rw [walshTransform, walshTransform,
          ← Finset.sum_sub_distrib]
        rfl
      · rw [walshTransform]
        apply Finset.sum_congr rfl
        intro w _hw
        simp [walshTerm, FABL.f₂DotProduct, dotProduct]

/-- Carlet Proposition 31 in standard decomposition coordinates: replacing
the smaller bent restriction preserves bentness. -/
theorem isBent_canonicalNormalExtensionReplacement
    (β β' : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hβ : IsBent β) (hβ' : IsBent β') (hf : IsBent f)
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = β u) :
    IsBent (canonicalNormalExtensionReplacement β' f) := by
  classical
  apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
    (canonicalNormalExtensionReplacement β' f)).2
  intro x
  let q := cubeTripleLinearEquiv k r x
  have hx : Fin.append q.1 (Fin.append q.2.1 q.2.2) = x := by
    change (cubeTripleLinearEquiv k r).symm q = x
    exact (cubeTripleLinearEquiv k r).symm_apply_apply x
  rw [← hx]
  have hzeroWalsh :
      walshTransform (0 : BooleanFunction r) q.2.1 =
        if q.2.1 = 0 then (2 : ℤ) ^ r else 0 := by
    have hzeroFunction :
        (0 : BooleanFunction r) = FABL.affineFunction 0 0 := by
      funext y
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
    rw [hzeroFunction, walshTransform_affineFunction]
    simp [bitSignInt_eq_if_one]
  have hdifference := walshTransform_canonicalNormalExtensionReplacement_sub
    β β' f hrestriction q.1 q.2.1 q.2.2
  by_cases hq : q.2.1 = 0
  · have hhalf : (k + (r + r)) / 2 = k / 2 + r := by
      rcases even_of_isBent β hβ with ⟨s, hs⟩
      omega
    have hrawF :=
      walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
        f hf (Fin.append q.1 (Fin.append q.2.1 q.2.2))
    have hdual := bentDual_canonical_normalExtension
      β f hβ hf hrestriction q.1 q.2.2
    have hrawβ :=
      walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual β hβ q.1
    have hrawβ' :=
      walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual β' hβ' q.1
    rw [hq, if_pos rfl] at hzeroWalsh
    rw [hq] at hrawF hdifference
    rw [hdual] at hrawF
    rw [hzeroWalsh] at hdifference
    have hreplacement :
        walshTransform (canonicalNormalExtensionReplacement β' f)
            (Fin.append q.1 (Fin.append 0 q.2.2)) =
          (2 : ℤ) ^ ((k + (r + r)) / 2) *
            bitSignInt (bentDual β' q.1) := by
      calc
        walshTransform (canonicalNormalExtensionReplacement β' f)
            (Fin.append q.1 (Fin.append 0 q.2.2)) =
            walshTransform f (Fin.append q.1 (Fin.append 0 q.2.2)) +
              (walshTransform β' q.1 - walshTransform β q.1) *
                (2 : ℤ) ^ r := by
          omega
        _ = (2 : ℤ) ^ ((k + (r + r)) / 2) *
            bitSignInt (bentDual β' q.1) := by
          rw [hrawF, hrawβ, hrawβ', hhalf, pow_add]
          ring
    rw [hq, hreplacement, Int.natAbs_mul, Int.natAbs_pow]
    have hsign : (bitSignInt (bentDual β' q.1)).natAbs = 1 := by
      rw [bitSignInt_eq_if_one]
      split <;> simp
    rw [hsign, mul_one]
    norm_num
  · rw [if_neg hq] at hzeroWalsh
    rw [hzeroWalsh, mul_zero] at hdifference
    have heq :
        walshTransform (canonicalNormalExtensionReplacement β' f)
            (Fin.append q.1 (Fin.append q.2.1 q.2.2)) =
          walshTransform f (Fin.append q.1 (Fin.append q.2.1 q.2.2)) := by
      omega
    rw [heq]
    exact natAbs_walshTransform_eq_two_pow_half_of_isBent f hf _

/-- Carlet Definition 8, expressed invariantly under a linear choice of
coordinates for the decomposition `V = U ⊕ W₁ ⊕ W₂`. -/
def IsNormalExtension
    (β : BooleanFunction k) (f : BooleanFunction n) : Prop :=
  IsBent β ∧ IsBent f ∧
    ∃ m : ℕ,
      ∃ L : FABL.F₂Cube (k + (m + m)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n,
        ∀ u w,
          f (L (Fin.append u (Fin.append w 0))) = β u

/-- The Boolean function on the zero-dimensional cube with value `ε`. -/
def zeroDimensionalBooleanFunction (ε : FABL.𝔽₂) : BooleanFunction 0 :=
  fun _ ↦ ε

@[simp] theorem zeroDimensionalBooleanFunction_apply
    (ε : FABL.𝔽₂) (x : FABL.F₂Cube 0) :
    zeroDimensionalBooleanFunction ε x = ε :=
  rfl

/-- Every Boolean function on the zero-dimensional cube is bent. -/
theorem isBent_zeroDimensionalBooleanFunction (ε : FABL.𝔽₂) :
    IsBent (zeroDimensionalBooleanFunction ε) := by
  apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
    (zeroDimensionalBooleanFunction ε)).2
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  fin_cases ε <;>
    simp [walshTransform, walshTerm, zeroDimensionalBooleanFunction,
      bitSignInt_eq_if_one, FABL.f₂DotProduct, dotProduct] <;>
    split <;> simp

/-- The linear-subspace convention for normality used in Carlet Section 6.9:
`f` is constant on a subspace of half the ambient dimension. -/
def IsSubspaceNormal (f : BooleanFunction n) : Prop :=
  ∃ H : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
    Module.finrank FABL.𝔽₂ H = n / 2 ∧
      IsConstantOnAffineFlat f H 0

/-- Linear changes of input coordinates preserve the linear-subspace
normality convention of Section 6.9. -/
theorem isSubspaceNormal_comp_linearEquiv_iff
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    IsSubspaceNormal (f ∘ L) ↔ IsSubspaceNormal f := by
  classical
  have transport
      (g : BooleanFunction n)
      (A : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
      (h : IsSubspaceNormal (g ∘ A)) : IsSubspaceNormal g := by
    obtain ⟨H, hHrank, c, hconstant⟩ := h
    let K := H.map A.toLinearMap
    refine ⟨K, ?_, c, ?_⟩
    · dsimp [K]
      rw [LinearEquiv.finrank_map_eq, hHrank]
    · intro y hy
      have hyK : y ∈ K := by
        simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hy
      obtain ⟨x, hxH, hxy⟩ := hyK
      have hxFlat : x ∈ FABL.binaryAffineSubspace H 0 := by
        simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hxH
      have hxValue := hconstant x hxFlat
      change g (A x) = c at hxValue
      change A x = y at hxy
      rw [hxy] at hxValue
      exact hxValue
  constructor
  · exact transport f L
  · intro hf
    apply transport (f ∘ L) L.symm
    convert hf using 1
    funext x
    simp

private theorem exists_superSubspace_finrank_eq
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hHk : Module.finrank FABL.𝔽₂ H ≤ k)
    (hkn : k ≤ n) :
    ∃ P : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      H ≤ P ∧ Module.finrank FABL.𝔽₂ P = k := by
  have hambient : Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
    simp [Module.finrank_fintype_fun_eq_card]
  induction k, hHk using Nat.le_induction with
  | base => exact ⟨H, le_rfl, rfl⟩
  | succ k _hk ih =>
      have hkn' : k ≤ n := (Nat.le_succ k).trans hkn
      obtain ⟨P, hHP, hPrank⟩ := ih hkn'
      have hPambient : Module.finrank FABL.𝔽₂ P <
          Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) := by
        rw [hPrank, hambient]
        exact hkn
      obtain ⟨v, hv⟩ := P.exists_of_finrank_lt hPambient
      have hvP : v ∉ P := by simpa using hv 1 one_ne_zero
      let Q := P ⊔ Submodule.span FABL.𝔽₂ {v}
      refine ⟨Q, hHP.trans le_sup_left, ?_⟩
      dsimp [Q]
      rw [Submodule.finrank_sup_span_singleton hvP, hPrank]

private theorem exists_subspace_le_finrank_eq
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hk : k ≤ Module.finrank FABL.𝔽₂ H) :
    ∃ P : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      P ≤ H ∧ Module.finrank FABL.𝔽₂ P = k := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hk
  let w : Fin k → FABL.F₂Cube n := fun i ↦ (v i).1
  have hw : LinearIndependent FABL.𝔽₂ w := by
    exact hv.map' H.subtype (Submodule.ker_subtype H)
  let P := Submodule.span FABL.𝔽₂ (Set.range w)
  refine ⟨P, ?_, ?_⟩
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    exact (v i).2
  · dsimp [P]
    rw [finrank_span_eq_card hw]
    simp

private theorem exists_bent_eq_zero_on_subspace
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hn : Even n)
    (hH : Module.finrank FABL.𝔽₂ H ≤ n / 2) :
    ∃ γ : BooleanFunction n, IsBent γ ∧
      ∀ x ∈ H, γ x = 0 := by
  rcases hn with ⟨d, rfl⟩
  have hhalf : (d + d) / 2 = d := by omega
  rw [hhalf] at hH
  obtain ⟨P, hHP, hPrank⟩ :=
    exists_superSubspace_finrank_eq H hH (by omega)
  obtain ⟨Q, hcompl⟩ := P.exists_isCompl
  have hQrank : Module.finrank FABL.𝔽₂ Q = d := by
    have hsum : Module.finrank FABL.𝔽₂ P +
        Module.finrank FABL.𝔽₂ Q = d + d := by
      simpa [Module.finrank_fintype_fun_eq_card] using
        Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hPrank] at hsum
    omega
  let eP : FABL.F₂Cube d ≃ₗ[FABL.𝔽₂] P :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hPrank, Module.finrank_fintype_fun_eq_card])
  let eQ : FABL.F₂Cube d ≃ₗ[FABL.𝔽₂] Q :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hQrank, Module.finrank_fintype_fun_eq_card])
  let L : FABL.F₂Cube (d + d) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (d + d) :=
    (cubeSplitLinearEquiv d d).trans
      ((eP.prodCongr eQ).trans (P.prodEquivOfIsCompl Q hcompl))
  let base : BooleanFunction (d + d) := FABL.innerProductModTwoBit
  let γ : BooleanFunction (d + d) := base ∘ L.symm
  have hbase : IsBent base := by
    change FABL.IsBent (FABL.innerProductModTwo d)
    exact FABL.isBent_innerProductModTwo d
  have hγ : IsBent γ :=
    (isBent_comp_affineEquiv_iff base L.symm.toAffineEquiv).2 hbase
  refine ⟨γ, hγ, ?_⟩
  intro x hx
  have hxP : x ∈ P := hHP hx
  let u : FABL.F₂Cube d := eP.symm ⟨x, hxP⟩
  have hL : L (Fin.append u 0) = x := by
    change (P.prodEquivOfIsCompl Q hcompl)
      ((eP.prodCongr eQ)
        ((cubeSplitLinearEquiv d d) (Fin.append u 0))) = x
    simp [cubeSplitLinearEquiv, u, funext_iff]
  change base (L.symm x) = 0
  rw [← hL, L.symm_apply_apply]
  change FABL.innerProductModTwoBit
    (FABL.joinF₂CubeBlocks u 0) = 0
  rw [FABL.innerProductModTwoBit_joinF₂CubeBlocks]
  simp [FABL.f₂DotProduct, dotProduct]

/-- The affine-input closure of normal extension.  It retains Definition 8
after choosing an affinely equivalent representative of the ambient bent
function. -/
def IsAffineNormalExtension
    (β : BooleanFunction k) (f : BooleanFunction n) : Prop :=
  ∃ A : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n,
    IsNormalExtension β (f ∘ A)

/-- Normality on affine flats is invariant under an affine change of input
coordinates. -/
theorem isKNormal_comp_affineEquiv_iff
    (f : BooleanFunction n)
    (A : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    IsKNormal (f ∘ A) k ↔ IsKNormal f k := by
  classical
  have transport
      (g : BooleanFunction n)
      (B : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
      (h : IsKNormal (g ∘ B) k) : IsKNormal g k := by
    obtain ⟨H, a, hHrank, b, hconstant⟩ := h
    let K : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
      H.map B.linear.toLinearMap
    refine ⟨K, B a, ?_, b, ?_⟩
    · dsimp [K]
      rw [LinearEquiv.finrank_map_eq, hHrank]
    · intro y hy
      have hyK : y + B a ∈ K :=
        (FABL.mem_binaryAffineSubspace_iff_add_mem K (B a) y).1 hy
      let x : FABL.F₂Cube n := B.linear.symm (y + B a)
      have hxH : x ∈ H := by
        dsimp [K] at hyK
        rw [Submodule.map_equiv_eq_comap_symm] at hyK
        exact hyK
      have hxa : x + a ∈ FABL.binaryAffineSubspace H a := by
        rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
        rw [add_assoc, ZModModule.add_self, add_zero]
        exact hxH
      have hBy : B (x + a) = y := by
        calc
          B (x + a) = B.linear x + B a := by
            simpa using B.map_vadd a x
          _ = y := by
            dsimp [x]
            rw [LinearEquiv.apply_symm_apply, add_assoc,
              ZModModule.add_self, add_zero]
      have hvalue := hconstant (x + a) hxa
      change g (B (x + a)) = b at hvalue
      simpa [hBy] using hvalue
  constructor
  · exact transport f A
  · intro hf
    apply transport (f ∘ A) A.symm
    convert hf using 1
    funext x
    simp

/-- Under the linear-subspace convention of Section 6.9, a bent function is
normal exactly when a zero-dimensional constant bent function normally
extends to it. -/
theorem exists_isNormalExtension_zeroDimensional_iff_isSubspaceNormal
    (f : BooleanFunction n) (hf : IsBent f) :
    (∃ ε : FABL.𝔽₂,
      IsNormalExtension (zeroDimensionalBooleanFunction ε) f) ↔
      IsSubspaceNormal f := by
  classical
  constructor
  · rintro ⟨ε, _hεBent, _hf, m, L, hrestriction⟩
    let H : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
      (normalExtensionHeadSubspace 0 m).map L.toLinearMap
    have hambient : m + m = n := by
      have hfinrank := LinearEquiv.finrank_eq L
      simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
    have hhalf : n / 2 = m := by omega
    refine ⟨H, ?_, ε, ?_⟩
    · dsimp [H]
      rw [LinearEquiv.finrank_map_eq]
      have hhead :=
        LinearEquiv.finrank_eq (normalExtensionHeadSubspaceLinearEquiv 0 m)
      simpa [Module.finrank_fintype_fun_eq_card, hhalf] using hhead.symm
    · intro x hx
      have hxH : x ∈ H := by
        simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hx
      obtain ⟨y, hy, rfl⟩ := hxH
      obtain ⟨z, rfl⟩ := hy
      let q := cubeSplitLinearEquiv 0 m z
      have hz :
          normalExtensionHeadLinearMap 0 m z =
            Fin.append q.1 (Fin.append q.2 0) := by
        exact normalExtensionHeadLinearMap_apply_split z
      rw [hz]
      simpa using hrestriction q.1 q.2
  · rintro ⟨H, hHrank, ε, hconstant⟩
    obtain ⟨H', hcompl⟩ := H.exists_isCompl
    let m := n / 2
    have hnEven := even_of_isBent f hf
    have hdouble : m + m = n := by
      rcases hnEven with ⟨t, rfl⟩
      omega
    have hH'rank : Module.finrank FABL.𝔽₂ H' = m := by
      have hsum : Module.finrank FABL.𝔽₂ H +
          Module.finrank FABL.𝔽₂ H' = n := by
        simpa [Module.finrank_fintype_fun_eq_card] using
          Submodule.finrank_add_eq_of_isCompl hcompl
      rw [hHrank] at hsum
      omega
    let eH : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] H :=
      LinearEquiv.ofFinrankEq _ _ (by
        simp [m, hHrank, Module.finrank_fintype_fun_eq_card])
    let eH' : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] H' :=
      LinearEquiv.ofFinrankEq _ _ (by
        simp [hH'rank, Module.finrank_fintype_fun_eq_card])
    let L : FABL.F₂Cube (0 + (m + m)) ≃ₗ[FABL.𝔽₂]
        FABL.F₂Cube n :=
      (cubeSplitLinearEquiv 0 (m + m)).trans
        ((LinearEquiv.uniqueProd (R := FABL.𝔽₂)).trans
          ((cubeSplitLinearEquiv m m).trans
            ((eH.prodCongr eH').trans
              (H.prodEquivOfIsCompl H' hcompl))))
    refine ⟨ε, isBent_zeroDimensionalBooleanFunction ε, hf, m, L, ?_⟩
    intro u w
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    have houter :
        (cubeSplitLinearEquiv 0 (m + m))
            (Fin.append 0 (Fin.append w 0)) =
          (0, Fin.append w 0) := by
      exact (Fin.appendEquiv 0 (m + m)).symm_apply_apply
        (0, Fin.append w 0)
    have hcoordinates :
        (cubeSplitLinearEquiv m m)
            ((LinearEquiv.uniqueProd
              (R := FABL.𝔽₂) (M := FABL.F₂Cube (m + m))
              (M₂ := FABL.F₂Cube 0))
              ((cubeSplitLinearEquiv 0 (m + m))
                (Fin.append 0 (Fin.append w 0)))) =
          (w, 0) := by
      rw [houter]
      exact (Fin.appendEquiv m m).symm_apply_apply (w, 0)
    have hL :
        L (Fin.append 0 (Fin.append w 0)) = (eH w : FABL.F₂Cube n) := by
      change (H.prodEquivOfIsCompl H' hcompl)
          ((eH.prodCongr eH')
            ((cubeSplitLinearEquiv m m)
              ((LinearEquiv.uniqueProd
                (R := FABL.𝔽₂) (M := FABL.F₂Cube (m + m))
                (M₂ := FABL.F₂Cube 0))
                ((cubeSplitLinearEquiv 0 (m + m))
                  (Fin.append 0 (Fin.append w 0)))))) = _
      rw [hcoordinates]
      simp
    rw [hL]
    apply hconstant
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    simpa only [add_zero] using (eH w).2

/-- With Chapter 5's affine-flat definition of normality, the
zero-dimensional characterization of Section 6.9 holds after taking the
affine-input closure of the normal-extension relation. -/
theorem exists_isAffineNormalExtension_zeroDimensional_iff_isKNormal
    (f : BooleanFunction n) (hf : IsBent f) :
    (∃ ε : FABL.𝔽₂,
      IsAffineNormalExtension (zeroDimensionalBooleanFunction ε) f) ↔
      IsKNormal f (n / 2) := by
  constructor
  · rintro ⟨ε, A, hextension⟩
    have hsubspace : IsSubspaceNormal (f ∘ A) :=
      (exists_isNormalExtension_zeroDimensional_iff_isSubspaceNormal
        (f ∘ A) hextension.2.1).1 ⟨ε, hextension⟩
    obtain ⟨H, hHrank, hconstant⟩ := hsubspace
    apply (isKNormal_comp_affineEquiv_iff f A).1
    exact ⟨H, 0, hHrank, hconstant⟩
  · rintro ⟨H, a, hHrank, ε, hconstant⟩
    let A : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n :=
      AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube n) a
    have hAf : IsBent (f ∘ A) :=
      (isBent_comp_affineEquiv_iff f A).2 hf
    have hsubspace : IsSubspaceNormal (f ∘ A) := by
      refine ⟨H, hHrank, ε, ?_⟩
      intro x hx
      apply hconstant
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hx ⊢
      have hxH : x ∈ H := by simpa only [add_zero] using hx
      change a + x + a ∈ H
      rw [add_comm a x, add_assoc, ZModModule.add_self, add_zero]
      exact hxH
    obtain ⟨δ, hextension⟩ :=
      (exists_isNormalExtension_zeroDimensional_iff_isSubspaceNormal
        (f ∘ A) hAf).2 hsubspace
    exact ⟨δ, A, hextension⟩

private def affineOnlyNormalBentExample : BooleanFunction 2 :=
  fun x ↦ (x 0 + 1) * (x 1 + 1)

private theorem isBent_affineOnlyNormalBentExample :
    IsBent affineOnlyNormalBentExample := by
  let oneVector : FABL.F₂Cube 2 := fun _ ↦ 1
  have hfunction : affineOnlyNormalBentExample =
      (FABL.completeQuadraticBit : BooleanFunction 2) +
        FABL.affineFunction 1 oneVector := by
    funext x
    rw [Pi.add_apply, completeQuadraticBit_two_dimension]
    simp [affineOnlyNormalBentExample, FABL.affineFunction,
      FABL.f₂DotProduct, dotProduct, oneVector, Fin.sum_univ_two]
    ring
  rw [hfunction]
  exact (isBent_add_affineFunction_iff
    (FABL.completeQuadraticBit : BooleanFunction 2) 1 oneVector).2
      isBent_completeQuadraticBit_two_dimension

@[simp] private theorem affineOnlyNormalBentExample_zero :
    affineOnlyNormalBentExample 0 = 1 := by
  simp [affineOnlyNormalBentExample]

private theorem affineOnlyNormalBentExample_eq_zero_of_ne_zero
    (x : FABL.F₂Cube 2) (hx : x ≠ 0) :
    affineOnlyNormalBentExample x = 0 := by
  have hfirst : x 0 = 0 ∨ x 0 = 1 := by
    by_cases h : x 0 = 0
    · exact Or.inl h
    · exact Or.inr (Fin.eq_one_of_ne_zero (x 0) h)
  have hsecond : x 1 = 0 ∨ x 1 = 1 := by
    by_cases h : x 1 = 0
    · exact Or.inl h
    · exact Or.inr (Fin.eq_one_of_ne_zero (x 1) h)
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · exfalso
    apply hx
    funext i
    fin_cases i <;> assumption
  · simp [affineOnlyNormalBentExample, hfirst, hsecond]
  · simp [affineOnlyNormalBentExample, hfirst, hsecond]
  · simp [affineOnlyNormalBentExample, hfirst, hsecond]

private theorem isKNormal_affineOnlyNormalBentExample :
    IsKNormal affineOnlyNormalBentExample 1 := by
  let e₀ : FABL.F₂Cube 2 := Pi.single 0 1
  let e₁ : FABL.F₂Cube 2 := Pi.single 1 1
  let H : Submodule FABL.𝔽₂ (FABL.F₂Cube 2) := FABL.𝔽₂ ∙ e₁
  have he₁ : e₁ ≠ 0 := by
    intro h
    have hcoordinate := congrFun h 1
    simp [e₁] at hcoordinate
  refine ⟨H, e₀, ?_, 0, ?_⟩
  · exact finrank_span_singleton he₁
  · intro x hx
    have hxH : x + e₀ ∈ H :=
      (FABL.mem_binaryAffineSubspace_iff_add_mem H e₀ x).1 hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxH
    have hxEq : x = c • e₁ + e₀ := by
      calc
        x = (x + e₀) + e₀ := by
          rw [add_assoc, ZModModule.add_self, add_zero]
        _ = c • e₁ + e₀ := by rw [hc]
    rw [hxEq]
    simp [affineOnlyNormalBentExample, e₀, e₁]

private theorem not_isSubspaceNormal_affineOnlyNormalBentExample :
    ¬ IsSubspaceNormal affineOnlyNormalBentExample := by
  rintro ⟨H, hHrank, b, hconstant⟩
  have hpositive : 0 < Module.finrank FABL.𝔽₂ H := by
    norm_num at hHrank
    omega
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := FABL.𝔽₂) (M := H)).1
      hpositive
  have hvAmbient : (v.1 : FABL.F₂Cube 2) ≠ 0 := by
    exact fun h ↦ hv (Subtype.ext h)
  have hzeroMem :
      (0 : FABL.F₂Cube 2) ∈ FABL.binaryAffineSubspace H 0 := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    exact H.zero_mem
  have hvMem :
      (v.1 : FABL.F₂Cube 2) ∈ FABL.binaryAffineSubspace H 0 := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    simpa only [add_zero] using v.2
  have hzero := hconstant 0 hzeroMem
  have hvValue := hconstant v.1 hvMem
  rw [affineOnlyNormalBentExample_zero] at hzero
  rw [affineOnlyNormalBentExample_eq_zero_of_ne_zero v.1 hvAmbient] at hvValue
  have : (1 : FABL.𝔽₂) = 0 := hzero.trans hvValue.symm
  exact one_ne_zero this

/-- Chapter 5 affine-flat normality does not imply the unclosed statement
`ε ⊑ f`: a translated two-variable quadratic bent function is normal only
on affine lines and on no one-dimensional linear subspace. -/
theorem exists_isKNormal_not_isNormalExtension_zeroDimensional :
    ∃ f : BooleanFunction 2,
      IsBent f ∧ IsKNormal f 1 ∧
        ¬ ∃ ε : FABL.𝔽₂,
          IsNormalExtension (zeroDimensionalBooleanFunction ε) f := by
  refine ⟨affineOnlyNormalBentExample,
    isBent_affineOnlyNormalBentExample,
    isKNormal_affineOnlyNormalBentExample, ?_⟩
  rw [exists_isNormalExtension_zeroDimensional_iff_isSubspaceNormal
    affineOnlyNormalBentExample isBent_affineOnlyNormalBentExample]
  exact not_isSubspaceNormal_affineOnlyNormalBentExample

/-- A normal extension includes bentness of its smaller function. -/
theorem IsNormalExtension.isBent_left
    {β : BooleanFunction k} {f : BooleanFunction n}
    (h : IsNormalExtension β f) : IsBent β :=
  h.1

/-- A normal extension includes bentness of its larger function. -/
theorem IsNormalExtension.isBent_right
    {β : BooleanFunction k} {f : BooleanFunction n}
    (h : IsNormalExtension β f) : IsBent f :=
  h.2.1

/-- Every bent function is a zero-codimension normal extension of itself. -/
theorem isNormalExtension_refl
    (f : BooleanFunction n) (hf : IsBent f) :
    IsNormalExtension f f := by
  refine ⟨hf, hf, 0, LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube n), ?_⟩
  intro u w
  congr 1
  rw [Fin.append_right_nil u (Fin.append w 0) rfl]
  rfl

/-- Carlet's normal-extension relation is transitive. -/
theorem IsNormalExtension.trans
    {β : BooleanFunction k} {f : BooleanFunction n}
    {g : BooleanFunction p}
    (hβf : IsNormalExtension β f) (hfg : IsNormalExtension f g) :
    IsNormalExtension β g := by
  obtain ⟨hβ, hf, r, L, hL⟩ := hβf
  obtain ⟨_hf, hg, s, M, hM⟩ := hfg
  refine ⟨hβ, hg, r + s, normalExtensionTransLinearEquiv L M, ?_⟩
  intro u w
  let y := (cubeSplitLinearEquiv r s) w
  have happly :
      normalExtensionTransLinearEquiv L M
          (Fin.append u (Fin.append w 0)) =
        M (Fin.append
          (L (Fin.append u (Fin.append y.1 0)))
          (Fin.append y.2 0)) := by
    dsimp [normalExtensionTransLinearEquiv]
    refine congrArg M ?_
    apply (cubeTripleLinearEquiv n s).injective
    suffices
        Fin.append (fun i ↦ u i)
            (Fin.append (fun i ↦ w (Fin.castAdd s i)) (fun _i ↦ 0)) =
          Fin.append u (Fin.append (fun i ↦ w (Fin.castAdd s i)) 0) by
      simpa [normalExtensionReassociationLinearEquiv, cubeTripleLinearEquiv,
        cubeSplitLinearEquiv, Fin.appendEquiv, y] using this
    rfl
  rw [happly]
  rw [hM, hL]

/-- Normal extension is preserved by bent duality; the two complementary
directions are exchanged by the dual coordinate decomposition. -/
theorem IsNormalExtension.bentDual
    {β : BooleanFunction k} {f : BooleanFunction n}
    (h : IsNormalExtension β f) :
    IsNormalExtension (CryptBoolean.bentDual β)
      (CryptBoolean.bentDual f) := by
  obtain ⟨hβ, hf, m, L, hrestriction⟩ := h
  have hdim : k + (m + m) = n := by
    have hfinrank := LinearEquiv.finrank_eq L
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  subst n
  let g : BooleanFunction (k + (m + m)) := f ∘ L
  have hg : IsBent g := by
    exact (isBent_comp_affineEquiv_iff f L.toAffineEquiv).2 hf
  let Ldual : FABL.F₂Cube (k + (m + m)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (k + (m + m)) :=
    (normalExtensionAuxiliarySwapLinearEquiv k m).trans
      (walshAdjointLinearEquiv L.symm)
  refine ⟨isBent_bentDual β hβ, isBent_bentDual f hf, m, Ldual, ?_⟩
  intro u w
  change CryptBoolean.bentDual f
      (walshAdjointLinearEquiv L.symm
        (normalExtensionAuxiliarySwapLinearEquiv k m
          (Fin.append u (Fin.append w 0)))) =
      CryptBoolean.bentDual β u
  rw [normalExtensionAuxiliarySwapLinearEquiv_apply]
  rw [← bentDual_comp_linearEquiv f L]
  exact bentDual_canonical_normalExtension β g hβ hg hrestriction u w

/-- Replace the distinguished restriction of a normal extension after
transporting to the coordinates of its direct-sum decomposition. -/
def normalExtensionReplacement
    (β' : BooleanFunction k) (f : BooleanFunction n)
    (L : FABL.F₂Cube (k + (r + r)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    BooleanFunction n :=
  canonicalNormalExtensionReplacement β' (f ∘ L) ∘ L.symm

@[simp] theorem normalExtensionReplacement_apply
    (β' : BooleanFunction k) (f : BooleanFunction n)
    (L : FABL.F₂Cube (k + (r + r)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (u : FABL.F₂Cube k) (w : FABL.F₂Cube r) :
    normalExtensionReplacement β' f L
        (L (Fin.append u (Fin.append w 0))) = β' u := by
  simp [normalExtensionReplacement,
    canonicalNormalExtensionReplacement_apply_append]

/-- Carlet Proposition 31: the restriction of a normal extension can be
replaced by any bent function on the smaller space. -/
theorem normalExtensionReplacement_isNormalExtension
    (β β' : BooleanFunction k) (f : BooleanFunction n)
    (hβ : IsBent β) (hβ' : IsBent β') (hf : IsBent f)
    (L : FABL.F₂Cube (k + (r + r)) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (hrestriction : ∀ u w,
      f (L (Fin.append u (Fin.append w 0))) = β u) :
    IsNormalExtension β' (normalExtensionReplacement β' f L) := by
  have hdim : k + (r + r) = n := by
    have hfinrank := LinearEquiv.finrank_eq L
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  subst n
  let g : BooleanFunction (k + (r + r)) := f ∘ L
  have hg : IsBent g :=
    (isBent_comp_affineEquiv_iff f L.toAffineEquiv).2 hf
  have hgrestriction : ∀ u w,
      g (Fin.append u (Fin.append w 0)) = β u := hrestriction
  have hcanonical :
      IsBent (canonicalNormalExtensionReplacement β' g) :=
    isBent_canonicalNormalExtensionReplacement
      β β' g hβ hβ' hg hgrestriction
  have hreplacement :
      IsBent (normalExtensionReplacement β' f L) := by
    exact (isBent_comp_affineEquiv_iff
      (canonicalNormalExtensionReplacement β' g)
      L.symm.toAffineEquiv).2 hcanonical
  refine ⟨hβ', hreplacement, r, L, ?_⟩
  exact normalExtensionReplacement_apply β' f L

private theorem half_le_finrank_projectedIntersection
    (beta : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hbeta : IsBent beta) (hf : IsBent f)
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = beta u)
    (N : Submodule FABL.𝔽₂ (FABL.F₂Cube (k + (r + r))))
    (hNrank : Module.finrank FABL.𝔽₂ N = (k + (r + r)) / 2)
    (c : FABL.𝔽₂)
    (hconstant : ∀ x ∈ FABL.binaryAffineSubspace N 0, f x = c) :
    k / 2 ≤ Module.finrank FABL.𝔽₂
      (normalExtensionProjectedIntersection N) := by
  classical
  rcases even_of_isBent beta hbeta with ⟨d, hd⟩
  subst k
  have hhalf : (d + d) / 2 = d := by omega
  have htotalHalf : ((d + d) + (r + r)) / 2 = d + r := by omega
  rw [hhalf]
  have hNrank' : Module.finrank FABL.𝔽₂ N = d + r := by
    simpa [htotalHalf] using hNrank
  let N0 := normalExtensionProjectedIntersection N
  by_contra hnot
  change ¬ d ≤ Module.finrank FABL.𝔽₂ N0 at hnot
  have hN0lt : Module.finrank FABL.𝔽₂ N0 < d := by omega
  have hN0ambient : Module.finrank FABL.𝔽₂ N0 <
      Module.finrank FABL.𝔽₂ (FABL.F₂Cube (d + d)) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨u0, hu0all⟩ := N0.exists_of_finrank_lt hN0ambient
  have hu0 : u0 ∉ N0 := by simpa using hu0all 1 one_ne_zero
  let T := N0 ⊔ Submodule.span FABL.𝔽₂ {u0}
  have hTrank : Module.finrank FABL.𝔽₂ T =
      Module.finrank FABL.𝔽₂ N0 + 1 := by
    exact Submodule.finrank_sup_span_singleton hu0
  have hTle : Module.finrank FABL.𝔽₂ T ≤ (d + d) / 2 := by
    rw [hTrank, hhalf]
    omega
  obtain ⟨gamma0, hgamma0, hgamma0T⟩ :=
    exists_bent_eq_zero_on_subspace T (by exact ⟨d, rfl⟩) hTle
  obtain ⟨ell, hellu0Ne, hN0ker⟩ := N0.exists_le_ker_of_notMem hu0
  have hellu0 : ell u0 = 1 := Fin.eq_one_of_ne_zero _ hellu0Ne
  have hellN0 (u : FABL.F₂Cube (d + d)) (hu : u ∈ N0) :
      ell u = 0 :=
    LinearMap.mem_ker.mp (hN0ker hu)
  have hellLinear : FABL.IsF₂Linear (fun u ↦ ell u) := by
    intro x y
    exact ell.map_add x y
  obtain ⟨a, ha⟩ :=
    (FABL.isF₂Linear_iff_exists_dotProduct (fun u ↦ ell u)).1
      hellLinear
  let gamma1 : BooleanFunction (d + d) :=
    gamma0 + FABL.affineFunction c 0
  let gamma2 : BooleanFunction (d + d) :=
    gamma0 + FABL.affineFunction c a
  have hgamma1 : IsBent gamma1 :=
    (isBent_add_affineFunction_iff gamma0 c 0).2 hgamma0
  have hgamma2 : IsBent gamma2 :=
    (isBent_add_affineFunction_iff gamma0 c a).2 hgamma0
  have hN0T : N0 ≤ T := le_sup_left
  have hu0T : u0 ∈ T := by
    change u0 ∈ N0 ⊔ Submodule.span FABL.𝔽₂ {u0}
    have hu0Span : u0 ∈ Submodule.span FABL.𝔽₂ {u0} :=
      Submodule.subset_span (by simp)
    exact
      (show Submodule.span FABL.𝔽₂ {u0} ≤
        N0 ⊔ Submodule.span FABL.𝔽₂ {u0} from le_sup_right) hu0Span
  have hgamma1N0 (u : FABL.F₂Cube (d + d)) (hu : u ∈ N0) :
      gamma1 u = c := by
    simp [gamma1, hgamma0T u (hN0T hu), FABL.affineFunction,
      FABL.f₂DotProduct, dotProduct]
  have hgamma2N0 (u : FABL.F₂Cube (d + d)) (hu : u ∈ N0) :
      gamma2 u = c := by
    have hdot : FABL.f₂DotProduct a u = 0 := by
      rw [← ha u, hellN0 u hu]
    simp [gamma2, hgamma0T u (hN0T hu), FABL.affineFunction, hdot]
  have hgamma1Shift (u : FABL.F₂Cube (d + d)) (hu : u ∈ N0) :
      gamma1 (u0 + u) = c := by
    have hsumT : u0 + u ∈ T := T.add_mem hu0T (hN0T hu)
    simp [gamma1, hgamma0T (u0 + u) hsumT, FABL.affineFunction,
      FABL.f₂DotProduct, dotProduct]
  have hgamma2Shift (u : FABL.F₂Cube (d + d)) (hu : u ∈ N0) :
      gamma2 (u0 + u) = c + 1 := by
    have hsumT : u0 + u ∈ T := T.add_mem hu0T (hN0T hu)
    have hellSum : ell (u0 + u) = 1 := by
      rw [ell.map_add, hellu0, hellN0 u hu, add_zero]
    have hdot : FABL.f₂DotProduct a (u0 + u) = 1 := by
      rw [← ha (u0 + u), hellSum]
    simp [gamma2, hgamma0T (u0 + u) hsumT,
      FABL.affineFunction, hdot]
  let F1 := canonicalNormalExtensionReplacement gamma1 f
  let F2 := canonicalNormalExtensionReplacement gamma2 f
  have hF1 : IsBent F1 :=
    isBent_canonicalNormalExtensionReplacement
      beta gamma1 f hbeta hgamma1 hf hrestriction
  have hF2 : IsBent F2 :=
    isBent_canonicalNormalExtensionReplacement
      beta gamma2 f hbeta hgamma2 hf hrestriction
  have replacementConstant
      (gamma : BooleanFunction (d + d))
      (hgammaN0 : ∀ u ∈ N0, gamma u = c) :
      ∀ x ∈ FABL.binaryAffineSubspace N 0,
        canonicalNormalExtensionReplacement gamma f x = c := by
    intro x hx
    have hxN : x ∈ N := by
      simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hx
    by_cases hxHead : x ∈ normalExtensionHeadSubspace (d + d) r
    · rw [canonicalNormalExtensionReplacement_eq_on_head _ _ _ hxHead]
      exact hgammaN0 _
        (normalExtensionProjectedIntersection_mem_of_mem hxN hxHead)
    · rw [canonicalNormalExtensionReplacement_eq_off_head _ _ _ hxHead]
      exact hconstant x hx
  have hF1constant : ∀ x ∈ FABL.binaryAffineSubspace N 0, F1 x = c :=
    replacementConstant gamma1 hgamma1N0
  have hF2constant : ∀ x ∈ FABL.binaryAffineSubspace N 0, F2 x = c :=
    replacementConstant gamma2 hgamma2N0
  let G1 : BooleanFunction ((d + d) + (r + r)) :=
    F1 + FABL.affineFunction c 0
  let G2 : BooleanFunction ((d + d) + (r + r)) :=
    F2 + FABL.affineFunction c 0
  have hdpos : 0 < d := by omega
  let eN : FABL.F₂Cube (d + r) ≃ₗ[FABL.𝔽₂] N :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hNrank', Module.finrank_fintype_fun_eq_card])
  let x0 : FABL.F₂Cube ((d + d) + (r + r)) :=
    Fin.append u0 (Fin.append 0 0)
  have hx0Head : x0 ∈ normalExtensionHeadSubspace (d + d) r := by
    rw [mem_normalExtensionHeadSubspace_iff_tail_eq_zero]
    suffices (fun _i : Fin r ↦ (0 : FABL.𝔽₂)) = 0 by
      simpa [x0, cubeTripleLinearEquiv, cubeSplitLinearEquiv] using this
    funext i
    rfl
  have hx0NotN : x0 ∉ N := by
    intro hx0N
    apply hu0
    have hprojected :=
      normalExtensionProjectedIntersection_mem_of_mem hx0N hx0Head
    simpa [x0] using hprojected
  have hnonlinearity1 : nonlinearity F1 =
      2 ^ (((d + d) + (r + r)) - 1) - 2 ^ ((d + r) - 1) := by
    have hvalue := nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent
      F1 hF1 (by omega)
    simpa [htotalHalf] using hvalue
  have hnonlinearity2 : nonlinearity F2 =
      2 ^ (((d + d) + (r + r)) - 1) - 2 ^ ((d + r) - 1) := by
    have hvalue := nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent
      F2 hF2 (by omega)
    simpa [htotalHalf] using hvalue
  have hbalanced1 : IsBalanced
      (coordinateAffineSubspaceRestriction
        G1 N x0 eN) := by
    change IsBalanced
      (coordinateAffineSubspaceRestriction
        (F1 + FABL.affineFunction c 0) N x0 eN)
    apply isBalanced_coordinateAffineSubspaceRestriction_add_affineFunction_of_eq_bound
      F1 N 0 eN (by omega) c 0
    · intro x hx
      rw [hF1constant x hx]
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
    · exact hnonlinearity1
    · simpa only [add_zero] using hx0NotN
  have hbalanced2 : IsBalanced
      (coordinateAffineSubspaceRestriction
        G2 N x0 eN) := by
    change IsBalanced
      (coordinateAffineSubspaceRestriction
        (F2 + FABL.affineFunction c 0) N x0 eN)
    apply isBalanced_coordinateAffineSubspaceRestriction_add_affineFunction_of_eq_bound
      F2 N 0 eN (by omega) c 0
    · intro x hx
      rw [hF2constant x hx]
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
    · exact hnonlinearity2
    · simpa only [add_zero] using hx0NotN
  have hsum1 :
      (∑ y : FABL.F₂Cube (d + r),
        bitSignInt (G1 ((eN y).1 + x0))) = 0 := by
    have hwalsh :=
      (isBalanced_iff_walshTransform_zero_eq_zero _).1 hbalanced1
    rw [walshTransform] at hwalsh
    simpa [walshTerm, coordinateAffineSubspaceRestriction_apply,
      FABL.f₂DotProduct, dotProduct, G1] using hwalsh
  have hsum2 :
      (∑ y : FABL.F₂Cube (d + r),
        bitSignInt (G2 ((eN y).1 + x0))) = 0 := by
    have hwalsh :=
      (isBalanced_iff_walshTransform_zero_eq_zero _).1 hbalanced2
    rw [walshTransform] at hwalsh
    simpa [walshTerm, coordinateAffineSubspaceRestriction_apply,
      FABL.f₂DotProduct, dotProduct, G2] using hwalsh
  let S : Finset (FABL.F₂Cube (d + r)) := Finset.univ.filter fun y ↦
    (eN y).1 + x0 ∈ normalExtensionHeadSubspace (d + d) r
  have hzeroS : (0 : FABL.F₂Cube (d + r)) ∈ S := by
    simp [S, hx0Head]
  have hterm (y : FABL.F₂Cube (d + r)) :
      bitSignInt (G1 ((eN y).1 + x0)) -
        bitSignInt (G2 ((eN y).1 + x0)) =
      if (eN y).1 + x0 ∈ normalExtensionHeadSubspace (d + d) r
      then 2 else 0 := by
    let x := (eN y).1 + x0
    by_cases hxHead : x ∈ normalExtensionHeadSubspace (d + d) r
    · rw [if_pos hxHead]
      have heNHead : (eN y).1 ∈
          normalExtensionHeadSubspace (d + d) r := by
        have hadd :=
          (normalExtensionHeadSubspace (d + d) r).add_mem hxHead hx0Head
        simpa [x, add_assoc, ZModModule.add_self] using hadd
      have hvN0 : normalExtensionPrefixLinearMap (d + d) r (eN y).1 ∈
          N0 := normalExtensionProjectedIntersection_mem_of_mem
            (eN y).2 heNHead
      have hprefix : normalExtensionPrefixLinearMap (d + d) r x =
          u0 + normalExtensionPrefixLinearMap (d + d) r (eN y).1 := by
        dsimp [x]
        rw [map_add, normalExtensionPrefixLinearMap_apply]
        abel
      have hF1x : F1 x = c := by
        change canonicalNormalExtensionReplacement gamma1 f x = c
        rw [canonicalNormalExtensionReplacement_eq_on_head _ _ _ hxHead,
          hprefix, hgamma1Shift _ hvN0]
      have hF2x : F2 x = c + 1 := by
        change canonicalNormalExtensionReplacement gamma2 f x = c + 1
        rw [canonicalNormalExtensionReplacement_eq_on_head _ _ _ hxHead,
          hprefix, hgamma2Shift _ hvN0]
      have hG1x : G1 x = 0 := by
        change F1 x + FABL.affineFunction c 0 x = 0
        rw [hF1x]
        simpa [FABL.affineFunction, FABL.f₂DotProduct, dotProduct] using
          ZModModule.add_self c
      have hG2x : G2 x = 1 := by
        change F2 x + FABL.affineFunction c 0 x = 1
        have haffineZero : FABL.affineFunction c 0 x = c := by
          simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
        rw [hF2x, haffineZero]
        calc
          (c + 1) + c = (c + c) + 1 := by abel
          _ = 1 := by rw [ZModModule.add_self, zero_add]
      change bitSignInt (G1 x) - bitSignInt (G2 x) = 2
      rw [hG1x, hG2x]
      norm_num [bitSignInt_eq_if_one]
    · rw [if_neg hxHead]
      have hF1x : F1 x = f x := by
        change canonicalNormalExtensionReplacement gamma1 f x = f x
        exact canonicalNormalExtensionReplacement_eq_off_head
          gamma1 f x hxHead
      have hF2x : F2 x = f x := by
        change canonicalNormalExtensionReplacement gamma2 f x = f x
        exact canonicalNormalExtensionReplacement_eq_off_head
          gamma2 f x hxHead
      have hG : G1 x = G2 x := by
        simp [G1, G2, hF1x, hF2x]
      change bitSignInt (G1 x) - bitSignInt (G2 x) = 0
      rw [hG, sub_self]
  have hsumDifference :
      (∑ y : FABL.F₂Cube (d + r),
        (bitSignInt (G1 ((eN y).1 + x0)) -
          bitSignInt (G2 ((eN y).1 + x0)))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum1, hsum2, sub_self]
  have hsumCard :
      (∑ y : FABL.F₂Cube (d + r),
        (bitSignInt (G1 ((eN y).1 + x0)) -
          bitSignInt (G2 ((eN y).1 + x0)))) =
        (S.card : ℤ) * 2 := by
    calc
      _ = ∑ y : FABL.F₂Cube (d + r),
          if (eN y).1 + x0 ∈ normalExtensionHeadSubspace (d + d) r
          then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro y _hy
        exact hterm y
      _ = (S.card : ℤ) * 2 := by
        rw [← Finset.sum_filter]
        change (∑ _y ∈ S, (2 : ℤ)) = (S.card : ℤ) * 2
        simp
  have hScard : 0 < S.card := Finset.card_pos.mpr ⟨0, hzeroS⟩
  have hzeroCard : (S.card : ℤ) * 2 = 0 := by
    rw [← hsumCard]
    exact hsumDifference
  have hcastZero : (S.card : ℤ) = 0 :=
    (mul_eq_zero.mp hzeroCard).resolve_right (by norm_num)
  have hNatZero : S.card = 0 := by
    exact_mod_cast hcastZero
  omega

private theorem isSubspaceNormal_of_canonicalNormalExtension
    (beta : BooleanFunction k)
    (f : BooleanFunction (k + (r + r)))
    (hbeta : IsBent beta) (hf : IsBent f)
    (hrestriction : ∀ u w,
      f (Fin.append u (Fin.append w 0)) = beta u)
    (hnormal : IsSubspaceNormal f) :
    IsSubspaceNormal beta := by
  obtain ⟨N, hNrank, c, hconstant⟩ := hnormal
  let N0 := normalExtensionProjectedIntersection N
  have hN0rank : k / 2 ≤ Module.finrank FABL.𝔽₂ N0 :=
    half_le_finrank_projectedIntersection beta f hbeta hf hrestriction
      N hNrank c hconstant
  obtain ⟨H, hHN0, hHrank⟩ :=
    exists_subspace_le_finrank_eq N0 hN0rank
  refine ⟨H, hHrank, c, ?_⟩
  intro u hu
  have huH : u ∈ H := by
    simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hu
  exact isConstantOn_projectedIntersection beta f N c
    hrestriction hconstant u (hHN0 huH)

/-- Carlet Proposition 30: linear-subspace normality descends along a
normal extension. -/
theorem IsNormalExtension.isSubspaceNormal_left
    {beta : BooleanFunction k} {f : BooleanFunction n}
    (hextension : IsNormalExtension beta f)
    (hnormal : IsSubspaceNormal f) :
    IsSubspaceNormal beta := by
  obtain ⟨hbeta, hf, r, L, hrestriction⟩ := hextension
  have hdim : k + (r + r) = n := by
    have hfinrank := LinearEquiv.finrank_eq L
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  subst n
  let g : BooleanFunction (k + (r + r)) := f ∘ L
  have hg : IsBent g :=
    (isBent_comp_affineEquiv_iff f L.toAffineEquiv).2 hf
  have hgnormal : IsSubspaceNormal g :=
    (isSubspaceNormal_comp_linearEquiv_iff f L).2 hnormal
  exact isSubspaceNormal_of_canonicalNormalExtension
    beta g hbeta hg hrestriction hgnormal

/-- Linear equivalence up to addition of a constant Boolean function. -/
def AreLinearlyEquivalentOrComplementary
    (f : BooleanFunction n) (g : BooleanFunction m) : Prop :=
  ∃ L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube m,
    ∃ c : FABL.𝔽₂, ∀ x, f x = g (L x) + c

private def prop29CubeThreeLinearEquiv (a b c : ℕ) :
    FABL.F₂Cube (a + (b + c)) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube a × (FABL.F₂Cube b × FABL.F₂Cube c)) :=
  (cubeSplitLinearEquiv a (b + c)).trans
    ((LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube a)).prodCongr
      (cubeSplitLinearEquiv b c))

@[simp] private theorem finAppend_add
    (u₁ u₂ : FABL.F₂Cube a) (v₁ v₂ : FABL.F₂Cube b) :
    Fin.append (u₁ + u₂) (v₁ + v₂) =
      Fin.append u₁ v₁ + Fin.append u₂ v₂ := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

@[simp] private theorem finAppend_smul
    (c : FABL.𝔽₂) (u : FABL.F₂Cube a) (v : FABL.F₂Cube b) :
    Fin.append (c • u) (c • v) = c • Fin.append u v := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

@[simp] private theorem finAppend_add_zero
    (u₁ u₂ : FABL.F₂Cube a) :
    Fin.append (u₁ + u₂) (0 : FABL.F₂Cube b) =
      Fin.append u₁ 0 + Fin.append u₂ 0 := by
  rw [← finAppend_add]
  simp

@[simp] private theorem finAppend_smul_zero
    (c : FABL.𝔽₂) (u : FABL.F₂Cube a) :
    Fin.append (c • u) (0 : FABL.F₂Cube b) =
      c • Fin.append u 0 := by
  rw [← finAppend_smul]
  simp

@[simp] private theorem cubeSplitLinearEquiv_symm_apply_prop29
    (u : FABL.F₂Cube a) (v : FABL.F₂Cube b) :
    (cubeSplitLinearEquiv a b).symm (u, v) = Fin.append u v := by
  apply (cubeSplitLinearEquiv a b).injective
  simp [cubeSplitLinearEquiv]

@[simp] private theorem cubeTripleLinearEquiv_symm_apply
    (u : FABL.F₂Cube a) (v w : FABL.F₂Cube b) :
    (cubeTripleLinearEquiv a b).symm (u, (v, w)) =
      Fin.append u (Fin.append v w) := by
  apply (cubeTripleLinearEquiv a b).injective
  simp [cubeTripleLinearEquiv, cubeSplitLinearEquiv]

@[simp] private theorem cubeTripleLinearEquiv_apply_append
    (u : FABL.F₂Cube a) (v w : FABL.F₂Cube b) :
    cubeTripleLinearEquiv a b (Fin.append u (Fin.append v w)) =
      (u, (v, w)) := by
  simp [cubeTripleLinearEquiv, cubeSplitLinearEquiv]

@[simp] private theorem prop29CubeThreeLinearEquiv_apply_append
    (u : FABL.F₂Cube a) (v : FABL.F₂Cube b)
    (w : FABL.F₂Cube c) :
    prop29CubeThreeLinearEquiv a b c (Fin.append u (Fin.append v w)) =
      (u, (v, w)) := by
  simp [prop29CubeThreeLinearEquiv, cubeSplitLinearEquiv]

private def compatibleNormalExtensionsLinearMap
    {k₁ k₂ n m r₁ r₂ : ℕ}
    (L₁ : FABL.F₂Cube (k₁ + (r₁ + r₁)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n)
    (L₂ : FABL.F₂Cube (k₂ + (r₂ + r₂)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube m)
    (E : FABL.F₂Cube k₁ ≃ₗ[FABL.𝔽₂] FABL.F₂Cube k₂) :
    FABL.F₂Cube (k₁ + (r₁ + r₂)) →ₗ[FABL.𝔽₂]
      FABL.F₂Cube (n + m) where
  toFun x :=
    let q := prop29CubeThreeLinearEquiv k₁ r₁ r₂ x
    (cubeSplitLinearEquiv n m).symm
      (
      (L₁ ((cubeTripleLinearEquiv k₁ r₁).symm
        (q.1, (q.2.1, 0))))
      , L₂ ((cubeTripleLinearEquiv k₂ r₂).symm
        (E q.1, (q.2.2, 0))))
  map_add' x y := by
    simp [map_add]
  map_smul' c x := by
    simp [map_smul]

@[simp] private theorem compatibleNormalExtensionsLinearMap_apply
    {k₁ k₂ n m r₁ r₂ : ℕ}
    (L₁ : FABL.F₂Cube (k₁ + (r₁ + r₁)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n)
    (L₂ : FABL.F₂Cube (k₂ + (r₂ + r₂)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube m)
    (E : FABL.F₂Cube k₁ ≃ₗ[FABL.𝔽₂] FABL.F₂Cube k₂)
    (u : FABL.F₂Cube k₁) (w₁ : FABL.F₂Cube r₁)
    (w₂ : FABL.F₂Cube r₂) :
    compatibleNormalExtensionsLinearMap L₁ L₂ E
        (Fin.append u (Fin.append w₁ w₂)) =
      Fin.append
        (L₁ (Fin.append u (Fin.append w₁ 0)))
        (L₂ (Fin.append (E u) (Fin.append w₂ 0))) := by
  simp [compatibleNormalExtensionsLinearMap]

private theorem booleanDirectSum_apply_append
    (f : BooleanFunction n) (g : BooleanFunction m)
    (x : FABL.F₂Cube n) (y : FABL.F₂Cube m) :
    booleanDirectSum f g (Fin.append x y) = f x + g y := by
  simp [booleanDirectSum]

private theorem compatibleNormalExtensionsLinearMap_injective
    {k₁ k₂ n m r₁ r₂ : ℕ}
    (L₁ : FABL.F₂Cube (k₁ + (r₁ + r₁)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n)
    (L₂ : FABL.F₂Cube (k₂ + (r₂ + r₂)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube m)
    (E : FABL.F₂Cube k₁ ≃ₗ[FABL.𝔽₂] FABL.F₂Cube k₂) :
    Function.Injective (compatibleNormalExtensionsLinearMap L₁ L₂ E) := by
  intro x y hxy
  let qx := prop29CubeThreeLinearEquiv k₁ r₁ r₂ x
  let qy := prop29CubeThreeLinearEquiv k₁ r₁ r₂ y
  have hpairs :
      (L₁ ((cubeTripleLinearEquiv k₁ r₁).symm
          (qx.1, (qx.2.1, 0))),
        L₂ ((cubeTripleLinearEquiv k₂ r₂).symm
          (E qx.1, (qx.2.2, 0)))) =
      (L₁ ((cubeTripleLinearEquiv k₁ r₁).symm
          (qy.1, (qy.2.1, 0))),
        L₂ ((cubeTripleLinearEquiv k₂ r₂).symm
          (E qy.1, (qy.2.2, 0)))) := by
    apply (cubeSplitLinearEquiv n m).symm.injective
    simpa [compatibleNormalExtensionsLinearMap, qx, qy] using hxy
  have hleft := L₁.injective (congrArg Prod.fst hpairs)
  have hleftCoordinates := congrArg
    (cubeTripleLinearEquiv k₁ r₁) hleft
  have hu : qx.1 = qy.1 := by
    simpa using congrArg (fun z ↦ z.1) hleftCoordinates
  have hw₁ : qx.2.1 = qy.2.1 := by
    simpa using congrArg (fun z ↦ z.2.1) hleftCoordinates
  have hright := L₂.injective (congrArg Prod.snd hpairs)
  have hrightCoordinates := congrArg
    (cubeTripleLinearEquiv k₂ r₂) hright
  have hw₂ : qx.2.2 = qy.2.2 := by
    simpa using congrArg (fun z ↦ z.2.1) hrightCoordinates
  apply (prop29CubeThreeLinearEquiv k₁ r₁ r₂).injective
  apply Prod.ext hu
  exact Prod.ext hw₁ hw₂

private theorem isSubspaceNormal_booleanDirectSum_of_compatibleNormalExtensions
    {k₁ k₂ n m : ℕ}
    {beta₁ : BooleanFunction k₁} {beta₂ : BooleanFunction k₂}
    {f₁ : BooleanFunction n} {f₂ : BooleanFunction m}
    (hext₁ : IsNormalExtension beta₁ f₁)
    (hext₂ : IsNormalExtension beta₂ f₂)
    (hcompatible : AreLinearlyEquivalentOrComplementary beta₁ beta₂) :
    IsSubspaceNormal (booleanDirectSum f₁ f₂) := by
  classical
  obtain ⟨hbeta₁, _hf₁, r₁, L₁, hL₁⟩ := hext₁
  obtain ⟨_hbeta₂, _hf₂, r₂, L₂, hL₂⟩ := hext₂
  obtain ⟨E, c, hrelation⟩ := hcompatible
  let T := compatibleNormalExtensionsLinearMap L₁ L₂ E
  let H : Submodule FABL.𝔽₂ (FABL.F₂Cube (n + m)) := LinearMap.range T
  have hTinjective : Function.Injective T :=
    compatibleNormalExtensionsLinearMap_injective L₁ L₂ E
  have hHdimension : Module.finrank FABL.𝔽₂ H = k₁ + (r₁ + r₂) := by
    have hfinrank := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective T hTinjective)
    simpa [H, Module.finrank_fintype_fun_eq_card] using hfinrank.symm
  have hL₁dimension : k₁ + (r₁ + r₁) = n := by
    have hfinrank := LinearEquiv.finrank_eq L₁
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  have hL₂dimension : k₂ + (r₂ + r₂) = m := by
    have hfinrank := LinearEquiv.finrank_eq L₂
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  have hEdimension : k₁ = k₂ := by
    have hfinrank := LinearEquiv.finrank_eq E
    simpa [Module.finrank_fintype_fun_eq_card] using hfinrank
  have hHrank : Module.finrank FABL.𝔽₂ H = (n + m) / 2 := by
    rcases even_of_isBent beta₁ hbeta₁ with ⟨d, hd⟩
    omega
  refine ⟨H, hHrank, c, ?_⟩
  intro x hx
  have hxH : x ∈ H := by
    simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hx
  obtain ⟨y, rfl⟩ := hxH
  let q := prop29CubeThreeLinearEquiv k₁ r₁ r₂ y
  have hy : Fin.append q.1 (Fin.append q.2.1 q.2.2) = y := by
    change (prop29CubeThreeLinearEquiv k₁ r₁ r₂).symm q = y
    exact (prop29CubeThreeLinearEquiv k₁ r₁ r₂).symm_apply_apply y
  rw [← hy, compatibleNormalExtensionsLinearMap_apply]
  rw [booleanDirectSum_apply_append, hL₁, hL₂, hrelation]
  calc
    (beta₂ (E q.1) + c) + beta₂ (E q.1) =
        (beta₂ (E q.1) + beta₂ (E q.1)) + c := by abel
    _ = c := by rw [ZModModule.add_self, zero_add]

private theorem isBent_of_maxWalshMagnitude_sq_le_two_pow
    (f : BooleanFunction k)
    (hmax : (maxWalshMagnitude f : ℝ) ^ 2 ≤ (2 : ℝ) ^ k) :
    IsBent f := by
  have hlower : (2 : ℝ) ^ k ≤ (maxWalshMagnitude f : ℝ) ^ 2 := by
    have hsum :
        (∑ a : FABL.F₂Cube k, (walshTransform f a : ℝ) ^ 2) ≤
          ∑ _a : FABL.F₂Cube k,
            (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      have habs := abs_walshTransform_le_maxWalshMagnitude f a
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
          (Nat.cast_nonneg (maxWalshMagnitude f))).2 habs
    rw [sum_walshTransform_sq_eq_two_pow_sq, Finset.sum_const,
      Finset.card_univ, card_f₂Cube, nsmul_eq_mul] at hsum
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hsum
    have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    nlinarith
  have hmaxEq : (maxWalshMagnitude f : ℝ) ^ 2 = (2 : ℝ) ^ k :=
    le_antisymm hmax hlower
  apply (hasFlatWalshSpectrum_iff_isBent f).1
  intro a
  have hcoeff : (walshTransform f a : ℝ) ^ 2 ≤
      (maxWalshMagnitude f : ℝ) ^ 2 := by
    have habs := abs_walshTransform_le_maxWalshMagnitude f a
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (Nat.cast_nonneg (maxWalshMagnitude f))).2 habs
  have hcoeffEq : (walshTransform f a : ℝ) ^ 2 =
      (maxWalshMagnitude f : ℝ) ^ 2 := by
    apply le_antisymm hcoeff
    by_contra hnot
    have hstrict : (walshTransform f a : ℝ) ^ 2 <
        (maxWalshMagnitude f : ℝ) ^ 2 := lt_of_not_ge hnot
    have hsumStrict :
        (∑ b : FABL.F₂Cube k, (walshTransform f b : ℝ) ^ 2) <
          ∑ _b : FABL.F₂Cube k,
            (maxWalshMagnitude f : ℝ) ^ 2 := by
      apply Finset.sum_lt_sum
      · intro b _hb
        have hb := abs_walshTransform_le_maxWalshMagnitude f b
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (walshTransform f b : ℝ))
            (Nat.cast_nonneg (maxWalshMagnitude f))).2 hb
      · exact ⟨a, Finset.mem_univ a, hstrict⟩
    rw [sum_walshTransform_sq_eq_two_pow_sq, Finset.sum_const,
      Finset.card_univ, card_f₂Cube, nsmul_eq_mul, hmaxEq] at hsumStrict
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hsumStrict
    have hpow : (2 : ℝ) ^ k * (2 : ℝ) ^ k =
        ((2 : ℝ) ^ k) ^ 2 := by ring
    rw [hpow] at hsumStrict
    exact (lt_irrefl _ hsumStrict).elim
  have hsquare : (walshTransform f a : ℝ) ^ 2 = (2 : ℝ) ^ k :=
    hcoeffEq.trans hmaxEq
  have hsqrt := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ k by positivity)
  have habsSquare : |(walshTransform f a : ℝ)| ^ 2 = (2 : ℝ) ^ k := by
    rw [sq_abs]
    exact hsquare
  nlinarith [abs_nonneg (walshTransform f a : ℝ),
    Real.sqrt_nonneg ((2 : ℝ) ^ k)]

private theorem natAbs_mul_two_pow_le_of_abs_intCast_le
    (z : ℤ) (r s : ℕ)
    (h : |((z * (2 : ℤ) ^ r : ℤ) : ℝ)| ≤
      ((2 ^ s : ℕ) : ℝ)) :
    2 ^ r * z.natAbs ≤ 2 ^ s := by
  have hcast : (((z * (2 : ℤ) ^ r).natAbs : ℕ) : ℝ) ≤
      ((2 ^ s : ℕ) : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hnat : (z * (2 : ℤ) ^ r).natAbs ≤ 2 ^ s := by
    exact_mod_cast hcast
  norm_num only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_of_nonneg,
    OfNat.ofNat, Nat.zero_le, mul_comm] at hnat ⊢
  exact hnat

private theorem natAbs_walshTransform_eq_of_eq_add_constant
    {f g : BooleanFunction k} (c : FABL.𝔽₂)
    (hfg : ∀ x, f x = g x + c) (a : FABL.F₂Cube k) :
    (walshTransform f a).natAbs = (walshTransform g a).natAbs := by
  have hwalsh : walshTransform f a = bitSignInt c * walshTransform g a := by
    rw [walshTransform, walshTransform]
    calc
      (∑ x : FABL.F₂Cube k, walshTerm f a x) =
          ∑ x : FABL.F₂Cube k, bitSignInt c * walshTerm g a x := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [walshTerm, walshTerm, hfg x, ← bitSignInt_add]
        congr 1
        abel
      _ = bitSignInt c * ∑ x : FABL.F₂Cube k, walshTerm g a x := by
        rw [Finset.mul_sum]
  rw [hwalsh, Int.natAbs_mul]
  have hsign : (bitSignInt c).natAbs = 1 := by
    rw [bitSignInt_eq_if_one]
    split <;> simp
  rw [hsign, one_mul]

private theorem exists_natAbs_walshTransform_eq_maxWalshMagnitude
    (f : BooleanFunction k) :
    ∃ a, (walshTransform f a).natAbs = maxWalshMagnitude f := by
  unfold maxWalshMagnitude
  obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube k))) Finset.univ_nonempty
    (fun u ↦ (walshTransform f u).natAbs)
  exact ⟨a, hmax.symm⟩

private theorem exists_compatibleNormalExtensions_of_isSubspaceNormal_booleanDirectSum
    {f₁ : BooleanFunction n} {f₂ : BooleanFunction m}
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂)
    (hnormal : IsSubspaceNormal (booleanDirectSum f₁ f₂)) :
    ∃ k₁ k₂, ∃ beta₁ : BooleanFunction k₁,
      ∃ beta₂ : BooleanFunction k₂,
        IsNormalExtension beta₁ f₁ ∧
          IsNormalExtension beta₂ f₂ ∧
            AreLinearlyEquivalentOrComplementary beta₁ beta₂ := by
  classical
  obtain ⟨N, hNrank, c, hconstant⟩ := hnormal
  let S := cubeSplitLinearEquiv n m
  let R : Submodule FABL.𝔽₂
      (FABL.F₂Cube n × FABL.F₂Cube m) := N.map S.toLinearMap
  have hconstantR (z : FABL.F₂Cube n × FABL.F₂Cube m) (hz : z ∈ R) :
      f₁ z.1 + f₂ z.2 = c := by
    obtain ⟨x, hxN, hxz⟩ := hz
    have hxFlat : x ∈ FABL.binaryAffineSubspace N 0 := by
      simpa [FABL.mem_binaryAffineSubspace_iff_add_mem] using hxN
    have hxValue := hconstant x hxFlat
    rw [← hxz]
    simpa [booleanDirectSum, S, cubeSplitLinearEquiv] using hxValue
  let M₁ := R.map (LinearMap.fst FABL.𝔽₂ (FABL.F₂Cube n) (FABL.F₂Cube m))
  let M₂ := R.map (LinearMap.snd FABL.𝔽₂ (FABL.F₂Cube n) (FABL.F₂Cube m))
  let P : R →ₗ[FABL.𝔽₂] M₁ :=
    (LinearMap.fst FABL.𝔽₂ (FABL.F₂Cube n) (FABL.F₂Cube m)).submoduleMap R
  let Q : R →ₗ[FABL.𝔽₂] M₂ :=
    (LinearMap.snd FABL.𝔽₂ (FABL.F₂Cube n) (FABL.F₂Cube m)).submoduleMap R
  let R' : Submodule FABL.𝔽₂ (M₁ × M₂) := LinearMap.range (P.prod Q)
  have hconstantR' (z : M₁ × M₂) (hz : z ∈ R') :
      f₁ z.1.1 + f₂ z.2.1 = c := by
    obtain ⟨q, hq⟩ := hz
    rw [← hq]
    exact hconstantR q.1 q.2
  have hR₁ : Function.Surjective (Prod.fst ∘ R'.subtype) := by
    intro x
    obtain ⟨z, hzR, hzx⟩ := x.2
    let zR : R := ⟨z, hzR⟩
    have hP : P zR = x := by
      apply Subtype.ext
      exact hzx
    let y : M₂ := Q zR
    let q : R' := ⟨(P zR, y), ⟨zR, rfl⟩⟩
    exact ⟨q, by simp [q, hP]⟩
  have hR₂ : Function.Surjective (Prod.snd ∘ R'.subtype) := by
    intro y
    obtain ⟨z, hzR, hzy⟩ := y.2
    let zR : R := ⟨z, hzR⟩
    have hQ : Q zR = y := by
      apply Subtype.ext
      exact hzy
    let x : M₁ := P zR
    let q : R' := ⟨(x, Q zR), ⟨zR, rfl⟩⟩
    exact ⟨q, by simp [q, hQ]⟩
  let W₁ := R'.goursatFst
  let W₂ := R'.goursatSnd
  obtain ⟨e, he⟩ := Submodule.goursat_surjective hR₁ hR₂
  have hinvariant₁ (x : M₁) (w : W₁) :
      f₁ (x + w.1).1 = f₁ x.1 := by
    obtain ⟨q, hqx⟩ := hR₁ x
    change q.1.1 = x at hqx
    have hwPair : (w.1, (0 : M₂)) ∈ R' := by
      apply R'.goursatFst_prod_goursatSnd_le
      exact ⟨w.2, W₂.zero_mem⟩
    have hbase := hconstantR' q.1 q.2
    have hshift := hconstantR' (q.1 + (w.1, 0))
      (R'.add_mem q.2 hwPair)
    apply add_right_cancel (b := f₂ q.1.2.1)
    simpa [hqx] using hshift.trans hbase.symm
  have hinvariant₂ (y : M₂) (w : W₂) :
      f₂ (y + w.1).1 = f₂ y.1 := by
    obtain ⟨q, hqy⟩ := hR₂ y
    change q.1.2 = y at hqy
    have hwPair : ((0 : M₁), w.1) ∈ R' := by
      apply R'.goursatFst_prod_goursatSnd_le
      exact ⟨W₁.zero_mem, w.2⟩
    have hbase := hconstantR' q.1 q.2
    have hshift := hconstantR' (q.1 + (0, w.1))
      (R'.add_mem q.2 hwPair)
    apply add_left_cancel (a := f₁ q.1.1.1)
    simpa [hqy] using hshift.trans hbase.symm
  obtain ⟨U₁, hW₁U₁⟩ := W₁.exists_isCompl
  obtain ⟨U₂, hW₂U₂⟩ := W₂.exists_isCompl
  let k₀ := Module.finrank FABL.𝔽₂ (M₁ ⧸ W₁)
  let r₁₀ := Module.finrank FABL.𝔽₂ W₁
  let r₂₀ := Module.finrank FABL.𝔽₂ W₂
  have hU₁rank : Module.finrank FABL.𝔽₂ U₁ = k₀ := by
    have hfinrank := LinearEquiv.finrank_eq
      (W₁.quotientEquivOfIsCompl U₁ hW₁U₁)
    simpa [k₀] using hfinrank.symm
  have hU₂rank : Module.finrank FABL.𝔽₂ U₂ = k₀ := by
    have heRank := LinearEquiv.finrank_eq e
    have hquotient₂ : Module.finrank FABL.𝔽₂ (M₂ ⧸ W₂) = k₀ := by
      simpa [k₀] using heRank.symm
    have hfinrank := LinearEquiv.finrank_eq
      (W₂.quotientEquivOfIsCompl U₂ hW₂U₂)
    exact hfinrank.symm.trans hquotient₂
  have hM₁rank : Module.finrank FABL.𝔽₂ M₁ = k₀ + r₁₀ := by
    have hquotient := W₁.finrank_quotient_add_finrank
    simpa [k₀, r₁₀] using hquotient.symm
  have hM₂rank : Module.finrank FABL.𝔽₂ M₂ = k₀ + r₂₀ := by
    have heRank := LinearEquiv.finrank_eq e
    have hquotient₂ : Module.finrank FABL.𝔽₂ (M₂ ⧸ W₂) = k₀ := by
      simpa [k₀] using heRank.symm
    have hquotient := W₂.finrank_quotient_add_finrank
    omega
  have hPQinjective : Function.Injective (P.prod Q) := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) hxy
    · exact congrArg (fun z ↦ z.2.1) hxy
  have hRrank : Module.finrank FABL.𝔽₂ R = (n + m) / 2 := by
    have hmap := LinearEquiv.finrank_map_eq S N
    simpa [R, hNrank] using hmap
  have hR'rank : Module.finrank FABL.𝔽₂ R' = (n + m) / 2 := by
    have hfinrank := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective (P.prod Q) hPQinjective)
    simpa [R', hRrank] using hfinrank.symm
  let p₁ : R' →ₗ[FABL.𝔽₂] M₁ :=
    (LinearMap.fst FABL.𝔽₂ M₁ M₂).comp R'.subtype
  let K₂ := LinearMap.ker p₁
  let s₂ : K₂ →ₗ[FABL.𝔽₂] M₂ :=
    ((LinearMap.snd FABL.𝔽₂ M₁ M₂).comp R'.subtype).domRestrict K₂
  have hs₂injective : Function.Injective s₂ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx := x.2
      have hy := y.2
      change x.1.1.1 = 0 at hx
      change y.1.1.1 = 0 at hy
      rw [hx, hy]
    · exact hxy
  have hs₂range : LinearMap.range s₂ = W₂ := by
    change LinearMap.range
      (((LinearMap.snd FABL.𝔽₂ M₁ M₂).comp R'.subtype).domRestrict
        (LinearMap.ker
          ((LinearMap.fst FABL.𝔽₂ M₁ M₂).comp R'.subtype))) =
      R'.goursatSnd
    rw [LinearMap.range_domRestrict]
    rfl
  have hK₂rank : Module.finrank FABL.𝔽₂ K₂ = r₂₀ := by
    have hfinrank := LinearEquiv.finrank_eq
      (LinearEquiv.ofInjective s₂ hs₂injective)
    rw [hs₂range] at hfinrank
    simpa [r₂₀] using hfinrank
  have hR'dimension : (n + m) / 2 = k₀ + r₁₀ + r₂₀ := by
    have hp₁Range : LinearMap.range p₁ = ⊤ :=
      LinearMap.range_eq_top.2 hR₁
    have hrankNullity := p₁.finrank_range_add_finrank_ker
    rw [hp₁Range] at hrankNullity
    simpa [K₂, hM₁rank, hK₂rank, hR'rank] using hrankNullity.symm
  let phi : U₁ ≃ₗ[FABL.𝔽₂] U₂ :=
    (W₁.quotientEquivOfIsCompl U₁ hW₁U₁).symm |>.trans
      (e.trans (W₂.quotientEquivOfIsCompl U₂ hW₂U₂))
  let eU₁ : FABL.F₂Cube k₀ ≃ₗ[FABL.𝔽₂] U₁ :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hU₁rank, Module.finrank_fintype_fun_eq_card])
  let eU₂ : FABL.F₂Cube k₀ ≃ₗ[FABL.𝔽₂] U₂ := eU₁.trans phi
  let eW₁ : FABL.F₂Cube r₁₀ ≃ₗ[FABL.𝔽₂] W₁ :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [r₁₀, Module.finrank_fintype_fun_eq_card])
  let eW₂ : FABL.F₂Cube r₂₀ ≃ₗ[FABL.𝔽₂] W₂ :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [r₂₀, Module.finrank_fintype_fun_eq_card])
  let eM₁ : FABL.F₂Cube (k₀ + r₁₀) ≃ₗ[FABL.𝔽₂] M₁ :=
    (cubeSplitLinearEquiv k₀ r₁₀).trans
      ((eU₁.prodCongr eW₁).trans
        (U₁.prodEquivOfIsCompl W₁ hW₁U₁.symm))
  let eM₂ : FABL.F₂Cube (k₀ + r₂₀) ≃ₗ[FABL.𝔽₂] M₂ :=
    (cubeSplitLinearEquiv k₀ r₂₀).trans
      ((eU₂.prodCongr eW₂).trans
        (U₂.prodEquivOfIsCompl W₂ hW₂U₂.symm))
  let beta₁ : BooleanFunction k₀ := fun u ↦
    f₁ (eU₁ u).1.1
  let beta₂ : BooleanFunction k₀ := fun u ↦
    f₂ (eU₂ u).1.1
  have hrestriction₁ (u : FABL.F₂Cube k₀) (w : FABL.F₂Cube r₁₀) :
      f₁ (eM₁ (Fin.append u w)).1 = beta₁ u := by
    have h := hinvariant₁ (eU₁ u).1 (eW₁ w)
    simpa [eM₁, beta₁, cubeSplitLinearEquiv] using h
  have hrestriction₂ (u : FABL.F₂Cube k₀) (w : FABL.F₂Cube r₂₀) :
      f₂ (eM₂ (Fin.append u w)).1 = beta₂ u := by
    have h := hinvariant₂ (eU₂ u).1 (eW₂ w)
    simpa [eM₂, beta₂, cubeSplitLinearEquiv] using h
  have hphiValue (u : U₁) :
      f₁ u.1.1 + f₂ (phi u).1.1 = c := by
    have hgraph :
        (W₁.mkQ u.1, W₂.mkQ (phi u).1) ∈ e.graph := by
      rw [LinearMap.mem_graph_iff]
      simp [phi, Submodule.mk_quotientEquivOfIsCompl_apply]
    rw [← he] at hgraph
    obtain ⟨q, hq⟩ := hgraph
    have hq₁ : W₁.mkQ q.1.1 = W₁.mkQ u.1 := by
      exact congrArg Prod.fst hq
    have hq₂ : W₂.mkQ q.1.2 = W₂.mkQ (phi u).1 := by
      exact congrArg Prod.snd hq
    have hdiff₁ : q.1.1 - u.1 ∈ W₁ :=
      (Submodule.Quotient.eq W₁).mp hq₁
    have hdiff₂ : q.1.2 - (phi u).1 ∈ W₂ :=
      (Submodule.Quotient.eq W₂).mp hq₂
    let w₁ : W₁ := ⟨q.1.1 - u.1, hdiff₁⟩
    let w₂ : W₂ := ⟨q.1.2 - (phi u).1, hdiff₂⟩
    have hvalue₁ : f₁ q.1.1.1 = f₁ u.1.1 := by
      have h := hinvariant₁ u.1 w₁
      simpa [w₁, sub_eq_add_neg, add_assoc, ZModModule.add_self,
        add_zero] using h
    have hvalue₂ : f₂ q.1.2.1 = f₂ (phi u).1.1 := by
      have h := hinvariant₂ (phi u).1 w₂
      simpa [w₂, sub_eq_add_neg, add_assoc, ZModModule.add_self,
        add_zero] using h
    rw [← hvalue₁, ← hvalue₂]
    exact hconstantR' q.1 q.2
  have hbetaRelation (u : FABL.F₂Cube k₀) :
      beta₁ u = beta₂ u + c := by
    have hvalue := hphiValue (eU₁ u)
    change beta₁ u + beta₂ u = c at hvalue
    apply add_right_cancel (b := beta₂ u)
    calc
      beta₁ u + beta₂ u = c := hvalue
      _ = (beta₂ u + c) + beta₂ u := by
        symm
        calc
          (beta₂ u + c) + beta₂ u =
              (beta₂ u + beta₂ u) + c := by abel
          _ = c := by rw [ZModModule.add_self, zero_add]
  have hcoordinate₁ :
      coordinateAffineSubspaceRestriction f₁ M₁ 0 eM₁ =
        booleanDirectSum beta₁ (0 : BooleanFunction r₁₀) := by
    funext x
    let q := cubeSplitLinearEquiv k₀ r₁₀ x
    have hx : Fin.append q.1 q.2 = x := by
      change (cubeSplitLinearEquiv k₀ r₁₀).symm q = x
      exact (cubeSplitLinearEquiv k₀ r₁₀).symm_apply_apply x
    rw [← hx, coordinateAffineSubspaceRestriction_apply, add_zero,
      hrestriction₁]
    simp [booleanDirectSum]
  have hcoordinate₂ :
      coordinateAffineSubspaceRestriction f₂ M₂ 0 eM₂ =
        booleanDirectSum beta₂ (0 : BooleanFunction r₂₀) := by
    funext x
    let q := cubeSplitLinearEquiv k₀ r₂₀ x
    have hx : Fin.append q.1 q.2 = x := by
      change (cubeSplitLinearEquiv k₀ r₂₀).symm q = x
      exact (cubeSplitLinearEquiv k₀ r₂₀).symm_apply_apply x
    rw [← hx, coordinateAffineSubspaceRestriction_apply, add_zero,
      hrestriction₂]
    simp [booleanDirectSum]
  have hzeroWalsh (r : ℕ) :
      walshTransform (0 : BooleanFunction r) 0 = (2 : ℤ) ^ r := by
    rw [walshTransform]
    calc
      (∑ x : FABL.F₂Cube r, walshTerm (0 : BooleanFunction r) 0 x) =
          ∑ _x : FABL.F₂Cube r, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        norm_num [walshTerm, bitSignInt, FABL.f₂DotProduct, dotProduct]
      _ = (2 : ℤ) ^ r := by simp
  have hbound₁ (a : FABL.F₂Cube k₀) :
      2 ^ r₁₀ * (walshTransform beta₁ a).natAbs ≤ 2 ^ (n / 2) := by
    have h := abs_walshTransform_coordinateAffineSubspaceRestriction_le
      f₁ M₁ 0 eM₁ (Fin.append a 0)
    rw [hcoordinate₁, walshTransform_directSum, hzeroWalsh,
      maxWalshMagnitude_eq_two_pow_half_of_isBent f₁ hf₁] at h
    change
      |(((walshTransform beta₁ a) * (2 : ℤ) ^ r₁₀ : ℤ) : ℝ)| ≤
        ((2 ^ (n / 2) : ℕ) : ℝ) at h
    exact natAbs_mul_two_pow_le_of_abs_intCast_le
      (walshTransform beta₁ a) r₁₀ (n / 2) h
  have hbound₂ (a : FABL.F₂Cube k₀) :
      2 ^ r₂₀ * (walshTransform beta₂ a).natAbs ≤ 2 ^ (m / 2) := by
    have h := abs_walshTransform_coordinateAffineSubspaceRestriction_le
      f₂ M₂ 0 eM₂ (Fin.append a 0)
    rw [hcoordinate₂, walshTransform_directSum, hzeroWalsh,
      maxWalshMagnitude_eq_two_pow_half_of_isBent f₂ hf₂] at h
    change
      |(((walshTransform beta₂ a) * (2 : ℤ) ^ r₂₀ : ℤ) : ℝ)| ≤
        ((2 ^ (m / 2) : ℕ) : ℝ) at h
    exact natAbs_mul_two_pow_le_of_abs_intCast_le
      (walshTransform beta₂ a) r₂₀ (m / 2) h
  have htotalHalf : (n + m) / 2 = n / 2 + m / 2 := by
    rcases even_of_isBent f₁ hf₁ with ⟨d₁, hd₁⟩
    rcases even_of_isBent f₂ hf₂ with ⟨d₂, hd₂⟩
    omega
  have hdimension : n / 2 + m / 2 = k₀ + r₁₀ + r₂₀ := by
    rw [← htotalHalf]
    exact hR'dimension
  have hwalshRelation (a : FABL.F₂Cube k₀) :
      (walshTransform beta₁ a).natAbs =
        (walshTransform beta₂ a).natAbs :=
    natAbs_walshTransform_eq_of_eq_add_constant c hbetaRelation a
  obtain ⟨aMax, haMax⟩ :=
    exists_natAbs_walshTransform_eq_maxWalshMagnitude beta₁
  have hproduct := Nat.mul_le_mul (hbound₁ aMax) (hbound₂ aMax)
  rw [← hwalshRelation aMax, haMax] at hproduct
  have hproduct' :
      2 ^ (r₁₀ + r₂₀) * (maxWalshMagnitude beta₁) ^ 2 ≤
        2 ^ (n / 2 + m / 2) := by
    calc
      2 ^ (r₁₀ + r₂₀) * (maxWalshMagnitude beta₁) ^ 2 =
          (2 ^ r₁₀ * maxWalshMagnitude beta₁) *
            (2 ^ r₂₀ * maxWalshMagnitude beta₁) := by
        rw [pow_add]
        ring
      _ ≤ 2 ^ (n / 2) * 2 ^ (m / 2) := hproduct
      _ = 2 ^ (n / 2 + m / 2) := by rw [pow_add]
  have hfactor : 2 ^ (n / 2 + m / 2) =
      2 ^ (r₁₀ + r₂₀) * 2 ^ k₀ := by
    rw [hdimension]
    have hexponent : k₀ + r₁₀ + r₂₀ =
        (r₁₀ + r₂₀) + k₀ := by omega
    rw [hexponent, pow_add]
  rw [hfactor] at hproduct'
  have hmaxSquareNat : (maxWalshMagnitude beta₁) ^ 2 ≤ 2 ^ k₀ :=
    Nat.le_of_mul_le_mul_left hproduct' (by positivity)
  have hmaxSquareReal : (maxWalshMagnitude beta₁ : ℝ) ^ 2 ≤
      (2 : ℝ) ^ k₀ := by
    exact_mod_cast hmaxSquareNat
  have hbeta₁ : IsBent beta₁ :=
    isBent_of_maxWalshMagnitude_sq_le_two_pow beta₁ hmaxSquareReal
  have hbetaFunction : beta₁ = beta₂ + FABL.affineFunction c 0 := by
    funext u
    rw [hbetaRelation u]
    simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
  have hbeta₂ : IsBent beta₂ := by
    have hsum : IsBent (beta₂ + FABL.affineFunction c 0) := by
      rw [← hbetaFunction]
      exact hbeta₁
    exact (isBent_add_affineFunction_iff beta₂ c 0).1 hsum
  have hkEven := even_of_isBent beta₁ hbeta₁
  have hpowBound₁ : 2 ^ (r₁₀ + k₀ / 2) ≤ 2 ^ (n / 2) := by
    rw [pow_add]
    simpa only [natAbs_walshTransform_eq_two_pow_half_of_isBent
      beta₁ hbeta₁] using hbound₁ 0
  have hpowBound₂ : 2 ^ (r₂₀ + k₀ / 2) ≤ 2 ^ (m / 2) := by
    rw [pow_add]
    simpa only [natAbs_walshTransform_eq_two_pow_half_of_isBent
      beta₂ hbeta₂] using hbound₂ 0
  have hdimLe₁ : r₁₀ + k₀ / 2 ≤ n / 2 :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hpowBound₁
  have hdimLe₂ : r₂₀ + k₀ / 2 ≤ m / 2 :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hpowBound₂
  have hdimEq₁ : r₁₀ + k₀ / 2 = n / 2 := by
    rcases hkEven with ⟨d, hd⟩
    omega
  have hdimEq₂ : r₂₀ + k₀ / 2 = m / 2 := by
    rcases hkEven with ⟨d, hd⟩
    omega
  have hnDimension : n = k₀ + (r₁₀ + r₁₀) := by
    rcases even_of_isBent f₁ hf₁ with ⟨d₁, hd₁⟩
    rcases hkEven with ⟨d, hd⟩
    omega
  have hmDimension : m = k₀ + (r₂₀ + r₂₀) := by
    rcases even_of_isBent f₂ hf₂ with ⟨d₂, hd₂⟩
    rcases hkEven with ⟨d, hd⟩
    omega
  obtain ⟨C₁, hM₁C₁⟩ := M₁.exists_isCompl
  obtain ⟨C₂, hM₂C₂⟩ := M₂.exists_isCompl
  have hC₁rank : Module.finrank FABL.𝔽₂ C₁ = r₁₀ := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hM₁C₁
    rw [hM₁rank] at hsum
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
    omega
  have hC₂rank : Module.finrank FABL.𝔽₂ C₂ = r₂₀ := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hM₂C₂
    rw [hM₂rank] at hsum
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
    omega
  let eC₁ : FABL.F₂Cube r₁₀ ≃ₗ[FABL.𝔽₂] C₁ :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hC₁rank, Module.finrank_fintype_fun_eq_card])
  let eC₂ : FABL.F₂Cube r₂₀ ≃ₗ[FABL.𝔽₂] C₂ :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [hC₂rank, Module.finrank_fintype_fun_eq_card])
  let L₁ : FABL.F₂Cube (k₀ + (r₁₀ + r₁₀)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n :=
    (cubeTripleLinearEquiv k₀ r₁₀).trans
      ((eU₁.prodCongr (eW₁.prodCongr eC₁)).trans
        ((LinearEquiv.prodAssoc FABL.𝔽₂ U₁ W₁ C₁).symm.trans
          (((U₁.prodEquivOfIsCompl W₁ hW₁U₁.symm).prodCongr
            (LinearEquiv.refl FABL.𝔽₂ C₁)).trans
            (M₁.prodEquivOfIsCompl C₁ hM₁C₁))))
  let L₂ : FABL.F₂Cube (k₀ + (r₂₀ + r₂₀)) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube m :=
    (cubeTripleLinearEquiv k₀ r₂₀).trans
      ((eU₂.prodCongr (eW₂.prodCongr eC₂)).trans
        ((LinearEquiv.prodAssoc FABL.𝔽₂ U₂ W₂ C₂).symm.trans
          (((U₂.prodEquivOfIsCompl W₂ hW₂U₂.symm).prodCongr
            (LinearEquiv.refl FABL.𝔽₂ C₂)).trans
            (M₂.prodEquivOfIsCompl C₂ hM₂C₂))))
  have hL₁ (u : FABL.F₂Cube k₀) (w : FABL.F₂Cube r₁₀) :
      f₁ (L₁ (Fin.append u (Fin.append w 0))) = beta₁ u := by
    have hzero : (fun _i : Fin r₁₀ ↦ (0 : FABL.𝔽₂)) = 0 := rfl
    simpa [L₁, cubeTripleLinearEquiv, cubeSplitLinearEquiv,
      LinearEquiv.prodAssoc, hzero,
      eC₁, eM₁] using hrestriction₁ u w
  have hL₂ (u : FABL.F₂Cube k₀) (w : FABL.F₂Cube r₂₀) :
      f₂ (L₂ (Fin.append u (Fin.append w 0))) = beta₂ u := by
    have hzero : (fun _i : Fin r₂₀ ↦ (0 : FABL.𝔽₂)) = 0 := rfl
    simpa [L₂, cubeTripleLinearEquiv, cubeSplitLinearEquiv,
      LinearEquiv.prodAssoc, hzero,
      eC₂, eM₂] using hrestriction₂ u w
  have hext₁ : IsNormalExtension beta₁ f₁ :=
    ⟨hbeta₁, hf₁, r₁₀, L₁, hL₁⟩
  have hext₂ : IsNormalExtension beta₂ f₂ :=
    ⟨hbeta₂, hf₂, r₂₀, L₂, hL₂⟩
  exact ⟨k₀, k₀, beta₁, beta₂, hext₁, hext₂,
    LinearEquiv.refl FABL.𝔽₂ (FABL.F₂Cube k₀), c, hbetaRelation⟩

/-- Carlet Proposition 29: a direct sum of bent functions is normal on a
linear subspace exactly when there are linearly equivalent or complementary
normal extensions of its summands. -/
theorem isSubspaceNormal_booleanDirectSum_iff
    {f₁ : BooleanFunction n} {f₂ : BooleanFunction m}
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂) :
    IsSubspaceNormal (booleanDirectSum f₁ f₂) ↔
      ∃ k₁ k₂, ∃ beta₁ : BooleanFunction k₁,
        ∃ beta₂ : BooleanFunction k₂,
          IsNormalExtension beta₁ f₁ ∧
            IsNormalExtension beta₂ f₂ ∧
              AreLinearlyEquivalentOrComplementary beta₁ beta₂ := by
  constructor
  · exact exists_compatibleNormalExtensions_of_isSubspaceNormal_booleanDirectSum hf₁ hf₂
  · rintro ⟨k₁, k₂, beta₁, beta₂, hext₁, hext₂, hcompatible⟩
    exact isSubspaceNormal_booleanDirectSum_of_compatibleNormalExtensions
      hext₁ hext₂ hcompatible
end CryptBoolean
