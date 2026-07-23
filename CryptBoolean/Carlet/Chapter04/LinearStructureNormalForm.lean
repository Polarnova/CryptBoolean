/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.LinearStructures
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Carlet Proposition 14: linear-structure normal forms

Linear structures can be moved to the final coordinate block by an invertible linear change of
variables. On that block the function is a linear form, while all remaining dependence is confined
to the complementary coordinates.
-/

open Module
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m k : ℕ}

private def cubeAppendLinearEquiv (m k : ℕ) :
    FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube m × FABL.F₂Cube k) where
  __ := (Fin.appendEquiv m k).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext i <;> rfl

private def tailEmbeddingLinearMap (m k : ℕ) :
    FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k) :=
  (cubeAppendLinearEquiv m k).symm.toLinearMap.comp
    (LinearMap.inr FABL.𝔽₂ (FABL.F₂Cube m) (FABL.F₂Cube k))

@[simp] private theorem tailEmbeddingLinearMap_apply
    (y : FABL.F₂Cube k) :
    tailEmbeddingLinearMap m k y = Fin.append 0 y :=
  rfl

private theorem tailEmbeddingLinearMap_injective :
    Function.Injective (tailEmbeddingLinearMap m k) := by
  intro y z h
  funext i
  simpa using congrFun h (Fin.natAdd m i)

private theorem append_head_add_tail
    (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
    Fin.append x 0 + tailEmbeddingLinearMap m k y = Fin.append x y := by
  apply (cubeAppendLinearEquiv m k).injective
  simp [cubeAppendLinearEquiv]

private theorem append_add_tail
    (x : FABL.F₂Cube m) (z y : FABL.F₂Cube k) :
    Fin.append x z + tailEmbeddingLinearMap m k y = Fin.append x (z + y) := by
  apply (cubeAppendLinearEquiv m k).injective
  simp [cubeAppendLinearEquiv]

private theorem isLinearStructure_comp_linearEquiv_iff
    (f : BooleanFunction (m + k))
    (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k))
    (e : FABL.F₂Cube (m + k)) :
    IsLinearStructure (f ∘ L) e ↔ IsLinearStructure f (L e) := by
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε, fun x ↦ ?_⟩
    have h := hε (L.symm x)
    simpa only [FABL.booleanDerivative, Function.comp_apply, L.apply_symm_apply,
      L.map_add, L.symm_apply_apply] using h
  · rintro ⟨ε, hε⟩
    refine ⟨ε, fun x ↦ ?_⟩
    simpa only [FABL.booleanDerivative, Function.comp_apply, L.map_add] using hε (L x)

private theorem exists_linearEquiv_tail_mem_submodule
    (U : Submodule FABL.𝔽₂ (FABL.F₂Cube (m + k)))
    (hk : k ≤ Module.finrank FABL.𝔽₂ U) :
    ∃ L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k),
      ∀ y : FABL.F₂Cube k, L (tailEmbeddingLinearMap m k y) ∈ U := by
  let B : Basis (Fin (Module.finrank FABL.𝔽₂ U)) FABL.𝔽₂ U :=
    Module.finBasis FABL.𝔽₂ U
  let v : Fin k → U := fun i ↦ B (Fin.castLE hk i)
  have hv : LinearIndependent FABL.𝔽₂ v :=
    B.linearIndependent.comp (fun i ↦ Fin.castLE hk i) (Fin.castLE_injective hk)
  let uU : FABL.F₂Cube k →ₗ[FABL.𝔽₂] U :=
    Fintype.linearCombination FABL.𝔽₂ v
  have huU : Function.Injective uU := by
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  let u : FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k) :=
    U.subtype.comp uU
  have hu : Function.Injective u := (Submodule.subtype_injective U).comp huU
  let e : LinearMap.range (tailEmbeddingLinearMap m k) ≃ₗ[FABL.𝔽₂]
      LinearMap.range u :=
    (LinearEquiv.ofInjective (tailEmbeddingLinearMap m k)
      tailEmbeddingLinearMap_injective).symm.trans
        (LinearEquiv.ofInjective u hu)
  obtain ⟨L, hL⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨L, fun y ↦ ?_⟩
  let z : LinearMap.range (tailEmbeddingLinearMap m k) :=
    ⟨tailEmbeddingLinearMap m k y, LinearMap.mem_range_self _ y⟩
  have hpreimage :
      (LinearEquiv.ofInjective (tailEmbeddingLinearMap m k)
        tailEmbeddingLinearMap_injective).symm z = y := by
    apply tailEmbeddingLinearMap_injective
    simpa [z] using
      (LinearEquiv.ofInjective_symm_apply (tailEmbeddingLinearMap m k) z)
  have hz : L (tailEmbeddingLinearMap m k y) = u y := by
    have hz' := (hL z).symm
    change L (tailEmbeddingLinearMap m k y) =
      u ((LinearEquiv.ofInjective (tailEmbeddingLinearMap m k)
        tailEmbeddingLinearMap_injective).symm z) at hz'
    simpa [hpreimage] using hz'
  rw [hz]
  exact (uU y).property

/-- The source-facing separated-coordinate normal form in Carlet Proposition 14. -/
def HasSeparatedLinearStructureNormalForm
    (f : BooleanFunction (m + k)) : Prop :=
  ∃ (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k))
      (g : BooleanFunction m) (ε : FABL.F₂Cube k),
    ∀ (x : FABL.F₂Cube m) (y : FABL.F₂Cube k),
      f (L (Fin.append x y)) = g x + FABL.f₂DotProduct ε y

/-- Carlet Proposition 14, general form: `k` linear-kernel dimensions are exactly `k`
separated affine coordinates after an invertible linear change of variables. -/
theorem finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm
    (f : BooleanFunction (m + k)) :
    k ≤ Module.finrank FABL.𝔽₂ (linearKernel f) ↔
      HasSeparatedLinearStructureNormalForm f := by
  constructor
  · intro hk
    obtain ⟨L, hL⟩ := exists_linearEquiv_tail_mem_submodule (linearKernel f) hk
    let h : BooleanFunction (m + k) := f ∘ L
    have htail (y : FABL.F₂Cube k) :
        IsLinearStructure h (tailEmbeddingLinearMap m k y) :=
      (isLinearStructure_comp_linearEquiv_iff f L _).2 (hL y)
    let q : FABL.F₂Cube k → FABL.𝔽₂ :=
      fun y ↦ h (tailEmbeddingLinearMap m k y) + h 0
    have hq : FABL.IsF₂Linear q := by
      intro y z
      obtain ⟨δ, hδ⟩ := htail z
      have hd := (hδ (tailEmbeddingLinearMap m k y)).trans
        (hδ 0).symm
      rw [FABL.booleanDerivative, FABL.booleanDerivative] at hd
      simp only [zero_add] at hd
      change q (y + z) = q y + q z
      change h (tailEmbeddingLinearMap m k (y + z)) + h 0 =
        (h (tailEmbeddingLinearMap m k y) + h 0) +
          (h (tailEmbeddingLinearMap m k z) + h 0)
      rw [(tailEmbeddingLinearMap m k).map_add]
      calc
        h (tailEmbeddingLinearMap m k y + tailEmbeddingLinearMap m k z) + h 0 =
            h (tailEmbeddingLinearMap m k y) + h (tailEmbeddingLinearMap m k z) := by
          calc
            _ =
                (h (tailEmbeddingLinearMap m k y) +
                    h (tailEmbeddingLinearMap m k y)) +
                  (h (tailEmbeddingLinearMap m k y + tailEmbeddingLinearMap m k z) +
                    h 0) := by rw [ZModModule.add_self, zero_add]
            _ = h (tailEmbeddingLinearMap m k y) +
                (h (tailEmbeddingLinearMap m k y) +
                  h (tailEmbeddingLinearMap m k y + tailEmbeddingLinearMap m k z)) +
                    h 0 := by abel
            _ = h (tailEmbeddingLinearMap m k y) +
                (h 0 + h (tailEmbeddingLinearMap m k z)) + h 0 := by rw [hd]
            _ = h (tailEmbeddingLinearMap m k y) + h (tailEmbeddingLinearMap m k z) +
                (h 0 + h 0) := by abel
            _ = _ := by rw [ZModModule.add_self, add_zero]
        _ = (h (tailEmbeddingLinearMap m k y) + h 0) +
            (h (tailEmbeddingLinearMap m k z) + h 0) := by
          calc
            h (tailEmbeddingLinearMap m k y) + h (tailEmbeddingLinearMap m k z) =
                (h (tailEmbeddingLinearMap m k y) +
                  h (tailEmbeddingLinearMap m k z)) + (h 0 + h 0) := by
              rw [ZModModule.add_self, add_zero]
            _ = (h (tailEmbeddingLinearMap m k y) + h 0) +
                (h (tailEmbeddingLinearMap m k z) + h 0) := by abel
    obtain ⟨ε, hε⟩ := (FABL.isF₂Linear_iff_exists_dotProduct q).1 hq
    refine ⟨L, fun x ↦ h (Fin.append x 0), ε, fun x y ↦ ?_⟩
    obtain ⟨δ, hδ⟩ := htail y
    have hd := (hδ (Fin.append x 0)).trans (hδ 0).symm
    rw [FABL.booleanDerivative, FABL.booleanDerivative] at hd
    simp only [zero_add] at hd
    change h (Fin.append x y) = h (Fin.append x 0) + FABL.f₂DotProduct ε y
    rw [← hε y]
    change h (Fin.append x y) = h (Fin.append x 0) +
      (h (tailEmbeddingLinearMap m k y) + h 0)
    rw [append_head_add_tail] at hd
    calc
      h (Fin.append x y) =
          (h (Fin.append x 0) + h (Fin.append x 0)) + h (Fin.append x y) := by
        rw [ZModModule.add_self, zero_add]
      _ = h (Fin.append x 0) +
          (h (Fin.append x 0) + h (Fin.append x y)) := by abel
      _ = h (Fin.append x 0) + (h 0 + h (tailEmbeddingLinearMap m k y)) := by
        rw [hd]
      _ = _ := by abel
  · rintro ⟨L, g, ε, hnormal⟩
    let uAmbient : FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k) :=
      L.toLinearMap.comp (tailEmbeddingLinearMap m k)
    have huMem (y : FABL.F₂Cube k) : uAmbient y ∈ linearKernel f := by
      apply (isLinearStructure_comp_linearEquiv_iff f L _).1
      refine ⟨FABL.f₂DotProduct ε y, fun z ↦ ?_⟩
      let p := (Fin.appendEquiv m k).symm z
      have hz : z = Fin.append p.1 p.2 := by
        exact ((Fin.appendEquiv m k).apply_symm_apply z).symm
      rw [FABL.booleanDerivative, hz, append_add_tail]
      change f (L (Fin.append p.1 p.2)) +
          f (L (Fin.append p.1 (p.2 + y))) = FABL.f₂DotProduct ε y
      rw [hnormal, hnormal]
      simp only [FABL.f₂DotProduct, dotProduct, Pi.add_apply]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      calc
        g p.1 + ∑ i, ε i * p.2 i +
            (g p.1 + ((∑ i, ε i * p.2 i) + ∑ i, ε i * y i)) =
            (g p.1 + g p.1) +
              ((∑ i, ε i * p.2 i) + ∑ i, ε i * p.2 i) +
                ∑ i, ε i * y i := by abel
        _ = ∑ i, ε i * y i := by
          rw [ZModModule.add_self, zero_add, ZModModule.add_self, zero_add]
    let u : FABL.F₂Cube k →ₗ[FABL.𝔽₂] linearKernel f :=
      LinearMap.codRestrict (linearKernel f) uAmbient huMem
    have hu : Function.Injective u := by
      intro y z hyz
      apply tailEmbeddingLinearMap_injective
      apply L.injective
      exact congrArg Subtype.val hyz
    have hfin := LinearMap.finrank_le_finrank_of_injective hu
    simpa [Module.finrank_fintype_fun_eq_card] using hfin

/-- Carlet Proposition 14, one-direction form: a nonzero linear structure is equivalent to
separating the final coordinate as `g(x₁,…,xₙ₋₁) + ε xₙ`. -/
theorem exists_nonzero_linearStructure_iff_exists_single_coordinate_normalForm
    (f : BooleanFunction (m + 1)) :
    (∃ e : FABL.F₂Cube (m + 1), e ≠ 0 ∧ IsLinearStructure f e) ↔
      ∃ (L : FABL.F₂Cube (m + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1))
          (g : BooleanFunction m) (ε : FABL.𝔽₂),
        ∀ (x : FABL.F₂Cube m) (a : FABL.𝔽₂),
          f (L (Fin.append x ![a])) = g x + ε * a := by
  have hnonzero :
      (∃ e : FABL.F₂Cube (m + 1), e ≠ 0 ∧ IsLinearStructure f e) ↔
        1 ≤ Module.finrank FABL.𝔽₂ (linearKernel f) := by
    rw [Submodule.one_le_finrank_iff, Submodule.ne_bot_iff]
    constructor
    · rintro ⟨e, he, hstructure⟩
      exact ⟨e, hstructure, he⟩
    · rintro ⟨e, hekernel, he⟩
      exact ⟨e, he, hekernel⟩
  constructor
  · intro hstructure
    have hfin := hnonzero.mp hstructure
    obtain ⟨L, g, ε, hnormal⟩ :=
      (finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm f).mp hfin
    refine ⟨L, g, ε 0, fun x a ↦ ?_⟩
    simpa [FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ] using hnormal x ![a]
  · rintro ⟨L, g, ε, hnormal⟩
    apply hnonzero.mpr
    apply (finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm f).mpr
    refine ⟨L, g, ![ε], fun x y ↦ ?_⟩
    have hy : y = ![y 0] := by
      funext i
      fin_cases i
      rfl
    rw [hy]
    simpa [FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ] using hnormal x (y 0)

end CryptBoolean
