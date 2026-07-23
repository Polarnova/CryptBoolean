/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.FastAlgebraic
public import CryptBoolean.Carlet.Chapter04.LinearStructureNormalForm
public import Mathlib.LinearAlgebra.Prod

/-!
# Upper bounds on algebraic immunity

The universal half-dimension bound, its functorial form under surjective affine
factorization, and the improvement supplied by a large linear kernel.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m n k : ℕ}

/-- Every coordinate of an affine map between binary cubes has algebraic degree at most one. -/
theorem functionAlgebraicDegree_affineMap_coordinate_le_one_general
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m) (i : Fin m) :
    FABL.functionAlgebraicDegree (fun x ↦ L x i) ≤ 1 := by
  have hlinear : FABL.IsF₂Linear (fun x ↦ L.linear x i) := by
    intro x y
    exact congrArg (fun z ↦ z i) (L.linear.map_add x y)
  obtain ⟨a, ha⟩ := (FABL.isF₂Linear_iff_exists_dotProduct _).mp hlinear
  have hcoordinate :
      (fun x ↦ L x i) = FABL.affineFunction (L 0 i) a := by
    funext x
    have hdecomp : L x = L.linear x + L 0 := by
      simpa using congrFun (AffineMap.decomp L) x
    calc
      L x i = L.linear x i + L 0 i := by
        simpa using congrArg (fun z ↦ z i) hdecomp
      _ = FABL.f₂DotProduct a x + L 0 i := by rw [ha x]
      _ = L 0 i + FABL.f₂DotProduct a x := add_comm _ _
      _ = FABL.affineFunction (L 0 i) a x := rfl
  rw [hcoordinate]
  exact FABL.functionAlgebraicDegree_affineFunction_le_one (L 0 i) a

/-- Substituting affine coordinates of a different ambient dimension into an ANF monomial
does not increase its degree. -/
theorem functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card_general
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m)
    (S : Finset (Fin m)) :
    FABL.functionAlgebraicDegree (fun x ↦ FABL.anfMonomial S (L x)) ≤ S.card := by
  calc
    FABL.functionAlgebraicDegree (fun x ↦ FABL.anfMonomial S (L x)) ≤
        ∑ i ∈ S, FABL.functionAlgebraicDegree (fun x ↦ L x i) := by
      have hfunctions : (∏ i ∈ S, (fun x ↦ L x i)) =
          (fun x ↦ FABL.anfMonomial S (L x)) := by
        funext x
        simp [FABL.anfMonomial, Finset.prod_apply]
      rw [← hfunctions]
      exact FABL.functionAlgebraicDegree_finset_prod_le S (fun i x ↦ L x i)
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact functionAlgebraicDegree_affineMap_coordinate_le_one_general L i
    _ = S.card := by simp

/-- Composition with an affine map between binary cubes cannot increase algebraic degree. -/
theorem functionAlgebraicDegree_comp_affineMap_le_general
    (f : BooleanFunction m)
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m) :
    FABL.functionAlgebraicDegree (f ∘ L) ≤
      FABL.functionAlgebraicDegree f := by
  classical
  let term : Finset (Fin m) → BooleanFunction n :=
    fun S x ↦ FABL.anfCoeff f S * FABL.anfMonomial S (L x)
  have hsum : f ∘ L = ∑ S, term S := by
    funext x
    simp only [Function.comp_apply, Fintype.sum_apply, term]
    exact (congrFun (FABL.anfEval_anfCoeff f) (L x)).symm
  rw [hsum]
  exact FABL.functionAlgebraicDegree_finset_sum_le Finset.univ term
      (FABL.functionAlgebraicDegree f) (by
        intro S _
        by_cases hS : FABL.anfCoeff f S = 0
        · have hterm : term S = 0 := by
            funext x
            simp [term, hS]
          rw [hterm, FABL.functionAlgebraicDegree_zero]
          exact Nat.zero_le _
        · have hSone : FABL.anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
          have hterm : term S = fun x ↦ FABL.anfMonomial S (L x) := by
            funext x
            simp [term, hSone]
          rw [hterm]
          apply (functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card_general
            L S).trans
          exact (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) _).mp
            (by rfl) S hS)

private theorem IsAlgebraicImmunityWitness.comp_surjectiveAffineMap
    {f g : BooleanFunction m} (h : IsAlgebraicImmunityWitness f g)
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m)
    (hL : Function.Surjective L) :
    IsAlgebraicImmunityWitness (f ∘ L) (g ∘ L) := by
  have hnonzero (hg : g ≠ 0) : g ∘ L ≠ 0 := by
    intro hzero
    apply hg
    funext y
    obtain ⟨x, rfl⟩ := hL y
    exact congrFun hzero x
  rcases h with h | h
  · left
    refine ⟨hnonzero h.1, ?_⟩
    funext x
    simpa [Function.comp_apply] using congrFun h.2 (L x)
  · right
    refine ⟨hnonzero h.1, ?_⟩
    funext x
    simpa [Function.comp_apply] using congrFun h.2 (L x)

/-- Pulling a Boolean function back along a surjective affine map cannot increase
algebraic immunity. -/
theorem algebraicImmunity_comp_surjectiveAffineMap_le
    (f : BooleanFunction m)
    (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube m)
    (hL : Function.Surjective L) :
    algebraicImmunity (f ∘ L) ≤ algebraicImmunity f := by
  obtain ⟨g, hg, hdegree⟩ :=
    exists_witness_functionAlgebraicDegree_eq_algebraicImmunity f
  calc
    algebraicImmunity (f ∘ L) ≤
        FABL.functionAlgebraicDegree (g ∘ L) :=
      algebraicImmunity_le_functionAlgebraicDegree (f ∘ L) (g ∘ L)
        (hg.comp_surjectiveAffineMap L hL)
    _ ≤ FABL.functionAlgebraicDegree g :=
      functionAlgebraicDegree_comp_affineMap_le_general g L
    _ = algebraicImmunity f := hdegree

/-- Carlet's universal algebraic-immunity bound `AI(f) ≤ ⌈n/2⌉`. -/
theorem algebraicImmunity_le_ceiling_half (f : BooleanFunction n) :
    algebraicImmunity f ≤ (n + 1) / 2 := by
  let d := (n + 1) / 2
  have hsum : n ≤ d + d := by
    dsimp [d]
    omega
  obtain ⟨g, h, hg, hgdegree, hhdegree, hrelation⟩ :=
    exists_fastAlgebraicRelation_of_add_ge (f := f) (e := d) (d := d) hsum
  obtain ⟨q, hq, hqdegree, hzero⟩ :=
    (exists_lowDegreeRelation_iff_exists_algebraicImmunityWitness f d).mp
      ⟨g, h, hg, hgdegree, hhdegree, hrelation⟩
  have hwitness : IsAlgebraicImmunityWitness f q := by
    rcases hzero with hzero | hzero
    · exact Or.inl ⟨hq, hzero⟩
    · exact Or.inr ⟨hq, hzero⟩
  exact (algebraicImmunity_le_functionAlgebraicDegree f q hwitness).trans hqdegree

/-- A function factors through at most `k` affine coordinates when it is the pullback of a
`k`-variable Boolean function along a surjective affine map. -/
def HasSurjectiveAffineFactorization (f : BooleanFunction n) (k : ℕ) : Prop :=
  ∃ (L : FABL.F₂Cube n →ᵃ[FABL.𝔽₂] FABL.F₂Cube k)
      (g : BooleanFunction k),
    Function.Surjective L ∧ f = g ∘ L

/-- Carlet's `k`-variable refinement: affine factorization through `k` coordinates gives
`AI(f) ≤ ⌈k/2⌉`. -/
theorem algebraicImmunity_le_ceiling_half_of_hasSurjectiveAffineFactorization
    (f : BooleanFunction n) (hf : HasSurjectiveAffineFactorization f k) :
    algebraicImmunity f ≤ (k + 1) / 2 := by
  obtain ⟨L, g, hL, rfl⟩ := hf
  exact (algebraicImmunity_comp_surjectiveAffineMap_le g L hL).trans
    (algebraicImmunity_le_ceiling_half g)

private def splitCubeLinearEquiv (m k : ℕ) :
    FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube m × FABL.F₂Cube k) where
  __ := (Fin.appendEquiv m k).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext i <;> rfl

private def singletonCubeLinearEquiv :
    FABL.𝔽₂ ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 1 where
  toFun a := ![a]
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i
    rfl
  map_add' _ _ := by
    funext i
    fin_cases i
    rfl
  map_smul' _ _ := by
    funext i
    fin_cases i
    rfl

private def tailDotLinearMap (a : FABL.F₂Cube k) :
    FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.𝔽₂ where
  toFun y := FABL.f₂DotProduct a y
  map_add' y z := by
    simp [FABL.f₂DotProduct, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' c y := by
    rw [FABL.f₂DotProduct, FABL.f₂DotProduct, dotProduct, dotProduct]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      ∑ i, a i * (c * y i) = ∑ i, c * (a i * y i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = c * ∑ i, a i * y i := by rw [Finset.mul_sum]

private def headFactorLinearMap
    (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k)) :
    FABL.F₂Cube (m + k) →ₗ[FABL.𝔽₂] FABL.F₂Cube m :=
  (LinearMap.fst FABL.𝔽₂ (FABL.F₂Cube m) (FABL.F₂Cube k)).comp
    ((splitCubeLinearEquiv m k).toLinearMap.comp L.symm.toLinearMap)

private def separatedFactorLinearMap
    (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k))
    (a : FABL.F₂Cube k) :
    FABL.F₂Cube (m + k) →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1) :=
  (splitCubeLinearEquiv m 1).symm.toLinearMap.comp
    ((headFactorLinearMap L).prod
      (singletonCubeLinearEquiv.toLinearMap.comp
        ((tailDotLinearMap a).comp
          ((LinearMap.snd FABL.𝔽₂ (FABL.F₂Cube m) (FABL.F₂Cube k)).comp
            ((splitCubeLinearEquiv m k).toLinearMap.comp L.symm.toLinearMap)))))

private theorem tailDotLinearMap_surjective
    (a : FABL.F₂Cube k) (ha : a ≠ 0) :
    Function.Surjective (tailDotLinearMap a) := by
  have hexists : ∃ i : Fin k, a i ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hexists
  have hiOne : a i = 1 := Fin.eq_one_of_ne_zero _ hi
  intro b
  let y : FABL.F₂Cube k := fun j ↦ if j = i then b else 0
  refine ⟨y, ?_⟩
  change FABL.f₂DotProduct a y = b
  rw [FABL.f₂DotProduct, dotProduct, Finset.sum_eq_single i]
  · simp [y, hiOne]
  · intro j _ hji
    simp [y, hji]
  · simp

private theorem headFactorLinearMap_surjective
    (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k)) :
    Function.Surjective (headFactorLinearMap L) := by
  intro x
  refine ⟨L (Fin.append x 0), ?_⟩
  simp [headFactorLinearMap, splitCubeLinearEquiv]

private theorem separatedFactorLinearMap_surjective
    (L : FABL.F₂Cube (m + k) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + k))
    (a : FABL.F₂Cube k) (ha : a ≠ 0) :
    Function.Surjective (separatedFactorLinearMap L a) := by
  intro z
  let p := (Fin.appendEquiv m 1).symm z
  obtain ⟨y, hy⟩ := tailDotLinearMap_surjective a ha (p.2 0)
  refine ⟨L (Fin.append p.1 y), ?_⟩
  have hz : z = Fin.append p.1 p.2 := by
    exact ((Fin.appendEquiv m 1).apply_symm_apply z).symm
  rw [hz]
  apply (splitCubeLinearEquiv m 1).injective
  apply Prod.ext
  · funext i
    simp [separatedFactorLinearMap, headFactorLinearMap,
      splitCubeLinearEquiv, p]
  · funext i
    fin_cases i
    simpa [separatedFactorLinearMap, headFactorLinearMap,
      splitCubeLinearEquiv, singletonCubeLinearEquiv] using hy

/-- A separated linear-structure normal form with `m` nonlinear coordinates factors through
`m` affine coordinates when its tail form vanishes, and through `m+1` otherwise. -/
theorem hasSurjectiveAffineFactorization_of_hasSeparatedLinearStructureNormalForm
    (f : BooleanFunction (m + k))
    (hf : HasSeparatedLinearStructureNormalForm f) :
    HasSurjectiveAffineFactorization f m ∨
      HasSurjectiveAffineFactorization f (m + 1) := by
  obtain ⟨L, g, ε, hnormal⟩ := hf
  by_cases hε : ε = 0
  · left
    let A : FABL.F₂Cube (m + k) →ᵃ[FABL.𝔽₂] FABL.F₂Cube m :=
      (headFactorLinearMap L).toAffineMap
    refine ⟨A, g, headFactorLinearMap_surjective L, ?_⟩
    funext z
    let p := (Fin.appendEquiv m k).symm (L.symm z)
    have hz : z = L (Fin.append p.1 p.2) := by
      rw [← L.apply_symm_apply z]
      exact congrArg L (((Fin.appendEquiv m k).apply_symm_apply (L.symm z)).symm)
    rw [hz, hnormal, hε]
    simp [A, headFactorLinearMap, splitCubeLinearEquiv, p,
      FABL.f₂DotProduct]
  · right
    let A : FABL.F₂Cube (m + k) →ᵃ[FABL.𝔽₂] FABL.F₂Cube (m + 1) :=
      (separatedFactorLinearMap L ε).toAffineMap
    let G : BooleanFunction (m + 1) := fun z ↦
      let p := (Fin.appendEquiv m 1).symm z
      g p.1 + p.2 0
    refine ⟨A, G, separatedFactorLinearMap_surjective L ε hε, ?_⟩
    funext z
    let p := (Fin.appendEquiv m k).symm (L.symm z)
    have hz : z = L (Fin.append p.1 p.2) := by
      rw [← L.apply_symm_apply z]
      exact congrArg L (((Fin.appendEquiv m k).apply_symm_apply (L.symm z)).symm)
    rw [hz, hnormal]
    simp [A, G, separatedFactorLinearMap, headFactorLinearMap,
      splitCubeLinearEquiv, singletonCubeLinearEquiv, tailDotLinearMap, p]

/-- Carlet's linear-kernel refinement: `m` nonlinear coordinates and an affine tail give
`AI(f) ≤ ⌈m/2+1⌉ = ⌈(m+1)/2⌉`. -/
theorem algebraicImmunity_le_ceiling_half_add_one_of_hasSeparatedLinearStructureNormalForm
    (f : BooleanFunction (m + k))
    (hf : HasSeparatedLinearStructureNormalForm f) :
    algebraicImmunity f ≤ (m + 2) / 2 := by
  rcases hasSurjectiveAffineFactorization_of_hasSeparatedLinearStructureNormalForm f hf with
    hfactor | hfactor
  · exact (algebraicImmunity_le_ceiling_half_of_hasSurjectiveAffineFactorization
      f hfactor).trans (by omega)
  · simpa [Nat.add_assoc] using
      (algebraicImmunity_le_ceiling_half_of_hasSurjectiveAffineFactorization f hfactor)

/-- If the linear kernel contains `k` independent directions in dimension `m+k`, then
`AI(f) ≤ ⌈m/2+1⌉`. -/
theorem algebraicImmunity_le_ceiling_half_add_one_of_linearKernel_finrank_ge
    (f : BooleanFunction (m + k))
    (hk : k ≤ Module.finrank FABL.𝔽₂ (linearKernel f)) :
    algebraicImmunity f ≤ (m + 2) / 2 := by
  apply algebraicImmunity_le_ceiling_half_add_one_of_hasSeparatedLinearStructureNormalForm
  exact (finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm f).mp hk

end CryptBoolean
