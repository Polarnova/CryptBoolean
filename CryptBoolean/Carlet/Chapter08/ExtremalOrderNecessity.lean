/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.CoordinateQuadraticRigidity
public import CryptBoolean.Carlet.Chapter08.EmbeddedCoordinateRestrictions
public import CryptBoolean.Carlet.Chapter08.ExtremalOrderBent

import CryptBoolean.Carlet.Chapter06.NormalExtension
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Necessity at extremal propagation order

The restriction upgrades and rigidity reductions used in Carlet's
classification of propagation criteria at order `n-l-2`.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

@[simp] private theorem cubeReindexLinearEquiv_coordinateDirection
    {r : ℕ} (e : Equiv.Perm (Fin r)) (i : Fin r) :
    cubeReindexLinearEquiv e (coordinateDirection i) =
      coordinateDirection (e i) := by
  funext j
  simp [cubeReindexLinearEquiv, coordinateDirection,
    FABL.f₂CubeOfFinset_apply, Equiv.symm_apply_eq]

private theorem walshAdjointLinearEquiv_cubeReindex_symm
    {r : ℕ} (e : Equiv.Perm (Fin r)) (a : FABL.F₂Cube r) :
    walshAdjointLinearEquiv (cubeReindexLinearEquiv e).symm a =
      cubeReindexLinearEquiv e a := by
  apply (dotProductEquiv FABL.𝔽₂ (Fin r)).injective
  apply LinearMap.ext
  intro x
  rw [dotProductEquiv_apply_apply, dotProductEquiv_apply_apply]
  calc
    dotProduct
        (walshAdjointLinearEquiv (cubeReindexLinearEquiv e).symm a) x =
        ((dotProductEquiv FABL.𝔽₂ (Fin r)) a).comp
          (cubeReindexLinearEquiv e).symm.toLinearMap x := by
      exact DFunLike.congr_fun
        ((dotProductEquiv FABL.𝔽₂ (Fin r)).apply_symm_apply
          (((dotProductEquiv FABL.𝔽₂ (Fin r)) a).comp
            (cubeReindexLinearEquiv e).symm.toLinearMap)) x
    _ = dotProduct a ((cubeReindexLinearEquiv e).symm x) :=
      dotProductEquiv_apply_apply FABL.𝔽₂ (Fin r) _ _
    _ = dotProduct (cubeReindexLinearEquiv e a) x := by
      unfold dotProduct
      apply Fintype.sum_equiv e
      intro i
      simp [cubeReindexLinearEquiv]

private theorem bentDual_comp_cubeReindexLinearEquiv
    {r : ℕ} (f : BooleanFunction r) (e : Equiv.Perm (Fin r)) :
    bentDual (f ∘ cubeReindexLinearEquiv e) =
      bentDual f ∘ cubeReindexLinearEquiv e := by
  funext a
  rw [bentDual_comp_linearEquiv,
    walshAdjointLinearEquiv_cubeReindex_symm]
  rfl

private theorem secondBooleanDerivative_comp_linearEquiv
    {r s : ℕ} (f : BooleanFunction s)
    (L : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (a b : FABL.F₂Cube r) :
    secondBooleanDerivative (f ∘ L) a b =
      secondBooleanDerivative f (L a) (L b) ∘ L := by
  funext x
  simp only [secondBooleanDerivative_apply, Function.comp_apply,
    map_add]


private theorem functionExtend_add {r : ℕ} (e : Fin r ↪ Fin n)
    (x y : FABL.F₂Cube r) (x₀ y₀ : FABL.F₂Cube n) :
    Function.extend e (x + y) (x₀ + y₀) =
      Function.extend e x x₀ + Function.extend e y y₀ := by
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    simp only [e.injective.extend_apply, Pi.add_apply]
  · rw [Function.extend_apply' (x + y) (x₀ + y₀) i hi]
    simp only [Pi.add_apply]
    rw [Function.extend_apply' _ _ i hi,
      Function.extend_apply' _ _ i hi]

private theorem functionExtend_pullback {r : ℕ} (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) :
    Function.extend e (fun q ↦ x₀ (e q)) x₀ = x₀ := by
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ i hi]

private theorem functionExtend_coordinateDirection_zero {r : ℕ}
    (e : Fin r ↪ Fin n) (i : Fin r) :
    Function.extend e (coordinateDirection i) 0 =
      coordinateDirection (e i) := by
  funext j
  by_cases hj : ∃ q, e q = j
  · obtain ⟨q, rfl⟩ := hj
    rw [e.injective.extend_apply]
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, e.injective.eq_iff]
  · rw [Function.extend_apply' _ _ j hj]
    have hji : j ≠ e i := by
      intro h
      exact hj ⟨i, h.symm⟩
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hji]

private theorem secondBooleanDerivative_embeddedCoordinateRestriction_apply
    {r : ℕ} (f : BooleanFunction n) (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) (a b x : FABL.F₂Cube r) :
    secondBooleanDerivative (embeddedCoordinateRestriction f e x₀) a b x =
      secondBooleanDerivative f
        (Function.extend e a 0) (Function.extend e b 0)
        (Function.extend e x x₀) := by
  have hxa : Function.extend e (x + a) x₀ =
      Function.extend e x x₀ + Function.extend e a 0 := by
    simpa using functionExtend_add e x a x₀ 0
  have hxb : Function.extend e (x + b) x₀ =
      Function.extend e x x₀ + Function.extend e b 0 := by
    simpa using functionExtend_add e x b x₀ 0
  have hxab : Function.extend e (x + a + b) x₀ =
      Function.extend e x x₀ + Function.extend e a 0 +
        Function.extend e b 0 := by
    calc
      Function.extend e (x + a + b) x₀ =
          Function.extend e (x + a) x₀ + Function.extend e b 0 := by
        simpa using functionExtend_add e (x + a) b x₀ 0
      _ = Function.extend e x x₀ + Function.extend e a 0 +
          Function.extend e b 0 := by rw [hxa]
  simp only [secondBooleanDerivative_apply, embeddedCoordinateRestriction]
  rw [hxa, hxb, hxab]

private theorem secondBooleanDerivative_affineFunction
    {r : ℕ} (c : FABL.𝔽₂) (u a b : FABL.F₂Cube r) :
    secondBooleanDerivative (FABL.affineFunction c u) a b = 0 := by
  funext x
  simp only [secondBooleanDerivative_apply, FABL.affineFunction]
  have hxa : FABL.f₂DotProduct u (x + a) =
      FABL.f₂DotProduct u x + FABL.f₂DotProduct u a :=
    dotProduct_add u x a
  have hxb : FABL.f₂DotProduct u (x + b) =
      FABL.f₂DotProduct u x + FABL.f₂DotProduct u b :=
    dotProduct_add u x b
  have hxab : FABL.f₂DotProduct u (x + a + b) =
      FABL.f₂DotProduct u x + FABL.f₂DotProduct u a +
        FABL.f₂DotProduct u b := by
    calc
      FABL.f₂DotProduct u (x + a + b) =
          FABL.f₂DotProduct u (x + a) + FABL.f₂DotProduct u b :=
        dotProduct_add u (x + a) b
      _ = FABL.f₂DotProduct u x + FABL.f₂DotProduct u a +
          FABL.f₂DotProduct u b := by rw [hxa]
  rw [hxa, hxb, hxab]
  simp only [Pi.zero_apply]
  have htwo : (2 : FABL.𝔽₂) = 0 := ZMod.natCast_self 2
  have hfour : (4 : FABL.𝔽₂) = 0 := by decide
  ring_nf
  simp [htwo, hfour]

private theorem embeddedCoordinateRestriction_comp_cubeReindexLinearEquiv
    {r : ℕ} (f : BooleanFunction n) (e : Fin r ↪ Fin n)
    (x₀ : FABL.F₂Cube n) (σ : Equiv.Perm (Fin r)) :
    embeddedCoordinateRestriction f (σ.toEmbedding.trans e) x₀ =
      embeddedCoordinateRestriction f e x₀ ∘ cubeReindexLinearEquiv σ := by
  funext x
  change f (Function.extend (σ.toEmbedding.trans e) x x₀) =
    f (Function.extend e (cubeReindexLinearEquiv σ x) x₀)
  congr 1
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [e.injective.extend_apply]
    rw [← show (σ.toEmbedding.trans e) (σ.symm q) = e q by simp,
      (σ.toEmbedding.trans e).injective.extend_apply]
    simp [cubeReindexLinearEquiv]
  · rw [Function.extend_apply' _ _ i hi,
      Function.extend_apply' _ _ i]
    rintro ⟨q, hq⟩
    exact hi ⟨σ q, hq⟩

private theorem firstBlockSlice_embeddedCoordinateRestriction
    {r : ℕ} (f : BooleanFunction n) (e : Fin (r + 2) ↪ Fin n)
    (x₀ : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    firstBlockSlice (embeddedCoordinateRestriction f e x₀) y =
      embeddedCoordinateRestriction f
        ((Fin.castAddEmb 2).trans e)
        (Function.extend e (Fin.append 0 y) x₀) := by
  funext x
  change f (Function.extend e (Fin.append x y) x₀) =
    f (Function.extend ((Fin.castAddEmb 2).trans e) x
      (Function.extend e (Fin.append 0 y) x₀))
  congr 1
  funext i
  by_cases hi : ∃ q, e q = i
  · obtain ⟨q, rfl⟩ := hi
    rw [e.injective.extend_apply]
    refine Fin.addCases (fun p ↦ ?_) (fun t ↦ ?_) q
    · rw [← show ((Fin.castAddEmb 2).trans e) p = e (p.castAdd 2) by rfl,
        ((Fin.castAddEmb 2).trans e).injective.extend_apply]
      simp
    · have houtside :
          ¬ ∃ p, ((Fin.castAddEmb 2).trans e) p = e (Fin.natAdd r t) := by
        rintro ⟨p, hp⟩
        have hp' := congrArg Fin.val (e.injective hp)
        simp [Fin.castAddEmb, Fin.castLEEmb] at hp'
        omega
      rw [Function.extend_apply' _ _ _ houtside,
        e.injective.extend_apply]
      simp
  · rw [Function.extend_apply' _ _ i hi,
      Function.extend_apply' _ _ i]
    · rw [Function.extend_apply' _ _ i hi]
    · rintro ⟨p, hp⟩
      exact hi ⟨p.castAdd 2, hp⟩

private theorem finAppend_zero_single_eq_coordinateDirection_natAdd
    (r : ℕ) (j : Fin 2) :
    Fin.append (0 : FABL.F₂Cube r) (Pi.single j 1) =
      coordinateDirection (Fin.natAdd r j) := by
  funext i
  refine Fin.addCases (fun p ↦ ?_) (fun q ↦ ?_) i
  · have hne : Fin.castAdd 2 p ≠ Fin.natAdd r j := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
      omega
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hne]
  · rw [Fin.append_right, Pi.single_apply]
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply]

private theorem bentDual_secondBooleanDerivative_lastPair_of_extremal_order
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l) f)
    (e : Fin (l + 2) ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    secondBooleanDerivative (bentDual (embeddedCoordinateRestriction f e x₀))
        (coordinateDirection (Fin.natAdd l 0))
        (coordinateDirection (Fin.natAdd l 1)) = 1 := by
  let F := embeddedCoordinateRestriction f e x₀
  have hparameters : l + (n - l) = n := by omega
  have hlower :
      SatisfiesPropagationCriterionOfOrder l (n - l - 2) f :=
    hf.mono_order (by omega) (by omega)
  have hF : IsBent F := by
    apply isBent_embeddedCoordinateRestriction_of_order_pred_two
      (r := l + 2) (k := n - l - 2) f
      (by simpa using hlower) (by omega) (by omega)
      (heven.add (by decide)) e x₀
  have hslices (y : FABL.F₂Cube 2) :
      IsBent (firstBlockSlice F y) := by
    rw [show firstBlockSlice F y =
        embeddedCoordinateRestriction f ((Fin.castAddEmb 2).trans e)
          (Function.extend e (Fin.append 0 y) x₀) by
      exact firstBlockSlice_embeddedCoordinateRestriction f e x₀ y]
    exact isBent_embeddedCoordinateRestriction_of_order_dimension
      f hf hparameters ((Fin.castAddEmb 2).trans e)
        (Function.extend e (Fin.append 0 y) x₀)
  have hlast :=
    (isBent_firstBlockSlices_iff_bentDual_secondDerivative_eq_one
      F hF heven).1 hslices
  rw [finAppend_zero_single_eq_coordinateDirection_natAdd l 0,
    finAppend_zero_single_eq_coordinateDirection_natAdd l 1] at hlast
  exact hlast

private theorem bentDual_coordinateSecondDerivatives_eq_one_of_extremal_order
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l) f)
    (e : Fin (l + 2) ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    ∀ i j : Fin (l + 2), i ≠ j →
      secondBooleanDerivative (bentDual (embeddedCoordinateRestriction f e x₀))
        (coordinateDirection i) (coordinateDirection j) = 1 := by
  classical
  intro i j hij
  let p : Fin 2 ↪ Fin (l + 2) := Function.Embedding.embFinTwo
    (show Fin.natAdd l 0 ≠ Fin.natAdd l 1 by simp)
  let q : Fin 2 ↪ Fin (l + 2) := Function.Embedding.embFinTwo hij
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair p q
    p.injective q.injective
  have hpzero : p 0 = Fin.natAdd l 0 := by
    exact Function.Embedding.embFinTwo_apply_zero _
  have hpone : p 1 = Fin.natAdd l 1 := by
    exact Function.Embedding.embFinTwo_apply_one _
  have hqzero : q 0 = i := by
    exact Function.Embedding.embFinTwo_apply_zero _
  have hqone : q 1 = j := by
    exact Function.Embedding.embFinTwo_apply_one _
  have hσzero : σ (Fin.natAdd l 0) = i := by
    rw [← hpzero, ← hqzero]
    exact hσ 0
  have hσone : σ (Fin.natAdd l 1) = j := by
    rw [← hpone, ← hqone]
    exact hσ 1
  let F := embeddedCoordinateRestriction f e x₀
  let L := cubeReindexLinearEquiv σ
  have hlast := bentDual_secondBooleanDerivative_lastPair_of_extremal_order
    f l hl heven hlRange hf (σ.toEmbedding.trans e) x₀
  have hrestriction :
      embeddedCoordinateRestriction f (σ.toEmbedding.trans e) x₀ = F ∘ L := by
    exact embeddedCoordinateRestriction_comp_cubeReindexLinearEquiv f e x₀ σ
  have hdual :
      bentDual (embeddedCoordinateRestriction f (σ.toEmbedding.trans e) x₀) =
        bentDual F ∘ L := by
    rw [hrestriction]
    exact bentDual_comp_cubeReindexLinearEquiv F σ
  rw [hdual, secondBooleanDerivative_comp_linearEquiv] at hlast
  rw [cubeReindexLinearEquiv_coordinateDirection,
    cubeReindexLinearEquiv_coordinateDirection, hσzero, hσone] at hlast
  funext z
  have hz := congrFun hlast (L.symm z)
  simpa [L] using hz

private theorem secondBooleanDerivative_lastPair_embeddedCoordinateRestriction_eq_one
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l) f)
    (e : Fin (l + 2) ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    secondBooleanDerivative (embeddedCoordinateRestriction f e x₀)
        (coordinateDirection (Fin.natAdd l 0))
        (coordinateDirection (Fin.natAdd l 1)) = 1 := by
  let F := embeddedCoordinateRestriction f e x₀
  have hlower :
      SatisfiesPropagationCriterionOfOrder l (n - l - 2) f :=
    hf.mono_order (by omega) (by omega)
  have hF : IsBent F := by
    apply isBent_embeddedCoordinateRestriction_of_order_pred_two
      (r := l + 2) (k := n - l - 2) f
      (by simpa using hlower) (by omega) (by omega)
      (heven.add (by decide)) e x₀
  obtain ⟨c, u, hdual⟩ :=
    exists_completeQuadraticBit_add_affineFunction_of_coordinateSecondDerivatives_eq_one
      (bentDual F)
      (bentDual_coordinateSecondDerivatives_eq_one_of_extremal_order
        f l hl heven hlRange hf e x₀)
  have hdualBent : IsBent (bentDual F) := isBent_bentDual F hF
  have hslices (y : FABL.F₂Cube 2) :
      IsBent (firstBlockSlice (bentDual F) y) := by
    rw [hdual]
    exact isBent_firstBlockSlice_completeQuadraticBit_add_affineFunction
      heven c u y
  have hlast :=
    (isBent_firstBlockSlices_iff_bentDual_secondDerivative_eq_one
      (bentDual F) hdualBent heven).1 hslices
  rw [bentDual_bentDual F hF,
    finAppend_zero_single_eq_coordinateDirection_natAdd l 0,
    finAppend_zero_single_eq_coordinateDirection_natAdd l 1] at hlast
  exact hlast

private theorem isBent_embeddedCoordinateRestriction_completeQuadratic_add_affine
    {r : ℕ} (heven : Even r) (c : FABL.𝔽₂) (u : FABL.F₂Cube n)
    (e : Fin r ↪ Fin n) (x₀ : FABL.F₂Cube n) :
    IsBent (embeddedCoordinateRestriction
      ((FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u) e x₀) := by
  let g := embeddedCoordinateRestriction
    ((FABL.completeQuadraticBit : BooleanFunction n) +
      FABL.affineFunction c u) e x₀
  have hpairs (i j : Fin r) (hij : i ≠ j) :
      secondBooleanDerivative g (coordinateDirection i)
        (coordinateDirection j) = 1 := by
    funext x
    rw [secondBooleanDerivative_embeddedCoordinateRestriction_apply]
    rw [functionExtend_coordinateDirection_zero,
      functionExtend_coordinateDirection_zero]
    have heij : e i ≠ e j := fun h ↦ hij (e.injective h)
    rw [secondBooleanDerivative_add,
      secondBooleanDerivative_completeQuadraticBit_coordinateDirections_eq_one
        (e i) (e j) heij,
      secondBooleanDerivative_affineFunction]
    rfl
  obtain ⟨c', u', hg⟩ :=
    exists_completeQuadraticBit_add_affineFunction_of_coordinateSecondDerivatives_eq_one
      g hpairs
  change IsBent g
  rw [hg, isBent_add_affineFunction_iff]
  exact isBent_completeQuadraticBit heven

/-- The complete quadratic function plus an affine summand satisfies the
maximal coordinate order at every even propagation level. -/
theorem satisfiesPropagationCriterionOfOrder_dimension_completeQuadraticBit_add_affineFunction
    (l : ℕ) (heven : Even l) (hl : l ≤ n) (c : FABL.𝔽₂)
    (u : FABL.F₂Cube n) :
    SatisfiesPropagationCriterionOfOrder l (n - l)
      ((FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u) := by
  intro J z hfixed
  have hJle : J.card ≤ n := by
    simpa using Finset.card_le_univ J
  have hcomplement : n - J.card = n - l := by
    simpa [FABL.FixedIndex] using hfixed
  have hJcard : J.card = l := by omega
  let x₀ : FABL.F₂Cube n := fun i ↦
    if hi : i ∈ J then 0 else FABL.binarySignEquiv.symm (z ⟨i, hi⟩)
  have hz : coordinateFixedSignAssignment J x₀ = z := by
    funext i
    simp [coordinateFixedSignAssignment, x₀, i.property]
  have hevenJ : Even J.card := by simpa [hJcard] using heven
  have hembedded :=
    isBent_embeddedCoordinateRestriction_completeQuadratic_add_affine
      hevenJ c u (FABL.freeCoordinateEmbedding J) x₀
  have hrestriction :
      embeddedCoordinateRestriction
          ((FABL.completeQuadraticBit : BooleanFunction n) +
            FABL.affineFunction c u)
          (FABL.freeCoordinateEmbedding J) x₀ =
        coordinateRestriction
          ((FABL.completeQuadraticBit : BooleanFunction n) +
            FABL.affineFunction c u) J
          (coordinateFixedSignAssignment J x₀) := by
    funext x
    exact (coordinateRestriction_fixedAssignment_apply _ J x₀ x).symm
  rw [hrestriction] at hembedded
  have hcanonical :
      IsBent (coordinateRestriction
        ((FABL.completeQuadraticBit : BooleanFunction n) +
          FABL.affineFunction c u) J
        (coordinateFixedSignAssignment J x₀)) :=
    hembedded
  rw [hz] at hcanonical
  have hpc :=
    (isBent_iff_satisfiesPropagationCriterion_dimension _).1 hcanonical
  simpa [hJcard] using hpc

/-- Carlet Proposition 2, necessary direction: at a positive even level, the
maximal coordinate order forces the complete quadratic function up to an
affine summand. -/
theorem exists_completeQuadraticBit_add_affineFunction_of_order_dimension
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l) f) :
    ∃ c u, f =
      (FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u := by
  classical
  apply exists_completeQuadraticBit_add_affineFunction_of_coordinateSecondDerivatives_eq_one
  intro i j hij
  funext x₀
  let pair : Fin 2 ↪ Fin n := Function.Embedding.embFinTwo hij
  let available : Finset (Fin n) := ({i, j} : Finset (Fin n))ᶜ
  have havailable : l ≤ available.card := by
    dsimp [available]
    rw [Finset.card_compl]
    simp [hij]
    omega
  obtain ⟨base, hbase⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin l) (s := available) (by simpa using havailable)
  have hdisjoint : Disjoint (Set.range base) (Set.range pair) := by
    rw [Set.disjoint_range_iff]
    intro p q hpq
    have hbaseAvailable : base p ∈ available := hbase ⟨p, rfl⟩
    have hpairExcluded : pair q ∈ ({i, j} : Finset (Fin n)) := by
      rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
      · rw [show pair (0 : Fin 2) = i by
          exact Function.Embedding.embFinTwo_apply_zero _]
        simp
      · rw [show pair (1 : Fin 2) = j by
          exact Function.Embedding.embFinTwo_apply_one _]
        simp
    exact (Finset.mem_compl.mp hbaseAvailable)
      (by simpa [hpq] using hpairExcluded)
  let e : Fin (l + 2) ↪ Fin n := Fin.Embedding.append hdisjoint
  have hezero : e (Fin.natAdd l 0) = i := by
    change Fin.append base pair (Fin.natAdd l 0) = i
    rw [Fin.append_right]
    exact Function.Embedding.embFinTwo_apply_zero _
  have heone : e (Fin.natAdd l 1) = j := by
    change Fin.append base pair (Fin.natAdd l 1) = j
    rw [Fin.append_right]
    exact Function.Embedding.embFinTwo_apply_one _
  have hlocal :=
    secondBooleanDerivative_lastPair_embeddedCoordinateRestriction_eq_one
      f l hl heven hlRange hf e x₀
  let x : FABL.F₂Cube (l + 2) := fun q ↦ x₀ (e q)
  have hvalue := congrFun hlocal x
  rw [secondBooleanDerivative_embeddedCoordinateRestriction_apply] at hvalue
  rw [functionExtend_coordinateDirection_zero,
    functionExtend_coordinateDirection_zero, hezero, heone] at hvalue
  have hx : Function.extend e x x₀ = x₀ := by
    exact functionExtend_pullback e x₀
  rw [hx] at hvalue
  exact hvalue

/-- Carlet Proposition 2: at a positive even level, maximal coordinate-order
propagation is equivalent to the complete quadratic function up to an affine
summand. -/
theorem satisfiesPropagationCriterionOfOrder_dimension_iff_completeQuadratic_add_affine
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n) :
    SatisfiesPropagationCriterionOfOrder l (n - l) f ↔
      ∃ c u, f =
        (FABL.completeQuadraticBit : BooleanFunction n) +
          FABL.affineFunction c u := by
  constructor
  · exact exists_completeQuadraticBit_add_affineFunction_of_order_dimension
      f l hl heven hlRange
  · rintro ⟨c, u, rfl⟩
    exact satisfiesPropagationCriterionOfOrder_dimension_completeQuadraticBit_add_affineFunction
      l heven (by omega) c u

/-- If every restriction to `l+2` free coordinates satisfies `PC(l)`, with
`l` positive and even, then every such restriction is bent and hence satisfies
the full propagation criterion `PC(l+2)`. -/
theorem satisfiesPropagationCriterionOfOrder_add_two_of_even
    (f : BooleanFunction n) (l k : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hparameters : l + k + 2 = n)
    (hf : SatisfiesPropagationCriterionOfOrder l k f) :
    SatisfiesPropagationCriterionOfOrder (l + 2) k f := by
  intro J z hfixed
  have hJle : J.card ≤ n := by
    simpa using Finset.card_le_univ J
  have hcomplement : n - J.card = k := by
    simpa [FABL.FixedIndex] using hfixed
  have hJcard : J.card = l + 2 := by omega
  have hlocal :
      SatisfiesPropagationCriterion (J.card - 2)
        (coordinateRestriction f J z) := by
    simpa [hJcard] using hf J z hfixed
  have hJEven : Even J.card := by
    rw [hJcard]
    exact heven.add (by decide)
  have hfull :=
    satisfiesPropagationCriterion_dimension_of_pred_two_of_even
      (coordinateRestriction f J z) (by omega) hJEven hlocal
  simpa [hJcard] using hfull

/-- At Carlet's extremal order, a positive even propagation level upgrades by
two while keeping the same fixed-coordinate order. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_add_two_of_even
    (f : BooleanFunction n) (l : ℕ) (hl : 2 ≤ l) (heven : Even l)
    (hlRange : l + 2 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l - 2) f) :
    SatisfiesPropagationCriterionOfOrder (l + 2) (n - l - 2) f := by
  apply satisfiesPropagationCriterionOfOrder_add_two_of_even
    f l (n - l - 2) hl heven
  · omega
  · exact hf

/-- The even-level case of Carlet Theorem 5: two below maximal coordinate
order, only the complete quadratic function and its affine translates occur. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_even
    (f : BooleanFunction n) (l : ℕ) (hl : 0 < l) (heven : Even l)
    (hlRange : l + 4 ≤ n) :
    SatisfiesPropagationCriterionOfOrder l (n - l - 2) f ↔
      ∃ c u, f =
        (FABL.completeQuadraticBit : BooleanFunction n) +
          FABL.affineFunction c u := by
  have hltwo : 2 ≤ l := by
    obtain ⟨r, rfl⟩ := heven
    omega
  constructor
  · intro hf
    have hupgrade :=
      satisfiesPropagationCriterionOfOrder_extremal_add_two_of_even
        f l hltwo heven (by omega) hf
    have hendpoint :
        SatisfiesPropagationCriterionOfOrder (l + 2) (n - (l + 2)) f := by
      simpa [Nat.sub_sub] using hupgrade
    exact exists_completeQuadraticBit_add_affineFunction_of_order_dimension
      f (l + 2) (by omega) (heven.add (by decide)) (by omega) hendpoint
  · rintro ⟨c, u, rfl⟩
    exact
      satisfiesPropagationCriterionOfOrder_extremal_completeQuadraticBit_add_affineFunction
        l c u (by omega)

/-- At Carlet's extremal order, an odd propagation level at least five
upgrades by three while reducing the fixed-coordinate order by one. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_add_three_of_odd
    (f : BooleanFunction n) (l : ℕ) (hl : 5 ≤ l) (hodd : Odd l)
    (hlRange : l + 5 ≤ n)
    (hf : SatisfiesPropagationCriterionOfOrder l (n - l - 2) f) :
    SatisfiesPropagationCriterionOfOrder (l + 3) (n - l - 3) f := by
  intro J z hfixed
  have hJle : J.card ≤ n := by
    simpa using Finset.card_le_univ J
  have hcomplement : n - J.card = n - l - 3 := by
    simpa [FABL.FixedIndex] using hfixed
  have hJcard : J.card = l + 3 := by omega
  let x₀ : FABL.F₂Cube n := fun i ↦
    if hi : i ∈ J then 0 else FABL.binarySignEquiv.symm (z ⟨i, hi⟩)
  have hz : coordinateFixedSignAssignment J x₀ = z := by
    funext i
    simp [coordinateFixedSignAssignment, x₀, i.property]
  let e := FABL.freeCoordinateEmbedding J
  let g := embeddedCoordinateRestriction f e x₀
  have hgOrder : SatisfiesPropagationCriterionOfOrder l 1 g := by
    exact satisfiesPropagationCriterionOfOrder_embeddedCoordinateRestriction
      f hf (by omega) e x₀
  have hgOrder' :
      SatisfiesPropagationCriterionOfOrder (J.card - 3) 1 g := by
    simpa [hJcard] using hgOrder
  have hJEven : Even J.card := by
    obtain ⟨r, hr⟩ := hodd
    refine ⟨r + 2, ?_⟩
    omega
  have hgBent : IsBent g :=
    isBent_of_satisfiesPropagationCriterionOfOrder_pred_three_of_even
      g (by omega) hJEven hgOrder'
  have hrestriction :
      g = coordinateRestriction f J (coordinateFixedSignAssignment J x₀) := by
    funext x
    exact (coordinateRestriction_fixedAssignment_apply f J x₀ x).symm
  rw [hrestriction, hz] at hgBent
  have hfull :=
    (isBent_iff_satisfiesPropagationCriterion_dimension _).1 hgBent
  simpa [hJcard] using hfull

/-- The odd-level case of Carlet Theorem 5: two below maximal coordinate
order, only the complete quadratic function and its affine translates occur. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_odd
    (f : BooleanFunction n) (l : ℕ) (hl : 5 ≤ l) (hodd : Odd l)
    (hlRange : l + 5 ≤ n) :
    SatisfiesPropagationCriterionOfOrder l (n - l - 2) f ↔
      ∃ c u, f =
        (FABL.completeQuadraticBit : BooleanFunction n) +
          FABL.affineFunction c u := by
  have heven : Even (l + 3) := by
    obtain ⟨r, hr⟩ := hodd
    refine ⟨r + 2, ?_⟩
    omega
  constructor
  · intro hf
    have hupgrade :=
      satisfiesPropagationCriterionOfOrder_extremal_add_three_of_odd
        f l hl hodd hlRange hf
    have hendpoint :
        SatisfiesPropagationCriterionOfOrder (l + 3) (n - (l + 3)) f := by
      simpa [Nat.sub_sub] using hupgrade
    exact exists_completeQuadraticBit_add_affineFunction_of_order_dimension
      f (l + 3) (by omega) heven (by omega) hendpoint
  · rintro ⟨c, u, rfl⟩
    exact
      satisfiesPropagationCriterionOfOrder_extremal_completeQuadraticBit_add_affineFunction
        l c u (by omega)

/-- Carlet Theorem 5: in the stated even and odd ranges, the extremal
propagation criterion characterizes the complete quadratic function up to an
affine summand. -/
theorem satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic
    (f : BooleanFunction n) (l : ℕ)
    (hrange :
      (6 ≤ n ∧ 0 < l ∧ Even l ∧ l + 4 ≤ n) ∨
      (10 ≤ n ∧ 5 ≤ l ∧ Odd l ∧ l + 5 ≤ n)) :
    SatisfiesPropagationCriterionOfOrder l (n - l - 2) f ↔
      ∃ c u, f =
        (FABL.completeQuadraticBit : BooleanFunction n) +
          FABL.affineFunction c u := by
  rcases hrange with heven | hodd
  · exact satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_even
      f l heven.2.1 heven.2.2.1 heven.2.2.2
  · exact satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_odd
      f l hodd.2.1 hodd.2.2.1 hodd.2.2.2

end CryptBoolean
