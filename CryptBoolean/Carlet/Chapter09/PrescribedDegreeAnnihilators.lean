/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.GeneralProperties
public import FABL.Chapter03.Restrictions

/-!
# Prescribed-degree annihilator estimates

Carlet Chapter 9: the refined annihilator-space dimension estimate and its
product-weight consequence used in the higher-order nonlinearity bound.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private abbrev FreeBinaryCube (S : Finset (Fin n)) := S → FABL.𝔽₂
private abbrev FixedBinaryCube (S : Finset (Fin n)) := FABL.FixedIndex S → FABL.𝔽₂

private def binaryCubeSplitEquiv (S : Finset (Fin n)) :
    FABL.F₂Cube n ≃ FreeBinaryCube S × FixedBinaryCube S :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ i ∈ S) (fun _ ↦ FABL.𝔽₂)

private def combineBinaryCube (S : Finset (Fin n))
    (y : FreeBinaryCube S) (z : FixedBinaryCube S) : FABL.F₂Cube n :=
  (binaryCubeSplitEquiv S).symm (y, z)

@[simp] private theorem combineBinaryCube_apply_free
    (S : Finset (Fin n)) (y : FreeBinaryCube S) (z : FixedBinaryCube S) (i : S) :
    combineBinaryCube S y z i = y i := by
  simp [combineBinaryCube, binaryCubeSplitEquiv,
    Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

@[simp] private theorem combineBinaryCube_apply_fixed
    (S : Finset (Fin n)) (y : FreeBinaryCube S) (z : FixedBinaryCube S)
    (i : FABL.FixedIndex S) :
    combineBinaryCube S y z i = z i := by
  simp [combineBinaryCube, binaryCubeSplitEquiv,
    Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

private def indexedMonomial {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (x : ι → FABL.𝔽₂) : FABL.𝔽₂ :=
  ∏ i ∈ T, x i

private theorem anfMonomial_combineBinaryCube
    (S U : Finset (Fin n)) (y : FreeBinaryCube S) (z : FixedBinaryCube S) :
    FABL.anfMonomial U (combineBinaryCube S y z) =
      indexedMonomial (FABL.freeFrequencyPart S U) y *
        indexedMonomial (FABL.fixedFrequencyPart S U) z := by
  classical
  calc
    FABL.anfMonomial U (combineBinaryCube S y z) =
        FABL.anfMonomial
          (FABL.liftFreeFrequency (FABL.freeFrequencyPart S U) ∪
            FABL.liftFixedFrequency (FABL.fixedFrequencyPart S U))
          (combineBinaryCube S y z) := by
      rw [FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart]
    _ = _ := by
      rw [FABL.anfMonomial, Finset.prod_union
        (FABL.disjoint_liftFreeFrequency_liftFixedFrequency _ _)]
      congr 1
      · simp [indexedMonomial, FABL.liftFreeFrequency]
      · simp [indexedMonomial, FABL.liftFixedFrequency]

private theorem sum_indexedMonomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) :
    (∑ x : ι → FABL.𝔽₂, indexedMonomial T x) =
      if T = Finset.univ then 1 else 0 := by
  let factor : ι → FABL.𝔽₂ → FABL.𝔽₂ :=
    fun i b ↦ if i ∈ T then b else 1
  have hsumId : (∑ b : FABL.𝔽₂, b) = 1 := by
    change (0 : FABL.𝔽₂) + 1 = 1
    exact zero_add 1
  have hsumOne : (∑ _b : FABL.𝔽₂, (1 : FABL.𝔽₂)) = 0 := by
    change (1 : FABL.𝔽₂) + 1 = 0
    exact ZModModule.add_self 1
  have hprod (x : ι → FABL.𝔽₂) :
      (∏ i, factor i (x i)) = indexedMonomial T x := by
    classical
    simp [factor, indexedMonomial]
  calc
    (∑ x : ι → FABL.𝔽₂, indexedMonomial T x) =
        ∑ x : ι → FABL.𝔽₂, ∏ i, factor i (x i) := by
      apply Fintype.sum_congr
      intro x
      exact (hprod x).symm
    _ = ∏ i, ∑ b : FABL.𝔽₂, factor i b :=
      (Fintype.prod_sum factor).symm
    _ = if T = Finset.univ then 1 else 0 := by
      by_cases hT : T = Finset.univ
      · subst T
        rw [if_pos rfl]
        apply Finset.prod_eq_one
        intro i _hi
        simpa [factor] using hsumId
      · rw [if_neg hT]
        obtain ⟨i, hi⟩ : ∃ i, i ∉ T := by
          by_contra h
          push Not at h
          exact hT (Finset.eq_univ_of_forall h)
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simpa [factor, hi] using hsumOne


private theorem sum_combineBinaryCube_eq_anfCoeff
    (h : BooleanFunction n) (S : Finset (Fin n))
    (hdegree : FABL.functionAlgebraicDegree h ≤ S.card)
    (z : FixedBinaryCube S) :
    (∑ y : FreeBinaryCube S, h (combineBinaryCube S y z)) = FABL.anfCoeff h S := by
  classical
  calc
    (∑ y : FreeBinaryCube S, h (combineBinaryCube S y z)) =
        ∑ y : FreeBinaryCube S,
          ∑ U : Finset (Fin n),
            FABL.anfCoeff h U *
              FABL.anfMonomial U (combineBinaryCube S y z) := by
      apply Fintype.sum_congr
      intro y
      exact congrFun (FABL.anfEval_anfCoeff h).symm (combineBinaryCube S y z)
    _ = ∑ U : Finset (Fin n),
          ∑ y : FreeBinaryCube S,
            FABL.anfCoeff h U *
              FABL.anfMonomial U (combineBinaryCube S y z) := by
      rw [Finset.sum_comm]
    _ = ∑ U : Finset (Fin n),
          FABL.anfCoeff h U * indexedMonomial (FABL.fixedFrequencyPart S U) z *
            (∑ y : FreeBinaryCube S,
              indexedMonomial (FABL.freeFrequencyPart S U) y) := by
      apply Fintype.sum_congr
      intro U
      calc
        (∑ y : FreeBinaryCube S,
            FABL.anfCoeff h U * FABL.anfMonomial U (combineBinaryCube S y z)) =
            ∑ y : FreeBinaryCube S,
              FABL.anfCoeff h U *
                (indexedMonomial (FABL.freeFrequencyPart S U) y *
                  indexedMonomial (FABL.fixedFrequencyPart S U) z) := by
          apply Fintype.sum_congr
          intro y
          rw [anfMonomial_combineBinaryCube]
        _ = ∑ y : FreeBinaryCube S,
              (FABL.anfCoeff h U *
                indexedMonomial (FABL.fixedFrequencyPart S U) z) *
                  indexedMonomial (FABL.freeFrequencyPart S U) y := by
          apply Fintype.sum_congr
          intro y
          ring
        _ = _ := by rw [← Finset.mul_sum]
    _ = ∑ U : Finset (Fin n),
          FABL.anfCoeff h U * indexedMonomial (FABL.fixedFrequencyPart S U) z *
            (if FABL.freeFrequencyPart S U = Finset.univ then 1 else 0) := by
      apply Fintype.sum_congr
      intro U
      rw [sum_indexedMonomial]
    _ = FABL.anfCoeff h S := by
      rw [Fintype.sum_eq_single S]
      · have hfree : FABL.freeFrequencyPart S S = Finset.univ := by
          ext i
          simp [FABL.freeFrequencyPart]
        have hfixed : FABL.fixedFrequencyPart S S = ∅ := by
          ext i
          simp [FABL.fixedFrequencyPart, i.property]
        simp [hfree, hfixed, indexedMonomial]
      · intro U hUS
        by_cases hcoeff : FABL.anfCoeff h U = 0
        · simp [hcoeff]
        · have hcard : U.card ≤ S.card :=
            (FABL.algebraicDegree_le_iff (FABL.anfCoeff h) S.card).mp
              hdegree U hcoeff
          have hfree : FABL.freeFrequencyPart S U ≠ Finset.univ := by
            intro hfree
            have hsubset : S ⊆ U := by
              intro i hi
              let j : S := ⟨i, hi⟩
              have hj : j ∈ FABL.freeFrequencyPart S U := by rw [hfree]; simp
              simpa using (FABL.mem_freeFrequencyPart S U j).mp hj
            exact hUS (Finset.eq_of_subset_of_card_le hsubset hcard).symm
          rw [if_neg hfree, mul_zero]


private theorem exists_support_in_fixedFiber
    (h : BooleanFunction n) (S : Finset (Fin n))
    (hdegree : FABL.functionAlgebraicDegree h ≤ S.card)
    (hcoeff : FABL.anfCoeff h S ≠ 0) (z : FixedBinaryCube S) :
    ∃ y : FreeBinaryCube S, h (combineBinaryCube S y z) = 1 := by
  have hsum : (∑ y : FreeBinaryCube S, h (combineBinaryCube S y z)) ≠ 0 := by
    rw [sum_combineBinaryCube_eq_anfCoeff h S hdegree z]
    exact hcoeff
  obtain ⟨y, _hy, hy⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hsum
  exact ⟨y, Fin.eq_one_of_ne_zero _ hy⟩

private theorem exists_anfCoefficient_card_eq_functionAlgebraicDegree
    (h : BooleanFunction n) (hne : h ≠ 0) :
    ∃ S : Finset (Fin n),
      FABL.anfCoeff h S ≠ 0 ∧ S.card = FABL.functionAlgebraicDegree h := by
  classical
  have hsupport : (FABL.anfSupport (FABL.anfCoeff h)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    rw [← FABL.anfEval_anfCoeff h]
    funext x
    rw [FABL.anfEval]
    apply Finset.sum_eq_zero
    intro S _hS
    have hzero : FABL.anfCoeff h S = 0 := by
      by_contra hcoeff
      have hmem : S ∈ FABL.anfSupport (FABL.anfCoeff h) :=
        (FABL.mem_anfSupport _ _).2 hcoeff
      rw [hempty] at hmem
      simp at hmem
    simp [hzero]
  obtain ⟨S, hSmem, hsup⟩ := Finset.exists_mem_eq_sup
    (FABL.anfSupport (FABL.anfCoeff h)) hsupport Finset.card
  refine ⟨S, (FABL.mem_anfSupport _ _).1 hSmem, ?_⟩
  exact hsup.symm


private noncomputable def fixedIndexEquivFin (S : Finset (Fin n)) :
    FABL.FixedIndex S ≃ Fin (n - S.card) :=
  Fintype.equivOfCardEq (by
    simp [FABL.FixedIndex])

private noncomputable def fixedBinaryCubeLinearEquiv (S : Finset (Fin n)) :
    FixedBinaryCube S ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n - S.card) :=
  LinearEquiv.piCongrLeft FABL.𝔽₂
    (fun _ : Fin (n - S.card) ↦ FABL.𝔽₂) (fixedIndexEquivFin S)

private def fixedCoordinateRestrictionLinearMap (S : Finset (Fin n)) :
    FABL.F₂Cube n →ₗ[FABL.𝔽₂] FixedBinaryCube S where
  toFun x i := x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def fixedCoordinateProjection (S : Finset (Fin n)) :
    FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube (n - S.card) :=
  (fixedBinaryCubeLinearEquiv S).toLinearMap.comp
    (fixedCoordinateRestrictionLinearMap S)

private theorem fixedCoordinateRestriction_combineBinaryCube
    (S : Finset (Fin n)) (y : FreeBinaryCube S) (z : FixedBinaryCube S) :
    fixedCoordinateRestrictionLinearMap S (combineBinaryCube S y z) = z := by
  funext i
  exact combineBinaryCube_apply_fixed S y z i

private theorem fixedCoordinateProjection_combineBinaryCube
    (S : Finset (Fin n)) (y : FreeBinaryCube S) (z : FixedBinaryCube S) :
    fixedCoordinateProjection S (combineBinaryCube S y z) =
      fixedBinaryCubeLinearEquiv S z := by
  change fixedBinaryCubeLinearEquiv S
      (fixedCoordinateRestrictionLinearMap S (combineBinaryCube S y z)) = _
  rw [fixedCoordinateRestriction_combineBinaryCube]

/-- Every fiber of `P` contains a support point of `h`. -/
private def HasSupportSection {m : ℕ} (h : BooleanFunction n)
    (P : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube m) : Prop :=
  ∀ y, ∃ x, h x = 1 ∧ P x = y

private theorem fixedCoordinateProjection_hasSupportSection
    (h : BooleanFunction n) (S : Finset (Fin n))
    (hdegree : FABL.functionAlgebraicDegree h ≤ S.card)
    (hcoeff : FABL.anfCoeff h S ≠ 0) :
    HasSupportSection h (fixedCoordinateProjection S) := by
  intro y
  let z : FixedBinaryCube S := (fixedBinaryCubeLinearEquiv S).symm y
  obtain ⟨x, hx⟩ := exists_support_in_fixedFiber h S hdegree hcoeff z
  refine ⟨combineBinaryCube S x z, hx, ?_⟩
  rw [fixedCoordinateProjection_combineBinaryCube]
  exact (fixedBinaryCubeLinearEquiv S).apply_symm_apply y

private theorem exists_supportSection_projection
    (h : BooleanFunction n) (hne : h ≠ 0) :
    ∃ P : FABL.F₂Cube n →ₗ[FABL.𝔽₂]
        FABL.F₂Cube (n - FABL.functionAlgebraicDegree h),
      HasSupportSection h P := by
  obtain ⟨S, hcoeff, hScard⟩ :=
    exists_anfCoefficient_card_eq_functionAlgebraicDegree h hne
  rw [← hScard]
  exact ⟨fixedCoordinateProjection S,
    fixedCoordinateProjection_hasSupportSection h S (by rw [hScard]) hcoeff⟩


private def reedMullerPullbackLinearMap {m : ℕ} (k : ℕ)
    (P : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube m) :
    reedMuller k m →ₗ[FABL.𝔽₂] reedMuller k n where
  toFun q := ⟨q.1 ∘ P,
    (functionAlgebraicDegree_comp_affineMap_le_general q.1 P.toAffineMap).trans q.2⟩
  map_add' q q' := by
    apply Subtype.ext
    rfl
  map_smul' c q := by
    apply Subtype.ext
    rfl

private noncomputable def annihilatorCoefficientPullbackLinearMap
    {m : ℕ} (k : ℕ)
    (P : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube m) :
    (↥(FABL.lowDegreeFourierFamily m k) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      (↥(FABL.lowDegreeFourierFamily n k) → FABL.𝔽₂) :=
  (reedMullerAnfEquiv k n).toLinearMap.comp
    ((reedMullerPullbackLinearMap k P).comp
      (reedMullerAnfEquiv k m).symm.toLinearMap)

private theorem annihilatorEvaluation_comp_pullback_injective
    {m : ℕ} (h : BooleanFunction n) (k : ℕ)
    (P : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube m)
    (hsupport : HasSupportSection h P) :
    Function.Injective
      ((annihilatorEvaluationLinearMap h k).comp
        (annihilatorCoefficientPullbackLinearMap k P)) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro c hc
    have hcEval := LinearMap.mem_ker.mp hc
    let q : reedMuller k m := (reedMullerAnfEquiv k m).symm c
    have hqZero : q.1 = 0 := by
      funext y
      obtain ⟨x, hxSupport, hxProjection⟩ := hsupport y
      have hxMem : x ∈ support h := (mem_support h x).2 hxSupport
      have hx := congrFun hcEval ⟨x, hxMem⟩
      dsimp [annihilatorCoefficientPullbackLinearMap,
        reedMullerPullbackLinearMap, annihilatorEvaluationLinearMap] at hx
      rw [(reedMullerAnfEquiv k n).symm_apply_apply] at hx
      change q.1 (P x) = 0 at hx
      rw [hxProjection] at hx
      exact hx
    have hqSubtypeZero : q = 0 := Subtype.ext hqZero
    have hcZero := congrArg (reedMullerAnfEquiv k m) hqSubtypeZero
    simpa [q] using hcZero
  · exact bot_le


/-- Dimension of the degree-at-most-`k` annihilator space. -/
noncomputable def annihilatorSpaceDimension
    (h : BooleanFunction n) (k : ℕ) : ℕ :=
  Module.finrank FABL.𝔽₂
    (LinearMap.ker (annihilatorEvaluationLinearMap h k))

private theorem sum_choose_le_annihilatorEvaluation_range_finrank_of_supportSection
    {m : ℕ} (h : BooleanFunction n) (k : ℕ)
    (P : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.F₂Cube m)
    (hsupport : HasSupportSection h P) :
    (∑ i ∈ Finset.range (k + 1), Nat.choose m i) ≤
      Module.finrank FABL.𝔽₂
        (LinearMap.range (annihilatorEvaluationLinearMap h k)) := by
  let E := annihilatorCoefficientPullbackLinearMap k P
  let L := annihilatorEvaluationLinearMap h k
  have hinjective : Function.Injective (L.comp E) :=
    annihilatorEvaluation_comp_pullback_injective h k P hsupport
  calc
    (∑ i ∈ Finset.range (k + 1), Nat.choose m i) =
        Module.finrank FABL.𝔽₂
          (↥(FABL.lowDegreeFourierFamily m k) → FABL.𝔽₂) :=
      (annihilatorEvaluationLinearMap_domain_finrank m k).symm
    _ = Module.finrank FABL.𝔽₂ (LinearMap.range (L.comp E)) :=
      (LinearEquiv.ofInjective (L.comp E) hinjective).finrank_eq
    _ ≤ Module.finrank FABL.𝔽₂ (LinearMap.range L) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range E L)

private theorem annihilatorSpaceDimension_add_sum_choose_sub_exactDegree_le
    (h : BooleanFunction n) (hne : h ≠ 0) (k : ℕ) :
    annihilatorSpaceDimension h k +
        (∑ i ∈ Finset.range (k + 1),
          Nat.choose (n - FABL.functionAlgebraicDegree h) i) ≤
      ∑ i ∈ Finset.range (k + 1), Nat.choose n i := by
  obtain ⟨P, hsupport⟩ := exists_supportSection_projection h hne
  have hrange :=
    sum_choose_le_annihilatorEvaluation_range_finrank_of_supportSection
      h k P hsupport
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (annihilatorEvaluationLinearMap h k)
  rw [annihilatorEvaluationLinearMap_domain_finrank] at hrank
  unfold annihilatorSpaceDimension
  omega

/-- Carlet's prescribed-degree annihilator-dimension estimate, in additive
form: a nonzero degree-at-most-`r` function loses at least the dimension of
`R(k,n-r)` from its annihilator space. -/
theorem annihilatorSpaceDimension_add_sum_choose_sub_degree_le
    (h : BooleanFunction n) (hne : h ≠ 0) (r k : ℕ)
    (hdegree : FABL.functionAlgebraicDegree h ≤ r) :
    annihilatorSpaceDimension h k +
        (∑ i ∈ Finset.range (k + 1), Nat.choose (n - r) i) ≤
      ∑ i ∈ Finset.range (k + 1), Nat.choose n i := by
  have hdimension : n - r ≤ n - FABL.functionAlgebraicDegree h :=
    Nat.sub_le_sub_left hdegree n
  have hsum :
      (∑ i ∈ Finset.range (k + 1), Nat.choose (n - r) i) ≤
        ∑ i ∈ Finset.range (k + 1),
          Nat.choose (n - FABL.functionAlgebraicDegree h) i := by
    apply Finset.sum_le_sum
    intro i _hi
    exact Nat.choose_le_choose i hdimension
  exact (Nat.add_le_add_left hsum _).trans
    (annihilatorSpaceDimension_add_sum_choose_sub_exactDegree_le h hne k)

private theorem annihilatorSpaceDimension_mul_le
    (f h : BooleanFunction n) (k : ℕ)
    (hdegree : FABL.functionAlgebraicDegree h + k < algebraicImmunity f) :
    annihilatorSpaceDimension (f * h) k ≤ annihilatorSpaceDimension h k := by
  unfold annihilatorSpaceDimension
  have hinclusion :
      LinearMap.ker (annihilatorEvaluationLinearMap h k) ≤
        LinearMap.ker (annihilatorEvaluationLinearMap (f * h) k) := by
    intro c hc
    have hproduct :
        h * ((reedMullerAnfEquiv k n).symm c).1 = 0 :=
      (mem_ker_annihilatorEvaluationLinearMap_iff h c).1 hc
    rw [mem_ker_annihilatorEvaluationLinearMap_iff]
    calc
      (f * h) * ((reedMullerAnfEquiv k n).symm c).1 =
          f * (h * ((reedMullerAnfEquiv k n).symm c).1) := by ac_rfl
      _ = 0 := by rw [hproduct, mul_zero]
  by_contra hdimension
  have hlt : Module.finrank FABL.𝔽₂
      (LinearMap.ker (annihilatorEvaluationLinearMap h k)) <
      Module.finrank FABL.𝔽₂
        (LinearMap.ker (annihilatorEvaluationLinearMap (f * h) k)) := by
    exact Nat.lt_of_not_ge hdimension
  have hstrict :
      LinearMap.ker (annihilatorEvaluationLinearMap h k) <
        LinearMap.ker (annihilatorEvaluationLinearMap (f * h) k) :=
    Submodule.lt_of_le_of_finrank_lt_finrank hinclusion hlt
  obtain ⟨c, hcFh, hcH⟩ := SetLike.exists_of_lt hstrict
  let q : reedMuller k n := (reedMullerAnfEquiv k n).symm c
  have hqNe : h * q.1 ≠ 0 := by
    intro hzero
    apply hcH
    exact (mem_ker_annihilatorEvaluationLinearMap_iff h c).2 hzero
  have hFhq : (f * h) * q.1 = 0 :=
    (mem_ker_annihilatorEvaluationLinearMap_iff (f * h) c).1 hcFh
  let p : BooleanFunction n := h * q.1
  have hpDegree : FABL.functionAlgebraicDegree p ≤
      FABL.functionAlgebraicDegree h + k := by
    exact (FABL.functionAlgebraicDegree_mul_le_add h q.1).trans
      (Nat.add_le_add_left q.2 _)
  have hpWitness : IsAlgebraicImmunityWitness f p := by
    left
    refine ⟨hqNe, ?_⟩
    calc
      f * p = (f * h) * q.1 := by ac_rfl
      _ = 0 := hFhq
  have hAI := algebraicImmunity_le_functionAlgebraicDegree f p hpWitness
  omega

/-- A prescribed-degree multiplier of degree below `AI(f)` cannot make the
product `f * h` lighter than the Reed–Muller dimension in the remaining
coordinates. -/
theorem sum_choose_sub_degree_le_hammingWeight_mul
    (f h : BooleanFunction n) (hne : h ≠ 0) (r : ℕ)
    (hdegree : FABL.functionAlgebraicDegree h ≤ r)
    (hrAI : r < algebraicImmunity f) :
    (∑ i ∈ Finset.range (algebraicImmunity f - r),
      Nat.choose (n - r) i) ≤ hammingWeight (f * h) := by
  let k := algebraicImmunity f - r - 1
  have hkSucc : k + 1 = algebraicImmunity f - r := by
    dsimp [k]
    omega
  have hkernelMul : annihilatorSpaceDimension (f * h) k ≤
      annihilatorSpaceDimension h k :=
    annihilatorSpaceDimension_mul_le f h k (by
      dsimp [k]
      omega)
  have hdimensionH :=
    annihilatorSpaceDimension_add_sum_choose_sub_degree_le
      h hne r k hdegree
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (annihilatorEvaluationLinearMap (f * h) k)
  have hrange : Module.finrank FABL.𝔽₂
      (LinearMap.range (annihilatorEvaluationLinearMap (f * h) k)) ≤
      hammingWeight (f * h) := by
    calc
      Module.finrank FABL.𝔽₂
          (LinearMap.range (annihilatorEvaluationLinearMap (f * h) k)) ≤
          Module.finrank FABL.𝔽₂
            (↥(support (f * h)) → FABL.𝔽₂) :=
        Submodule.finrank_le _
      _ = hammingWeight (f * h) :=
        annihilatorEvaluationLinearMap_codomain_finrank (f * h)
  rw [annihilatorEvaluationLinearMap_domain_finrank] at hrankNullity
  unfold annihilatorSpaceDimension at hkernelMul hdimensionH
  rw [hkSucc] at hdimensionH hrankNullity
  omega


end CryptBoolean
