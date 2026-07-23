/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenPatternOrbitSums
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenOrbitSoundness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rank-seven weight-sixteen orbit aggregation

Complete canonical affine-map sums are converted into lower bounds for
injective affine maps and then for the corresponding sets of distinct words.
The final classification-facing result takes the rank-seven classification as
an explicit hypothesis.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Injective affine maps from the seven-variable cube into the ambient cube. -/
noncomputable def rankSevenWeightSixteenInjectiveAffineMapData (n : ℕ) :
    Finset (SevenVariableAffineMapData n) := by
  classical
  exact Finset.univ.filter fun d ↦ LinearIndependent FABL.𝔽₂ d.2

theorem mem_rankSevenWeightSixteenInjectiveAffineMapData_iff
    (d : SevenVariableAffineMapData n) :
    d ∈ rankSevenWeightSixteenInjectiveAffineMapData n ↔
      LinearIndependent FABL.𝔽₂ d.2 := by
  simp [rankSevenWeightSixteenInjectiveAffineMapData]

private theorem injective_union_rankDeficientSevenVariableAffineMapData :
    rankSevenWeightSixteenInjectiveAffineMapData n ∪
      rankDeficientSevenVariableAffineMapData n = Finset.univ := by
  ext d
  simp only [Finset.mem_union, mem_rankSevenWeightSixteenInjectiveAffineMapData_iff,
    mem_rankDeficientSevenVariableAffineMapData_iff, Finset.mem_univ, iff_true]
  rw [sevenVariableAffinePoint_injective_iff]
  exact Classical.em _

private theorem disjoint_injective_rankDeficientSevenVariableAffineMapData :
    Disjoint (rankSevenWeightSixteenInjectiveAffineMapData n)
      (rankDeficientSevenVariableAffineMapData n) := by
  rw [Finset.disjoint_left]
  intro d hdInjective hdDeficient
  rw [mem_rankSevenWeightSixteenInjectiveAffineMapData_iff] at hdInjective
  rw [mem_rankDeficientSevenVariableAffineMapData_iff,
    sevenVariableAffinePoint_injective_iff] at hdDeficient
  exact hdDeficient hdInjective

private theorem realSignView_eq_one_or_neg_one
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    realSignView f x = 1 ∨ realSignView f x = -1 := by
  rcases FABL.signValue_eq_neg_one_or_one (FABL.signEncodedFunction f x) with h | h
  · right
    simpa [realSignView, FABL.realSignEncodedFunction] using h
  · left
    simpa [realSignView, FABL.realSignEncodedFunction] using h

private theorem prod_realSignView_comp_eq_one_or_neg_one
    {I : Type*} (f : BooleanFunction n) (s : Finset I)
    (g : I → FABL.F₂Cube n) :
    (∏ x ∈ s, realSignView f (g x)) = 1 ∨
      (∏ x ∈ s, realSignView f (g x)) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx]
      rcases realSignView_eq_one_or_neg_one f (g x) with hfx | hfx <;>
        rcases ih with hs | hs <;> simp [hfx, hs]

private theorem rankSevenWeightSixteenPatternAffineProduct_le_one
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d ≤ 1 := by
  unfold rankSevenWeightSixteenPatternAffineProduct
  rcases prod_realSignView_comp_eq_one_or_neg_one f
      (rankSevenWeightSixteenPattern c) (sevenVariableAffinePoint d) with h | h
  · rw [h]
  · rw [h]
    norm_num

/-- The sum over injective affine maps in one canonical pattern class loses
at most the number of rank-deficient affine-map data. -/
theorem rankSevenWeightSixteenInjectiveAffineMapCharacterSum_ge_neg_card_deficient
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass) :
    (∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
      rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) ≥
      -((rankDeficientSevenVariableAffineMapData n).card : ℝ) := by
  have hcomplete :
      0 ≤ rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
        (realSignView f) c :=
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_nonneg
      (realSignView f) c
  have hdeficient :
      (∑ d ∈ rankDeficientSevenVariableAffineMapData n,
        rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) ≤
          ((rankDeficientSevenVariableAffineMapData n).card : ℝ) := by
    calc
      (∑ d ∈ rankDeficientSevenVariableAffineMapData n,
          rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) ≤
          ∑ _d ∈ rankDeficientSevenVariableAffineMapData n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _hd
        exact rankSevenWeightSixteenPatternAffineProduct_le_one f c d
      _ = ((rankDeficientSevenVariableAffineMapData n).card : ℝ) := by simp
  have hsplit :
      rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
          (realSignView f) c =
        (∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
          rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) +
        ∑ d ∈ rankDeficientSevenVariableAffineMapData n,
          rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d := by
    unfold rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
    rw [← Finset.sum_union
      disjoint_injective_rankDeficientSevenVariableAffineMapData,
      injective_union_rankDeficientSevenVariableAffineMapData]
  rw [hsplit] at hcomplete
  linarith

/-- Dimension-free `127 q⁷` lower bound for injective affine-map
characters in each canonical rank-seven pattern class. -/
theorem rankSevenWeightSixteenInjectiveAffineMapCharacterSum_ge
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass) :
    (∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
      rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) ≥
      -(127 * (2 ^ n : ℝ) ^ 7) := by
  have hlower :=
    rankSevenWeightSixteenInjectiveAffineMapCharacterSum_ge_neg_card_deficient f c
  have hcardNat := card_rankDeficientSevenVariableAffineMapData_le n
  have hcardReal :
      ((rankDeficientSevenVariableAffineMapData n).card : ℝ) ≤
        127 * (2 ^ n : ℝ) ^ 7 := by
    exact_mod_cast hcardNat
  linarith

private theorem binarySign_sum_eq_prod
    {I : Type*}
    (s : Finset I) (g : I → FABL.𝔽₂) :
    FABL.binarySign (∑ x ∈ s, g x) =
      ∏ x ∈ s, FABL.binarySign (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx,
        AddChar.map_add_eq_mul, ih]

private theorem booleanFunctionPairing_eq_sum_support_finset
    (f h : BooleanFunction n) :
    booleanFunctionPairing n f h = ∑ x ∈ support h, f x := by
  rw [booleanFunctionPairing_apply]
  rw [support, FABL.f₂OneSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hhx : h x = 0
  · simp [hhx]
  · have hhxOne : h x = 1 := Fin.eq_one_of_ne_zero _ hhx
    simp [hhxOne]

private theorem realSignView_eq_binarySign
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    realSignView f x = FABL.binarySign (f x) := by
  rw [realSignView, FABL.realSignEncodedFunction, FABL.signEncodedFunction,
    FABL.signValue_signEncode_eq_binarySign]

/-- On injective affine maps, the canonical pattern product is exactly the
character of the corresponding distinct support word. -/
theorem rankSevenWeightSixteenPatternAffineProduct_realSignView
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d =
      FABL.binarySign (booleanFunctionPairing n f
        (rankSevenWeightSixteenPatternWord c d)) := by
  rw [booleanFunctionPairing_eq_sum_support_finset,
    support_rankSevenWeightSixteenPatternWord,
    binarySign_sum_eq_prod]
  unfold rankSevenWeightSixteenPatternAffineProduct
  unfold rankSevenWeightSixteenPatternImage
  rw [Finset.prod_image
    (sevenVariableAffinePoint_injective_iff d |>.2 hd).injOn]
  apply Finset.prod_congr rfl
  intro x _hx
  exact realSignView_eq_binarySign f (sevenVariableAffinePoint d x)

/-- The distinct support words in one canonical rank-seven affine orbit. -/
noncomputable def rankSevenWeightSixteenPatternOrbitWords
    (n : ℕ) (c : RankSevenWeightSixteenPatternClass) :
    Finset (BooleanFunction n) :=
  (rankSevenWeightSixteenInjectiveAffineMapData n).image
    (rankSevenWeightSixteenPatternWord c)

/-- The injective affine-map fiber over one support word. -/
noncomputable def rankSevenWeightSixteenPatternWordFiber
    (n : ℕ) (c : RankSevenWeightSixteenPatternClass)
    (h : BooleanFunction n) : Finset (SevenVariableAffineMapData n) :=
  (rankSevenWeightSixteenInjectiveAffineMapData n).filter fun d ↦
    rankSevenWeightSixteenPatternWord c d = h

theorem mem_rankSevenWeightSixteenPatternOrbitWords_iff
    (c : RankSevenWeightSixteenPatternClass) (h : BooleanFunction n) :
    h ∈ rankSevenWeightSixteenPatternOrbitWords n c ↔
      ∃ d : SevenVariableAffineMapData n,
        LinearIndependent FABL.𝔽₂ d.2 ∧
          rankSevenWeightSixteenPatternWord c d = h := by
  simp [rankSevenWeightSixteenPatternOrbitWords,
    mem_rankSevenWeightSixteenInjectiveAffineMapData_iff]

theorem mem_rankSevenWeightSixteenPatternWordFiber_iff
    (c : RankSevenWeightSixteenPatternClass) (h : BooleanFunction n)
    (d : SevenVariableAffineMapData n) :
    d ∈ rankSevenWeightSixteenPatternWordFiber n c h ↔
      LinearIndependent FABL.𝔽₂ d.2 ∧
        rankSevenWeightSixteenPatternWord c d = h := by
  simp [rankSevenWeightSixteenPatternWordFiber,
    mem_rankSevenWeightSixteenInjectiveAffineMapData_iff]

/-- Postcomposition of affine-map data by an affine automorphism of the
ambient binary cube. -/
def sevenVariableAffineMapDataPostcomposeEquiv
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) :
    SevenVariableAffineMapData n ≃ SevenVariableAffineMapData n where
  toFun d := (t + g d.1, fun i ↦ g (d.2 i))
  invFun d := (g.symm (t + d.1), fun i ↦ g.symm (d.2 i))
  left_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · change g.symm (t + (t + g u)) = u
      rw [← add_assoc, ZModModule.add_self, zero_add,
        LinearEquiv.symm_apply_apply]
    · funext i
      exact g.symm_apply_apply (v i)
  right_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · change t + g (g.symm (t + u)) = u
      rw [LinearEquiv.apply_symm_apply, ← add_assoc,
        ZModModule.add_self, zero_add]
    · funext i
      exact g.apply_symm_apply (v i)

private theorem sevenVariableAffinePoint_postcompose
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) (d : SevenVariableAffineMapData n)
    (x : FABL.F₂Cube 7) :
    sevenVariableAffinePoint (sevenVariableAffineMapDataPostcomposeEquiv g t d) x =
      t + g (sevenVariableAffinePoint d x) := by
  change (t + g d.1) + ∑ i, x i • g (d.2 i) =
    t + g (d.1 + ∑ i, x i • d.2 i)
  rw [map_add, map_sum]
  simp only [map_smul]
  abel

private theorem linearIndependent_postcompose_iff
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) (d : SevenVariableAffineMapData n) :
    LinearIndependent FABL.𝔽₂
        (sevenVariableAffineMapDataPostcomposeEquiv g t d).2 ↔
      LinearIndependent FABL.𝔽₂ d.2 := by
  change LinearIndependent FABL.𝔽₂ (fun i ↦ g (d.2 i)) ↔
    LinearIndependent FABL.𝔽₂ d.2
  constructor
  · intro h
    have hmapped := h.map' g.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr g.symm.injective)
    change LinearIndependent FABL.𝔽₂
      (fun i ↦ g.symm (g (d.2 i))) at hmapped
    simpa only [LinearEquiv.symm_apply_apply] using hmapped
  · intro h
    have hmapped :=
      h.map' g.toLinearMap (LinearMap.ker_eq_bot.mpr g.injective)
    change LinearIndependent FABL.𝔽₂ (fun i ↦ g (d.2 i)) at hmapped
    exact hmapped

private theorem rankSevenWeightSixteenPatternImage_postcompose
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternImage c
        (sevenVariableAffineMapDataPostcomposeEquiv g t d) =
      (rankSevenWeightSixteenPatternImage c d).image (fun x ↦ t + g x) := by
  unfold rankSevenWeightSixteenPatternImage
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _hx
  exact sevenVariableAffinePoint_postcompose g t d x

private theorem rankSevenWeightSixteenPatternWord_eq_iff_image_eq
    (c : RankSevenWeightSixteenPatternClass)
    (d e : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternWord c d =
        rankSevenWeightSixteenPatternWord c e ↔
      rankSevenWeightSixteenPatternImage c d =
        rankSevenWeightSixteenPatternImage c e := by
  constructor
  · intro h
    have hs := congrArg support h
    simpa only [support_rankSevenWeightSixteenPatternWord] using hs
  · intro h
    funext x
    simp only [rankSevenWeightSixteenPatternWord, h]

private theorem rankSevenWeightSixteenPatternWord_postcompose_eq_iff
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) (c : RankSevenWeightSixteenPatternClass)
    (d e : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternWord c
        (sevenVariableAffineMapDataPostcomposeEquiv g t d) =
        rankSevenWeightSixteenPatternWord c
          (sevenVariableAffineMapDataPostcomposeEquiv g t e) ↔
      rankSevenWeightSixteenPatternWord c d =
        rankSevenWeightSixteenPatternWord c e := by
  simp only [rankSevenWeightSixteenPatternWord_eq_iff_image_eq,
    rankSevenWeightSixteenPatternImage_postcompose]
  exact Finset.image_inj (fun x y hxy ↦ g.injective (add_left_cancel hxy))

private noncomputable def sevenDirectionSpanLinearEquiv
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) :
    Submodule.span FABL.𝔽₂ (Set.range d.2) ≃ₗ[FABL.𝔽₂]
      Submodule.span FABL.𝔽₂ (Set.range e.2) :=
  hd.linearCombinationEquiv.symm.trans he.linearCombinationEquiv

private theorem sevenDirectionSpanLinearEquiv_apply
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) (i : Fin 7) :
    (sevenDirectionSpanLinearEquiv d e hd he
      ⟨d.2 i, Submodule.subset_span (Set.mem_range_self i)⟩ : FABL.F₂Cube n) =
        e.2 i := by
  have hrepr : hd.repr
      ⟨d.2 i, Submodule.subset_span (Set.mem_range_self i)⟩ =
        Finsupp.single i 1 :=
    hd.repr_eq_single i _ rfl
  change (he.linearCombinationEquiv
      (hd.repr
        ⟨d.2 i, Submodule.subset_span (Set.mem_range_self i)⟩) :
      FABL.F₂Cube n) = e.2 i
  rw [hrepr]
  simp

private noncomputable def rankSevenAmbientLinearEquiv
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) :
    FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
  Classical.choose
    (Submodule.exists_linearEquiv_restrict_eq
      (sevenDirectionSpanLinearEquiv d e hd he))

private theorem rankSevenAmbientLinearEquiv_apply_direction
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) (i : Fin 7) :
    rankSevenAmbientLinearEquiv d e hd he (d.2 i) = e.2 i := by
  let hrestrict := Classical.choose_spec
    (Submodule.exists_linearEquiv_restrict_eq
      (sevenDirectionSpanLinearEquiv d e hd he))
  have hi := hrestrict
    ⟨d.2 i, Submodule.subset_span (Set.mem_range_self i)⟩
  change sevenDirectionSpanLinearEquiv d e hd he
      ⟨d.2 i, Submodule.subset_span (Set.mem_range_self i)⟩ =
    rankSevenAmbientLinearEquiv d e hd he (d.2 i) at hi
  rw [← hi]
  exact sevenDirectionSpanLinearEquiv_apply d e hd he i

private noncomputable def rankSevenAffineDataTransportEquiv
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) :
    SevenVariableAffineMapData n ≃ SevenVariableAffineMapData n :=
  let g := rankSevenAmbientLinearEquiv d e hd he
  sevenVariableAffineMapDataPostcomposeEquiv g (e.1 + g d.1)

private theorem rankSevenAffineDataTransportEquiv_apply
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) :
    rankSevenAffineDataTransportEquiv d e hd he d = e := by
  apply Prod.ext
  · change (e.1 + rankSevenAmbientLinearEquiv d e hd he d.1) +
      rankSevenAmbientLinearEquiv d e hd he d.1 = e.1
    rw [add_assoc, ZModModule.add_self, add_zero]
  · funext i
    exact rankSevenAmbientLinearEquiv_apply_direction d e hd he i

private theorem image_patternWordFiber_postcompose
    (g : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n)
    (t : FABL.F₂Cube n) (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) :
    (rankSevenWeightSixteenPatternWordFiber n c
        (rankSevenWeightSixteenPatternWord c d)).image
          (sevenVariableAffineMapDataPostcomposeEquiv g t) =
      rankSevenWeightSixteenPatternWordFiber n c
        (rankSevenWeightSixteenPatternWord c
          (sevenVariableAffineMapDataPostcomposeEquiv g t d)) := by
  ext q
  constructor
  · rw [Finset.mem_image]
    rintro ⟨p, hp, rfl⟩
    rw [mem_rankSevenWeightSixteenPatternWordFiber_iff] at hp ⊢
    exact ⟨(linearIndependent_postcompose_iff g t p).2 hp.1,
      (rankSevenWeightSixteenPatternWord_postcompose_eq_iff g t c p d).2 hp.2⟩
  · intro hq
    rw [mem_rankSevenWeightSixteenPatternWordFiber_iff] at hq
    let E := sevenVariableAffineMapDataPostcomposeEquiv g t
    let p := E.symm q
    have hEp : E p = q := E.apply_symm_apply q
    have hpIndependent : LinearIndependent FABL.𝔽₂ p.2 := by
      apply (linearIndependent_postcompose_iff g t p).1
      rw [hEp]
      exact hq.1
    have hpWord : rankSevenWeightSixteenPatternWord c p =
        rankSevenWeightSixteenPatternWord c d := by
      apply (rankSevenWeightSixteenPatternWord_postcompose_eq_iff g t c p d).1
      rw [hEp]
      exact hq.2
    rw [Finset.mem_image]
    exact ⟨p,
      (mem_rankSevenWeightSixteenPatternWordFiber_iff c _ p).2
        ⟨hpIndependent, hpWord⟩,
      hEp⟩

private theorem card_patternWordFiber_eq_of_representatives
    (c : RankSevenWeightSixteenPatternClass)
    (d e : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (he : LinearIndependent FABL.𝔽₂ e.2) :
    (rankSevenWeightSixteenPatternWordFiber n c
        (rankSevenWeightSixteenPatternWord c d)).card =
      (rankSevenWeightSixteenPatternWordFiber n c
        (rankSevenWeightSixteenPatternWord c e)).card := by
  let g := rankSevenAmbientLinearEquiv d e hd he
  let t := e.1 + g d.1
  let E := sevenVariableAffineMapDataPostcomposeEquiv g t
  have hEd : E d = e := by
    simpa only [g, t, E, rankSevenAffineDataTransportEquiv] using
      rankSevenAffineDataTransportEquiv_apply d e hd he
  have himage := image_patternWordFiber_postcompose g t c d
  rw [hEd] at himage
  rw [← himage, Finset.card_image_of_injective _ E.injective]

/-- All words in one canonical pattern orbit have the same number of
injective affine-map representatives. -/
theorem card_rankSevenWeightSixteenPatternWordFiber_eq_of_mem_orbit
    (c : RankSevenWeightSixteenPatternClass)
    {h k : BooleanFunction n}
    (hh : h ∈ rankSevenWeightSixteenPatternOrbitWords n c)
    (hk : k ∈ rankSevenWeightSixteenPatternOrbitWords n c) :
    (rankSevenWeightSixteenPatternWordFiber n c h).card =
      (rankSevenWeightSixteenPatternWordFiber n c k).card := by
  rw [mem_rankSevenWeightSixteenPatternOrbitWords_iff] at hh hk
  obtain ⟨d, hd, rfl⟩ := hh
  obtain ⟨e, he, rfl⟩ := hk
  exact card_patternWordFiber_eq_of_representatives c d e hd he

/-- Every word in a canonical pattern orbit has at least one injective
affine-map representative. -/
theorem card_rankSevenWeightSixteenPatternWordFiber_pos
    (c : RankSevenWeightSixteenPatternClass)
    {h : BooleanFunction n}
    (hh : h ∈ rankSevenWeightSixteenPatternOrbitWords n c) :
    0 < (rankSevenWeightSixteenPatternWordFiber n c h).card := by
  rw [mem_rankSevenWeightSixteenPatternOrbitWords_iff] at hh
  obtain ⟨d, hd, hword⟩ := hh
  apply Finset.card_pos.mpr
  refine ⟨d, ?_⟩
  exact (mem_rankSevenWeightSixteenPatternWordFiber_iff c h d).2
    ⟨hd, hword⟩

/-- Character sum over the distinct words in one canonical rank-seven
pattern orbit. -/
noncomputable def rankSevenWeightSixteenPatternOrbitCharacterSum
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass) : ℝ :=
  ∑ h ∈ rankSevenWeightSixteenPatternOrbitWords n c,
    FABL.binarySign (booleanFunctionPairing n f h)

private theorem injectiveAffineMapCharacterSum_eq_fiber_mul_orbitCharacterSum
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass)
    {h₀ : BooleanFunction n}
    (hh₀ : h₀ ∈ rankSevenWeightSixteenPatternOrbitWords n c) :
    (∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
      rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) =
      ((rankSevenWeightSixteenPatternWordFiber n c h₀).card : ℝ) *
        rankSevenWeightSixteenPatternOrbitCharacterSum f c := by
  calc
    (∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
        rankSevenWeightSixteenPatternAffineProduct (realSignView f) c d) =
        ∑ d ∈ rankSevenWeightSixteenInjectiveAffineMapData n,
          FABL.binarySign (booleanFunctionPairing n f
            (rankSevenWeightSixteenPatternWord c d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [rankSevenWeightSixteenPatternAffineProduct_realSignView f c d
        ((mem_rankSevenWeightSixteenInjectiveAffineMapData_iff d).1 hd)]
    _ = ∑ h ∈ rankSevenWeightSixteenPatternOrbitWords n c,
          ∑ d ∈ rankSevenWeightSixteenPatternWordFiber n c h,
            FABL.binarySign (booleanFunctionPairing n f
              (rankSevenWeightSixteenPatternWord c d)) := by
      symm
      unfold rankSevenWeightSixteenPatternWordFiber
      apply Finset.sum_fiberwise_of_maps_to
      intro d hd
      exact Finset.mem_image_of_mem _ hd
    _ = ∑ h ∈ rankSevenWeightSixteenPatternOrbitWords n c,
          ((rankSevenWeightSixteenPatternWordFiber n c h).card : ℝ) *
            FABL.binarySign (booleanFunctionPairing n f h) := by
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        (∑ d ∈ rankSevenWeightSixteenPatternWordFiber n c h,
            FABL.binarySign (booleanFunctionPairing n f
              (rankSevenWeightSixteenPatternWord c d))) =
            ∑ _d ∈ rankSevenWeightSixteenPatternWordFiber n c h,
              FABL.binarySign (booleanFunctionPairing n f h) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [(mem_rankSevenWeightSixteenPatternWordFiber_iff c h d).1 hd |>.2]
        _ = ((rankSevenWeightSixteenPatternWordFiber n c h).card : ℝ) *
            FABL.binarySign (booleanFunctionPairing n f h) := by simp
    _ = ((rankSevenWeightSixteenPatternWordFiber n c h₀).card : ℝ) *
        rankSevenWeightSixteenPatternOrbitCharacterSum f c := by
      unfold rankSevenWeightSixteenPatternOrbitCharacterSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro h hh
      rw [card_rankSevenWeightSixteenPatternWordFiber_eq_of_mem_orbit c hh hh₀]

/-- Each distinct canonical rank-seven word orbit inherits the same
`-127 q⁷` lower bound as its injective affine-map sum; the unknown positive
automorphism multiplicity need not be computed. -/
theorem rankSevenWeightSixteenPatternOrbitCharacterSum_ge
    (f : BooleanFunction n) (c : RankSevenWeightSixteenPatternClass) :
    rankSevenWeightSixteenPatternOrbitCharacterSum f c ≥
      -(127 * (2 ^ n : ℝ) ^ 7) := by
  by_cases hempty : rankSevenWeightSixteenPatternOrbitWords n c = ∅
  · have hbound : 0 ≤ 127 * (2 ^ n : ℝ) ^ 7 := by positivity
    unfold rankSevenWeightSixteenPatternOrbitCharacterSum
    rw [hempty]
    simp only [Finset.sum_empty]
    exact neg_nonpos.mpr hbound
  · obtain ⟨h₀, hh₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let m : ℝ :=
      (rankSevenWeightSixteenPatternWordFiber n c h₀).card
    let S : ℝ := rankSevenWeightSixteenPatternOrbitCharacterSum f c
    have hmNat : 1 ≤
        (rankSevenWeightSixteenPatternWordFiber n c h₀).card :=
      (Nat.succ_le_iff).2
        (card_rankSevenWeightSixteenPatternWordFiber_pos c hh₀)
    have hm : 1 ≤ m := by
      dsimp only [m]
      exact_mod_cast hmNat
    have hdata := rankSevenWeightSixteenInjectiveAffineMapCharacterSum_ge f c
    have heq := injectiveAffineMapCharacterSum_eq_fiber_mul_orbitCharacterSum
      f c hh₀
    change _ = m * S at heq
    rw [heq] at hdata
    by_cases hS : 0 ≤ S
    · have hneg : -(127 * (2 ^ n : ℝ) ^ 7) ≤ 0 :=
        neg_nonpos.mpr (by positivity)
      exact hneg.trans hS
    · have hnonneg : 0 ≤ (m - 1) * (-S) :=
        mul_nonneg (sub_nonneg.mpr hm) (neg_nonneg.mpr (le_of_not_ge hS))
      change S ≥ -(127 * (2 ^ n : ℝ) ^ 7)
      nlinarith

/-- A weight-sixteen word has support-affine-span rank seven when one
support point exhibits a seven-dimensional difference span. -/
def HasSupportAffineSpanRankSeven (h : BooleanFunction n) : Prop :=
  ∃ p : FABL.F₂Cube n, p ∈ support h ∧
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) = 7

/-- Every injective canonical pattern image has support-affine-span rank
seven. -/
theorem hasSupportAffineSpanRankSeven_rankSevenWeightSixteenPatternWord
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2) :
    HasSupportAffineSpanRankSeven
      (rankSevenWeightSixteenPatternWord c d) := by
  refine ⟨d.1, ?_,
    finrank_supportDifferenceSpan_rankSevenWeightSixteenPatternWord c d hd⟩
  rw [support_rankSevenWeightSixteenPatternWord]
  unfold rankSevenWeightSixteenPatternImage
  exact Finset.mem_image.2 ⟨0, zero_mem_rankSevenWeightSixteenPattern c, by
    simp [sevenVariableAffinePoint]⟩

/-- The rank-seven part of the weight-sixteen dual spectrum. -/
noncomputable def orderTwoWeightSixteenRankSevenDualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoWeightSixteenDualWords n).filter
    HasSupportAffineSpanRankSeven

/-- The complementary, rank-at-most-six part of the weight-sixteen dual
spectrum.  The rank bound is proved below from the codimension-three
condition. -/
noncomputable def orderTwoWeightSixteenRankAtMostSixResidualWords (n : ℕ) :
    Finset (BooleanFunction n) := by
  classical
  exact (orderTwoWeightSixteenDualWords n).filter fun h ↦
    ¬HasSupportAffineSpanRankSeven h

@[simp] theorem mem_orderTwoWeightSixteenRankSevenDualWords_iff
    (h : BooleanFunction n) :
    h ∈ orderTwoWeightSixteenRankSevenDualWords n ↔
      h ∈ orderTwoWeightSixteenDualWords n ∧
        HasSupportAffineSpanRankSeven h := by
  simp [orderTwoWeightSixteenRankSevenDualWords]

@[simp] theorem mem_orderTwoWeightSixteenRankAtMostSixResidualWords_iff
    (h : BooleanFunction n) :
    h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n ↔
      h ∈ orderTwoWeightSixteenDualWords n ∧
        ¬HasSupportAffineSpanRankSeven h := by
  simp [orderTwoWeightSixteenRankAtMostSixResidualWords]

/-- Every residual word really has support-affine-span rank at most six at
each support point. -/
theorem finrank_supportDifferenceSpan_le_six_of_mem_weightSixteenResidual
    (hn : 3 ≤ n) {h : BooleanFunction n}
    (hh : h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n)
    (p : FABL.F₂Cube n) (hp : p ∈ support h) :
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤ 6 := by
  have hhData :=
    (mem_orderTwoWeightSixteenRankAtMostSixResidualWords_iff h).1 hh
  have hdualData : h ∈ reedMuller (n - 3) n ∧
      hammingWeight h = 16 := by
    simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hhData.1
  have hle := finrank_supportDifferenceSpan_le_seven_of_weight_sixteen
    h p hp hn hdualData.1 hdualData.2
  have hne : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≠ 7 := by
    intro heq
    exact hhData.2 ⟨p, hp, heq⟩
  omega

/-- The union of the three canonical rank-seven affine word orbits. -/
noncomputable def rankSevenWeightSixteenPatternOrbitUnion (n : ℕ) :
    Finset (BooleanFunction n) :=
  (Finset.univ : Finset RankSevenWeightSixteenPatternClass).biUnion
    (rankSevenWeightSixteenPatternOrbitWords n)

/-- Explicit classification interface: the rank-seven dual words are exactly
the union of the three canonical orbits, and those orbits are pairwise
disjoint.  This is an ordinary proposition, not a primitive assumption or typeclass. -/
def HasRankSevenWeightSixteenOrbitClassification (n : ℕ) : Prop :=
  (∀ h : BooleanFunction n,
      h ∈ orderTwoWeightSixteenRankSevenDualWords n ↔
        ∃ c : RankSevenWeightSixteenPatternClass,
          h ∈ rankSevenWeightSixteenPatternOrbitWords n c) ∧
    Set.PairwiseDisjoint
      (↑(Finset.univ : Finset RankSevenWeightSixteenPatternClass))
      (rankSevenWeightSixteenPatternOrbitWords n)

/-- The raw certificate-producing classifier supplies the covering half of
the rank-seven orbit classification. -/
theorem mem_rankSevenWeightSixteenPatternOrbitUnion_of_certificate
    (hcertificate : ∀ h : BooleanFunction n,
      h ∈ orderTwoWeightSixteenDualWords n →
      HasSupportAffineSpanRankSeven h →
      RankSevenWeightSixteenPatternCertificate h)
    {h : BooleanFunction n}
    (hh : h ∈ orderTwoWeightSixteenRankSevenDualWords n) :
    h ∈ rankSevenWeightSixteenPatternOrbitUnion n := by
  have hhData := (mem_orderTwoWeightSixteenRankSevenDualWords_iff h).1 hh
  let certificate := hcertificate h hhData.1 hhData.2
  rw [rankSevenWeightSixteenPatternOrbitUnion, Finset.mem_biUnion]
  refine ⟨certificate.patternClass, Finset.mem_univ _, ?_⟩
  exact (mem_rankSevenWeightSixteenPatternOrbitWords_iff
    certificate.patternClass h).2
      ⟨certificate.affineData, certificate.independent,
        certificate.word_eq.symm⟩

/-- Every word in an injective canonical pattern orbit is a genuine
rank-seven weight-sixteen dual word. -/
theorem mem_orderTwoWeightSixteenRankSevenDualWords_of_mem_patternOrbitWords
    (c : RankSevenWeightSixteenPatternClass)
    {h : BooleanFunction n}
    (hh : h ∈ rankSevenWeightSixteenPatternOrbitWords n c) :
    h ∈ orderTwoWeightSixteenRankSevenDualWords n := by
  rw [mem_rankSevenWeightSixteenPatternOrbitWords_iff] at hh
  obtain ⟨d, hd, rfl⟩ := hh
  rw [mem_orderTwoWeightSixteenRankSevenDualWords_iff]
  exact ⟨
    rankSevenWeightSixteenPatternWord_mem_orderTwoWeightSixteenDualWords c d hd,
    hasSupportAffineSpanRankSeven_rankSevenWeightSixteenPatternWord c d hd⟩

/-- A certificate classifier and orbit disjointness combine
to discharge the complete rank-seven classification interface. -/
theorem hasRankSevenWeightSixteenOrbitClassification_of_certificate_and_disjointness
    (hcertificate : ∀ h : BooleanFunction n,
      h ∈ orderTwoWeightSixteenDualWords n →
      HasSupportAffineSpanRankSeven h →
      RankSevenWeightSixteenPatternCertificate h)
    (hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset RankSevenWeightSixteenPatternClass))
      (rankSevenWeightSixteenPatternOrbitWords n)) :
    HasRankSevenWeightSixteenOrbitClassification n := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, hdisjoint⟩
  · intro hh
    have hunion :=
      mem_rankSevenWeightSixteenPatternOrbitUnion_of_certificate
        hcertificate hh
    rw [rankSevenWeightSixteenPatternOrbitUnion,
      Finset.mem_biUnion] at hunion
    obtain ⟨c, _hc, hhOrbit⟩ := hunion
    exact ⟨c, hhOrbit⟩
  · rintro ⟨c, hhOrbit⟩
    exact
      mem_orderTwoWeightSixteenRankSevenDualWords_of_mem_patternOrbitWords
        c hhOrbit

/-- The Boolean word whose support is the image of an arbitrary mask under a
seven-variable affine map. -/
def sevenVariableAffineMaskWord
    (d : SevenVariableAffineMapData n)
    (m : Finset (FABL.F₂Cube 7)) : BooleanFunction n :=
  fun x ↦ if x ∈ m.image (sevenVariableAffinePoint d) then 1 else 0

@[simp] theorem support_sevenVariableAffineMaskWord
    (d : SevenVariableAffineMapData n)
    (m : Finset (FABL.F₂Cube 7)) :
    support (sevenVariableAffineMaskWord d m) =
      m.image (sevenVariableAffinePoint d) := by
  ext x
  simp [support, FABL.f₂OneSupport, sevenVariableAffineMaskWord]

/-- Rank-deficient affine maps paired with all `2^128` masks on the
seven-variable Boolean cube. -/
noncomputable def rankDeficientSevenVariableAffineMaskData (n : ℕ) :
    Finset (SevenVariableAffineMapData n × Finset (FABL.F₂Cube 7)) :=
  (rankDeficientSevenVariableAffineMapData n).product
    ((Finset.univ : Finset (FABL.F₂Cube 7)).powerset)

/-- Every word produced by rank-deficient affine data and an arbitrary
seven-variable mask. -/
noncomputable def rankDeficientSevenVariableAffineMaskImageWords (n : ℕ) :
    Finset (BooleanFunction n) :=
  (rankDeficientSevenVariableAffineMaskData n).image fun dm ↦
    sevenVariableAffineMaskWord dm.1 dm.2

/-- There are exactly `2^128` masks on the seven-variable Boolean cube. -/
theorem card_sevenVariableAffineMasks :
    ((Finset.univ : Finset (FABL.F₂Cube 7)).powerset).card = 2 ^ 128 := by
  rw [Finset.card_powerset, Finset.card_univ, FABL.card_f₂Cube]
  norm_num

/-- Arbitrary-mask images of rank-deficient affine maps contribute at most
`127 · 2^128 · q⁷` distinct words. -/
theorem card_rankDeficientSevenVariableAffineMaskImageWords_le (n : ℕ) :
    (rankDeficientSevenVariableAffineMaskImageWords n).card ≤
      127 * 2 ^ 128 * (2 ^ n) ^ 7 := by
  calc
    (rankDeficientSevenVariableAffineMaskImageWords n).card ≤
        (rankDeficientSevenVariableAffineMaskData n).card :=
      Finset.card_image_le
    _ = (rankDeficientSevenVariableAffineMapData n).card * 2 ^ 128 := by
      unfold rankDeficientSevenVariableAffineMaskData
      calc
        ((rankDeficientSevenVariableAffineMapData n).product
            ((Finset.univ : Finset (FABL.F₂Cube 7)).powerset)).card =
            (rankDeficientSevenVariableAffineMapData n).card *
              ((Finset.univ : Finset (FABL.F₂Cube 7)).powerset).card :=
          Finset.card_product _ _
        _ = (rankDeficientSevenVariableAffineMapData n).card * 2 ^ 128 := by
          rw [card_sevenVariableAffineMasks]
    _ ≤ (127 * (2 ^ n) ^ 7) * 2 ^ 128 :=
      Nat.mul_le_mul_right (2 ^ 128)
        (card_rankDeficientSevenVariableAffineMapData_le n)
    _ = 127 * 2 ^ 128 * (2 ^ n) ^ 7 := by ring

/-- Minimal low-rank covering interface: every residual word is an arbitrary
mask image of one rank-deficient seven-variable affine map. -/
def HasRankAtMostSixWeightSixteenDeficientAffineMaskCover (n : ℕ) : Prop :=
  ∀ h : BooleanFunction n,
    h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n →
      ∃ (d : SevenVariableAffineMapData n)
        (m : Finset (FABL.F₂Cube 7)),
        d ∈ rankDeficientSevenVariableAffineMapData n ∧
          sevenVariableAffineMaskWord d m = h

private noncomputable def supportDifferenceSpanPaddedBasis
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hle : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7) :
    Fin 7 → supportDifferenceSpan h p :=
  Function.extend (Fin.castLE hle)
    (Module.finBasis FABL.𝔽₂ (supportDifferenceSpan h p))
    (fun _ ↦ 0)

private theorem supportDifferenceSpanPaddedBasis_apply
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hle : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7)
    (i : Fin (Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p))) :
    supportDifferenceSpanPaddedBasis h p hle (Fin.castLE hle i) =
      Module.finBasis FABL.𝔽₂ (supportDifferenceSpan h p) i := by
  unfold supportDifferenceSpanPaddedBasis
  exact (Fin.castLE_injective hle).extend_apply
    (Module.finBasis FABL.𝔽₂ (supportDifferenceSpan h p)) (fun _ ↦ 0) i

private theorem span_range_supportDifferenceSpanPaddedBasis_eq_top
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hle : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7) :
    Submodule.span FABL.𝔽₂
        (Set.range (supportDifferenceSpanPaddedBasis h p hle)) = ⊤ := by
  apply top_unique
  rw [← (Module.finBasis FABL.𝔽₂
    (supportDifferenceSpan h p)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castLE hle i,
    supportDifferenceSpanPaddedBasis_apply h p hle i⟩

private noncomputable def supportDifferenceSpanSevenVariableAffineMapData
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hle : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7) :
    SevenVariableAffineMapData n :=
  (p, fun i ↦ (supportDifferenceSpanPaddedBasis h p hle i :
    FABL.F₂Cube n))

private theorem supportDifferenceSpanSevenVariableAffineMapData_mem_deficient
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hleSix : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 6)
    (hleSeven : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7) :
    supportDifferenceSpanSevenVariableAffineMapData h p hleSeven ∈
      rankDeficientSevenVariableAffineMapData n := by
  rw [mem_rankDeficientSevenVariableAffineMapData_iff,
    sevenVariableAffinePoint_injective_iff]
  intro hindependent
  have hindependentSubtype : LinearIndependent FABL.𝔽₂
      (supportDifferenceSpanPaddedBasis h p hleSeven) := by
    apply LinearIndependent.of_comp
      (supportDifferenceSpan h p).subtype
    change LinearIndependent FABL.𝔽₂ (fun i ↦
      (supportDifferenceSpanPaddedBasis h p hleSeven i :
        FABL.F₂Cube n))
    simpa only [supportDifferenceSpanSevenVariableAffineMapData] using hindependent
  have hcard :=
    (linearIndependent_iff_card_le_finrank_span).1 hindependentSubtype
  rw [Set.finrank,
    span_range_supportDifferenceSpanPaddedBasis_eq_top h p hleSeven,
    finrank_top] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

private theorem supportDifferenceSpanSevenVariableAffinePoint_surjective_on
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hle : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7)
    {x : FABL.F₂Cube n}
    (hx : x ∈ FABL.binaryAffineSubspace
      (supportDifferenceSpan h p) p) :
    ∃ z : FABL.F₂Cube 7,
      sevenVariableAffinePoint
        (supportDifferenceSpanSevenVariableAffineMapData h p hle) z = x := by
  have hxSpan : x + p ∈ supportDifferenceSpan h p :=
    (FABL.mem_binaryAffineSubspace_iff_add_mem
      (supportDifferenceSpan h p) p x).1 hx
  have hsurjective : Function.Surjective
      (Fintype.linearCombination FABL.𝔽₂
        (supportDifferenceSpanPaddedBasis h p hle)) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination FABL.𝔽₂
      (supportDifferenceSpanPaddedBasis h p hle)).1
      (span_range_supportDifferenceSpanPaddedBasis_eq_top h p hle)
  obtain ⟨z, hz⟩ := hsurjective ⟨x + p, hxSpan⟩
  refine ⟨z, ?_⟩
  have hzValue := congrArg Subtype.val hz
  simp only [Fintype.linearCombination_apply, Submodule.coe_sum,
    Submodule.coe_smul] at hzValue
  change p + ∑ i : Fin 7,
    z i • (supportDifferenceSpanPaddedBasis h p hle i :
      FABL.F₂Cube n) = x
  rw [hzValue]
  calc
    p + (x + p) = x + (p + p) := by abel
    _ = x := by rw [ZModModule.add_self, add_zero]

/-- The mask consisting exactly of the preimages of a Boolean support. -/
noncomputable def sevenVariableAffineSupportPreimageMask
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n) :
    Finset (FABL.F₂Cube 7) :=
  Finset.univ.filter fun z ↦ sevenVariableAffinePoint d z ∈ support h

private theorem image_sevenVariableAffineSupportPreimageMask_eq_support
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hsurjective : ∀ x ∈ support h, ∃ z : FABL.F₂Cube 7,
      sevenVariableAffinePoint d z = x) :
    (sevenVariableAffineSupportPreimageMask h d).image
        (sevenVariableAffinePoint d) = support h := by
  ext x
  constructor
  · rw [Finset.mem_image]
    rintro ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.1 hz).2
  · intro hx
    obtain ⟨z, hz⟩ := hsurjective x hx
    rw [Finset.mem_image]
    exact ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz ▸ hx⟩, hz⟩

private theorem sevenVariableAffineMaskWord_supportPreimage_eq
    (h : BooleanFunction n) (d : SevenVariableAffineMapData n)
    (hsurjective : ∀ x ∈ support h, ∃ z : FABL.F₂Cube 7,
      sevenVariableAffinePoint d z = x) :
    sevenVariableAffineMaskWord d
      (sevenVariableAffineSupportPreimageMask h d) = h := by
  have himage := image_sevenVariableAffineSupportPreimageMask_eq_support
    h d hsurjective
  funext x
  rw [sevenVariableAffineMaskWord, himage]
  by_cases hx : h x = 0
  · simp [support, FABL.f₂OneSupport, hx]
  · have hxOne : h x = 1 := Fin.eq_one_of_ne_zero _ hx
    simp [support, FABL.f₂OneSupport, hxOne]

/-- Every rank-at-most-six residual word has an arbitrary-mask
rank-deficient affine representation. -/
theorem hasRankAtMostSixWeightSixteenDeficientAffineMaskCover
    (hn : 3 ≤ n) :
    HasRankAtMostSixWeightSixteenDeficientAffineMaskCover n := by
  intro h hh
  have hhData :=
    (mem_orderTwoWeightSixteenRankAtMostSixResidualWords_iff h).1 hh
  have hdualData : h ∈ reedMuller (n - 3) n ∧
      hammingWeight h = 16 := by
    simpa only [orderTwoWeightSixteenDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hhData.1
  have hsupportCard : (support h).card = 16 := by
    simpa only [hammingWeight_eq_card_support] using hdualData.2
  obtain ⟨p, hp⟩ : (support h).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hleSix :=
    finrank_supportDifferenceSpan_le_six_of_mem_weightSixteenResidual
      hn hh p hp
  have hleSeven : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) ≤ 7 := hleSix.trans (by norm_num)
  let d := supportDifferenceSpanSevenVariableAffineMapData h p hleSeven
  let m := sevenVariableAffineSupportPreimageMask h d
  refine ⟨d, m, ?_, ?_⟩
  · exact supportDifferenceSpanSevenVariableAffineMapData_mem_deficient
      h p hleSix hleSeven
  · apply sevenVariableAffineMaskWord_supportPreimage_eq
    intro x hx
    apply supportDifferenceSpanSevenVariableAffinePoint_surjective_on
      h p hleSeven
    exact support_subset_binaryAffineSubspace_supportDifferenceSpan h p hx

theorem orderTwoWeightSixteenRankAtMostSixResidualWords_subset_affineMaskImage_of_cover
    (hcover : HasRankAtMostSixWeightSixteenDeficientAffineMaskCover n) :
    orderTwoWeightSixteenRankAtMostSixResidualWords n ⊆
      rankDeficientSevenVariableAffineMaskImageWords n := by
  intro h hh
  obtain ⟨d, m, hd, hword⟩ := hcover h hh
  rw [rankDeficientSevenVariableAffineMaskImageWords, Finset.mem_image]
  refine ⟨(d, m), ?_, hword⟩
  simp [rankDeficientSevenVariableAffineMaskData, hd]

/-- The residual word set inherits the `127 · 2^128 · q⁷` cardinality
bound from an arbitrary-mask rank-deficient affine cover. -/
theorem card_orderTwoWeightSixteenRankAtMostSixResidualWords_le_of_cover
    (hcover : HasRankAtMostSixWeightSixteenDeficientAffineMaskCover n) :
    (orderTwoWeightSixteenRankAtMostSixResidualWords n).card ≤
      127 * 2 ^ 128 * (2 ^ n) ^ 7 :=
  (Finset.card_le_card
    (orderTwoWeightSixteenRankAtMostSixResidualWords_subset_affineMaskImage_of_cover
      hcover)).trans
    (card_rankDeficientSevenVariableAffineMaskImageWords_le n)

/-- Unconditional low-rank residual count obtained from support-affine-span
parameterization. -/
theorem card_orderTwoWeightSixteenRankAtMostSixResidualWords_le
    (hn : 3 ≤ n) :
    (orderTwoWeightSixteenRankAtMostSixResidualWords n).card ≤
      127 * 2 ^ 128 * (2 ^ n) ^ 7 :=
  card_orderTwoWeightSixteenRankAtMostSixResidualWords_le_of_cover
    (hasRankAtMostSixWeightSixteenDeficientAffineMaskCover hn)

/-- Character sum over the rank-seven part of the weight-sixteen spectrum. -/
noncomputable def orderTwoWeightSixteenRankSevenCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightSixteenRankSevenDualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

/-- Character sum over the complementary rank-at-most-six residual words. -/
noncomputable def orderTwoWeightSixteenRankAtMostSixResidualCharacterSum
    (f : BooleanFunction n) : ℝ :=
  ∑ h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n,
    FABL.binarySign (booleanFunctionPairing n f h)

/-- The rank-seven/residual split is an exact partition of the weight-sixteen
dual character sum. -/
theorem orderTwoWeightSixteenCharacterSum_eq_rankSeven_add_residual
    (f : BooleanFunction n) :
    orderTwoWeightSixteenCharacterSum f =
      orderTwoWeightSixteenRankSevenCharacterSum f +
        orderTwoWeightSixteenRankAtMostSixResidualCharacterSum f := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (orderTwoWeightSixteenDualWords n)
    HasSupportAffineSpanRankSeven
    (fun h ↦ FABL.binarySign (booleanFunctionPairing n f h))
  simpa only [orderTwoWeightSixteenCharacterSum,
    orderTwoWeightSixteenRankSevenCharacterSum,
    orderTwoWeightSixteenRankAtMostSixResidualCharacterSum,
    orderTwoWeightSixteenRankSevenDualWords,
    orderTwoWeightSixteenRankAtMostSixResidualWords] using hsplit.symm

private theorem orderTwoWeightSixteenRankSevenDualWords_eq_orbitUnion
    (hclassification : HasRankSevenWeightSixteenOrbitClassification n) :
    orderTwoWeightSixteenRankSevenDualWords n =
      rankSevenWeightSixteenPatternOrbitUnion n := by
  ext h
  rw [hclassification.1 h]
  simp [rankSevenWeightSixteenPatternOrbitUnion]

private theorem orderTwoWeightSixteenRankSevenCharacterSum_eq_sum_orbits
    (f : BooleanFunction n)
    (hclassification : HasRankSevenWeightSixteenOrbitClassification n) :
    orderTwoWeightSixteenRankSevenCharacterSum f =
      ∑ c : RankSevenWeightSixteenPatternClass,
        rankSevenWeightSixteenPatternOrbitCharacterSum f c := by
  unfold orderTwoWeightSixteenRankSevenCharacterSum
  rw [orderTwoWeightSixteenRankSevenDualWords_eq_orbitUnion
    hclassification]
  unfold rankSevenWeightSixteenPatternOrbitUnion
  rw [Finset.sum_biUnion hclassification.2]
  rfl

/-- The three distinct rank-seven word orbits together lose at most
`3 · 127 q⁷`. -/
theorem orderTwoWeightSixteenRankSevenCharacterSum_ge
    (f : BooleanFunction n)
    (hclassification : HasRankSevenWeightSixteenOrbitClassification n) :
    orderTwoWeightSixteenRankSevenCharacterSum f ≥
      -(3 * (127 * (2 ^ n : ℝ) ^ 7)) := by
  rw [orderTwoWeightSixteenRankSevenCharacterSum_eq_sum_orbits
    f hclassification]
  calc
    -(3 * (127 * (2 ^ n : ℝ) ^ 7)) =
        ∑ _c : RankSevenWeightSixteenPatternClass,
          -(127 * (2 ^ n : ℝ) ^ 7) := by
      rw [Finset.sum_const, Finset.card_univ,
        show Fintype.card RankSevenWeightSixteenPatternClass = 3 by decide]
      norm_num
    _ ≤ ∑ c : RankSevenWeightSixteenPatternClass,
        rankSevenWeightSixteenPatternOrbitCharacterSum f c := by
      apply Finset.sum_le_sum
      intro c _hc
      exact rankSevenWeightSixteenPatternOrbitCharacterSum_ge f c

private theorem binarySign_ge_neg_one (b : FABL.𝔽₂) :
    -1 ≤ FABL.binarySign b := by
  by_cases hb : b = 0
  · rw [hb]
    norm_num
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
    rw [hbOne, FABL.binarySign_one]

/-- The covered rank-at-most-six residual character sum loses at most its
`127 · 2^128 · q⁷` arbitrary-mask cardinality bound. -/
theorem orderTwoWeightSixteenRankAtMostSixResidualCharacterSum_ge
    (f : BooleanFunction n)
    (hcover : HasRankAtMostSixWeightSixteenDeficientAffineMaskCover n) :
    orderTwoWeightSixteenRankAtMostSixResidualCharacterSum f ≥
      -(127 * 2 ^ 128 * (2 ^ n : ℝ) ^ 7) := by
  have hterm :
      -((orderTwoWeightSixteenRankAtMostSixResidualWords n).card : ℝ) ≤
        orderTwoWeightSixteenRankAtMostSixResidualCharacterSum f := by
    calc
      -((orderTwoWeightSixteenRankAtMostSixResidualWords n).card : ℝ) =
          ∑ _h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n,
            (-1 : ℝ) := by simp
      _ ≤ ∑ h ∈ orderTwoWeightSixteenRankAtMostSixResidualWords n,
          FABL.binarySign (booleanFunctionPairing n f h) := by
        apply Finset.sum_le_sum
        intro h _hh
        exact binarySign_ge_neg_one (booleanFunctionPairing n f h)
      _ = orderTwoWeightSixteenRankAtMostSixResidualCharacterSum f := rfl
  have hcardNat :=
    card_orderTwoWeightSixteenRankAtMostSixResidualWords_le_of_cover hcover
  have hcardReal :
      ((orderTwoWeightSixteenRankAtMostSixResidualWords n).card : ℝ) ≤
        127 * 2 ^ 128 * (2 ^ n : ℝ) ^ 7 := by
    exact_mod_cast hcardNat
  linarith

/-- Aggregating the three rank-seven pattern orbits and an arbitrary-mask
low-rank cover gives a dimension-free constant times `q⁷` lower bound for
the full weight-sixteen dual character sum. -/
theorem orderTwoWeightSixteenCharacterSum_ge_of_orbitClassification
    (f : BooleanFunction n)
    (hclassification : HasRankSevenWeightSixteenOrbitClassification n)
    (hcover : HasRankAtMostSixWeightSixteenDeficientAffineMaskCover n) :
    orderTwoWeightSixteenCharacterSum f ≥
      -((3 * 127 + 127 * 2 ^ 128) * (2 ^ n : ℝ) ^ 7) := by
  rw [orderTwoWeightSixteenCharacterSum_eq_rankSeven_add_residual]
  have hrank := orderTwoWeightSixteenRankSevenCharacterSum_ge
    f hclassification
  have hresidual :=
    orderTwoWeightSixteenRankAtMostSixResidualCharacterSum_ge f hcover
  linarith

end CryptBoolean
