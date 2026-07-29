/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.HigherOrderAlgebraicImmunity

/-!
# Mesnager's higher-order nonlinearity bound

Carlet Chapter 9: Mesnager's refinement of the positive-order nonlinearity
bound in terms of algebraic immunity.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private noncomputable def annihilatorMismatchEvaluationLinearMap
    (f g : BooleanFunction n) (s : ℕ) :
    LinearMap.ker (annihilatorEvaluationLinearMap g s) →ₗ[FABL.𝔽₂]
      (↥(support (f * (g + 1))) → FABL.𝔽₂) where
  toFun c x := ((reedMullerAnfEquiv s n).symm c.1).1 x.1
  map_add' c c' := by
    funext x
    exact congrFun (congrArg Subtype.val
      (map_add (reedMullerAnfEquiv s n).symm c.1 c'.1)) x.1
  map_smul' a c := by
    funext x
    exact congrFun (congrArg Subtype.val
      (map_smul (reedMullerAnfEquiv s n).symm a c.1)) x.1

private theorem annihilatorMismatchEvaluationLinearMap_injective
    (f g : BooleanFunction n) (s : ℕ)
    (hsAI : s < algebraicImmunity f) :
    Function.Injective (annihilatorMismatchEvaluationLinearMap f g s) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro c hc
    have hcMismatch := LinearMap.mem_ker.mp hc
    have hcAnnihilator :
        g * ((reedMullerAnfEquiv s n).symm c.1).1 = 0 :=
      (mem_ker_annihilatorEvaluationLinearMap_iff g c.1).1 c.2
    let q : reedMuller s n := (reedMullerAnfEquiv s n).symm c.1
    have hfq : f * q.1 = 0 := by
      funext x
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
        by_cases hgx : g x = 0
        · have hgCompOne : g x + 1 = 1 := by rw [hgx, zero_add]
          have hxSupport : x ∈ support (f * (g + 1)) := by
            rw [mem_support]
            simp [hfxOne, hgCompOne]
          have hx := congrFun hcMismatch ⟨x, hxSupport⟩
          change q.1 x = 0 at hx
          simp [hfxOne, hx]
        · have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
          have hx := congrFun hcAnnihilator x
          change g x * q.1 x = 0 at hx
          rw [hgxOne, one_mul] at hx
          simp [hfxOne, hx]
    have hqZero : q.1 = 0 := by
      by_contra hqNe
      have hAI := algebraicImmunity_le_functionAlgebraicDegree f q.1
        (Or.inl ⟨hqNe, hfq⟩)
      have hAIle : algebraicImmunity f ≤ s := hAI.trans q.2
      omega
    have hqSubtypeZero : q = 0 := Subtype.ext hqZero
    have hcZero := congrArg (reedMullerAnfEquiv s n) hqSubtypeZero
    apply Subtype.ext
    simpa [q] using hcZero
  · exact bot_le

/-- The dimension of degree-at-most-`s` annihilators of `g` is bounded by
the part of the distance from `f` to `g` where `f` is one. -/
theorem annihilatorSpaceDimension_le_hammingWeight_productMismatch
    (f g : BooleanFunction n) (s : ℕ)
    (hsAI : s < algebraicImmunity f) :
    annihilatorSpaceDimension g s ≤ hammingWeight (f * (g + 1)) := by
  unfold annihilatorSpaceDimension
  calc
    Module.finrank FABL.𝔽₂
        (LinearMap.ker (annihilatorEvaluationLinearMap g s)) ≤
        Module.finrank FABL.𝔽₂
          (↥(support (f * (g + 1))) → FABL.𝔽₂) :=
      LinearMap.finrank_le_finrank_of_injective
        (annihilatorMismatchEvaluationLinearMap_injective f g s hsAI)
    _ = hammingWeight (f * (g + 1)) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
        ← hammingWeight_eq_card_support]

private noncomputable def lowDegreeMultiplicationLinearMap
    (g : BooleanFunction n) (s : ℕ) :
    (↥(FABL.lowDegreeFourierFamily n s) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      BooleanFunction n where
  toFun c := g * ((reedMullerAnfEquiv s n).symm c).1
  map_add' c c' := by
    rw [map_add]
    exact mul_add g _ _
  map_smul' a c := by
    rw [map_smul]
    funext x
    change g x * (a * ((reedMullerAnfEquiv s n).symm c).1 x) =
      a * (g x * ((reedMullerAnfEquiv s n).symm c).1 x)
    ring

private theorem ker_lowDegreeMultiplicationLinearMap
    (g : BooleanFunction n) (s : ℕ) :
    LinearMap.ker (lowDegreeMultiplicationLinearMap g s) =
      LinearMap.ker (annihilatorEvaluationLinearMap g s) := by
  ext c
  rw [LinearMap.mem_ker]
  change g * ((reedMullerAnfEquiv s n).symm c).1 = 0 ↔ _
  exact (mem_ker_annihilatorEvaluationLinearMap_iff g c).symm

private theorem finrank_range_lowDegreeMultiplication_add_annihilatorSpaceDimension
    (g : BooleanFunction n) (s : ℕ) :
    Module.finrank FABL.𝔽₂
        (LinearMap.range (lowDegreeMultiplicationLinearMap g s)) +
      annihilatorSpaceDimension g s =
        ∑ i ∈ Finset.range (s + 1), Nat.choose n i := by
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (lowDegreeMultiplicationLinearMap g s)
  rw [ker_lowDegreeMultiplicationLinearMap] at hrankNullity
  unfold annihilatorSpaceDimension
  rw [annihilatorEvaluationLinearMap_domain_finrank] at hrankNullity
  exact hrankNullity

private noncomputable def fixedDegreeBand
    (S : Finset (Fin n)) (d s : ℕ) :
    Finset (Finset (FABL.FixedIndex S)) :=
  (Finset.Icc (s + 1 - d) s).biUnion fun i ↦
    Finset.powersetCard i (Finset.univ : Finset (FABL.FixedIndex S))

@[simp] private theorem mem_fixedDegreeBand
    (S : Finset (Fin n)) (d s : ℕ) (V : Finset (FABL.FixedIndex S)) :
    V ∈ fixedDegreeBand S d s ↔ s + 1 - d ≤ V.card ∧ V.card ≤ s := by
  classical
  simp [fixedDegreeBand]

private theorem card_fixedDegreeBand
    (S : Finset (Fin n)) (d s : ℕ) :
    (fixedDegreeBand S d s).card =
      ∑ i ∈ Finset.Icc (s + 1 - d) s, Nat.choose (n - S.card) i := by
  classical
  have hdisjoint :
      ((Finset.Icc (s + 1 - d) s : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun i ↦ Finset.powersetCard i
          (Finset.univ : Finset (FABL.FixedIndex S))) := by
    intro i hi j hj hij
    change Disjoint
      (Finset.powersetCard i (Finset.univ : Finset (FABL.FixedIndex S)))
      (Finset.powersetCard j (Finset.univ : Finset (FABL.FixedIndex S)))
    rw [Finset.disjoint_left]
    intro V hVi hVj
    have hiCard := (Finset.mem_powersetCard.mp hVi).2
    have hjCard := (Finset.mem_powersetCard.mp hVj).2
    exact hij (hiCard.symm.trans hjCard)
  rw [fixedDegreeBand, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.card_powersetCard]
  congr 1
  simp [FABL.FixedIndex]

private noncomputable def fixedBandCoefficientLinearMap
    (S : Finset (Fin n)) (d s : ℕ) :
    (↥(fixedDegreeBand S d s) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      (Finset (Fin n) → FABL.𝔽₂) where
  toFun c U := ∑ V : ↥(fixedDegreeBand S d s),
    if U = FABL.liftFixedFrequency V.1 then c V else 0
  map_add' c c' := by
    funext U
    change (∑ V, if U = FABL.liftFixedFrequency V.1 then
        c V + c' V else 0) =
      (∑ V, if U = FABL.liftFixedFrequency V.1 then c V else 0) +
        ∑ V, if U = FABL.liftFixedFrequency V.1 then c' V else 0
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro V
    by_cases hU : U = FABL.liftFixedFrequency V.1
    · simp [hU]
    · simp [hU]
  map_smul' a c := by
    funext U
    change (∑ V, if U = FABL.liftFixedFrequency V.1 then
        a * c V else 0) =
      a * ∑ V, if U = FABL.liftFixedFrequency V.1 then c V else 0
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro V
    by_cases hU : U = FABL.liftFixedFrequency V.1
    · simp [hU]
    · simp [hU]

private noncomputable def anfEvalLinearMap (n : ℕ) :
    (Finset (Fin n) → FABL.𝔽₂) →ₗ[FABL.𝔽₂] BooleanFunction n where
  toFun := FABL.anfEval
  map_add' c c' := by
    funext x
    exact FABL.anfEval_add c c' x
  map_smul' a c := by
    funext x
    simp only [FABL.anfEval, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro U
    simp only [RingHom.id_apply]
    ring

private noncomputable def fixedBandPolynomialLinearMap
    (S : Finset (Fin n)) (d s : ℕ) :
    (↥(fixedDegreeBand S d s) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      BooleanFunction n :=
  (anfEvalLinearMap n).comp (fixedBandCoefficientLinearMap S d s)

private theorem anfCoeff_anfEval_eq
    (c : Finset (Fin n) → FABL.𝔽₂) :
    FABL.anfCoeff (FABL.anfEval c) = c := by
  apply FABL.anfEval_injective
  rw [FABL.anfEval_anfCoeff]

private theorem anfCoeff_fixedBandPolynomialLinearMap
    (S : Finset (Fin n)) (d s : ℕ)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂) :
    FABL.anfCoeff (fixedBandPolynomialLinearMap S d s c) =
      fixedBandCoefficientLinearMap S d s c := by
  exact anfCoeff_anfEval_eq (fixedBandCoefficientLinearMap S d s c)

private theorem liftFixedFrequency_injective
    (S : Finset (Fin n)) :
    Function.Injective
      (FABL.liftFixedFrequency :
        Finset (FABL.FixedIndex S) → Finset (Fin n)) := by
  intro V W hVW
  exact Finset.map_injective
    (Function.Embedding.subtype fun i : Fin n ↦ i ∉ S) hVW

private theorem fixedBandCoefficientLinearMap_apply_lift
    (S : Finset (Fin n)) (d s : ℕ)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂)
    (V : ↥(fixedDegreeBand S d s)) :
    fixedBandCoefficientLinearMap S d s c
        (FABL.liftFixedFrequency V.1) = c V := by
  classical
  change (∑ W, if FABL.liftFixedFrequency V.1 =
      FABL.liftFixedFrequency W.1 then c W else 0) = c V
  calc
    (∑ W, if FABL.liftFixedFrequency V.1 =
        FABL.liftFixedFrequency W.1 then c W else 0) =
        (if FABL.liftFixedFrequency V.1 =
          FABL.liftFixedFrequency V.1 then c V else 0) := by
      apply Fintype.sum_eq_single V
      intro W hWV
      rw [if_neg]
      intro hlift
      exact hWV (Subtype.ext (liftFixedFrequency_injective S hlift.symm))
    _ = c V := if_pos rfl

private theorem card_liftFixedFrequency
    (S : Finset (Fin n)) (V : Finset (FABL.FixedIndex S)) :
    (FABL.liftFixedFrequency V).card = V.card := by
  exact Finset.card_map _

private theorem functionAlgebraicDegree_fixedBandPolynomialLinearMap_le
    (S : Finset (Fin n)) (d s : ℕ)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂) :
    FABL.functionAlgebraicDegree
        (fixedBandPolynomialLinearMap S d s c) ≤ s := by
  rw [FABL.functionAlgebraicDegree,
    anfCoeff_fixedBandPolynomialLinearMap,
    FABL.algebraicDegree_le_iff]
  intro U hU
  change (∑ V : ↥(fixedDegreeBand S d s),
    if U = FABL.liftFixedFrequency V.1 then c V else 0) ≠ 0 at hU
  obtain ⟨V, _hVmem, hV⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hU
  by_cases hUV : U = FABL.liftFixedFrequency V.1
  · rw [hUV, card_liftFixedFrequency]
    exact (mem_fixedDegreeBand S d s V.1).1 V.2 |>.2
  · simp [hUV] at hV

private noncomputable def fixedBandPolynomialReedMullerLinearMap
    (S : Finset (Fin n)) (d s : ℕ) :
    (↥(fixedDegreeBand S d s) → FABL.𝔽₂) →ₗ[FABL.𝔽₂]
      reedMuller s n where
  toFun c := ⟨fixedBandPolynomialLinearMap S d s c,
    functionAlgebraicDegree_fixedBandPolynomialLinearMap_le S d s c⟩
  map_add' c c' := by
    apply Subtype.ext
    exact map_add (fixedBandPolynomialLinearMap S d s) c c'
  map_smul' a c := by
    apply Subtype.ext
    exact map_smul (fixedBandPolynomialLinearMap S d s) a c

private theorem exists_liftFixedFrequency_of_fixedBandCoefficient_ne_zero
    (S : Finset (Fin n)) (d s : ℕ)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂)
    (U : Finset (Fin n))
    (hU : fixedBandCoefficientLinearMap S d s c U ≠ 0) :
    ∃ V : ↥(fixedDegreeBand S d s),
      U = FABL.liftFixedFrequency V.1 ∧ c V ≠ 0 := by
  classical
  change (∑ V : ↥(fixedDegreeBand S d s),
    if U = FABL.liftFixedFrequency V.1 then c V else 0) ≠ 0 at hU
  obtain ⟨V, _hVmem, hV⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hU
  by_cases hUV : U = FABL.liftFixedFrequency V.1
  · exact ⟨V, hUV, by simpa [hUV] using hV⟩
  · simp [hUV] at hV

private theorem disjoint_self_liftFixedFrequency
    (S : Finset (Fin n)) (V : Finset (FABL.FixedIndex S)) :
    Disjoint S (FABL.liftFixedFrequency V) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiS hiV
  obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hiV
  rw [← hji] at hiS
  exact j.property hiS

private theorem eq_of_union_eq_union_of_disjoint_left
    (S A B : Finset (Fin n))
    (hA : Disjoint S A) (hB : Disjoint S B)
    (hunion : S ∪ A = S ∪ B) :
    A = B := by
  ext i
  constructor
  · intro hiA
    have hiUnion : i ∈ S ∪ B := by rw [← hunion]; exact Finset.mem_union_right S hiA
    rcases Finset.mem_union.mp hiUnion with hiS | hiB
    · exact (Finset.disjoint_left.mp hA hiS hiA).elim
    · exact hiB
  · intro hiB
    have hiUnion : i ∈ S ∪ A := by rw [hunion]; exact Finset.mem_union_right S hiB
    rcases Finset.mem_union.mp hiUnion with hiS | hiA
    · exact (Finset.disjoint_left.mp hB hiS hiB).elim
    · exact hiA

private theorem anfCoeff_mul_fixedBandPolynomial_at_top_union
    (g : BooleanFunction n) (S : Finset (Fin n))
    (hScoeff : FABL.anfCoeff g S ≠ 0)
    (hScard : S.card = FABL.functionAlgebraicDegree g)
    (d s : ℕ)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂)
    (V : ↥(fixedDegreeBand S d s)) :
    FABL.anfCoeff (g * fixedBandPolynomialLinearMap S d s c)
        (S ∪ FABL.liftFixedFrequency V.1) = c V := by
  classical
  rw [FABL.anfCoeff_mul, FABL.anfMul,
    anfCoeff_fixedBandPolynomialLinearMap]
  calc
    (∑ A, ∑ B,
        if S ∪ FABL.liftFixedFrequency V.1 = A ∪ B then
          FABL.anfCoeff g A * fixedBandCoefficientLinearMap S d s c B
        else 0) =
        ∑ B,
          if S ∪ FABL.liftFixedFrequency V.1 = S ∪ B then
            FABL.anfCoeff g S * fixedBandCoefficientLinearMap S d s c B
          else 0 := by
      apply Fintype.sum_eq_single S
      intro A hAS
      apply Finset.sum_eq_zero
      intro B _hB
      by_cases hunion :
          S ∪ FABL.liftFixedFrequency V.1 = A ∪ B
      · rw [if_pos hunion]
        by_cases hAcoeff : FABL.anfCoeff g A = 0
        · simp [hAcoeff]
        by_cases hBcoeff : fixedBandCoefficientLinearMap S d s c B = 0
        · simp [hBcoeff]
        obtain ⟨W, hBW, _hWcoeff⟩ :=
          exists_liftFixedFrequency_of_fixedBandCoefficient_ne_zero
            S d s c B hBcoeff
        have hBdisjoint : Disjoint S B := by
          rw [hBW]
          exact disjoint_self_liftFixedFrequency S W.1
        have hSsubsetA : S ⊆ A := by
          intro i hiS
          have hiUnion : i ∈ A ∪ B := by
            rw [← hunion]
            exact Finset.mem_union_left _ hiS
          rcases Finset.mem_union.mp hiUnion with hiA | hiB
          · exact hiA
          · exact (Finset.disjoint_left.mp hBdisjoint hiS hiB).elim
        have hAcard : A.card ≤ S.card := by
          rw [hScard]
          exact (FABL.algebraicDegree_le_iff (FABL.anfCoeff g)
            (FABL.functionAlgebraicDegree g)).1 le_rfl A hAcoeff
        exact (hAS (Finset.eq_of_subset_of_card_le hSsubsetA hAcard).symm).elim
      · rw [if_neg hunion]
    _ =
        (if S ∪ FABL.liftFixedFrequency V.1 =
            S ∪ FABL.liftFixedFrequency V.1 then
          FABL.anfCoeff g S *
            fixedBandCoefficientLinearMap S d s c
              (FABL.liftFixedFrequency V.1)
        else 0) := by
      apply Fintype.sum_eq_single (FABL.liftFixedFrequency V.1)
      intro B hBV
      by_cases hunion :
          S ∪ FABL.liftFixedFrequency V.1 = S ∪ B
      · rw [if_pos hunion]
        by_cases hBcoeff : fixedBandCoefficientLinearMap S d s c B = 0
        · simp [hBcoeff]
        obtain ⟨W, hBW, _hWcoeff⟩ :=
          exists_liftFixedFrequency_of_fixedBandCoefficient_ne_zero
            S d s c B hBcoeff
        have hEq : FABL.liftFixedFrequency V.1 = B :=
          eq_of_union_eq_union_of_disjoint_left S
            (FABL.liftFixedFrequency V.1) B
            (disjoint_self_liftFixedFrequency S V.1)
            (by rw [hBW]; exact disjoint_self_liftFixedFrequency S W.1)
            hunion
        exact (hBV hEq.symm).elim
      · rw [if_neg hunion]
    _ = c V := by
      rw [if_pos rfl, fixedBandCoefficientLinearMap_apply_lift]
      have hSOne : FABL.anfCoeff g S = 1 :=
        Fin.eq_one_of_ne_zero _ hScoeff
      rw [hSOne, one_mul]

private theorem functionAlgebraicDegree_mul_fixedBandPolynomial_gt
    (g : BooleanFunction n) (S : Finset (Fin n))
    (hScoeff : FABL.anfCoeff g S ≠ 0)
    (hScard : S.card = FABL.functionAlgebraicDegree g)
    (d s : ℕ) (hd : d = S.card)
    (c : ↥(fixedDegreeBand S d s) → FABL.𝔽₂)
    (hc : c ≠ 0) :
    s < FABL.functionAlgebraicDegree
      (g * fixedBandPolynomialLinearMap S d s c) := by
  obtain ⟨V, hV⟩ := Function.ne_iff.mp hc
  have hVNe : c V ≠ 0 := by simpa using hV
  have hcoeff : FABL.anfCoeff
      (g * fixedBandPolynomialLinearMap S d s c)
      (S ∪ FABL.liftFixedFrequency V.1) ≠ 0 := by
    rw [anfCoeff_mul_fixedBandPolynomial_at_top_union
      g S hScoeff hScard d s c V]
    exact hVNe
  have hcard := (FABL.algebraicDegree_le_iff
    (FABL.anfCoeff (g * fixedBandPolynomialLinearMap S d s c))
    (FABL.functionAlgebraicDegree
      (g * fixedBandPolynomialLinearMap S d s c))).1 le_rfl
    (S ∪ FABL.liftFixedFrequency V.1) hcoeff
  have hdisjoint := disjoint_self_liftFixedFrequency S V.1
  rw [Finset.card_union_of_disjoint hdisjoint,
    card_liftFixedFrequency] at hcard
  have hVlower := (mem_fixedDegreeBand S d s V.1).1 V.2 |>.1
  omega

private noncomputable def annihilatorBandWitnessLinearMap
    (g : BooleanFunction n) (S : Finset (Fin n)) (d s : ℕ) :
    (LinearMap.ker (annihilatorEvaluationLinearMap (g + 1) s) ×
      (↥(fixedDegreeBand S d s) → FABL.𝔽₂)) →ₗ[FABL.𝔽₂]
      (↥(FABL.lowDegreeFourierFamily n s) → FABL.𝔽₂) where
  toFun z := z.1.1 + reedMullerAnfEquiv s n
    (fixedBandPolynomialReedMullerLinearMap S d s z.2)
  map_add' z z' := by
    rcases z with ⟨z₁, z₂⟩
    rcases z' with ⟨z₁', z₂'⟩
    change (z₁ + z₁').1 + reedMullerAnfEquiv s n
        (fixedBandPolynomialReedMullerLinearMap S d s (z₂ + z₂')) = _
    simp only [map_add]
    change z₁.1 + z₁'.1 +
      (reedMullerAnfEquiv s n (fixedBandPolynomialReedMullerLinearMap S d s z₂) +
        reedMullerAnfEquiv s n (fixedBandPolynomialReedMullerLinearMap S d s z₂')) = _
    abel
  map_smul' a z := by
    rcases z with ⟨z₁, z₂⟩
    change (a • z₁).1 + reedMullerAnfEquiv s n
        (fixedBandPolynomialReedMullerLinearMap S d s (a • z₂)) = _
    simp only [map_smul]
    funext U
    change a * z₁.1 U + a *
        (reedMullerAnfEquiv s n
          (fixedBandPolynomialReedMullerLinearMap S d s z₂)) U =
      a * (z₁.1 U +
        (reedMullerAnfEquiv s n
          (fixedBandPolynomialReedMullerLinearMap S d s z₂)) U)
    ring

private noncomputable def annihilatorBandSumLinearMap
    (g : BooleanFunction n) (S : Finset (Fin n)) (d s : ℕ) :
    (LinearMap.ker (annihilatorEvaluationLinearMap (g + 1) s) ×
      (↥(fixedDegreeBand S d s) → FABL.𝔽₂)) →ₗ[FABL.𝔽₂]
      LinearMap.range (lowDegreeMultiplicationLinearMap g s) :=
  (lowDegreeMultiplicationLinearMap g s).rangeRestrict.comp
    (annihilatorBandWitnessLinearMap g S d s)

private theorem annihilatorBandSumLinearMap_injective
    (g : BooleanFunction n) (S : Finset (Fin n))
    (hScoeff : FABL.anfCoeff g S ≠ 0)
    (hScard : S.card = FABL.functionAlgebraicDegree g)
    (d s : ℕ) (hd : d = S.card) :
    Function.Injective (annihilatorBandSumLinearMap g S d s) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · rintro z hz
    have hzZero := LinearMap.mem_ker.mp hz
    have hzFunction := congrArg Subtype.val hzZero
    let q : reedMuller s n := (reedMullerAnfEquiv s n).symm z.1.1
    let p : reedMuller s n :=
      fixedBandPolynomialReedMullerLinearMap S d s z.2
    have hqAnnihilator : (g + 1) * q.1 = 0 :=
      (mem_ker_annihilatorEvaluationLinearMap_iff (g + 1) z.1.1).1 z.1.2
    have hgq : g * q.1 = q.1 := by
      rw [add_mul, one_mul] at hqAnnihilator
      exact (eq_neg_of_add_eq_zero_left hqAnnihilator).trans
        (ZModModule.neg_eq_self q.1)
    have hsumZero : g * (q.1 + p.1) = 0 := by
      change lowDegreeMultiplicationLinearMap g s
        (annihilatorBandWitnessLinearMap g S d s z) = 0 at hzFunction
      change lowDegreeMultiplicationLinearMap g s
        (z.1.1 + reedMullerAnfEquiv s n p) = 0 at hzFunction
      change g * ((reedMullerAnfEquiv s n).symm
        (z.1.1 + reedMullerAnfEquiv s n p)).1 = 0 at hzFunction
      rw [map_add, LinearEquiv.symm_apply_apply] at hzFunction
      simpa [q] using hzFunction
    have hgpEq : g * p.1 = q.1 := by
      rw [mul_add, hgq] at hsumZero
      have hqEq : q.1 = g * p.1 :=
        (eq_neg_of_add_eq_zero_left hsumZero).trans
          (ZModModule.neg_eq_self (g * p.1))
      exact hqEq.symm
    have hpCoefficientZero : z.2 = 0 := by
      by_contra hpNe
      have hpDegree := functionAlgebraicDegree_mul_fixedBandPolynomial_gt
        g S hScoeff hScard d s hd z.2 hpNe
      have hdegreeEq : FABL.functionAlgebraicDegree (g * p.1) =
          FABL.functionAlgebraicDegree q.1 := congrArg
        FABL.functionAlgebraicDegree hgpEq
      have hqDegree : FABL.functionAlgebraicDegree q.1 ≤ s := q.2
      dsimp [p] at hpDegree hdegreeEq
      have hcontradiction : s < FABL.functionAlgebraicDegree q.1 :=
        hpDegree.trans_eq hdegreeEq
      exact (Nat.not_lt_of_ge hqDegree hcontradiction).elim
    have hpZero : p.1 = 0 := by simp [p, hpCoefficientZero]
    have hqZero : q.1 = 0 := by rw [← hgpEq, hpZero, mul_zero]
    have hqSubtypeZero : q = 0 := Subtype.ext hqZero
    have hzFirst : z.1 = 0 := by
      apply Subtype.ext
      have hcoeff := congrArg (reedMullerAnfEquiv s n) hqSubtypeZero
      simpa [q] using hcoeff
    rw [Submodule.mem_bot]
    apply Prod.ext
    · exact hzFirst
    · exact hpCoefficientZero
  · exact bot_le

private theorem exists_top_anfCoefficient
    (g : BooleanFunction n) (hne : g ≠ 0) :
    ∃ S : Finset (Fin n),
      FABL.anfCoeff g S ≠ 0 ∧
        S.card = FABL.functionAlgebraicDegree g := by
  classical
  have hsupport : (FABL.anfSupport (FABL.anfCoeff g)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    rw [← FABL.anfEval_anfCoeff g]
    funext x
    rw [FABL.anfEval]
    apply Finset.sum_eq_zero
    intro S _hS
    have hzero : FABL.anfCoeff g S = 0 := by
      by_contra hcoeff
      have hmem : S ∈ FABL.anfSupport (FABL.anfCoeff g) :=
        (FABL.mem_anfSupport _ _).2 hcoeff
      rw [hempty] at hmem
      simp at hmem
    simp [hzero]
  obtain ⟨S, hSmem, hsup⟩ := Finset.exists_mem_eq_sup
    (FABL.anfSupport (FABL.anfCoeff g)) hsupport Finset.card
  exact ⟨S, (FABL.mem_anfSupport _ _).1 hSmem, hsup.symm⟩

private theorem annihilatorSpaceDimension_add_degreeBand_le_range
    (g : BooleanFunction n) (hne : g ≠ 0) (s : ℕ) :
    annihilatorSpaceDimension (g + 1) s +
        (∑ i ∈ Finset.Icc
          (s + 1 - FABL.functionAlgebraicDegree g) s,
          Nat.choose (n - FABL.functionAlgebraicDegree g) i) ≤
      Module.finrank FABL.𝔽₂
        (LinearMap.range (lowDegreeMultiplicationLinearMap g s)) := by
  obtain ⟨S, hScoeff, hScard⟩ := exists_top_anfCoefficient g hne
  have hinjective := annihilatorBandSumLinearMap_injective g S
    hScoeff hScard (FABL.functionAlgebraicDegree g) s hScard.symm
  have hfinrank := LinearMap.finrank_le_finrank_of_injective hinjective
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe, card_fixedDegreeBand] at hfinrank
  unfold annihilatorSpaceDimension
  rw [hScard] at hfinrank
  exact hfinrank

private def degreeBandSum (n r s : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc (s + 1 - r) s, Nat.choose (n - r) i

private theorem degreeBandSum_eq_range_sub (n r s : ℕ) :
    degreeBandSum n r s =
      (∑ i ∈ Finset.range (s + 1), Nat.choose (n - r) i) -
        ∑ i ∈ Finset.range (s + 1 - r), Nat.choose (n - r) i := by
  have hIcc : Finset.Icc (s + 1 - r) s =
      Finset.Ico (s + 1 - r) (s + 1) := by
    ext i
    simp
  rw [degreeBandSum, hIcc]
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i ↦ Nat.choose (n - r) i)
    (show s + 1 - r ≤ s + 1 by omega)
  omega

private theorem degreeBandSum_succ_le
    (n d s : ℕ) (hd : 0 < d) (hdn : d < n) :
    degreeBandSum n (d + 1) s ≤ degreeBandSum n d s := by
  let N := n - d - 1
  have hnSub : n - d = N + 1 := by
    dsimp [N]
    omega
  have hnSuccSub : n - (d + 1) = N := by
    dsimp [N]
    omega
  have hlower : s + 1 - (d + 1) = (s + 1 - d) - 1 := by
    omega
  have hlowerLe : s + 1 - d ≤ s := by omega
  have hmono :
      (∑ i ∈ Finset.range (s + 1 - d), Nat.choose N i) ≤
        ∑ i ∈ Finset.range s, Nat.choose N i :=
    sum_choose_range_mono N hlowerLe
  have hlowerPredLe : (s + 1 - d) - 1 ≤ s + 1 := by omega
  have hpredMono :
      (∑ i ∈ Finset.range ((s + 1 - d) - 1), Nat.choose N i) ≤
        ∑ i ∈ Finset.range (s + 1), Nat.choose N i :=
    sum_choose_range_mono N hlowerPredLe
  rw [degreeBandSum_eq_range_sub, degreeBandSum_eq_range_sub,
    hnSub, hnSuccSub, hlower,
    sum_choose_succ_dimension N (s + 1),
    sum_choose_succ_dimension N (s + 1 - d)]
  simp only [Nat.add_sub_cancel]
  omega

private theorem degreeBandSum_antitone
    (n d r s : ℕ) (hd : 0 < d) (hdr : d ≤ r) (hrn : r ≤ n) :
    degreeBandSum n r s ≤ degreeBandSum n d s := by
  induction r, hdr using Nat.le_induction with
  | base => exact le_rfl
  | succ r hdr ih =>
      have hrLtN : r < n := by omega
      exact (degreeBandSum_succ_le n r s (hd.trans_le hdr) hrLtN).trans
        (ih (by omega))

private theorem annihilatorSpaceDimension_add_degreeBand_le_range_of_degree_le
    (g : BooleanFunction n) (hgZero : g ≠ 0) (hgOne : g ≠ 1)
    (r s : ℕ) (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (hrn : r ≤ n) :
    annihilatorSpaceDimension (g + 1) s + degreeBandSum n r s ≤
      Module.finrank FABL.𝔽₂
        (LinearMap.range (lowDegreeMultiplicationLinearMap g s)) := by
  have hgDegreePos : 0 < FABL.functionAlgebraicDegree g := by
    by_contra hdegreeZero
    have hdegreeEq : FABL.functionAlgebraicDegree g = 0 := by omega
    obtain ⟨b, a, hgaffine⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one g (by omega)
    have haZero : a = 0 := by
      funext i
      have hcoeff : FABL.anfCoeff g {i} = 0 := by
        by_contra hne
        have hcard := (FABL.algebraicDegree_le_iff (FABL.anfCoeff g)
          (FABL.functionAlgebraicDegree g)).1 le_rfl {i} hne
        rw [hdegreeEq] at hcard
        simp at hcard
      rw [hgaffine, FABL.anfCoeff_affineFunction] at hcoeff
      simpa [FABL.affineCoefficients] using hcoeff
    subst a
    by_cases hb : b = 0
    · apply hgZero
      rw [hgaffine]
      funext x
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct, hb]
    · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
      apply hgOne
      rw [hgaffine]
      funext x
      simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct, hbOne]
  have hband := degreeBandSum_antitone n
    (FABL.functionAlgebraicDegree g) r s hgDegreePos hdegree hrn
  have hexact := annihilatorSpaceDimension_add_degreeBand_le_range
    g hgZero s
  change annihilatorSpaceDimension (g + 1) s + degreeBandSum n r s ≤ _
  exact (Nat.add_le_add_left hband _).trans hexact

private noncomputable def lowDegreeMultipleReedMullerLinearMap
    (g : BooleanFunction n) (r t s : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (horder : r + t ≤ s) :
    LinearMap.range (lowDegreeMultiplicationLinearMap g t) →ₗ[FABL.𝔽₂]
      reedMuller s n where
  toFun p := ⟨p.1, by
      obtain ⟨c, hc⟩ := p.2
      rw [← hc]
      exact (FABL.functionAlgebraicDegree_mul_le_add g
        ((reedMullerAnfEquiv t n).symm c).1).trans
          ((Nat.add_le_add hdegree ((reedMullerAnfEquiv t n).symm c).2).trans
            horder)⟩
  map_add' p p' := by
    apply Subtype.ext
    rfl
  map_smul' a p := by
    apply Subtype.ext
    rfl

private noncomputable def lowDegreeMultipleCoefficientLinearMap
    (g : BooleanFunction n) (r t s : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (horder : r + t ≤ s) :
    LinearMap.range (lowDegreeMultiplicationLinearMap g t) →ₗ[FABL.𝔽₂]
      (↥(FABL.lowDegreeFourierFamily n s) → FABL.𝔽₂) :=
  (reedMullerAnfEquiv s n).toLinearMap.comp
    (lowDegreeMultipleReedMullerLinearMap g r t s hdegree horder)

private noncomputable def lowDegreeMultipleToAnnihilatorLinearMap
    (g : BooleanFunction n) (r t s : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (horder : r + t ≤ s) :
    LinearMap.range (lowDegreeMultiplicationLinearMap g t) →ₗ[FABL.𝔽₂]
      LinearMap.ker (annihilatorEvaluationLinearMap (g + 1) s) :=
  LinearMap.codRestrict
    (LinearMap.ker (annihilatorEvaluationLinearMap (g + 1) s))
    (lowDegreeMultipleCoefficientLinearMap g r t s hdegree horder) (by
      intro p
      rw [mem_ker_annihilatorEvaluationLinearMap_iff]
      change (g + 1) * ((reedMullerAnfEquiv s n).symm
        (reedMullerAnfEquiv s n
          (lowDegreeMultipleReedMullerLinearMap
            g r t s hdegree horder p))).1 = 0
      rw [LinearEquiv.symm_apply_apply]
      change (g + 1) * p.1 = 0
      obtain ⟨a, ha⟩ := p.2
      rw [← ha]
      calc
        (g + 1) *
            (g * ((reedMullerAnfEquiv t n).symm a).1) =
            (g * (g + 1)) * ((reedMullerAnfEquiv t n).symm a).1 := by ac_rfl
        _ = 0 := by rw [booleanFunction_mul_complement, zero_mul])

private theorem lowDegreeMultipleToAnnihilatorLinearMap_injective
    (g : BooleanFunction n) (r t s : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (horder : r + t ≤ s) :
    Function.Injective
      (lowDegreeMultipleToAnnihilatorLinearMap g r t s hdegree horder) := by
  intro p p' hpp
  have hcoeff :
      (lowDegreeMultipleToAnnihilatorLinearMap g r t s hdegree horder p).1 =
        (lowDegreeMultipleToAnnihilatorLinearMap g r t s hdegree horder p').1 :=
    congrArg Subtype.val hpp
  have hRM := (reedMullerAnfEquiv s n).injective hcoeff
  have hval := congrArg Subtype.val hRM
  change p.1 = p'.1 at hval
  exact Subtype.ext hval

private theorem finrank_range_lowDegreeMultiplication_le_annihilatorSpaceDimension
    (g : BooleanFunction n) (r t s : ℕ)
    (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (horder : r + t ≤ s) :
    Module.finrank FABL.𝔽₂
        (LinearMap.range (lowDegreeMultiplicationLinearMap g t)) ≤
      annihilatorSpaceDimension (g + 1) s := by
  unfold annihilatorSpaceDimension
  exact LinearMap.finrank_le_finrank_of_injective
    (lowDegreeMultipleToAnnihilatorLinearMap_injective
      g r t s hdegree horder)

/-- Below `AI(f)`, the sum of the prescribed-degree annihilator dimensions
of `g` and its complement is bounded by the distance from `f` to `g`. -/
theorem annihilatorSpaceDimensions_add_le_hammingWeight_add
    (f g : BooleanFunction n) (s : ℕ)
    (hsAI : s < algebraicImmunity f) :
    annihilatorSpaceDimension g s + annihilatorSpaceDimension (g + 1) s ≤
      hammingWeight (f + g) := by
  have hleft := annihilatorSpaceDimension_le_hammingWeight_productMismatch
    f g s hsAI
  have hright := annihilatorSpaceDimension_le_hammingWeight_productMismatch
    (f + 1) (g + 1) s (by
      rw [algebraicImmunity_add_constant_one]
      exact hsAI)
  have hcancel : (g + 1) + 1 = g := by
    funext x
    change g x + 1 + 1 = g x
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [hcancel] at hright
  calc
    annihilatorSpaceDimension g s + annihilatorSpaceDimension (g + 1) s ≤
        hammingWeight (f * (g + 1)) + hammingWeight ((f + 1) * g) :=
      Nat.add_le_add hleft hright
    _ = hammingWeight (f + g) :=
      (hammingWeight_add_eq_product_partition f g).symm

private theorem degreeBand_lowerBound_hammingWeight_add_of_nonconstant
    (f g : BooleanFunction n) (hgZero : g ≠ 0) (hgOne : g ≠ 1)
    (r k : ℕ) (hdegree : FABL.functionAlgebraicDegree g ≤ r)
    (hrn : r ≤ n) (hkAI : k = algebraicImmunity f)
    (hrk : r < k) :
    (∑ i ∈ Finset.range (k - r), Nat.choose n i) +
        degreeBandSum n r (k - r - 1) ≤ hammingWeight (f + g) := by
  let t := k - r - 1
  let s := k - 1
  have ht : t + 1 = k - r := by dsimp [t]; omega
  have horder : r + t ≤ s := by dsimp [t, s]; omega
  have hsAI : s < algebraicImmunity f := by dsimp [s]; omega
  have hcompDegree : FABL.functionAlgebraicDegree (g + 1) ≤ r :=
    (FABL.functionAlgebraicDegree_add_le_max g 1).trans (by
      rw [FABL.functionAlgebraicDegree_one]
      exact max_le hdegree (Nat.zero_le r))
  have hrangeG :=
    finrank_range_lowDegreeMultiplication_le_annihilatorSpaceDimension
      g r t s hdegree horder
  have hrangeComp :=
    finrank_range_lowDegreeMultiplication_le_annihilatorSpaceDimension
      (g + 1) r t s hcompDegree horder
  have hcancel : (g + 1) + 1 = g := by
    funext x
    change g x + 1 + 1 = g x
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [hcancel] at hrangeComp
  have hdimensions := annihilatorSpaceDimensions_add_le_hammingWeight_add
    f g s hsAI
  have hranges :
      Module.finrank FABL.𝔽₂
          (LinearMap.range (lowDegreeMultiplicationLinearMap g t)) +
        Module.finrank FABL.𝔽₂
          (LinearMap.range (lowDegreeMultiplicationLinearMap (g + 1) t)) ≤
        hammingWeight (f + g) := by
    exact (Nat.add_le_add hrangeG hrangeComp).trans (by
      simpa [add_comm] using hdimensions)
  have hjoint :=
    annihilatorSpaceDimension_add_degreeBand_le_range_of_degree_le
      g hgZero hgOne r t hdegree hrn
  have hrankComp :=
    finrank_range_lowDegreeMultiplication_add_annihilatorSpaceDimension
      (g + 1) t
  rw [ht] at hrankComp
  change annihilatorSpaceDimension (g + 1) t +
      degreeBandSum n r t ≤ _ at hjoint
  change (∑ i ∈ Finset.range (k - r), Nat.choose n i) +
    degreeBandSum n r t ≤ hammingWeight (f + g)
  omega

private theorem choose_le_choose_add_diagonal
    (a i r : ℕ) :
    Nat.choose a i ≤ Nat.choose (a + r) (i + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        Nat.choose a i ≤ Nat.choose (a + r) (i + r) := ih
        _ ≤ Nat.choose ((a + r) + 1) ((i + r) + 1) := by
          rw [Nat.choose_succ_succ]
          omega
        _ = Nat.choose (a + (r + 1)) (i + (r + 1)) := by
          rw [show (a + r) + 1 = a + (r + 1) by omega,
            show (i + r) + 1 = i + (r + 1) by omega]

private theorem degreeBandSum_le_sum_Ico
    (n r k : ℕ) (hrn : r ≤ n) (hrk : r < k) :
    degreeBandSum n r (k - r - 1) ≤
      ∑ i ∈ Finset.Ico (k - r) k, Nat.choose n i := by
  classical
  let band := Finset.Icc (k - 2 * r) (k - r - 1)
  have hlower : k - r - r = k - 2 * r := by omega
  have hband : Finset.Icc ((k - r - 1) + 1 - r) (k - r - 1) =
      band := by
    dsimp [band]
    congr 1
    omega
  rw [degreeBandSum, hband]
  have hterm :
      (∑ i ∈ band, Nat.choose (n - r) i) ≤
        ∑ i ∈ band, Nat.choose n (i + r) := by
    apply Finset.sum_le_sum
    intro i _hi
    calc
      Nat.choose (n - r) i ≤
          Nat.choose ((n - r) + r) (i + r) :=
        choose_le_choose_add_diagonal (n - r) i r
      _ = Nat.choose n (i + r) := by rw [Nat.sub_add_cancel hrn]
  have hinjective : Set.InjOn (fun i : ℕ ↦ i + r) band := by
    intro i _hi j _hj hij
    exact Nat.add_right_cancel hij
  have himageSubset : band.image (fun i ↦ i + r) ⊆ Finset.Ico (k - r) k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hiBounds := Finset.mem_Icc.mp hi
    rw [Finset.mem_Ico]
    omega
  calc
    (∑ i ∈ band, Nat.choose (n - r) i) ≤
        ∑ i ∈ band, Nat.choose n (i + r) := hterm
    _ = ∑ j ∈ band.image (fun i ↦ i + r), Nat.choose n j := by
      symm
      exact Finset.sum_image hinjective
    _ ≤ ∑ i ∈ Finset.Ico (k - r) k, Nat.choose n i :=
      Finset.sum_le_sum_of_subset_of_nonneg himageSubset
        (fun _ _ _ ↦ Nat.zero_le _)

private theorem mesnagerCombinatorialBound_le_sum_choose
    (n r k : ℕ) (hrn : r ≤ n) (hrk : r < k) :
    (∑ i ∈ Finset.range (k - r), Nat.choose n i) +
        degreeBandSum n r (k - r - 1) ≤
      ∑ i ∈ Finset.range k, Nat.choose n i := by
  have hband := degreeBandSum_le_sum_Ico n r k hrn hrk
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i ↦ Nat.choose n i) (Nat.sub_le k r)
  omega

/-- Mesnager's improvement: for positive order below `AI(f)`, the
order-`r` nonlinearity is bounded below by a full-cube Reed–Muller dimension
plus the upper degree band in `n-r` variables. -/
theorem sum_choose_add_degreeBand_le_higherOrderNonlinearity
    (f : BooleanFunction n) (r : ℕ) (_hr : 0 < r)
    (hrAI : r < algebraicImmunity f) :
    (∑ i ∈ Finset.range (algebraicImmunity f - r), Nat.choose n i) +
        (∑ i ∈ Finset.Icc
          (algebraicImmunity f - 2 * r)
          (algebraicImmunity f - r - 1),
          Nat.choose (n - r) i) ≤
      higherOrderNonlinearity r f := by
  let k := algebraicImmunity f
  have hrk : r < k := by
    dsimp [k]
    exact hrAI
  have hrn : r ≤ n := by
    have hAI := algebraicImmunity_le_ceiling_half f
    omega
  have hbandEq : degreeBandSum n r (k - r - 1) =
      ∑ i ∈ Finset.Icc (k - 2 * r) (k - r - 1),
        Nat.choose (n - r) i := by
    have hlower : (k - r - 1) + 1 - r = k - 2 * r := by omega
    rw [degreeBandSum, hlower]
  have hconstantBound (c : BooleanFunction n) (hc : c = 0 ∨ c = 1) :
      (∑ i ∈ Finset.range (k - r), Nat.choose n i) +
          degreeBandSum n r (k - r - 1) ≤ hammingWeight (f + c) := by
    have hAIc : algebraicImmunity (f + c) = k := by
      rcases hc with rfl | rfl
      · simp [k]
      · exact (algebraicImmunity_add_constant_one f).trans rfl
    have hweight := sum_choose_below_algebraicImmunity_le_hammingWeight (f + c)
    rw [hAIc] at hweight
    exact (mesnagerCombinatorialBound_le_sum_choose n r k hrn (by
      dsimp [k]
      exact hrAI)).trans hweight
  obtain ⟨g, hgDegree, hgDistance⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  have hbound :
      (∑ i ∈ Finset.range (k - r), Nat.choose n i) +
          degreeBandSum n r (k - r - 1) ≤ hammingWeight (f + g) := by
    by_cases hgZero : g = 0
    · exact hconstantBound g (Or.inl hgZero)
    · by_cases hgOne : g = 1
      · exact hconstantBound g (Or.inr hgOne)
      · exact degreeBand_lowerBound_hammingWeight_add_of_nonconstant
          f g hgZero hgOne r k hgDegree hrn rfl (by
            dsimp [k]
            exact hrAI)
  rw [← hbandEq]
  calc
    (∑ i ∈ Finset.range (algebraicImmunity f - r), Nat.choose n i) +
        degreeBandSum n r (k - r - 1) ≤ hammingWeight (f + g) := by
      simpa [k] using hbound
    _ = hammingDistance f g :=
      (hammingDistance_eq_hammingWeight_add f g).symm
    _ = higherOrderNonlinearity r f := hgDistance


end CryptBoolean
