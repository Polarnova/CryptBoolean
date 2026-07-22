/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine

/-!
# Carlet Chapter 2 recovery from low-weight restrictions

The Boolean-lattice recovery formula of Carlet, pp. 13--14.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

/-- The coordinatewise support order on the binary cube. -/
def supportPrecedes (y x : FABL.F₂Cube n) : Prop :=
  FABL.f₂Support y ⊆ FABL.f₂Support x

instance supportPrecedesDecidable (y x : FABL.F₂Cube n) :
    Decidable (supportPrecedes y x) := by
  unfold supportPrecedes
  infer_instance

scoped infix:50 " ≼ " => supportPrecedes

/-- Carlet's set `E_d` of binary vectors of Hamming weight at most `d`. -/
def lowWeightInputs (d : ℕ) : Finset (FABL.F₂Cube n) :=
  Finset.univ.filter fun y ↦ (FABL.f₂Support y).card ≤ d

/-- The binomial-parity coefficient in Carlet's restriction-recovery formula. -/
def restrictionRecoveryCoefficient (d : ℕ) (x y : FABL.F₂Cube n) : FABL.𝔽₂ :=
  (∑ i ∈ Finset.range (d - (FABL.f₂Support y).card + 1),
    ((FABL.f₂Support x).card - (FABL.f₂Support y).card).choose i : ℕ)

/-- The number of subsets of `U` of cardinality at most `k`. -/
theorem card_powerset_filter_card_le (U : Finset (Fin n)) (k : ℕ) :
    #(U.powerset.filter fun S ↦ S.card ≤ k) =
      ∑ i ∈ Finset.range (k + 1), U.card.choose i := by
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ S ∈ U.powerset.filter (fun S ↦ S.card ≤ k), 1) =
        ∑ i ∈ Finset.range (k + 1),
          ∑ S ∈ U.powerset.filter (fun S ↦ S.card ≤ k) with S.card = i, 1 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S hS
      rw [Finset.mem_filter] at hS
      simpa using hS.2
    _ = ∑ i ∈ Finset.range (k + 1), U.card.choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.card_eq_sum_ones, ← Finset.card_powersetCard]
      congr 1
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hSU, hSk⟩, hSi⟩
        exact ⟨hSU, hSi⟩
      · rintro ⟨hSU, hSi⟩
        have hik : i ≤ k := by simpa using hi
        exact ⟨⟨hSU, hSi.trans_le hik⟩, hSi⟩

/-- The number of intermediate subsets `S` with `T ⊆ S ⊆ U` and `|S| ≤ d`. -/
theorem card_intermediate_subsets_le (T U : Finset (Fin n)) (d : ℕ)
    (hTU : T ⊆ U) (hTd : T.card ≤ d) :
    #(U.powerset.filter fun S ↦ T ⊆ S ∧ S.card ≤ d) =
      ∑ i ∈ Finset.range (d - T.card + 1), (U.card - T.card).choose i := by
  have hcard :
      #(U.powerset.filter fun S ↦ T ⊆ S ∧ S.card ≤ d) =
        #((U \ T).powerset.filter fun R ↦ R.card ≤ d - T.card) := by
    apply Finset.card_bij'
        (fun S _ ↦ S \ T) (fun R _ ↦ T ∪ R)
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      rw [Finset.mem_powerset] at hS ⊢
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hS.1 hx.1, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hS.2.1]
        omega
    · intro R hR
      rw [Finset.mem_filter] at hR ⊢
      rw [Finset.mem_powerset] at hR ⊢
      refine ⟨Finset.union_subset hTU ?_, Finset.subset_union_left, ?_⟩
      · exact hR.1.trans Finset.sdiff_subset
      · have hdisjoint : Disjoint T R :=
          disjoint_of_subset_right hR.1 disjoint_sdiff_self_right
        rw [Finset.card_union_of_disjoint hdisjoint]
        omega
    · intro S hS
      rw [Finset.mem_filter] at hS
      exact Finset.union_sdiff_of_subset hS.2.1
    · intro R hR
      rw [Finset.mem_filter, Finset.mem_powerset] at hR
      exact Finset.union_sdiff_cancel_left
        (disjoint_of_subset_right hR.1 disjoint_sdiff_self_right)
  rw [hcard, card_powerset_filter_card_le, Finset.card_sdiff_of_subset hTU]

/-- Carlet's recovery identity at the indicator vector of a coordinate subset. -/
theorem restrictionRecoveryFormula_f₂CubeOfFinset
    (f : BooleanFunction n) (d : ℕ)
    (hdegree : functionAlgebraicDegree f ≤ d) (U : Finset (Fin n)) :
    f (FABL.f₂CubeOfFinset U) =
      ∑ T ∈ U.powerset,
        if T.card ≤ d then
          f (FABL.f₂CubeOfFinset T) *
            (∑ i ∈ Finset.range (d - T.card + 1),
              (U.card - T.card).choose i : ℕ)
        else 0 := by
  classical
  change algebraicDegree (anfCoeff f) ≤ d at hdegree
  have hzero (S : Finset (Fin n)) (hSd : d < S.card) : anfCoeff f S = 0 := by
    by_contra hne
    have hle := (algebraicDegree_le_iff (anfCoeff f) d).mp hdegree S hne
    omega
  calc
    f (FABL.f₂CubeOfFinset U) =
        anfEval (anfCoeff f) (FABL.f₂CubeOfFinset U) :=
      (congrFun (anfEval_anfCoeff f) (FABL.f₂CubeOfFinset U)).symm
    _ = ∑ S ∈ U.powerset, anfCoeff f S :=
      anfEval_f₂CubeOfFinset (anfCoeff f) U
    _ =
        ∑ S ∈ U.powerset, if S.card ≤ d then anfCoeff f S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hSd : S.card ≤ d
      · rw [if_pos hSd]
      · rw [if_neg hSd, hzero S (by omega)]
    _ = ∑ S ∈ U.powerset,
          if S.card ≤ d then
            ∑ T ∈ S.powerset, f (FABL.f₂CubeOfFinset T)
          else 0 := by
      rfl
    _ = ∑ S ∈ U.powerset,
          ∑ T ∈ U.powerset,
            if T ⊆ S ∧ S.card ≤ d then f (FABL.f₂CubeOfFinset T) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.mem_powerset] at hS
      have hsub : S.powerset = U.powerset.filter (fun T ↦ T ⊆ S) := by
        ext T
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun h ↦ ⟨h.trans hS, h⟩, fun h ↦ h.2⟩
      rw [hsub, Finset.sum_filter]
      by_cases hSd : S.card ≤ d <;> simp [hSd]
    _ = ∑ T ∈ U.powerset,
          ∑ S ∈ U.powerset,
            if T ⊆ S ∧ S.card ≤ d then f (FABL.f₂CubeOfFinset T) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ U.powerset,
          if T.card ≤ d then
            f (FABL.f₂CubeOfFinset T) *
              (∑ i ∈ Finset.range (d - T.card + 1),
                (U.card - T.card).choose i : ℕ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_powerset] at hT
      by_cases hTd : T.card ≤ d
      · rw [if_pos hTd, ← Finset.sum_filter, Finset.sum_const,
          card_intermediate_subsets_le T U d hT hTd, nsmul_eq_mul]
        rw [Nat.cast_sum]
        ring
      · rw [if_neg hTd]
        apply Finset.sum_eq_zero
        intro S _
        by_cases hTS : T ⊆ S
        · have hSd : ¬S.card ≤ d := by
            intro hS
            exact hTd ((Finset.card_le_card hTS).trans hS)
          simp [hTS, hSd]
        · simp [hTS]

/-- Carlet, pp. 13--14: a Boolean function of degree at most `d < n` is
recovered at every input from its values on `E_d`. -/
theorem restrictionRecoveryFormula
    (f : BooleanFunction n) (d : ℕ)
    (hdegree : functionAlgebraicDegree f ≤ d) (_hdn : d < n)
    (x : FABL.F₂Cube n) :
    f x =
      ∑ y ∈ (lowWeightInputs d).filter (fun y ↦ supportPrecedes y x),
        f y * restrictionRecoveryCoefficient d x y := by
  classical
  let U := FABL.f₂Support x
  have hx : FABL.f₂CubeOfFinset U = x := by
    simpa [U] using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
  have hsupport (T : Finset (Fin n)) :
      FABL.f₂Support (FABL.f₂CubeOfFinset T) = T := by
    simpa using (FABL.f₂CubeEquivFinset n).apply_symm_apply T
  have hsum :
      (∑ T ∈ U.powerset.filter (fun T ↦ T.card ≤ d),
          f (FABL.f₂CubeOfFinset T) *
            (∑ i ∈ Finset.range (d - T.card + 1),
              (U.card - T.card).choose i : ℕ)) =
        ∑ y ∈ (lowWeightInputs d).filter (fun y ↦ supportPrecedes y x),
          f y * restrictionRecoveryCoefficient d x y := by
    apply Finset.sum_bij (fun T _ ↦ FABL.f₂CubeOfFinset T)
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      simp only [Finset.mem_filter, lowWeightInputs, Finset.mem_univ, true_and,
        supportPrecedes, hsupport]
      exact ⟨hT.2, by simpa [U] using hT.1⟩
    · intro T₁ _ T₂ _ h
      exact (FABL.f₂CubeEquivFinset n).symm.injective h
    · intro y hy
      simp only [Finset.mem_filter, lowWeightInputs, Finset.mem_univ, true_and] at hy
      refine ⟨FABL.f₂Support y, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨by simpa [supportPrecedes, U] using hy.2, hy.1⟩
      · simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply y
    · intro T hT
      simp only [restrictionRecoveryCoefficient, hsupport, U]
  calc
    f x = f (FABL.f₂CubeOfFinset U) := (congrArg f hx).symm
    _ = ∑ T ∈ U.powerset,
          if T.card ≤ d then
            f (FABL.f₂CubeOfFinset T) *
              (∑ i ∈ Finset.range (d - T.card + 1),
                (U.card - T.card).choose i : ℕ)
          else 0 := restrictionRecoveryFormula_f₂CubeOfFinset f d hdegree U
    _ = ∑ T ∈ U.powerset.filter (fun T ↦ T.card ≤ d),
          f (FABL.f₂CubeOfFinset T) *
            (∑ i ∈ Finset.range (d - T.card + 1),
              (U.card - T.card).choose i : ℕ) := by
      rw [Finset.sum_filter]
    _ = _ := hsum

/-- Values on `E_d` uniquely determine a Boolean function of degree at most `d < n`. -/
theorem eq_of_eq_on_lowWeightInputs
    (f g : BooleanFunction n) (d : ℕ)
    (hf : functionAlgebraicDegree f ≤ d)
    (hg : functionAlgebraicDegree g ≤ d) (hdn : d < n)
    (hfg : ∀ y ∈ lowWeightInputs d, f y = g y) :
    f = g := by
  funext x
  rw [restrictionRecoveryFormula f d hf hdn x,
    restrictionRecoveryFormula g d hg hdn x]
  apply Finset.sum_congr rfl
  intro y hy
  rw [hfg y (Finset.mem_filter.mp hy).1]

/-- Values on an affine image of `E_d` uniquely determine a Boolean function
of degree at most `d < n`. -/
theorem eq_of_eq_on_affineImage_lowWeightInputs
    (f g : BooleanFunction n) (d : ℕ)
    (hf : functionAlgebraicDegree f ≤ d)
    (hg : functionAlgebraicDegree g ≤ d) (hdn : d < n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (hfg : ∀ z ∈ (lowWeightInputs d).image (fun y ↦ L y), f z = g z) :
    f = g := by
  have hcomp : (f ∘ L) = (g ∘ L) := by
    apply eq_of_eq_on_lowWeightInputs (f ∘ L) (g ∘ L) d
    · rw [functionAlgebraicDegree_comp_affineEquiv]
      exact hf
    · rw [functionAlgebraicDegree_comp_affineEquiv]
      exact hg
    · exact hdn
    · intro y hy
      exact hfg (L y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  funext x
  have hx := congrFun hcomp (L.symm x)
  simpa using hx

end CryptBoolean
