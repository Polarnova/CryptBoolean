/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.GeneralProperties
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
public import CryptBoolean.Carlet.Chapter05.QuadraticNormalForm

/-!
# Nonlinearity bounds from algebraic immunity

Carlet Chapter 9: the basic ordinary and higher-order nonlinearity bounds and
Lobanov's refinement.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Binomial partial sums are monotone in their truncation bound. -/
theorem sum_choose_range_mono
    (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.range a, Nat.choose n i) ≤
      ∑ i ∈ Finset.range b, Nat.choose n i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hab) (fun _ _ _ ↦ Nat.zero_le _)

/-- The order-`r` nonlinearity is bounded below by the binomial sum strictly
below `AI(f)-r`. -/
theorem sum_choose_below_algebraicImmunity_sub_le_higherOrderNonlinearity
    (r : ℕ) (f : BooleanFunction n) :
    (∑ i ∈ Finset.range (algebraicImmunity f - r), Nat.choose n i) ≤
      higherOrderNonlinearity r f := by
  obtain ⟨g, hgDegree, hdistance⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
  have hAI : algebraicImmunity f - r ≤ algebraicImmunity (f + g) := by
    exact (Nat.sub_le_sub_left hgDegree (algebraicImmunity f)).trans
      (algebraicImmunity_sub_functionAlgebraicDegree_le_add f g)
  calc
    (∑ i ∈ Finset.range (algebraicImmunity f - r), Nat.choose n i) ≤
        ∑ i ∈ Finset.range (algebraicImmunity (f + g)), Nat.choose n i :=
      sum_choose_range_mono n hAI
    _ ≤ hammingWeight (f + g) :=
      sum_choose_below_algebraicImmunity_le_hammingWeight (f + g)
    _ = hammingDistance f g :=
      (hammingDistance_eq_hammingWeight_add f g).symm
    _ = higherOrderNonlinearity r f := hdistance

/-- A positive-dimensional Boolean function has nonlinearity at least the
binomial sum through degree `AI(f)-2`. -/
theorem sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity
    (f : BooleanFunction n) (_hn : 0 < n) :
    (∑ i ∈ Finset.range (algebraicImmunity f - 1), Nat.choose n i) ≤
      nonlinearity f := by
  rw [nonlinearity_eq_higherOrderNonlinearity_one]
  exact sum_choose_below_algebraicImmunity_sub_le_higherOrderNonlinearity 1 f

private theorem exists_affineFunction_normalizing_affineEquiv
    (b : FABL.𝔽₂) (a : FABL.F₂Cube (n + 1)) (ha : a ≠ 0) :
    ∃ E : FABL.F₂Cube (n + 1) ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube (n + 1),
      FABL.affineFunction b a ∘ E = fun x ↦ x 0 := by
  obtain ⟨hn, e, he⟩ := exists_dotProduct_normalizing_linearEquiv a ha
  let i : Fin (n + 1) := ⟨0, hn⟩
  let t : FABL.F₂Cube (n + 1) := Pi.single i b
  let E : FABL.F₂Cube (n + 1) ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube (n + 1) :=
    (AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube (n + 1)) t).trans
      e.toAffineEquiv
  refine ⟨E, ?_⟩
  funext x
  change b + FABL.f₂DotProduct a (E x) = _
  rw [show E x = e (t + x) by rfl, he]
  change b + (b + x i) = _
  rw [← add_assoc, ZModModule.add_self, zero_add]
  exact congrArg x (Fin.ext rfl)

private def firstCoordinateTailLinearMap (n : ℕ) :
    FABL.F₂Cube (n + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def firstCoordinateIndicator
    (b : FABL.𝔽₂) : BooleanFunction (n + 1) :=
  FABL.affineFunction (1 + b) (Pi.single 0 1)

@[simp] private theorem firstCoordinateIndicator_cons
    (b c : FABL.𝔽₂) (x : FABL.F₂Cube n) :
    firstCoordinateIndicator b (Fin.cons c x) = if c = b then 1 else 0 := by
  change 1 + b + FABL.f₂DotProduct (Pi.single 0 1) (Fin.cons c x) = _
  rw [show FABL.f₂DotProduct (Pi.single 0 1) (Fin.cons c x) = c by
    simp [FABL.f₂DotProduct, single_dotProduct]]
  by_cases hcb : c = b
  · rw [if_pos hcb, hcb, add_assoc, ZModModule.add_self, add_zero]
  · rw [if_neg hcb]
    have hsum : b + c = 1 := Fin.eq_one_of_ne_zero _ (by
      intro hzero
      apply hcb
      exact ((eq_neg_of_add_eq_zero_left hzero).trans
        (ZModModule.neg_eq_self c)).symm)
    rw [add_assoc, hsum, ZModModule.add_self]

private def firstCoordinateSliceLift
    (b : FABL.𝔽₂) (q : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun x ↦ firstCoordinateIndicator b x * q (Fin.tail x)

private theorem firstCoordinateSliceLift_ne_zero
    (b : FABL.𝔽₂) {q : BooleanFunction n} (hq : q ≠ 0) :
    firstCoordinateSliceLift b q ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hq
  have hx' : q x ≠ 0 := by simpa using hx
  intro hzero
  have happly := congrFun hzero (Fin.cons b x)
  apply hx'
  simpa [firstCoordinateSliceLift] using happly

private theorem functionAlgebraicDegree_firstCoordinateSliceLift_le
    (b : FABL.𝔽₂) (q : BooleanFunction n) :
    FABL.functionAlgebraicDegree (firstCoordinateSliceLift b q) ≤
      FABL.functionAlgebraicDegree q + 1 := by
  have htail :
      FABL.functionAlgebraicDegree
          (q ∘ (firstCoordinateTailLinearMap n).toAffineMap) ≤
        FABL.functionAlgebraicDegree q :=
    functionAlgebraicDegree_comp_affineMap_le_general q
      (firstCoordinateTailLinearMap n).toAffineMap
  have hindicator :
      FABL.functionAlgebraicDegree
          (firstCoordinateIndicator (n := n) b) ≤ 1 :=
    FABL.functionAlgebraicDegree_affineFunction_le_one _ _
  have hproduct := FABL.functionAlgebraicDegree_mul_le_add
    (firstCoordinateIndicator (n := n) b)
    (q ∘ (firstCoordinateTailLinearMap n).toAffineMap)
  have hlift :
      firstCoordinateSliceLift b q =
        firstCoordinateIndicator b *
          (q ∘ (firstCoordinateTailLinearMap n).toAffineMap) := rfl
  rw [hlift]
  exact hproduct.trans (by omega)

private theorem firstCoordinateSliceLift_isAnnihilator
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂)
    {q : BooleanFunction n} (hq : IsAnnihilator (firstCoordinateSlice f b) q) :
    IsAnnihilator f (firstCoordinateSliceLift b q) := by
  refine ⟨firstCoordinateSliceLift_ne_zero b hq.1, ?_⟩
  funext x
  by_cases hx : x 0 = b
  · rw [← Fin.cons_self_tail x, hx]
    simp only [Pi.mul_apply, firstCoordinateSliceLift,
      firstCoordinateIndicator_cons, if_pos, one_mul]
    exact congrFun hq.2 (Fin.tail x)
  · have hindicator : firstCoordinateIndicator b x = 0 := by
      rw [← Fin.cons_self_tail x, firstCoordinateIndicator_cons, if_neg hx]
    simp [firstCoordinateSliceLift, hindicator]

/-- Restriction to a coordinate hyperplane can lower algebraic immunity by at
most one. -/
theorem algebraicImmunity_le_firstCoordinateSlice_add_one
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂) :
    algebraicImmunity f ≤ algebraicImmunity (firstCoordinateSlice f b) + 1 := by
  obtain ⟨q, hq, hdegree⟩ :=
    exists_witness_functionAlgebraicDegree_eq_algebraicImmunity
      (firstCoordinateSlice f b)
  have hwitness : IsAlgebraicImmunityWitness f
      (firstCoordinateSliceLift b q) := by
    rcases hq with hq | hq
    · exact Or.inl (firstCoordinateSliceLift_isAnnihilator f b hq)
    · right
      have hslice :
          firstCoordinateSlice (f + 1) b = firstCoordinateSlice f b + 1 := by
        funext x
        rfl
      exact firstCoordinateSliceLift_isAnnihilator (f + 1) b
        (by simpa [hslice] using hq)
  calc
    algebraicImmunity f ≤
        FABL.functionAlgebraicDegree (firstCoordinateSliceLift b q) :=
      algebraicImmunity_le_functionAlgebraicDegree f _ hwitness
    _ ≤ FABL.functionAlgebraicDegree q + 1 :=
      functionAlgebraicDegree_firstCoordinateSliceLift_le b q
    _ = algebraicImmunity (firstCoordinateSlice f b) + 1 := by rw [hdegree]

/-- Pascal's identity summed through a strict degree bound. -/
theorem sum_choose_succ_dimension (n k : ℕ) :
    (∑ i ∈ Finset.range k, Nat.choose (n + 1) i) =
      (∑ i ∈ Finset.range k, Nat.choose n i) +
        ∑ i ∈ Finset.range (k - 1), Nat.choose n i := by
  cases k with
  | zero => simp
  | succ k =>
      simp only [Nat.succ_sub_one]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.choose_succ_succ,
        Finset.sum_add_distrib]
      ac_rfl

private theorem two_mul_sum_choose_pred_le_sum_choose_succ_dimension
    (n k : ℕ) :
    2 * (∑ i ∈ Finset.range (k - 1), Nat.choose n i) ≤
      ∑ i ∈ Finset.range k, Nat.choose (n + 1) i := by
  have hmono :
      (∑ i ∈ Finset.range (k - 1), Nat.choose n i) ≤
        ∑ i ∈ Finset.range k, Nat.choose n i :=
    sum_choose_range_mono n (Nat.sub_le k 1)
  rw [sum_choose_succ_dimension]
  omega

private theorem hammingDistance_firstCoordinate_eq_sliceWeights
    (f : BooleanFunction (n + 1)) :
    hammingDistance f (fun x ↦ x 0) =
      hammingWeight (firstCoordinateSlice f 0) +
        hammingWeight (firstCoordinateSlice f 1 + 1) := by
  rw [hammingDistance_eq_hammingWeight_add,
    hammingWeight_firstCoordinateSlices]
  have hzero :
      firstCoordinateSlice (f + fun x ↦ x 0) 0 =
        firstCoordinateSlice f 0 := by
    funext x
    simp [firstCoordinateSlice]
  have hone :
      firstCoordinateSlice (f + fun x ↦ x 0) 1 =
        firstCoordinateSlice f 1 + 1 := by
    funext x
    simp [firstCoordinateSlice]
  rw [hzero, hone]

/-- Lobanov's bound: nonlinearity is at least twice the binomial sum through
degree `AI(f)-2` in one fewer variable. -/
theorem two_mul_sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity
    (f : BooleanFunction n) :
    2 * (∑ i ∈ Finset.range (algebraicImmunity f - 1),
      Nat.choose (n - 1) i) ≤ nonlinearity f := by
  cases n with
  | zero =>
      have hAI : algebraicImmunity f = 0 := by
        have hbound := algebraicImmunity_le_ceiling_half f
        omega
      simp [hAI]
  | succ n =>
      obtain ⟨g, hgDegree, hgDistance⟩ :=
        exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity 1 f
      obtain ⟨b, a, hga⟩ :=
        FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one g hgDegree
      have hdistance :
          hammingDistance f (FABL.affineFunction b a) = nonlinearity f := by
        calc
          hammingDistance f (FABL.affineFunction b a) =
              hammingDistance f g := congrArg (hammingDistance f) hga.symm
          _ = higherOrderNonlinearity 1 f := hgDistance
          _ = nonlinearity f :=
            (nonlinearity_eq_higherOrderNonlinearity_one f).symm
      by_cases ha : a = 0
      · subst a
        have hAIAdd :
            algebraicImmunity (f + FABL.affineFunction b 0) =
              algebraicImmunity f := by
          by_cases hb : b = 0
          · subst b
            have haffine :
                FABL.affineFunction 0 (0 : FABL.F₂Cube (n + 1)) = 0 := by
              funext x
              simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
            rw [haffine, add_zero]
          · have hbOne : b = 1 := Fin.eq_one_of_ne_zero _ hb
            subst b
            have haffine :
                FABL.affineFunction 1 (0 : FABL.F₂Cube (n + 1)) = 1 := by
              funext x
              simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]
            rw [haffine, algebraicImmunity_add_constant_one]
        have hweight :=
          sum_choose_below_algebraicImmunity_le_hammingWeight
            (f + FABL.affineFunction b 0)
        rw [hAIAdd] at hweight
        have hweightDistance :
            hammingWeight (f + FABL.affineFunction b 0) = nonlinearity f := by
          rw [← hammingDistance_eq_hammingWeight_add]
          exact hdistance
        have hcombinatorial :=
          two_mul_sum_choose_pred_le_sum_choose_succ_dimension
            n (algebraicImmunity f)
        simpa using hcombinatorial.trans (hweight.trans_eq hweightDistance)
      · obtain ⟨E, hnormalize⟩ :=
          exists_affineFunction_normalizing_affineEquiv b a ha
        let F : BooleanFunction (n + 1) := f ∘ E
        have hAIF : algebraicImmunity F = algebraicImmunity f :=
          algebraicImmunity_comp_affineEquiv f E
        have hdistanceF :
            hammingDistance F (fun x ↦ x 0) = nonlinearity f := by
          calc
            hammingDistance F (fun x ↦ x 0) =
                hammingDistance (f ∘ E) (FABL.affineFunction b a ∘ E) := by
              rw [hnormalize]
            _ = hammingDistance f (FABL.affineFunction b a) :=
              hammingDistance_comp_affineEquiv f (FABL.affineFunction b a) E
            _ = nonlinearity f := hdistance
        have hsplit :
            nonlinearity f =
              hammingWeight (firstCoordinateSlice F 0) +
                hammingWeight (firstCoordinateSlice F 1 + 1) :=
          hdistanceF.symm.trans
            (hammingDistance_firstCoordinate_eq_sliceWeights F)
        by_cases hweights :
            hammingWeight (firstCoordinateSlice F 0) ≤
              hammingWeight (firstCoordinateSlice F 1 + 1)
        · have htwice :
              2 * hammingWeight (firstCoordinateSlice F 0) ≤
                nonlinearity f := by
            rw [hsplit]
            omega
          have hAI : algebraicImmunity f - 1 ≤
              algebraicImmunity (firstCoordinateSlice F 0) := by
            have hslice :=
              algebraicImmunity_le_firstCoordinateSlice_add_one F 0
            rw [hAIF] at hslice
            omega
          have hsum := sum_choose_range_mono n hAI
          have hweight :=
            sum_choose_below_algebraicImmunity_le_hammingWeight
              (firstCoordinateSlice F 0)
          simpa using
            (Nat.mul_le_mul_left 2 (hsum.trans hweight)).trans htwice
        · have htwice :
              2 * hammingWeight (firstCoordinateSlice F 1 + 1) ≤
                nonlinearity f := by
            rw [hsplit]
            omega
          have hAI : algebraicImmunity f - 1 ≤
              algebraicImmunity (firstCoordinateSlice F 1 + 1) := by
            have hslice :=
              algebraicImmunity_le_firstCoordinateSlice_add_one F 1
            rw [hAIF] at hslice
            rw [algebraicImmunity_add_constant_one]
            omega
          have hsum := sum_choose_range_mono n hAI
          have hweight :=
            sum_choose_below_algebraicImmunity_le_hammingWeight
              (firstCoordinateSlice F 1 + 1)
          simpa using
            (Nat.mul_le_mul_left 2 (hsum.trans hweight)).trans htwice

end CryptBoolean
