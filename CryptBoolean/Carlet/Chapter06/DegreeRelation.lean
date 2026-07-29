/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter06.DegreeBounds
public import CryptBoolean.Carlet.Chapter06.DualPoisson
public import CryptBoolean.Carlet.Chapter06.GeometricCharacterization
public import CryptBoolean.Carlet.Chapter06.McElieceAx

import FABL.Chapter05.DegreeOneWeight

/-!
# Algebraic degrees of a bent function and its dual

Carlet Proposition 19 and Relation (47), obtained from Poisson summation
and the McEliece--Ax divisibility theorem.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

attribute [local instance] submoduleFintype

private theorem two_le_functionAlgebraicDegree_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) (hn : 2 ≤ n) :
    2 ≤ FABL.functionAlgebraicDegree f := by
  by_contra hnot
  have hdegreeOne : FABL.functionAlgebraicDegree f ≤ 1 := by omega
  obtain ⟨b, a, hfa⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one f hdegreeOne
  have hnonlinearity := nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent f hf hn
  rw [hfa, nonlinearity_affineFunction] at hnonlinearity
  have hhalfLt : n / 2 - 1 < n - 1 := by
    have heven := even_of_isBent f hf
    rcases heven with ⟨k, hk⟩
    omega
  have hpowLt : 2 ^ (n / 2 - 1) < 2 ^ (n - 1) :=
    Nat.pow_lt_pow_right (by omega) hhalfLt
  omega

private noncomputable def perpendicularCoordinateZeroSubspacePowersetEquiv
    (I : Finset (Fin n)) :
    FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace I) ≃
      ↥I.powerset :=
  Equiv.subtypeEquiv (FABL.f₂CubeEquivFinset n) fun x ↦ by
    rw [FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset,
      Finset.mem_powerset, FABL.f₂CubeEquivFinset_apply]

private theorem sum_bitSignInt_perpendicular_coordinateZeroSubspace_eq_powerset
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    (∑ x : FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace I),
        bitSignInt (f x.1)) =
      ∑ T ∈ I.powerset, bitSignInt (f (FABL.f₂CubeOfFinset T)) := by
  classical
  calc
    (∑ x : FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace I),
        bitSignInt (f x.1)) =
        ∑ T : ↥I.powerset,
          bitSignInt (f (FABL.f₂CubeOfFinset T.1)) := by
      apply Fintype.sum_equiv
        (perpendicularCoordinateZeroSubspacePowersetEquiv I)
      intro x
      congr 2
      simpa [perpendicularCoordinateZeroSubspacePowersetEquiv] using
        (FABL.f₂CubeEquivFinset n).symm_apply_apply x.1 |>.symm
    _ = ∑ T ∈ I.powerset,
          bitSignInt (f (FABL.f₂CubeOfFinset T)) := by
      symm
      exact Finset.sum_subtype I.powerset (fun T ↦ Iff.rfl)
        (fun T ↦ bitSignInt (f (FABL.f₂CubeOfFinset T)))

private def anfPowersetOneCount
    (f : BooleanFunction n) (I : Finset (Fin n)) : ℕ :=
  (I.powerset.filter fun T ↦ f (FABL.f₂CubeOfFinset T) = 1).card

private theorem odd_anfPowersetOneCount_of_anfCoeff_ne_zero
    (f : BooleanFunction n) (I : Finset (Fin n))
    (hcoeff : FABL.anfCoeff f I ≠ 0) :
    Odd (anfPowersetOneCount f I) := by
  classical
  have hcast : ((anfPowersetOneCount f I : ℕ) : FABL.𝔽₂) =
      FABL.anfCoeff f I := by
    rw [anfPowersetOneCount, Finset.card_filter]
    change ((∑ T ∈ I.powerset,
      if f (FABL.f₂CubeOfFinset T) = 1 then 1 else 0 : ℕ) : FABL.𝔽₂) = _
    push_cast
    rw [FABL.anfCoeff]
    apply Finset.sum_congr rfl
    intro T _hT
    by_cases hTzero : f (FABL.f₂CubeOfFinset T) = 0
    · simp [hTzero]
    · have hTone : f (FABL.f₂CubeOfFinset T) = 1 :=
        Fin.eq_one_of_ne_zero _ hTzero
      simp [hTone]
  rw [← ZMod.natCast_ne_zero_iff_odd]
  simpa [hcast] using hcoeff

private theorem sum_bitSignInt_powerset_eq
    (f : BooleanFunction n) (I : Finset (Fin n)) :
    (∑ T ∈ I.powerset, bitSignInt (f (FABL.f₂CubeOfFinset T))) =
      (2 : ℤ) ^ I.card - 2 * (anfPowersetOneCount f I : ℤ) := by
  classical
  simp_rw [bitSignInt_eq_one_sub_two_mul_bitValueInt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_powerset,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  have hcount :
      (∑ T ∈ I.powerset, bitValueInt (f (FABL.f₂CubeOfFinset T))) =
        (anfPowersetOneCount f I : ℤ) := by
    rw [anfPowersetOneCount, Finset.card_filter]
    change (∑ T ∈ I.powerset, bitValueInt (f (FABL.f₂CubeOfFinset T))) =
      ((∑ T ∈ I.powerset,
        if f (FABL.f₂CubeOfFinset T) = 1 then 1 else 0 : ℕ) : ℤ)
    push_cast
    apply Finset.sum_congr rfl
    intro T _hT
    by_cases hTone : f (FABL.f₂CubeOfFinset T) = 1 <;>
      simp [bitValueInt, hTone]
  rw [hcount]
  norm_num

private theorem exact_two_divisibility_perpendicular_coordinateZeroSubspace
    (f : BooleanFunction n) (I : Finset (Fin n))
    (hcoeff : FABL.anfCoeff f I ≠ 0) (hIcard : 2 ≤ I.card) :
    ((2 : ℤ) ∣ ∑ x : FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace I), bitSignInt (f x.1)) ∧
      ¬((4 : ℤ) ∣ ∑ x : FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace I), bitSignInt (f x.1)) := by
  classical
  let w := anfPowersetOneCount f I
  have hodd : Odd w := odd_anfPowersetOneCount_of_anfCoeff_ne_zero f I hcoeff
  have hsum :
      (∑ x : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace I), bitSignInt (f x.1)) =
        (2 : ℤ) ^ I.card - 2 * (w : ℤ) := by
    rw [sum_bitSignInt_perpendicular_coordinateZeroSubspace_eq_powerset,
      sum_bitSignInt_powerset_eq]
  have hpowTwo : (2 : ℤ) ^ I.card =
      2 * (2 : ℤ) ^ (I.card - 1) := by
    conv_lhs =>
      rw [show I.card = (I.card - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hpowFour : (2 : ℤ) ^ I.card =
      4 * (2 : ℤ) ^ (I.card - 2) := by
    conv_lhs =>
      rw [show I.card = (I.card - 2) + 2 by omega]
    rw [pow_add]
    norm_num
    ring
  constructor
  · refine ⟨(2 : ℤ) ^ (I.card - 1) - (w : ℤ), ?_⟩
    rw [hsum, hpowTwo]
    ring
  · rintro ⟨z, hz⟩
    obtain ⟨q, hq⟩ := hodd
    have hqInt : (w : ℤ) = 2 * (q : ℤ) + 1 := by
      exact_mod_cast hq
    rw [hsum, hpowFour, hqInt] at hz
    omega

private theorem bentDual_sum_coordinateZeroSubspace
    (f : BooleanFunction n) (hf : IsBent f) (I : Finset (Fin n))
    (hIhalf : I.card ≤ n / 2) :
    (∑ u : FABL.F₂DecisionTree.coordinateZeroSubspace I,
        bitSignInt (bentDual f u.1)) =
      (2 : ℤ) ^ (n / 2 - I.card) *
        ∑ x : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace I),
            bitSignInt (f x.1) := by
  classical
  let E := FABL.F₂DecisionTree.coordinateZeroSubspace I
  have heven := even_of_isBent f hf
  have hsplit : n = n / 2 + n / 2 := by
    rcases heven with ⟨k, hk⟩
    omega
  have hfinrank : Module.finrank FABL.𝔽₂ E = n - I.card := by
    simpa [E] using finrank_coordinateZeroSubspace I
  have hscalar :
      ((2 : ℝ) ^ (n / 2))⁻¹ * (Fintype.card E : ℝ) =
        (2 : ℝ) ^ (n / 2 - I.card) := by
    rw [← Nat.card_eq_fintype_card,
      FABL.card_submodule_eq_two_pow_finrank, hfinrank]
    push_cast
    rw [show n - I.card = n / 2 + (n / 2 - I.card) by omega,
      pow_add]
    field_simp
  have hpoisson := bentDual_poissonSummationFormula f hf E 0 0
  have hreal :
      (∑ u : E, realSignView (bentDual f) u.1) =
        (2 : ℝ) ^ (n / 2 - I.card) *
          ∑ x : FABL.perpendicularSubspace E, realSignView f x.1 := by
    simpa [hscalar] using hpoisson
  apply Int.cast_injective (α := ℝ)
  push_cast
  simpa [E, bitSignInt_cast_eq_realSignView] using hreal

private theorem two_pow_ceilDiv_dualDegree_dvd_coordinateZeroSubspace_sum
    (f : BooleanFunction n) (hf : IsBent f) (hn : 2 ≤ n)
    (I : Finset (Fin n)) :
    (2 : ℤ) ^ ((n - I.card) ⌈/⌉
        FABL.functionAlgebraicDegree (bentDual f)) ∣
      ∑ u : FABL.F₂DecisionTree.coordinateZeroSubspace I,
        bitSignInt (bentDual f u.1) := by
  classical
  let E := FABL.F₂DecisionTree.coordinateZeroSubspace I
  have hfinrank : Module.finrank FABL.𝔽₂ E = n - I.card := by
    simpa [E] using finrank_coordinateZeroSubspace I
  let e : FABL.F₂Cube (n - I.card) ≃ₗ[FABL.𝔽₂] E :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card]
      simpa using hfinrank.symm)
  let L : FABL.F₂Cube (n - I.card) →ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
    E.subtype.comp e.toLinearMap
  let g : BooleanFunction (n - I.card) := fun y ↦ bentDual f (L y)
  have hdegree : FABL.functionAlgebraicDegree g ≤
      FABL.functionAlgebraicDegree (bentDual f) := by
    simpa [g, L, Function.comp_def] using
      (functionAlgebraicDegree_comp_affineMap_le_general
        (bentDual f) L.toAffineMap)
  have hdegreePos : 0 < FABL.functionAlgebraicDegree (bentDual f) :=
    (two_le_functionAlgebraicDegree_of_isBent
      (bentDual f) (isBent_bentDual f hf) hn).trans_lt' (by omega)
  have hdiv := two_pow_ceilDiv_dvd_booleanCharacterSum_of_degree_le
    g (FABL.functionAlgebraicDegree (bentDual f)) hdegreePos hdegree
  have hsum : (∑ y, bitSignInt (g y)) =
      ∑ u : E, bitSignInt (bentDual f u.1) := by
    simpa [g, L] using
      (Equiv.sum_comp e.toEquiv (fun u : E ↦ bitSignInt (bentDual f u.1)))
  rw [hsum] at hdiv
  exact hdiv

private theorem exponent_le_of_two_pow_dvd_mul_of_not_four_dvd
    (q s : ℕ) (R L : ℤ)
    (hL : L = (2 : ℤ) ^ s * R)
    (hdiv : (2 : ℤ) ^ q ∣ L)
    (hnotFour : ¬(4 : ℤ) ∣ R) :
    q ≤ s + 1 := by
  by_contra hnot
  have hsTwo : s + 2 ≤ q := by omega
  have hhigh : (2 : ℤ) ^ (s + 2) ∣ L :=
    (pow_dvd_pow (2 : ℤ) hsTwo).trans hdiv
  apply hnotFour
  obtain ⟨z, hz⟩ := hhigh
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ (by positivity : (2 : ℤ) ^ s ≠ 0)
  calc
    (2 : ℤ) ^ s * R = L := hL.symm
    _ = (2 : ℤ) ^ (s + 2) * z := hz
    _ = (2 : ℤ) ^ s * (4 * z) := by
      rw [pow_add]
      norm_num
      ring

private theorem ceilDiv_dualDegree_le_half_sub_degree_add_one
    (f : BooleanFunction n) (hf : IsBent f) (hn : 2 ≤ n) :
    (n - FABL.functionAlgebraicDegree f) ⌈/⌉
        FABL.functionAlgebraicDegree (bentDual f) ≤
      n / 2 - FABL.functionAlgebraicDegree f + 1 := by
  have heven := even_of_isBent f hf
  by_cases hnFour : 4 ≤ n
  · have hfDegreeTwo := two_le_functionAlgebraicDegree_of_isBent f hf hn
    have hfNe : f ≠ 0 := by
      intro hfZero
      subst f
      simp at hfDegreeTwo
    obtain ⟨I, hcoeff, hIdegree⟩ := FABL.exists_top_anfCoeff f hfNe
    have hIhalf : I.card ≤ n / 2 := by
      rw [hIdegree]
      exact functionAlgebraicDegree_le_half_of_isBent f hf hnFour
    have hL := bentDual_sum_coordinateZeroSubspace f hf I hIhalf
    have hdiv :=
      two_pow_ceilDiv_dualDegree_dvd_coordinateZeroSubspace_sum f hf hn I
    have hvaluation :=
      exact_two_divisibility_perpendicular_coordinateZeroSubspace
        f I hcoeff (by simpa [hIdegree] using hfDegreeTwo)
    have hbound := exponent_le_of_two_pow_dvd_mul_of_not_four_dvd
      ((n - I.card) ⌈/⌉ FABL.functionAlgebraicDegree (bentDual f))
      (n / 2 - I.card)
      (∑ x : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace I), bitSignInt (f x.1))
      (∑ u : FABL.F₂DecisionTree.coordinateZeroSubspace I,
          bitSignInt (bentDual f u.1))
      hL hdiv hvaluation.2
    simpa [hIdegree] using hbound
  · have hnTwo : n = 2 := by
      rcases heven with ⟨k, hk⟩
      omega
    subst n
    rw [functionAlgebraicDegree_eq_two_of_isBent f hf,
      functionAlgebraicDegree_eq_two_of_isBent
        (bentDual f) (isBent_bentDual f hf)]
    norm_num

private theorem relation47_of_ceilDiv_le
    (n d dualDegree : ℕ)
    (hnEven : Even n)
    (hdHalf : d ≤ n / 2)
    (hdualTwo : 2 ≤ dualDegree)
    (hceil : (n - d) ⌈/⌉ dualDegree ≤ n / 2 - d + 1) :
    ((n : ℚ) / 2 - (d : ℚ)) ≥
      (((n : ℚ) / 2 - (dualDegree : ℚ)) /
        ((dualDegree : ℚ) - 1)) := by
  have hdualPos : 0 < dualDegree := by omega
  have hmulNat : n - d ≤ dualDegree * (n / 2 - d + 1) :=
    (ceilDiv_le_iff_le_mul hdualPos).mp hceil
  have hsplit : n = n / 2 + n / 2 := by
    rcases hnEven with ⟨k, hk⟩
    omega
  have hdn : d ≤ n := hdHalf.trans (Nat.div_le_self n 2)
  have hmulQ :
      ((n : ℚ) - (d : ℚ)) ≤
        (dualDegree : ℚ) *
          (((n / 2 : ℕ) : ℚ) - (d : ℚ) + 1) := by
    have hcast : ((n - d : ℕ) : ℚ) ≤
        ((dualDegree * (n / 2 - d + 1) : ℕ) : ℚ) := by
      exact_mod_cast hmulNat
    simpa [Nat.cast_sub hdn, Nat.cast_sub hdHalf] using hcast
  have hsplitQ : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) := by
    have hcast : (n : ℚ) =
        ((n / 2 : ℕ) : ℚ) + ((n / 2 : ℕ) : ℚ) := by
      exact_mod_cast hsplit
    linarith
  have hhalfQ : (n : ℚ) / 2 = ((n / 2 : ℕ) : ℚ) := by
    rw [hsplitQ]
    ring
  have hproductQ :
      ((n / 2 : ℕ) : ℚ) - (dualDegree : ℚ) ≤
        (((n / 2 : ℕ) : ℚ) - (d : ℚ)) *
          ((dualDegree : ℚ) - 1) := by
    nlinarith [hmulQ, hsplitQ]
  have hdualTwoQ : (2 : ℚ) ≤ (dualDegree : ℚ) := by
    exact_mod_cast hdualTwo
  have hdenom : (0 : ℚ) < (dualDegree : ℚ) - 1 := by
    linarith
  apply (div_le_iff₀ hdenom).2
  rwa [hhalfQ]

/-- Carlet Proposition 19, Relation (47): if `f` is bent in positive even
dimension, then the algebraic degrees of `f` and its dual satisfy
`n / 2 - deg(f) ≥ (n / 2 - deg(f̃)) / (deg(f̃) - 1)`. -/
theorem bentDual_functionAlgebraicDegree_relation
    (f : BooleanFunction n) (hf : IsBent f) (hn : 2 ≤ n) :
    (n : ℚ) / 2 - (FABL.functionAlgebraicDegree f : ℚ) ≥
      ((n : ℚ) / 2 -
          (FABL.functionAlgebraicDegree (bentDual f) : ℚ)) /
        ((FABL.functionAlgebraicDegree (bentDual f) : ℚ) - 1) := by
  have heven := even_of_isBent f hf
  by_cases hnFour : 4 ≤ n
  · let d := FABL.functionAlgebraicDegree f
    let dDual := FABL.functionAlgebraicDegree (bentDual f)
    have hdLe : d ≤ n / 2 :=
      functionAlgebraicDegree_le_half_of_isBent f hf hnFour
    have hdDualTwo : 2 ≤ dDual :=
      two_le_functionAlgebraicDegree_of_isBent
        (bentDual f) (isBent_bentDual f hf) hn
    have hceil := ceilDiv_dualDegree_le_half_sub_degree_add_one f hf hn
    exact relation47_of_ceilDiv_le n d dDual heven hdLe hdDualTwo
      (by simpa [d, dDual] using hceil)
  · have hnTwo : n = 2 := by
      rcases heven with ⟨k, hk⟩
      omega
    subst n
    rw [functionAlgebraicDegree_eq_two_of_isBent f hf,
      functionAlgebraicDegree_eq_two_of_isBent
        (bentDual f) (isBent_bentDual f hf)]
    norm_num

end CryptBoolean
