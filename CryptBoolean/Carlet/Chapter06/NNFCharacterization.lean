/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FourierNNF
public import CryptBoolean.Carlet.Chapter06.WalshCongruence
public import FABL.Chapter06.F₂Polynomials.FourierToF₂Polynomial
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Algebra.Ring.Parity

/-!
# Numerical normal form characterization of bent functions

Carlet Proposition 23: divisibility and top-coefficient congruence conditions
on the integral numerical normal form of a bent Boolean function.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem modEq_sub_two_mul_iff_of_double
    (m t d b : ℤ) (hm : m = 2 * t) (hd : 2 * m ∣ d) :
    Int.ModEq (2 * m) (d - 2 * b) m ↔ Int.ModEq m b t := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  constructor
  · intro h
    have hplus : 2 * m ∣ m + 2 * b := by
      have hadd := dvd_add h hd
      have heq : m - (d - 2 * b) + d = m + 2 * b := by ring
      rwa [heq] at hadd
    have hcancel : m ∣ t + b := by
      have heq : m + 2 * b = 2 * (t + b) := by rw [hm]; ring
      rw [heq] at hplus
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hplus
    have hdouble : m ∣ 2 * t := by
      rw [hm]
    have hdiff := dvd_sub hdouble hcancel
    have heq : 2 * t - (t + b) = t - b := by ring
    rwa [heq] at hdiff
  · intro h
    have hdouble : m ∣ 2 * t := by
      rw [hm]
    have hplus : m ∣ t + b := by
      have hdiff := dvd_sub hdouble h
      have heq : 2 * t - (t - b) = t + b := by ring
      rwa [heq] at hdiff
    have htwice : 2 * m ∣ 2 * (t + b) := by
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mpr hplus
    have hbase : 2 * m ∣ m + 2 * b := by
      have heq : 2 * (t + b) = m + 2 * b := by rw [hm]; ring
      rwa [heq] at htwice
    have hdiff := dvd_sub hbase hd
    have heq : m + 2 * b - d = m - (d - 2 * b) := by ring
    rwa [heq] at hdiff

private theorem modEq_neg_one_pow_mul_half
    (m t z : ℤ) (hm : m = 2 * t) (hz : Int.ModEq m z t) (k : ℕ) :
    Int.ModEq m ((-1 : ℤ) ^ k * z) t := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul]
    exact hz
  · rw [hk.neg_one_pow, neg_one_mul, Int.modEq_iff_dvd]
    rw [Int.modEq_iff_dvd] at hz
    have hdouble : m ∣ 2 * t := by rw [hm]
    have hsum := dvd_sub hdouble hz
    have heq : 2 * t - (t - z) = t - -z := by ring
    rwa [heq] at hsum

/-- The integral Fourier coefficient obtained from the integral numerical
normal form by Carlet Relation (30). -/
noncomputable def booleanNNFFourierCoeffInt
    (f : BooleanFunction n) (u : FABL.F₂Cube n) : ℤ :=
  (-1 : ℤ) ^ (FABL.f₂Support u).card *
    ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
      FABL.f₂Support u ⊆ S),
      (2 : ℤ) ^ (n - S.card) * FABL.booleanNumericalCoeffInt f S

/-- The integral NNF Fourier coefficient is the raw Fourier transform of the
zero-one embedding. -/
theorem booleanNNFFourierCoeffInt_cast
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (booleanNNFFourierCoeffInt f u : ℝ) =
      rawFourierTransform (FABL.booleanRealEmbedding f) u := by
  classical
  rw [← FABL.numericalEval_numericalCoeff (FABL.booleanRealEmbedding f),
    rawFourierTransform_numericalEval]
  simp only [booleanNNFFourierCoeffInt, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_sum, Int.cast_ofNat,
    FABL.numericalCoeff_booleanRealEmbedding_eq_intCast]

private theorem signed_booleanNNFFourierCoeffInt_eq_sum_Ici
    (f : BooleanFunction n) (U : Finset (Fin n)) :
    (-1 : ℤ) ^ U.card *
        booleanNNFFourierCoeffInt f (FABL.f₂CubeOfFinset U) =
      ∑ S ∈ Finset.Ici U,
        (2 : ℤ) ^ (n - S.card) * FABL.booleanNumericalCoeffInt f S := by
  classical
  have hsupport :
      FABL.f₂Support (FABL.f₂CubeOfFinset U) = U :=
    (FABL.f₂CubeEquivFinset n).right_inv U
  rw [booleanNNFFourierCoeffInt, hsupport]
  have hsign : (-1 : ℤ) ^ U.card * (-1 : ℤ) ^ U.card = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hsign, one_mul]
  apply Finset.sum_congr
  · ext S
    simp
  · intro S _hS
    rfl

private theorem walshTransform_cast_eq_rawFourierTransform_sub_two_mul_nnf
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (walshTransform f u : ℝ) =
      rawFourierTransform (fun _ ↦ 1) u -
        2 * rawFourierTransform (FABL.booleanRealEmbedding f) u := by
  calc
    (walshTransform f u : ℝ) = rawFourierTransform (realSignView f) u := by
      simpa [rawFourierTransform] using
        walshTransform_cast_eq_sum_realSignView_mul_character f u
    _ = rawFourierTransform
        (fun x ↦ 1 - 2 * FABL.booleanRealEmbedding f x) u := by
      congr 1
      funext x
      by_cases hx : f x = 0
      · simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, FABL.booleanRealEmbedding, hx]
      · have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hx
        simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, FABL.booleanRealEmbedding, hxOne]
        norm_num
    _ = rawFourierTransform (fun _ ↦ 1) u -
        2 * rawFourierTransform (FABL.booleanRealEmbedding f) u := by
      rw [rawFourierTransform, rawFourierTransform, rawFourierTransform,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      ring

/-- The Walsh transform is the constant Fourier coefficient minus twice the
integral zero-one Fourier coefficient. -/
theorem walshTransform_eq_indicator_sub_two_mul_booleanNNFFourierCoeffInt
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    walshTransform f u =
      (if u = 0 then (2 : ℤ) ^ n else 0) -
        2 * booleanNNFFourierCoeffInt f u := by
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_cast_eq_rawFourierTransform_sub_two_mul_nnf,
    ← booleanNNFFourierCoeffInt_cast, rawFourierTransform_one]
  by_cases hu : u = 0 <;> simp [hu]

/-- Carlet Lemma 2 in the equivalent zero-one Fourier normalization. -/
theorem isBent_iff_forall_booleanNNFFourierCoeffInt_modeq
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n) :
    IsBent f ↔
      ∀ u : FABL.F₂Cube n,
        Int.ModEq ((2 : ℤ) ^ (n / 2))
          (booleanNNFFourierCoeffInt f u)
          ((2 : ℤ) ^ (n / 2 - 1)) := by
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hhalfPos : 1 ≤ n / 2 := by omega
  have hdouble : (2 : ℤ) ^ (n / 2) =
      2 * (2 : ℤ) ^ (n / 2 - 1) := by
    conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [isBent_iff_forall_walshTransform_modeq f hn hnTwo]
  constructor
  · intro h u
    have hdelta :
        2 * (2 : ℤ) ^ (n / 2) ∣
          if u = 0 then (2 : ℤ) ^ n else 0 := by
      by_cases hu : u = 0
      · rw [if_pos hu]
        have hle : n / 2 + 1 ≤ n := by omega
        simpa [pow_succ, mul_comm] using
          (pow_dvd_pow (2 : ℤ) hle)
      · simp [hu]
    have hw := h u
    rw [walshTransform_eq_indicator_sub_two_mul_booleanNNFFourierCoeffInt]
      at hw
    have hw' :
        Int.ModEq (2 * (2 : ℤ) ^ (n / 2))
          ((if u = 0 then (2 : ℤ) ^ n else 0) -
            2 * booleanNNFFourierCoeffInt f u)
          ((2 : ℤ) ^ (n / 2)) := by
      simpa [pow_succ, mul_comm] using hw
    exact (modEq_sub_two_mul_iff_of_double
      ((2 : ℤ) ^ (n / 2)) ((2 : ℤ) ^ (n / 2 - 1))
      (if u = 0 then (2 : ℤ) ^ n else 0)
      (booleanNNFFourierCoeffInt f u) hdouble hdelta).mp hw'
  · intro h u
    have hdelta :
        2 * (2 : ℤ) ^ (n / 2) ∣
          if u = 0 then (2 : ℤ) ^ n else 0 := by
      by_cases hu : u = 0
      · rw [if_pos hu]
        have hle : n / 2 + 1 ≤ n := by omega
        simpa [pow_succ, mul_comm] using
          (pow_dvd_pow (2 : ℤ) hle)
      · simp [hu]
    have hw := (modEq_sub_two_mul_iff_of_double
      ((2 : ℤ) ^ (n / 2)) ((2 : ℤ) ^ (n / 2 - 1))
      (if u = 0 then (2 : ℤ) ^ n else 0)
      (booleanNNFFourierCoeffInt f u) hdouble hdelta).mpr (h u)
    rw [walshTransform_eq_indicator_sub_two_mul_booleanNNFFourierCoeffInt]
    simpa [pow_succ, mul_comm] using hw

/-- The two divisibility conditions of Carlet Proposition 23. -/
def SatisfiesBentNNFCoefficientConditions (f : BooleanFunction n) : Prop :=
  (∀ I : Finset (Fin n),
      n / 2 < I.card → I.card < n →
        (2 : ℤ) ^ (I.card - n / 2) ∣
          FABL.booleanNumericalCoeffInt f I) ∧
    Int.ModEq ((2 : ℤ) ^ (n / 2))
      (FABL.booleanNumericalCoeffInt f Finset.univ)
      ((2 : ℤ) ^ (n / 2 - 1))

private theorem two_pow_half_dvd_weightedCoeff_of_conditions
    (f : BooleanFunction n) (hn : Even n)
    (hf : SatisfiesBentNNFCoefficientConditions f)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    (2 : ℤ) ^ (n / 2) ∣
      (2 : ℤ) ^ (n - S.card) * FABL.booleanNumericalCoeffInt f S := by
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hcardLe : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  by_cases hcard : S.card ≤ n / 2
  · exact (pow_dvd_pow (2 : ℤ) (by omega)).mul_right _
  · have hcardLt : S.card < n := by
      apply lt_of_le_of_ne hcardLe
      intro hcardEq
      apply hS
      apply Finset.eq_univ_of_card S
      simpa using hcardEq
    obtain ⟨z, hz⟩ := hf.1 S (by omega) hcardLt
    refine ⟨z, ?_⟩
    rw [hz, ← mul_assoc, ← pow_add]
    congr 2
    omega

private theorem forall_booleanNNFFourierCoeffInt_modeq_of_conditions
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : SatisfiesBentNNFCoefficientConditions f) :
    ∀ u : FABL.F₂Cube n,
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (booleanNNFFourierCoeffInt f u)
        ((2 : ℤ) ^ (n / 2 - 1)) := by
  intro u
  let U := FABL.f₂Support u
  let a : Finset (Fin n) → ℤ := fun S ↦
    (2 : ℤ) ^ (n - S.card) * FABL.booleanNumericalCoeffInt f S
  have hhalfPos : 1 ≤ n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hdouble : (2 : ℤ) ^ (n / 2) =
      2 * (2 : ℤ) ^ (n / 2 - 1) := by
    conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hcube : FABL.f₂CubeOfFinset U = u := by
    simpa [U] using (FABL.f₂CubeEquivFinset n).symm_apply_apply u
  have hrelation := signed_booleanNNFFourierCoeffInt_eq_sum_Ici f U
  rw [hcube] at hrelation
  change (-1 : ℤ) ^ U.card * booleanNNFFourierCoeffInt f u =
    ∑ S ∈ Finset.Ici U, a S at hrelation
  have huniv : (Finset.univ : Finset (Fin n)) ∈ Finset.Ici U := by simp
  have hdecomp := Finset.sum_erase_add (Finset.Ici U) a huniv
  have hrest : (2 : ℤ) ^ (n / 2) ∣
      ∑ S ∈ (Finset.Ici U).erase Finset.univ, a S := by
    apply Finset.dvd_sum
    intro S hS
    exact two_pow_half_dvd_weightedCoeff_of_conditions f hn hf S
      (Finset.ne_of_mem_erase hS)
  have htop : (2 : ℤ) ^ (n / 2) ∣
      (2 : ℤ) ^ (n / 2 - 1) - a Finset.univ := by
    have htopModeq :
        Int.ModEq ((2 : ℤ) ^ (n / 2))
          (FABL.booleanNumericalCoeffInt f Finset.univ)
          ((2 : ℤ) ^ (n / 2 - 1)) := hf.2
    rw [Int.modEq_iff_dvd] at htopModeq
    simpa [a] using htopModeq
  have hsum : (2 : ℤ) ^ (n / 2) ∣
      (2 : ℤ) ^ (n / 2 - 1) -
        ∑ S ∈ Finset.Ici U, a S := by
    have hdiff := dvd_sub htop hrest
    have heq :
        ((2 : ℤ) ^ (n / 2 - 1) - a Finset.univ) -
            ∑ S ∈ (Finset.Ici U).erase Finset.univ, a S =
          (2 : ℤ) ^ (n / 2 - 1) -
            ∑ S ∈ Finset.Ici U, a S := by
      rw [← hdecomp]
      ring
    rwa [heq] at hdiff
  have hsigned :
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        ((-1 : ℤ) ^ U.card * booleanNNFFourierCoeffInt f u)
        ((2 : ℤ) ^ (n / 2 - 1)) := by
    rw [Int.modEq_iff_dvd, hrelation]
    exact hsum
  have hunsigned := modEq_neg_one_pow_mul_half
    ((2 : ℤ) ^ (n / 2)) ((2 : ℤ) ^ (n / 2 - 1))
    ((-1 : ℤ) ^ U.card * booleanNNFFourierCoeffInt f u)
    hdouble hsigned U.card
  have hsign : (-1 : ℤ) ^ U.card * (-1 : ℤ) ^ U.card = 1 := by
    rw [← mul_pow]
    norm_num
  simpa [← mul_assoc, hsign] using hunsigned

private theorem conditions_of_forall_booleanNNFFourierCoeffInt_modeq
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : ∀ u : FABL.F₂Cube n,
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (booleanNNFFourierCoeffInt f u)
        ((2 : ℤ) ^ (n / 2 - 1))) :
    SatisfiesBentNNFCoefficientConditions f := by
  classical
  let a : Finset (Fin n) → ℤ := fun S ↦
    (2 : ℤ) ^ (n - S.card) * FABL.booleanNumericalCoeffInt f S
  let g : Finset (Fin n) → ℤ := fun U ↦
    (-1 : ℤ) ^ U.card *
      booleanNNFFourierCoeffInt f (FABL.f₂CubeOfFinset U)
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hhalfPos : 1 ≤ n / 2 := by omega
  have hdouble : (2 : ℤ) ^ (n / 2) =
      2 * (2 : ℤ) ^ (n / 2 - 1) := by
    conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hg (U : Finset (Fin n)) :
      Int.ModEq ((2 : ℤ) ^ (n / 2)) (g U)
        ((2 : ℤ) ^ (n / 2 - 1)) := by
    exact modEq_neg_one_pow_mul_half
      ((2 : ℤ) ^ (n / 2)) ((2 : ℤ) ^ (n / 2 - 1))
      (booleanNNFFourierCoeffInt f (FABL.f₂CubeOfFinset U))
      hdouble (hf (FABL.f₂CubeOfFinset U)) U.card
  have hzeta (U : Finset (Fin n)) :
      g U = ∑ S ∈ Finset.Ici U, a S := by
    exact signed_booleanNNFFourierCoeffInt_eq_sum_Ici f U
  have hinversion (I : Finset (Fin n)) :
      a I = ∑ U ∈ Finset.Ici I,
        IncidenceAlgebra.mu ℤ I U * g U :=
    IncidenceAlgebra.moebius_inversion_top a g hzeta I
  have haModeq (I : Finset (Fin n)) :
      Int.ModEq ((2 : ℤ) ^ (n / 2)) (a I)
        (if I = Finset.univ then
          (2 : ℤ) ^ (n / 2 - 1) else 0) := by
    have hterms : (2 : ℤ) ^ (n / 2) ∣
        ∑ U ∈ Finset.Ici I,
          IncidenceAlgebra.mu ℤ I U *
            ((2 : ℤ) ^ (n / 2 - 1) - g U) := by
      apply Finset.dvd_sum
      intro U _hU
      have hU := hg U
      rw [Int.modEq_iff_dvd] at hU
      exact hU.mul_left _
    have hsumEq :
        (∑ U ∈ Finset.Ici I,
            IncidenceAlgebra.mu ℤ I U *
              ((2 : ℤ) ^ (n / 2 - 1) - g U)) =
          (∑ U ∈ Finset.Ici I, IncidenceAlgebra.mu ℤ I U) *
              (2 : ℤ) ^ (n / 2 - 1) -
            ∑ U ∈ Finset.Ici I,
              IncidenceAlgebra.mu ℤ I U * g U := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    have hmu :
        (∑ U ∈ Finset.Ici I, IncidenceAlgebra.mu ℤ I U) =
          if I = Finset.univ then 1 else 0 := by
      have hinterval : Finset.Ici I =
          Finset.Icc I (Finset.univ : Finset (Fin n)) := by
        ext U
        simp
      rw [hinterval]
      exact IncidenceAlgebra.sum_Icc_mu_right I Finset.univ
    rw [hsumEq, hmu, ← hinversion I] at hterms
    rw [Int.modEq_iff_dvd]
    simpa [apply_ite] using hterms
  constructor
  · intro I hIhalf hIn
    have hIne : I ≠ (Finset.univ : Finset (Fin n)) := by
      intro hI
      subst I
      simp at hIn
    have hdivWeighted := haModeq I
    rw [if_neg hIne, Int.modEq_iff_dvd] at hdivWeighted
    have hdivWeighted' : (2 : ℤ) ^ (n / 2) ∣ a I := by
      simpa only [zero_sub, dvd_neg] using hdivWeighted
    have hpow : (2 : ℤ) ^ (n / 2) =
        (2 : ℤ) ^ (n - I.card) *
          (2 : ℤ) ^ (I.card - n / 2) := by
      rw [← pow_add]
      congr 1
      omega
    change (2 : ℤ) ^ (n / 2) ∣
      (2 : ℤ) ^ (n - I.card) *
        FABL.booleanNumericalCoeffInt f I at hdivWeighted'
    rw [hpow] at hdivWeighted'
    exact (mul_dvd_mul_iff_left
      (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0))).mp hdivWeighted'
  · have htop := haModeq (Finset.univ : Finset (Fin n))
    simpa [a] using htop

/-- Carlet Proposition 23: in even dimension at least two, a Boolean function
is bent exactly when its integral numerical normal form satisfies the stated
intermediate divisibility conditions and top-coefficient congruence. -/
theorem isBent_iff_nnfCoefficientConditions
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n) :
    IsBent f ↔ SatisfiesBentNNFCoefficientConditions f := by
  rw [isBent_iff_forall_booleanNNFFourierCoeffInt_modeq f hn hnTwo]
  constructor
  · exact conditions_of_forall_booleanNNFFourierCoeffInt_modeq f hn hnTwo
  · exact forall_booleanNNFFourierCoeffInt_modeq_of_conditions f hn hnTwo

end CryptBoolean
