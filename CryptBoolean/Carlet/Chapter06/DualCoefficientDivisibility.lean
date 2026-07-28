/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.DualNNF
public import CryptBoolean.Carlet.Chapter06.NNFCharacterization

/-!
# Numerical and algebraic coefficients of the bent dual

Carlet Proposition 17 and the complementary half-degree ANF coefficient
relation between a bent function and its dual.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem nnfCoefficient_divisibility_of_isBent
    (f : BooleanFunction n) (hf : IsBent f)
    (I : Finset (Fin n)) (hI : I ≠ Finset.univ)
    (hIhalf : n / 2 < I.card) :
    (2 : ℤ) ^ (I.card - n / 2) ∣
      FABL.booleanNumericalCoeffInt f I := by
  have hIcardLe : I.card ≤ n := by
    simpa using Finset.card_le_univ I
  have hIcardLt : I.card < n := by
    apply lt_of_le_of_ne hIcardLe
    intro hcard
    apply hI
    apply Finset.eq_univ_of_card
    simpa using hcard
  have hnTwo : 2 ≤ n := by omega
  exact ((isBent_iff_nnfCoefficientConditions f
    (even_of_isBent f hf) hnTwo).mp hf).1 I hIhalf hIcardLt

/-- Carlet Proposition 17: away from the top monomial, every NNF
coefficient above half dimension has the stated power-of-two divisor, for
both a bent function and its dual. -/
theorem bentDual_and_self_nnfCoefficient_divisibility
    (f : BooleanFunction n) (hf : IsBent f)
    (I : Finset (Fin n)) (hI : I ≠ Finset.univ)
    (hIhalf : n / 2 < I.card) :
    ((2 : ℤ) ^ (I.card - n / 2) ∣
        FABL.booleanNumericalCoeffInt (bentDual f) I) ∧
      ((2 : ℤ) ^ (I.card - n / 2) ∣
        FABL.booleanNumericalCoeffInt f I) := by
  exact ⟨nnfCoefficient_divisibility_of_isBent
      (bentDual f) (isBent_bentDual f hf) I hI hIhalf,
    nnfCoefficient_divisibility_of_isBent f hf I hI hIhalf⟩

private theorem numericalCoeff_rawFourierTransform_numericalEval
    (c : FABL.NumericalCoefficients n) (I : Finset (Fin n)) :
    FABL.numericalCoeff
        (rawFourierTransform (FABL.numericalEval c)) I =
      (-1 : ℝ) ^ I.card *
        ∑ S : Finset (Fin n),
          (2 : ℝ) ^ (I ∩ S).card *
            ((2 : ℝ) ^ (n - S.card) * c S) := by
  classical
  rw [FABL.numericalCoeff_eq_mobius_sum]
  simp_rw [rawFourierTransform_numericalEval]
  have hsupport (T : Finset (Fin n)) :
      FABL.f₂Support (FABL.f₂CubeOfFinset T) = T :=
    (FABL.f₂CubeEquivFinset n).right_inv T
  simp_rw [hsupport]
  simp_rw [mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _hS
  have hsign (T : Finset (Fin n)) (hT : T ∈ I.powerset) :
      (-1 : ℝ) ^ (I.card - T.card) * (-1 : ℝ) ^ T.card =
        (-1 : ℝ) ^ I.card := by
    rw [← pow_add]
    congr 1
    exact Nat.sub_add_cancel
      (Finset.card_le_card (Finset.mem_powerset.mp hT))
  rw [← Finset.sum_filter]
  have hfilter :
      I.powerset.filter (fun T : Finset (Fin n) ↦ T ⊆ S) =
        (I ∩ S).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro h x hx
      exact Finset.mem_inter.mpr ⟨h.1 hx, h.2 hx⟩
    · intro h
      exact ⟨fun x hx ↦ (Finset.mem_inter.mp (h hx)).1,
        fun x hx ↦ (Finset.mem_inter.mp (h hx)).2⟩
  rw [hfilter]
  calc
    ∑ T ∈ (I ∩ S).powerset,
        (-1 : ℝ) ^ (I.card - T.card) *
          ((-1 : ℝ) ^ T.card *
            ((2 : ℝ) ^ (n - S.card) * c S)) =
        ∑ _T ∈ (I ∩ S).powerset,
          (-1 : ℝ) ^ I.card *
            ((2 : ℝ) ^ (n - S.card) * c S) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTI : T ∈ I.powerset := Finset.mem_powerset.mpr
        ((Finset.mem_powerset.mp hT).trans Finset.inter_subset_left)
      rw [← mul_assoc, hsign T hTI]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powerset]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

private theorem numericalCoeff_bentDual_eq_rawFourierTransform
    (f : BooleanFunction n) (hf : IsBent f)
    (I : Finset (Fin n)) (hI : I ≠ ∅) :
    FABL.numericalCoeff
        (FABL.booleanRealEmbedding (bentDual f)) I =
      -((-1 : ℝ) ^ I.card * ((2 : ℝ) ^ (n / 2) / 2)) +
        FABL.numericalCoeff
            (rawFourierTransform (FABL.booleanRealEmbedding f)) I /
          (2 : ℝ) ^ (n / 2) := by
  classical
  have hsupport (T : Finset (Fin n)) :
      FABL.f₂Support (FABL.f₂CubeOfFinset T) = T :=
    (FABL.f₂CubeEquivFinset n).right_inv T
  have hzero (T : Finset (Fin n)) :
      FABL.f₂CubeOfFinset T = 0 ↔ T = ∅ := by
    constructor
    · intro h
      have := congrArg FABL.f₂Support h
      rw [hsupport T] at this
      simpa [FABL.f₂Support] using this
    · intro h
      subst T
      ext i
      simp [FABL.f₂CubeOfFinset_apply]
  have hsign (T : Finset (Fin n)) (hT : T ∈ I.powerset) :
      (-1 : ℝ) ^ (I.card - T.card) * (-1 : ℝ) ^ T.card =
        (-1 : ℝ) ^ I.card := by
    rw [← pow_add]
    congr 1
    exact Nat.sub_add_cancel
      (Finset.card_le_card (Finset.mem_powerset.mp hT))
  have hsign' (T : Finset (Fin n)) (hT : T ∈ I.powerset) :
      (-1 : ℝ) ^ (I.card - T.card) =
        (-1 : ℝ) ^ I.card * (-1 : ℝ) ^ T.card := by
    calc
      (-1 : ℝ) ^ (I.card - T.card) =
          (-1 : ℝ) ^ (I.card - T.card) * 1 := by ring
      _ = (-1 : ℝ) ^ (I.card - T.card) *
          (((-1 : ℝ) ^ T.card) * ((-1 : ℝ) ^ T.card)) := by
        rw [← mul_pow]
        norm_num
      _ = ((-1 : ℝ) ^ (I.card - T.card) *
          (-1 : ℝ) ^ T.card) * (-1 : ℝ) ^ T.card := by ring
      _ = (-1 : ℝ) ^ I.card * (-1 : ℝ) ^ T.card := by
        rw [hsign T hT]
  have hsumSign :
      (∑ T ∈ I.powerset, (-1 : ℝ) ^ (I.card - T.card)) = 0 := by
    calc
      (∑ T ∈ I.powerset, (-1 : ℝ) ^ (I.card - T.card)) =
          ∑ T ∈ I.powerset,
            (-1 : ℝ) ^ I.card * (-1 : ℝ) ^ T.card := by
        apply Finset.sum_congr rfl
        intro T hT
        exact hsign' T hT
      _ = (-1 : ℝ) ^ I.card *
          ∑ T ∈ I.powerset, (-1 : ℝ) ^ T.card := by
        rw [Finset.mul_sum]
      _ = 0 := by
        have hsumZ := Finset.sum_powerset_neg_one_pow_card
          (x := I)
        rw [if_neg hI] at hsumZ
        have hsumR :
            (∑ T ∈ I.powerset, (-1 : ℝ) ^ T.card) = 0 := by
          exact_mod_cast hsumZ
        rw [hsumR, mul_zero]
  rw [FABL.numericalCoeff_eq_mobius_sum]
  simp_rw [booleanRealEmbedding_bentDual_eq_rawFourierTransform f hf]
  simp_rw [hzero]
  have hconst :
      (∑ T ∈ I.powerset,
        (-1 : ℝ) ^ (I.card - T.card) * ((1 : ℝ) / 2)) = 0 := by
    rw [← Finset.sum_mul, hsumSign, zero_mul]
  have hdelta :
      (∑ T ∈ I.powerset,
        (-1 : ℝ) ^ (I.card - T.card) *
          (if T = ∅ then (2 : ℝ) ^ (n / 2) / 2 else 0)) =
        (-1 : ℝ) ^ I.card * ((2 : ℝ) ^ (n / 2) / 2) := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hraw :
      (∑ T ∈ I.powerset,
        (-1 : ℝ) ^ (I.card - T.card) *
          (rawFourierTransform (FABL.booleanRealEmbedding f)
            (FABL.f₂CubeOfFinset T) / (2 : ℝ) ^ (n / 2))) =
        FABL.numericalCoeff
            (rawFourierTransform (FABL.booleanRealEmbedding f)) I /
          (2 : ℝ) ^ (n / 2) := by
    rw [FABL.numericalCoeff_eq_mobius_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro T _hT
    ring
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hconst, hdelta, hraw]
  ring

private theorem numericalCoeff_bentDual_half_eq
    (f : BooleanFunction n) (hf : IsBent f) (hn : 4 ≤ n)
    (I : Finset (Fin n)) (hIcard : I.card = n / 2) :
    FABL.numericalCoeff
        (FABL.booleanRealEmbedding (bentDual f)) I =
      (-1 : ℝ) ^ I.card *
        (-((2 : ℝ) ^ (n / 2 - 1)) +
          ∑ S : Finset (Fin n),
            (2 : ℝ) ^ (n / 2 - (S \ I).card) *
              FABL.numericalCoeff (FABL.booleanRealEmbedding f) S) := by
  classical
  have hsplit : n = n / 2 + n / 2 := by
    rcases even_of_isBent f hf with ⟨k, hk⟩
    omega
  have hhalfTwo : 2 ≤ n / 2 := by omega
  have hI : I ≠ ∅ := by
    intro h
    subst I
    simp at hIcard
    omega
  rw [numericalCoeff_bentDual_eq_rawFourierTransform f hf I hI]
  nth_rewrite 1 [← FABL.numericalEval_numericalCoeff
    (FABL.booleanRealEmbedding f)]
  rw [numericalCoeff_rawFourierTransform_numericalEval
    (c := FABL.numericalCoeff (FABL.booleanRealEmbedding f)) I]
  have hpowHalf : (2 : ℝ) ^ (n / 2) / 2 =
      (2 : ℝ) ^ (n / 2 - 1) := by
    conv_lhs =>
      rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpowHalf]
  have hterm (S : Finset (Fin n)) :
      (2 : ℝ) ^ (I ∩ S).card *
            ((2 : ℝ) ^ (n - S.card) *
              FABL.numericalCoeff (FABL.booleanRealEmbedding f) S) /
          (2 : ℝ) ^ (n / 2) =
        (2 : ℝ) ^ (n / 2 - (S \ I).card) *
          FABL.numericalCoeff (FABL.booleanRealEmbedding f) S := by
    have hScard : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    have hdecomp : (S ∩ I).card + (S \ I).card = S.card := by
      exact Finset.card_inter_add_card_sdiff S I
    have hdiffLe : (S \ I).card ≤ n / 2 := by
      have hsubset : S \ I ⊆ Finset.univ \ I := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
          (Finset.mem_sdiff.mp hx).2⟩
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ I),
        Finset.card_univ, Fintype.card_fin, hIcard] at hcard
      omega
    have hexp :
        (I ∩ S).card + (n - S.card) =
          n / 2 + (n / 2 - (S \ I).card) := by
      rw [Finset.inter_comm] at hdecomp
      omega
    calc
      (2 : ℝ) ^ (I ∩ S).card *
            ((2 : ℝ) ^ (n - S.card) *
              FABL.numericalCoeff (FABL.booleanRealEmbedding f) S) /
          (2 : ℝ) ^ (n / 2) =
          ((2 : ℝ) ^ ((I ∩ S).card + (n - S.card)) /
            (2 : ℝ) ^ (n / 2)) *
              FABL.numericalCoeff (FABL.booleanRealEmbedding f) S := by
        rw [pow_add]
        ring
      _ = (((2 : ℝ) ^ (n / 2) *
            (2 : ℝ) ^ (n / 2 - (S \ I).card)) /
              (2 : ℝ) ^ (n / 2)) *
            FABL.numericalCoeff (FABL.booleanRealEmbedding f) S := by
        rw [hexp, pow_add]
      _ = _ := by
        field_simp
  rw [mul_div_assoc, Finset.sum_div]
  simp_rw [hterm]
  ring

private theorem booleanNumericalCoeffInt_bentDual_half_eq
    (f : BooleanFunction n) (hf : IsBent f) (hn : 4 ≤ n)
    (I : Finset (Fin n)) (hIcard : I.card = n / 2) :
    FABL.booleanNumericalCoeffInt (bentDual f) I =
      (-1 : ℤ) ^ I.card *
        (-((2 : ℤ) ^ (n / 2 - 1)) +
          ∑ S : Finset (Fin n),
            (2 : ℤ) ^ (n / 2 - (S \ I).card) *
              FABL.booleanNumericalCoeffInt f S) := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_neg, Int.cast_pow,
    Int.cast_sum, Int.cast_ofNat]
  simp_rw [← FABL.numericalCoeff_booleanRealEmbedding_eq_intCast]
  simpa using numericalCoeff_bentDual_half_eq f hf hn I hIcard

/-- For a bent function in dimension at least four, the half-degree ANF
coefficient of the dual is the coefficient of the complementary monomial of
the original function. -/
theorem anfCoeff_bentDual_eq_complement_of_card_eq_half
    (f : BooleanFunction n) (hf : IsBent f) (hn : 4 ≤ n)
    (I : Finset (Fin n)) (hIcard : I.card = n / 2) :
    FABL.anfCoeff (bentDual f) I =
      FABL.anfCoeff f (Finset.univ \ I) := by
  rw [← FABL.booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff,
    ← FABL.booleanNumericalCoeffInt_cast_f₂_eq_anfCoeff]
  have hInt := booleanNumericalCoeffInt_bentDual_half_eq
    f hf hn I hIcard
  have hcast := congrArg (fun z : ℤ ↦ (z : FABL.𝔽₂)) hInt
  simp only [Int.cast_mul, Int.cast_add, Int.cast_neg, Int.cast_pow,
    Int.cast_sum, Int.cast_ofNat, Int.cast_one] at hcast
  have hsplit : n = n / 2 + n / 2 := by
    rcases even_of_isBent f hf with ⟨k, hk⟩
    omega
  have hhalfTwo : 2 ≤ n / 2 := by omega
  have htwoPow : (2 : FABL.𝔽₂) ^ (n / 2 - 1) = 0 := by
    rw [show (2 : FABL.𝔽₂) = 0 by decide]
    simp [show n / 2 - 1 ≠ 0 by omega]
  have hsign : (-((1 : FABL.𝔽₂))) ^ I.card = 1 := by
    simp
  rw [hsign, one_mul, htwoPow, neg_zero, zero_add] at hcast
  let J : Finset (Fin n) := Finset.univ \ I
  have hJcard : J.card = n / 2 := by
    dsimp [J]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I),
      Finset.card_univ, Fintype.card_fin, hIcard]
    omega
  have hJdiff : (J \ I).card = n / 2 := by
    rw [show J \ I = J by
      ext x
      simp [J]]
    exact hJcard
  have hconditions := (isBent_iff_nnfCoefficientConditions f
    (even_of_isBent f hf) (by omega)).mp hf
  have hterm (S : Finset (Fin n)) (hS : S ≠ J) :
      (2 : FABL.𝔽₂) ^ (n / 2 - (S \ I).card) *
          (FABL.booleanNumericalCoeffInt f S : FABL.𝔽₂) = 0 := by
    have hdiffSubset : S \ I ⊆ J := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
        (Finset.mem_sdiff.mp hx).2⟩
    have hdiffLe : (S \ I).card ≤ n / 2 := by
      rw [← hJcard]
      exact Finset.card_le_card hdiffSubset
    by_cases hdiffLt : (S \ I).card < n / 2
    · rw [show (2 : FABL.𝔽₂) = 0 by decide]
      simp [show n / 2 - (S \ I).card ≠ 0 by omega]
    · have hdiffEq : (S \ I).card = n / 2 := by omega
      have hsdiffEq : S \ I = J := by
        apply Finset.eq_of_subset_of_card_le hdiffSubset
        rw [hJcard, hdiffEq]
      have hJsubS : J ⊆ S := by
        rw [← hsdiffEq]
        exact Finset.sdiff_subset
      have hJssubS : J ⊂ S := hJsubS.ssubset_of_ne hS.symm
      by_cases hSuniv : S = Finset.univ
      · subst S
        have htop := hconditions.2
        rw [Int.modEq_iff_dvd] at htop
        have htwoHalf : (2 : ℤ) ∣ (2 : ℤ) ^ (n / 2) := by
          simpa using
            (pow_dvd_pow (2 : ℤ) (show 1 ≤ n / 2 by omega))
        have htwoHalfPred : (2 : ℤ) ∣
            (2 : ℤ) ^ (n / 2 - 1) := by
          simpa using
            (pow_dvd_pow (2 : ℤ) (show 1 ≤ n / 2 - 1 by omega))
        have htwoDiff : (2 : ℤ) ∣
            (2 : ℤ) ^ (n / 2 - 1) -
              FABL.booleanNumericalCoeffInt f Finset.univ :=
          dvd_trans htwoHalf htop
        have htwoCoeff : (2 : ℤ) ∣
            FABL.booleanNumericalCoeffInt f Finset.univ := by
          have := dvd_sub htwoHalfPred htwoDiff
          simpa only [sub_sub_cancel] using this
        obtain ⟨z, hz⟩ := htwoCoeff
        rw [hz]
        simp only [Int.cast_mul, Int.cast_ofNat]
        rw [show (2 : FABL.𝔽₂) = 0 by decide]
        simp
      · have hScardLt : S.card < n := by
          have hle : S.card ≤ n := by
            simpa using Finset.card_le_univ S
          apply lt_of_le_of_ne hle
          intro hcard
          apply hSuniv
          exact Finset.eq_univ_of_card S (by simpa using hcard)
        have hScardHalf : n / 2 < S.card := by
          rw [← hJcard]
          exact Finset.card_lt_card hJssubS
        obtain ⟨z, hz⟩ := hconditions.1 S hScardHalf hScardLt
        rw [hz]
        have hpowPos : 0 < S.card - n / 2 := by omega
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
        rw [show (2 : FABL.𝔽₂) = 0 by decide]
        simp [hpowPos.ne']
  rw [hcast]
  change (∑ S : Finset (Fin n),
      (2 : FABL.𝔽₂) ^ (n / 2 - (S \ I).card) *
        (FABL.booleanNumericalCoeffInt f S : FABL.𝔽₂)) =
    (FABL.booleanNumericalCoeffInt f J : FABL.𝔽₂)
  rw [Finset.sum_eq_single J]
  · rw [hJdiff, Nat.sub_self, pow_zero, one_mul]
  · intro S _hS hSJ
    exact hterm S hSJ
  · simp

/-- The complementary half-degree ANF coefficient relation is symmetric
between a bent function and its dual. -/
theorem anfCoeff_eq_bentDual_complement_of_card_eq_half
    (f : BooleanFunction n) (hf : IsBent f) (hn : 4 ≤ n)
    (I : Finset (Fin n)) (hIcard : I.card = n / 2) :
    FABL.anfCoeff f I =
      FABL.anfCoeff (bentDual f) (Finset.univ \ I) := by
  simpa [bentDual_bentDual f hf] using
    anfCoeff_bentDual_eq_complement_of_card_eq_half
      (bentDual f) (isBent_bentDual f hf) hn I hIcard

end CryptBoolean
