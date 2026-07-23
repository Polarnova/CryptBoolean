/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.IndicatorSpectralBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Carlet Chapter 4 kth-order nonhomomorphicity

The ordered zero-sum tuples with even output parity are expressed by a raw Walsh moment.  For
even orders at least four, affine functions uniquely maximize this count and bent functions
uniquely minimize it.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

/-- The coordinate sum of an ordered tuple in the binary cube. -/
def booleanTupleSum (x : Fin k → FABL.F₂Cube n) : FABL.F₂Cube n :=
  ∑ i, x i

/-- The output parity of a Boolean function on an ordered tuple. -/
def booleanTupleOutputSum
    (f : BooleanFunction n) (x : Fin k → FABL.F₂Cube n) : FABL.𝔽₂ :=
  ∑ i, f (x i)

/-- Carlet's p.67 count: ordered zero-sum tuples having even output parity.

The cited Zhang--Zheng paper calls this the kth homomorphicity; Carlet calls the same even-output
count the kth-order nonhomomorphicity. -/
noncomputable def kthNonhomomorphicity
    (f : BooleanFunction n) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
    booleanTupleSum x = 0 ∧ booleanTupleOutputSum f x = 0).card

private theorem addChar_sum_eq_prod
    {ι A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (g : ι → A) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

private theorem product_realSignView_eq_binarySign_outputSum
    (f : BooleanFunction n) (x : Fin k → FABL.F₂Cube n) :
    ∏ i, realSignView f (x i) = FABL.binarySign (booleanTupleOutputSum f x) := by
  rw [booleanTupleOutputSum,
    addChar_sum_eq_prod FABL.binarySign Finset.univ (fun i ↦ f (x i))]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [realSignView, FABL.realSignEncodedFunction, FABL.signEncodedFunction,
    FABL.signValue_signEncode_eq_binarySign]

private theorem product_vectorWalshCharacter_eq_character_tupleSum
    (a : FABL.F₂Cube n) (x : Fin k → FABL.F₂Cube n) :
    ∏ i, FABL.vectorWalshCharacter a (x i) =
      FABL.vectorWalshCharacter a (booleanTupleSum x) := by
  rw [booleanTupleSum,
    addChar_sum_eq_prod (FABL.vectorWalshCharacter a) Finset.univ x]

private theorem sum_vectorWalshCharacter_frequency
    (x : FABL.F₂Cube n) :
    ∑ a, FABL.vectorWalshCharacter a x =
      if x = 0 then (2 : ℝ) ^ n else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  · rw [if_neg hx]
    have hexpect := FABL.expect_vectorWalshCharacter x
    rw [if_neg hx, Fintype.expect_eq_sum_div_card] at hexpect
    have h : ∑ a, FABL.vectorWalshCharacter x a = 0 :=
      (div_eq_zero_iff.mp hexpect).resolve_right (by positivity)
    rw [← h]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [FABL.vectorWalshCharacter_apply, FABL.vectorWalshCharacter_apply]
    exact congrArg FABL.binarySign (dotProduct_comm a x)

private theorem indicator_zero_tupleSum_mul_two_pow
    (x : Fin k → FABL.F₂Cube n) :
    (if booleanTupleSum x = 0 then (2 : ℝ) ^ n else 0) =
      ∑ a, FABL.vectorWalshCharacter a (booleanTupleSum x) := by
  rw [sum_vectorWalshCharacter_frequency]

private theorem two_pow_mul_zeroSumTupleCount
    (hk : 0 < k) :
    (2 : ℝ) ^ n *
        (((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
          booleanTupleSum x = 0).card : ℝ) =
      ((2 : ℝ) ^ n) ^ k := by
  classical
  rw [show
    ((((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
      booleanTupleSum x = 0).card : ℕ) : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter
        (fun x ↦ booleanTupleSum x = 0), (1 : ℝ) by simp]
  rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  simp_rw [mul_ite, mul_one, mul_zero]
  calc
    (∑ x : (Fin k → FABL.F₂Cube n),
          if booleanTupleSum x = 0 then (2 : ℝ) ^ n else 0) =
        ∑ x : (Fin k → FABL.F₂Cube n),
          ∑ a, FABL.vectorWalshCharacter a (booleanTupleSum x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact indicator_zero_tupleSum_mul_two_pow x
    _ = ∑ a : FABL.F₂Cube n,
          ∑ x : (Fin k → FABL.F₂Cube n),
            ∏ i, FABL.vectorWalshCharacter a (x i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro x _hx
      exact (product_vectorWalshCharacter_eq_character_tupleSum a x).symm
    _ = ∑ a : FABL.F₂Cube n,
          (∑ y, FABL.vectorWalshCharacter a y) ^ k := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Fintype.sum_pow]
    _ = ((2 : ℝ) ^ n) ^ k := by
      calc
        ∑ a : FABL.F₂Cube n,
            (∑ y, FABL.vectorWalshCharacter a y) ^ k =
            ((∑ y, FABL.vectorWalshCharacter (0 : FABL.F₂Cube n) y) ^ k) := by
          rw [Finset.sum_eq_single 0]
          · intro a _ha ha
            have hexpect := FABL.expect_vectorWalshCharacter a
            rw [if_neg ha, Fintype.expect_eq_sum_div_card] at hexpect
            have hzero : ∑ y, FABL.vectorWalshCharacter a y = 0 :=
              (div_eq_zero_iff.mp hexpect).resolve_right (by positivity)
            rw [hzero, zero_pow hk.ne']
          · simp
        _ = ((2 : ℝ) ^ n) ^ k := by simp

private theorem two_pow_mul_signedZeroSumTupleSum
    (f : BooleanFunction n) :
    (2 : ℝ) ^ n *
        (∑ x : (Fin k → FABL.F₂Cube n),
          if booleanTupleSum x = 0 then
            ∏ i, realSignView f (x i)
          else 0) =
      ∑ a, (walshTransform f a : ℝ) ^ k := by
  classical
  rw [Finset.mul_sum]
  calc
    ∑ x : (Fin k → FABL.F₂Cube n),
          (2 : ℝ) ^ n *
            (if booleanTupleSum x = 0 then
              ∏ i, realSignView f (x i)
            else 0) =
        ∑ x : (Fin k → FABL.F₂Cube n),
          (∑ a, FABL.vectorWalshCharacter a (booleanTupleSum x)) *
            ∏ i, realSignView f (x i) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← indicator_zero_tupleSum_mul_two_pow]
      by_cases hx : booleanTupleSum x = 0 <;> simp [hx]
    _ = ∑ a : FABL.F₂Cube n,
          ∑ x : (Fin k → FABL.F₂Cube n),
            ∏ i, (realSignView f (x i) *
              FABL.vectorWalshCharacter a (x i)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← product_vectorWalshCharacter_eq_character_tupleSum]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      ring
    _ = ∑ a : FABL.F₂Cube n,
          (∑ y, realSignView f y * FABL.vectorWalshCharacter a y) ^ k := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Fintype.sum_pow]
    _ = ∑ a, (walshTransform f a : ℝ) ^ k := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [walshTransform_cast_eq_sum_realSignView_mul_character]

private theorem two_mul_kthNonhomomorphicity_eq_zeroSum_add_signed
    (f : BooleanFunction n) :
    2 * (kthNonhomomorphicity f k : ℝ) =
      (((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
        booleanTupleSum x = 0).card : ℝ) +
      ∑ x : (Fin k → FABL.F₂Cube n),
        if booleanTupleSum x = 0 then
          ∏ i, realSignView f (x i)
        else 0 := by
  classical
  rw [kthNonhomomorphicity]
  rw [show
    ((((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
      booleanTupleSum x = 0 ∧ booleanTupleOutputSum f x = 0).card : ℕ) : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter
        (fun x ↦ booleanTupleSum x = 0 ∧ booleanTupleOutputSum f x = 0),
        (1 : ℝ) by simp]
  rw [Finset.sum_filter]
  rw [show
    ((((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
      booleanTupleSum x = 0).card : ℕ) : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter
        (fun x ↦ booleanTupleSum x = 0), (1 : ℝ) by simp]
  rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hsum : booleanTupleSum x = 0
  · rw [product_realSignView_eq_binarySign_outputSum]
    by_cases hout : booleanTupleOutputSum f x = 0
    · norm_num [hsum, hout]
    · have hout_one : booleanTupleOutputSum f x = 1 :=
        Fin.eq_one_of_ne_zero _ hout
      simp [hsum, hout_one]
  · simp [hsum]

/-- Division-free Walsh-moment identity for Carlet's kth-order count. -/
theorem two_mul_two_pow_mul_kthNonhomomorphicity
    (f : BooleanFunction n) (hk : 0 < k) :
    2 * (2 : ℝ) ^ n * (kthNonhomomorphicity f k : ℝ) =
      ((2 : ℝ) ^ n) ^ k +
        ∑ a, (walshTransform f a : ℝ) ^ k := by
  have hcount := two_mul_kthNonhomomorphicity_eq_zeroSum_add_signed
    (n := n) (k := k) f
  have hzero := two_pow_mul_zeroSumTupleCount (n := n) hk
  have hsigned := two_pow_mul_signedZeroSumTupleSum (n := n) (k := k) f
  calc
    2 * (2 : ℝ) ^ n * (kthNonhomomorphicity f k : ℝ) =
        (2 : ℝ) ^ n * (2 * (kthNonhomomorphicity f k : ℝ)) := by ring
    _ = (2 : ℝ) ^ n *
          ((((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
            booleanTupleSum x = 0).card : ℝ) +
          ∑ x : (Fin k → FABL.F₂Cube n),
            if booleanTupleSum x = 0 then
              ∏ i, realSignView f (x i)
            else 0) := by rw [hcount]
    _ = ((2 : ℝ) ^ n) ^ k +
        ∑ a, (walshTransform f a : ℝ) ^ k := by
      rw [mul_add, hzero, hsigned]

/-- Carlet's p.67 Walsh-moment formula, written with positive denominators. -/
theorem kthNonhomomorphicity_cast_eq_walshMoment
    (f : BooleanFunction n) (hk : 0 < k) :
    (kthNonhomomorphicity f k : ℝ) =
      ((2 : ℝ) ^ n) ^ (k - 1) / 2 +
        (∑ a, (walshTransform f a : ℝ) ^ k) /
          (2 * (2 : ℝ) ^ n) := by
  have h := two_mul_two_pow_mul_kthNonhomomorphicity (n := n) (k := k) f hk
  obtain ⟨r, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  subst k
  simp only [Nat.succ_sub_one]
  rw [pow_succ] at h
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Carlet's printed p.67 formula, with the negative power written as a positive denominator. -/
theorem kthNonhomomorphicity_cast_eq_carlet_formula
    (f : BooleanFunction n) (hk : 0 < k) :
    (kthNonhomomorphicity f k : ℝ) =
      (2 : ℝ) ^ ((k - 1) * n) / 2 +
        (∑ a, (walshTransform f a : ℝ) ^ k) /
          (2 : ℝ) ^ (n + 1) := by
  simpa [pow_mul, pow_succ, Nat.mul_comm, mul_comm] using
    kthNonhomomorphicity_cast_eq_walshMoment (n := n) (k := k) f hk

/-- A Boolean function is affine when it is one of FABL's canonical affine functions. -/
def IsAffineBooleanFunction (f : BooleanFunction n) : Prop :=
  ∃ b a, f = FABL.affineFunction b a

/-- A Boolean function is affine exactly when its Carlet nonlinearity vanishes. -/
theorem isAffineBooleanFunction_iff_nonlinearity_eq_zero
    (f : BooleanFunction n) :
    IsAffineBooleanFunction f ↔ nonlinearity f = 0 := by
  classical
  constructor
  · rintro ⟨b, a, rfl⟩
    unfold nonlinearity
    apply Nat.eq_zero_of_le_zero
    calc
      (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
          Finset.univ_nonempty
          (fun p ↦ hammingDistance (FABL.affineFunction b a)
            (FABL.affineFunction p.1 p.2)) ≤
          hammingDistance (FABL.affineFunction b a)
            (FABL.affineFunction b a) :=
        Finset.inf'_le
        (fun p : FABL.𝔽₂ × FABL.F₂Cube n ↦
          hammingDistance (FABL.affineFunction b a)
            (FABL.affineFunction p.1 p.2))
        (Finset.mem_univ (b, a))
      _ = 0 := hammingDist_eq_zero.mpr rfl
  · intro hzero
    unfold nonlinearity at hzero
    obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)))
      Finset.univ_nonempty
      (fun q ↦ hammingDistance f (FABL.affineFunction q.1 q.2))
    refine ⟨p.1, p.2, ?_⟩
    apply hammingDist_eq_zero.mp
    change hammingDistance f (FABL.affineFunction p.1 p.2) = 0
    rw [← hmin]
    exact hzero

/-- Every raw Walsh coefficient is bounded by the binary-cube cardinality. -/
theorem abs_walshTransform_le_two_pow
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    |(walshTransform f a : ℝ)| ≤ (2 : ℝ) ^ n := by
  have hnat : maxWalshMagnitude f ≤ 2 ^ n := by
    have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
    omega
  exact (abs_walshTransform_le_maxWalshMagnitude f a).trans (by exact_mod_cast hnat)

private theorem sum_walshTransform_evenMoment_le_peak
    (f : BooleanFunction n) (r : ℕ) (hr : 0 < r) :
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) ≤
      (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
        ((2 : ℝ) ^ n) ^ 2 := by
  calc
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) =
        ∑ a, ((walshTransform f a : ℝ) ^ 2) ^ r := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [pow_mul]
    _ ≤ ∑ a, (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
          (walshTransform f a : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      have hsq : (walshTransform f a : ℝ) ^ 2 ≤
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
            (Nat.cast_nonneg (maxWalshMagnitude f))).mpr
              (abs_walshTransform_le_maxWalshMagnitude f a)
      have hpow :
          ((walshTransform f a : ℝ) ^ 2) ^ (r - 1) ≤
            ((maxWalshMagnitude f : ℝ) ^ 2) ^ (r - 1) :=
        pow_le_pow_left₀ (sq_nonneg _) hsq _
      have hr_eq : r = (r - 1) + 1 := by omega
      calc
        ((walshTransform f a : ℝ) ^ 2) ^ r =
            ((walshTransform f a : ℝ) ^ 2) ^ (r - 1) *
              (walshTransform f a : ℝ) ^ 2 := by
          conv_lhs => rw [hr_eq]
          rw [pow_succ]
        _ ≤ ((maxWalshMagnitude f : ℝ) ^ 2) ^ (r - 1) *
              (walshTransform f a : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
        _ = (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
              (walshTransform f a : ℝ) ^ 2 := by rw [pow_mul]
    _ = (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
        ∑ a, (walshTransform f a : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ = (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
        ((2 : ℝ) ^ n) ^ 2 := by
      rw [sum_walshTransform_sq_eq_two_pow_sq]

/-- The even raw Walsh moment is at most the corresponding power of the cube cardinality. -/
theorem sum_walshTransform_evenMoment_le
    (f : BooleanFunction n) (r : ℕ) (hr : 0 < r) :
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) ≤
      ((2 : ℝ) ^ n) ^ (2 * r) := by
  have hpeak := sum_walshTransform_evenMoment_le_peak f r hr
  have hmax : (maxWalshMagnitude f : ℝ) ≤ (2 : ℝ) ^ n := by
    have hnat : maxWalshMagnitude f ≤ 2 ^ n := by
      have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
      omega
    exact_mod_cast hnat
  calc
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) ≤
        (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) *
          ((2 : ℝ) ^ n) ^ 2 := hpeak
    _ ≤ ((2 : ℝ) ^ n) ^ (2 * (r - 1)) *
          ((2 : ℝ) ^ n) ^ 2 := by
      gcongr
    _ = ((2 : ℝ) ^ n) ^ (2 * r) := by
      rw [← pow_add]
      congr 1
      omega

private theorem isAffineBooleanFunction_of_evenMoment_eq_max
    (f : BooleanFunction n) (r : ℕ) (hr : 2 ≤ r)
    (hmoment :
      (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) =
        ((2 : ℝ) ^ n) ^ (2 * r)) :
    IsAffineBooleanFunction f := by
  have hpeak := sum_walshTransform_evenMoment_le_peak f r (by omega)
  rw [hmoment] at hpeak
  have hpower :
      ((2 : ℝ) ^ n) ^ (2 * r) =
        ((2 : ℝ) ^ n) ^ (2 * (r - 1)) * ((2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpower] at hpeak
  have hpows :
      ((2 : ℝ) ^ n) ^ (2 * (r - 1)) ≤
        (maxWalshMagnitude f : ℝ) ^ (2 * (r - 1)) := by
    exact le_of_mul_le_mul_right hpeak (by positivity)
  have hexponent : 2 * (r - 1) ≠ 0 := by omega
  have hcard_le_max :
      (2 : ℝ) ^ n ≤ (maxWalshMagnitude f : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) hexponent).mp hpows
  have hmax_le_card : (maxWalshMagnitude f : ℝ) ≤ (2 : ℝ) ^ n := by
    have hnat : maxWalshMagnitude f ≤ 2 ^ n := by
      have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
      omega
    exact_mod_cast hnat
  have hmax : maxWalshMagnitude f = 2 ^ n := by
    exact_mod_cast le_antisymm hmax_le_card hcard_le_max
  apply (isAffineBooleanFunction_iff_nonlinearity_eq_zero f).2
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  omega

private theorem booleanTupleOutputSum_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n)
    (x : Fin k → FABL.F₂Cube n) :
    booleanTupleOutputSum (FABL.affineFunction b a) x =
      k • b + FABL.f₂DotProduct a (booleanTupleSum x) := by
  classical
  unfold booleanTupleOutputSum booleanTupleSum FABL.affineFunction FABL.f₂DotProduct
  simp only [dotProduct, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.card_univ, Fintype.card_fin]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]

private theorem even_nsmul_f₂_eq_zero
    (b : FABL.𝔽₂) (hk : Even k) :
    k • b = 0 := by
  obtain ⟨r, rfl⟩ := hk
  rw [add_nsmul]
  exact CharTwo.add_self_eq_zero (r • b)

/-- An affine function attains Carlet's maximum kth-order count. -/
theorem kthNonhomomorphicity_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n)
    (hkEven : Even k) (hk : 0 < k) :
    (kthNonhomomorphicity (FABL.affineFunction b a) k : ℝ) =
      ((2 : ℝ) ^ n) ^ (k - 1) := by
  classical
  have hfilters :
      ((Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
        booleanTupleSum x = 0 ∧
          booleanTupleOutputSum (FABL.affineFunction b a) x = 0) =
      (Finset.univ : Finset (Fin k → FABL.F₂Cube n)).filter fun x ↦
        booleanTupleSum x = 0 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hsum
      refine ⟨hsum, ?_⟩
      rw [booleanTupleOutputSum_affineFunction, even_nsmul_f₂_eq_zero b hkEven,
        hsum]
      simp [FABL.f₂DotProduct]
  rw [kthNonhomomorphicity, hfilters]
  have hzero := two_pow_mul_zeroSumTupleCount (n := n) hk
  obtain ⟨r, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  subst k
  simp only [Nat.succ_sub_one]
  rw [pow_succ] at hzero
  apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0)
  simpa [mul_comm] using hzero

/-- For even order at least four, Carlet's kth-order count is at most the number of
zero-sum tuples. -/
theorem kthNonhomomorphicity_cast_le_max
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k) :
    (kthNonhomomorphicity f k : ℝ) ≤
      ((2 : ℝ) ^ n) ^ (k - 1) := by
  obtain ⟨r, hk_eq⟩ := hkEven
  subst k
  have hr : 2 ≤ r := by omega
  have hkpos : 0 < r + r := by omega
  have hformula :=
    kthNonhomomorphicity_cast_eq_walshMoment (n := n) (k := r + r) f hkpos
  have hmoment := sum_walshTransform_evenMoment_le f r (by omega)
  have htwo : r + r = 2 * r := by omega
  rw [← htwo] at hmoment
  rw [hformula]
  have hpower :
      ((2 : ℝ) ^ n) ^ (r + r) =
        ((2 : ℝ) ^ n) ^ (r + r - 1) * (2 : ℝ) ^ n := by
    conv_lhs => rw [show r + r = (r + r - 1) + 1 by omega]
    rw [pow_succ]
  calc
    ((2 : ℝ) ^ n) ^ (r + r - 1) / 2 +
        (∑ a, (walshTransform f a : ℝ) ^ (r + r)) /
          (2 * (2 : ℝ) ^ n) ≤
        ((2 : ℝ) ^ n) ^ (r + r - 1) / 2 +
          ((2 : ℝ) ^ n) ^ (r + r) / (2 * (2 : ℝ) ^ n) := by
      gcongr
    _ = ((2 : ℝ) ^ n) ^ (r + r - 1) := by
      rw [hpower]
      field_simp
      ring

/-- Equality in Carlet's maximum kth-order bound characterizes affine Boolean functions. -/
theorem kthNonhomomorphicity_cast_eq_max_iff_isAffine
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k) :
    (kthNonhomomorphicity f k : ℝ) =
        ((2 : ℝ) ^ n) ^ (k - 1) ↔
      IsAffineBooleanFunction f := by
  constructor
  · intro hcount
    obtain ⟨r, hk_eq⟩ := hkEven
    subst k
    have hr : 2 ≤ r := by omega
    have hkpos : 0 < r + r := by omega
    have hformula :=
      kthNonhomomorphicity_cast_eq_walshMoment (n := n) (k := r + r) f hkpos
    have hpower :
        ((2 : ℝ) ^ n) ^ (r + r) =
          ((2 : ℝ) ^ n) ^ (r + r - 1) * (2 : ℝ) ^ n := by
      conv_lhs => rw [show r + r = (r + r - 1) + 1 by omega]
      rw [pow_succ]
    have hmoment :
        (∑ a, (walshTransform f a : ℝ) ^ (r + r)) =
          ((2 : ℝ) ^ n) ^ (r + r) := by
      rw [hcount] at hformula
      rw [hpower]
      have hN : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp at hformula ⊢
      nlinarith
    have htwo : r + r = 2 * r := by omega
    rw [htwo] at hmoment
    exact isAffineBooleanFunction_of_evenMoment_eq_max f r hr hmoment
  · intro haffine
    obtain ⟨b, a, rfl⟩ := haffine
    exact kthNonhomomorphicity_affineFunction b a hkEven (by omega)

/-- Carlet's source-range maximum theorem, including the printed upper bound on the order. -/
theorem carlet_kthNonhomomorphicity_cast_eq_max_iff_isAffine
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k)
    (_hkCard : k ≤ 2 ^ n) :
    (kthNonhomomorphicity f k : ℝ) =
        ((2 : ℝ) ^ n) ^ (k - 1) ↔
      IsAffineBooleanFunction f :=
  kthNonhomomorphicity_cast_eq_max_iff_isAffine f hkEven hkFour

private theorem sum_inv_two_pow_eq_one :
    (∑ _a : FABL.F₂Cube n, ((2 : ℝ) ^ n)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
  push_cast
  field_simp

private theorem weightedMean_walshTransform_sq
    (f : BooleanFunction n) :
    (∑ a, ((2 : ℝ) ^ n)⁻¹ • (walshTransform f a : ℝ) ^ 2) =
      (2 : ℝ) ^ n := by
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum, sum_walshTransform_sq_eq_two_pow_sq]
  field_simp

private theorem weightedMean_walshTransform_sq_pow
    (f : BooleanFunction n) (r : ℕ) :
    (∑ a, ((2 : ℝ) ^ n)⁻¹ • ((walshTransform f a : ℝ) ^ 2) ^ r) =
      ((2 : ℝ) ^ n)⁻¹ *
        ∑ a, (walshTransform f a : ℝ) ^ (2 * r) := by
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [pow_mul]

/-- The even raw Walsh moment has the power-mean lower bound. -/
theorem two_pow_pow_succ_le_sum_walshTransform_evenMoment
    (f : BooleanFunction n) (r : ℕ) (hr : 2 ≤ r) :
    ((2 : ℝ) ^ n) ^ (r + 1) ≤
      ∑ a, (walshTransform f a : ℝ) ^ (2 * r) := by
  have hjensen :=
    (strictConvexOn_pow hr).convexOn.map_sum_le
      (t := (Finset.univ : Finset (FABL.F₂Cube n)))
      (w := fun _a ↦ ((2 : ℝ) ^ n)⁻¹)
      (p := fun a ↦ (walshTransform f a : ℝ) ^ 2)
      (fun _a _ha ↦ by positivity)
      (sum_inv_two_pow_eq_one (n := n))
      (fun a _ha ↦
        show (0 : ℝ) ≤ (walshTransform f a : ℝ) ^ 2 from sq_nonneg _)
  rw [weightedMean_walshTransform_sq,
    weightedMean_walshTransform_sq_pow] at hjensen
  rw [pow_succ]
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  apply (le_mul_inv_iff₀ hN).mp
  simpa [mul_comm] using hjensen

private theorem walshTransform_evenMoment_eq_min_iff_constant_sq
    (f : BooleanFunction n) (r : ℕ) (hr : 2 ≤ r) :
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) =
        ((2 : ℝ) ^ n) ^ (r + 1) ↔
      ∀ a, (walshTransform f a : ℝ) ^ 2 = (2 : ℝ) ^ n := by
  have hjensen :=
    (strictConvexOn_pow hr).map_sum_eq_iff
      (t := (Finset.univ : Finset (FABL.F₂Cube n)))
      (w := fun _a ↦ ((2 : ℝ) ^ n)⁻¹)
      (p := fun a ↦ (walshTransform f a : ℝ) ^ 2)
      (fun _a _ha ↦ by positivity)
      (sum_inv_two_pow_eq_one (n := n))
      (fun a _ha ↦
        show (0 : ℝ) ≤ (walshTransform f a : ℝ) ^ 2 from sq_nonneg _)
  rw [weightedMean_walshTransform_sq,
    weightedMean_walshTransform_sq_pow] at hjensen
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  constructor
  · intro hmoment a
    apply (hjensen.mp ?_) a (Finset.mem_univ a)
    rw [hmoment, pow_succ]
    field_simp
  · intro hconstant
    have hj := hjensen.mpr fun a _ha ↦ hconstant a
    field_simp at hj
    rw [pow_succ]
    simpa [mul_comm] using hj.symm

private theorem walshTransform_sq_eq_two_pow_iff_abs_eq_sqrt
    (z : ℝ) :
    z ^ 2 = (2 : ℝ) ^ n ↔
      |z| = Real.sqrt ((2 : ℝ) ^ n) := by
  constructor
  · intro hz
    have hsqrt : (Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = (2 : ℝ) ^ n :=
      Real.sq_sqrt (by positivity)
    have habsSq : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith [abs_nonneg z, Real.sqrt_nonneg ((2 : ℝ) ^ n)]
  · intro hz
    have hsquares := congrArg (fun x : ℝ ↦ x ^ 2) hz
    rw [sq_abs, Real.sq_sqrt (by positivity)] at hsquares
    exact hsquares

/-- Equality in the even Walsh power-mean bound is equivalent to bentness. -/
theorem sum_walshTransform_evenMoment_eq_min_iff_isBent
    (f : BooleanFunction n) (r : ℕ) (hr : 2 ≤ r) :
    (∑ a, (walshTransform f a : ℝ) ^ (2 * r)) =
        ((2 : ℝ) ^ n) ^ (r + 1) ↔
      IsBent f := by
  rw [walshTransform_evenMoment_eq_min_iff_constant_sq f r hr,
    ← hasFlatWalshSpectrum_iff_isBent]
  constructor
  · intro h a
    exact (walshTransform_sq_eq_two_pow_iff_abs_eq_sqrt
      (n := n) (walshTransform f a : ℝ)).1 (h a)
  · intro h a
    exact (walshTransform_sq_eq_two_pow_iff_abs_eq_sqrt
      (n := n) (walshTransform f a : ℝ)).2 (h a)

/-- For even order at least four, Carlet's kth-order count has the bent-function lower bound. -/
theorem kthNonhomomorphicity_cast_min_le
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k) :
    ((2 : ℝ) ^ n) ^ (k - 1) / 2 +
        ((2 : ℝ) ^ n) ^ (k / 2) / 2 ≤
      (kthNonhomomorphicity f k : ℝ) := by
  obtain ⟨r, hk_eq⟩ := hkEven
  subst k
  have hr : 2 ≤ r := by omega
  have hkpos : 0 < r + r := by omega
  have hformula :=
    kthNonhomomorphicity_cast_eq_walshMoment (n := n) (k := r + r) f hkpos
  have hmoment :=
    two_pow_pow_succ_le_sum_walshTransform_evenMoment f r hr
  have htwo : r + r = 2 * r := by omega
  rw [← htwo] at hmoment
  have hhalf : (r + r) / 2 = r := by omega
  rw [hhalf, hformula]
  have hscaled :
      ((2 : ℝ) ^ n) ^ r / 2 ≤
        (∑ a, (walshTransform f a : ℝ) ^ (r + r)) /
          (2 * (2 : ℝ) ^ n) := by
    calc
      ((2 : ℝ) ^ n) ^ r / 2 =
          ((2 : ℝ) ^ n) ^ (r + 1) / (2 * (2 : ℝ) ^ n) := by
        rw [pow_succ]
        field_simp
      _ ≤ (∑ a, (walshTransform f a : ℝ) ^ (r + r)) /
          (2 * (2 : ℝ) ^ n) := by
        gcongr
  linarith

/-- Equality in Carlet's minimum kth-order bound characterizes bent Boolean functions. -/
theorem kthNonhomomorphicity_cast_eq_min_iff_isBent
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k) :
    (kthNonhomomorphicity f k : ℝ) =
        ((2 : ℝ) ^ n) ^ (k - 1) / 2 +
          ((2 : ℝ) ^ n) ^ (k / 2) / 2 ↔
      IsBent f := by
  obtain ⟨r, hk_eq⟩ := hkEven
  subst k
  have hr : 2 ≤ r := by omega
  have hkpos : 0 < r + r := by omega
  have hformula :=
    kthNonhomomorphicity_cast_eq_walshMoment (n := n) (k := r + r) f hkpos
  have hhalf : (r + r) / 2 = r := by omega
  rw [hhalf]
  constructor
  · intro hcount
    have hmoment :
        (∑ a, (walshTransform f a : ℝ) ^ (r + r)) =
          ((2 : ℝ) ^ n) ^ (r + 1) := by
      rw [hcount] at hformula
      rw [pow_succ]
      have hN : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp at hformula ⊢
      nlinarith
    have htwo : r + r = 2 * r := by omega
    rw [htwo] at hmoment
    exact (sum_walshTransform_evenMoment_eq_min_iff_isBent f r hr).1 hmoment
  · intro hbent
    have hmoment :=
      (sum_walshTransform_evenMoment_eq_min_iff_isBent f r hr).2 hbent
    have htwo : r + r = 2 * r := by omega
    rw [← htwo] at hmoment
    rw [hformula, hmoment, pow_succ]
    field_simp

/-- Carlet's source-range minimum theorem, including the printed upper bound on the order. -/
theorem carlet_kthNonhomomorphicity_cast_eq_min_iff_isBent
    (f : BooleanFunction n) (hkEven : Even k) (hkFour : 4 ≤ k)
    (_hkCard : k ≤ 2 ^ n) :
    (kthNonhomomorphicity f k : ℝ) =
        ((2 : ℝ) ^ n) ^ (k - 1) / 2 +
          ((2 : ℝ) ^ n) ^ (k / 2) / 2 ↔
      IsBent f :=
  kthNonhomomorphicity_cast_eq_min_iff_isBent f hkEven hkFour

end CryptBoolean
