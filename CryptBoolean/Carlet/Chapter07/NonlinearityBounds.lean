/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree
public import CryptBoolean.Carlet.Chapter07.DegreeDivisibility

import CryptBoolean.Carlet.Chapter07.MaximumCorrelation

/-!
# Refined nonlinearity bounds for resilient functions

Carlet's degree-sensitive and Parseval refinements of the Sarkar--Maitra
bound, together with the strict even-dimensional bound for resilient Boolean
functions.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem nonlinearity_add_two_pow_le_of_walshTransform_divisibility
    (f : BooleanFunction n) (q : ℕ) (hq : q + 1 ≤ n)
    (hdiv : ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (q + 1) ∣ walshTransform f a) :
    nonlinearity f + 2 ^ q ≤ 2 ^ (n - 1) := by
  obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
  have hdivNat : 2 ^ (q + 1) ∣ (walshTransform f a).natAbs := by
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdiv a
  have hlower : 2 ^ (q + 1) ≤ (walshTransform f a).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hdivNat
  have hupper :
      (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
    unfold maxWalshMagnitude
    exact Finset.le_sup'
      (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ a)
  have hmax : 2 ^ (q + 1) ≤ maxWalshMagnitude f :=
    hlower.trans hupper
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hdimension : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have hamplitude : 2 ^ (q + 1) = 2 * 2 ^ q := by
    rw [pow_succ]
    ring
  omega

/-- A positive-degree `m`-resilient function has nonlinearity at most
`2^(n-1) - 2^(m+1+⌊(n-m-2)/deg(f)⌋)`. -/
theorem nonlinearity_le_two_pow_sub_two_pow_degree_quotient_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsResilient m f) :
    nonlinearity f ≤
      2 ^ (n - 1) -
        2 ^ (m + 1 +
          (n - m - 2) / FABL.functionAlgebraicDegree f) := by
  let q := m + 1 +
    (n - m - 2) / FABL.functionAlgebraicDegree f
  have hq : q + 1 ≤ n := by
    have hdivLe :
        (n - m - 2) / FABL.functionAlgebraicDegree f ≤ n - m - 2 :=
      Nat.div_le_self _ _
    dsimp [q]
    omega
  apply Nat.le_sub_of_add_le
  apply nonlinearity_add_two_pow_le_of_walshTransform_divisibility f q hq
  intro a
  have hdiv :=
    two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isResilient
      f m hm hd hf a
  simpa [q, show q + 1 = m + 2 +
      (n - m - 2) / FABL.functionAlgebraicDegree f by
        dsimp [q]
        omega] using hdiv

/-- Equality in the Sarkar--Maitra bound for a positive-degree resilient
function forces equality in Siegenthaler's degree bound. -/
theorem functionAlgebraicDegree_eq_sub_sub_one_of_sarkarMaitra_equality
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsResilient m f)
    (hnonlinearity :
      nonlinearity f = 2 ^ (n - 1) - 2 ^ (m + 1)) :
    FABL.functionAlgebraicDegree f = n - m - 1 := by
  let q := m + 1 +
    (n - m - 2) / FABL.functionAlgebraicDegree f
  have hq : q + 1 ≤ n := by
    have hdivLe :
        (n - m - 2) / FABL.functionAlgebraicDegree f ≤ n - m - 2 :=
      Nat.div_le_self _ _
    dsimp [q]
    omega
  have hrefined : nonlinearity f + 2 ^ q ≤ 2 ^ (n - 1) := by
    apply nonlinearity_add_two_pow_le_of_walshTransform_divisibility f q hq
    intro a
    have hdiv :=
      two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isResilient
        f m hm hd hf a
    simpa [q, show q + 1 = m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f by
          dsimp [q]
          omega] using hdiv
  have hbasePower : 2 ^ (m + 1) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbase :
      nonlinearity f + 2 ^ (m + 1) = 2 ^ (n - 1) := by
    rw [hnonlinearity, Nat.sub_add_cancel hbasePower]
  have hquotientZero :
      (n - m - 2) / FABL.functionAlgebraicDegree f = 0 := by
    have hpower : 2 ^ q ≤ 2 ^ (m + 1) := by omega
    have hexponent : q ≤ m + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpower
    dsimp [q] at hexponent
    apply Nat.eq_zero_of_le_zero
    exact (Nat.add_le_add_iff_left
      (n := m + 1)
      (m := (n - m - 2) / FABL.functionAlgebraicDegree f)
      (k := 0)).mp (by simpa using hexponent)
  have hdegreeLower : n - m - 2 < FABL.functionAlgebraicDegree f := by
    by_contra hnot
    have hpositive :
        0 < (n - m - 2) / FABL.functionAlgebraicDegree f :=
      Nat.div_pos (by omega) hd
    omega
  have hdegreeUpper :
      FABL.functionAlgebraicDegree f ≤ n - m - 1 :=
    functionAlgebraicDegree_le_sub_sub_one_of_isResilient
      f m hf (by omega)
  omega

private theorem two_pow_pred_dvd_nonlinearity_of_walshTransform_divisibility
    (f : BooleanFunction n) (q : ℕ) (hq : q + 1 ≤ n)
    (hdiv : ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (q + 1) ∣ walshTransform f a) :
    2 ^ q ∣ nonlinearity f := by
  have hmax : 2 ^ (q + 1) ∣ maxWalshMagnitude f := by
    unfold maxWalshMagnitude
    obtain ⟨a, _ha, hsup⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      Finset.univ_nonempty
      (fun u ↦ (walshTransform f u).natAbs)
    have haDiv : 2 ^ (q + 1) ∣ (walshTransform f a).natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdiv a
    rwa [hsup]
  have hcube : (2 : ℤ) ^ (q + 1) ∣ (2 : ℤ) ^ n :=
    pow_dvd_pow (2 : ℤ) hq
  have hmaxInt :
      (2 : ℤ) ^ (q + 1) ∣ (maxWalshMagnitude f : ℤ) := by
    exact_mod_cast hmax
  have htwice :
      (2 : ℤ) ^ (q + 1) ∣ 2 * (nonlinearity f : ℤ) := by
    have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
    have hrelationInt :
        2 * (nonlinearity f : ℤ) + (maxWalshMagnitude f : ℤ) =
          (2 : ℤ) ^ n := by
      exact_mod_cast hrelation
    have hid :
        2 * (nonlinearity f : ℤ) =
          (2 : ℤ) ^ n - (maxWalshMagnitude f : ℤ) := by
      omega
    rw [hid]
    exact hcube.sub hmaxInt
  obtain ⟨r, hr⟩ := htwice
  have hnonlinearityInt :
      (2 : ℤ) ^ q ∣ (nonlinearity f : ℤ) := by
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      2 * (nonlinearity f : ℤ) = (2 : ℤ) ^ (q + 1) * r := hr
      _ = 2 * ((2 : ℤ) ^ q * r) := by rw [pow_succ]; ring
  exact_mod_cast hnonlinearityInt

private theorem relation36_integer_value
    (hn : 0 < n) (heven : Even n) :
    ((2 ^ (n - 1) - 2 ^ (n / 2 - 1) : ℕ) : ℝ) =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
  have hnTwo : 2 ≤ n := by
    rcases heven with ⟨k, hk⟩
    omega
  have hhalf : 1 ≤ n / 2 := by
    rcases heven with ⟨k, hk⟩
    omega
  have hhalfLe : n / 2 - 1 ≤ n - 1 := by omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) hhalfLe)]
  push_cast
  have hnCast : (n : ℝ) - 1 = (n - 1 : ℕ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hhalfCast : (n : ℝ) / 2 - 1 = (n / 2 - 1 : ℕ) := by
    rcases heven with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have hhalfEq : (k + k) / 2 = k := by omega
    rw [hhalfEq, Nat.cast_sub hk]
    push_cast
    ring
  rw [hnCast, hhalfCast]
  norm_num

private theorem nonlinearity_lt_even_covering_bound_of_isBalanced
    (f : BooleanFunction n) (hn : 0 < n) (heven : Even n)
    (hf : IsBalanced f) :
    nonlinearity f < 2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  have hle := nonlinearity_cast_le_relation_36 f
  have hne :
      (nonlinearity f : ℝ) ≠
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
    intro heq
    exact (not_isBalanced_of_isBent f
      ((nonlinearity_cast_eq_relation_36_iff_isBent f).mp heq)) hf
  have hlt :
      (nonlinearity f : ℝ) <
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) :=
    lt_of_le_of_ne hle hne
  rw [← relation36_integer_value hn heven] at hlt
  exact_mod_cast hlt

private theorem two_pow_m_add_one_dvd_even_covering_bound
    (m n : ℕ) (hm : m + 2 ≤ n / 2) :
    2 ^ (m + 1) ∣ 2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  have hfirst : m + 1 ≤ n - 1 := by
    have hhalfLe := Nat.div_le_self n 2
    omega
  have hsecond : m + 1 ≤ n / 2 - 1 := by omega
  obtain ⟨a, ha⟩ := pow_dvd_pow (2 : ℕ) hfirst
  obtain ⟨b, hb⟩ := pow_dvd_pow (2 : ℕ) hsecond
  refine ⟨a - b, ?_⟩
  rw [ha, hb, Nat.mul_sub_left_distrib]

/-- If `n` is positive and even and `m ≤ n/2-2`, every `m`-resilient
Boolean function satisfies the strict-grid refinement of Relation (36). -/
theorem nonlinearity_le_even_dimension_resilient_bound
    (f : BooleanFunction n) (m : ℕ) (hn : 0 < n) (heven : Even n)
    (hm : m ≤ n / 2 - 2) (hf : IsResilient m f) :
    nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (n / 2 - 1) - 2 ^ (m + 1) := by
  have hnTwo : 2 ≤ n := by
    rcases heven with ⟨k, hk⟩
    omega
  have hmWalsh : m + 2 ≤ n := by
    have hhalfLe := Nat.div_le_self n 2
    omega
  have hgrid : 2 ^ (m + 1) ∣ nonlinearity f := by
    apply two_pow_pred_dvd_nonlinearity_of_walshTransform_divisibility
      f (m + 1) hmWalsh
    simpa only [Nat.add_assoc, Nat.add_left_inj] using
      two_pow_m_add_two_dvd_walshTransform_of_isResilient f m hmWalsh hf
  have hstrict :=
    nonlinearity_lt_even_covering_bound_of_isBalanced f hn heven hf.2
  by_cases hnSmall : n < 4
  · have hnEq : n = 2 := by
      rcases heven with ⟨k, hk⟩
      omega
    subst n
    have hmZero : m = 0 := by
      norm_num at hm
      omega
    subst m
    norm_num at hstrict ⊢
    omega
  · have hnFour : 4 ≤ n := by omega
    have hmHalf : m + 2 ≤ n / 2 := by omega
    have hboundGrid :=
      two_pow_m_add_one_dvd_even_covering_bound m n hmHalf
    obtain ⟨x, hx⟩ := hgrid
    obtain ⟨y, hy⟩ := hboundGrid
    rw [hx, hy] at hstrict
    have hxy : x < y :=
      (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ (m + 1))).mp hstrict
    apply Nat.le_sub_of_add_le
    rw [hx, hy]
    calc
      2 ^ (m + 1) * x + 2 ^ (m + 1) =
          2 ^ (m + 1) * (x + 1) := by ring
      _ ≤ 2 ^ (m + 1) * y :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hxy)

private theorem sum_choose_high_tail_eq_sub_low
    (m n : ℕ) (hm : m < n) :
    (∑ j ∈ Finset.Icc (m + 1) n, Nat.choose n j) =
      2 ^ n - ∑ j ∈ Finset.range (m + 1), Nat.choose n j := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j ↦ Nat.choose n j) (show m + 1 ≤ n + 1 by omega)
  have htail : Finset.Icc (m + 1) n = Finset.Ico (m + 1) (n + 1) := by
    ext j
    simp
  rw [htail]
  have hfull := Nat.sum_range_choose n
  omega

private theorem sum_walshSupport_sq_eq_two_pow_sq
    (f : BooleanFunction n) :
    (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) =
      ((2 : ℝ) ^ n) ^ 2 := by
  calc
    (∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2) =
        ∑ a, (walshTransform f a : ℝ) ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ha hnot
      have hzero : walshTransform f a = 0 :=
        not_ne_iff.mp (by simpa only [mem_walshSupport] using hnot)
      simp [hzero]
    _ = ((2 : ℝ) ^ n) ^ 2 := sum_walshTransform_sq_eq_two_pow_sq f

/-- Carlet Relation (57): Parseval and the number of Walsh frequencies not
forced to vanish refine the resilient nonlinearity bound. -/
theorem nonlinearity_le_parseval_resilient_bound
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    nonlinearity f ≤
      2 ^ (n - 1) - 2 ^ (m + 1) *
        ⌈((2 : ℝ) ^ (n - m - 2) /
          Real.sqrt
            (2 ^ n -
              ∑ i ∈ Finset.range (m + 1), Nat.choose n i : ℕ))⌉₊ := by
  classical
  let N : ℕ :=
    2 ^ n - ∑ i ∈ Finset.range (m + 1), Nat.choose n i
  have hmLt : m < n := by omega
  have hsupportCard : (walshSupport f).card ≤ N := by
    have hcard :=
      card_walshSupport_filter_subset_le_sum_choose_of_isResilient
        f (Finset.univ : Finset (Fin n)) m hmLt hf
    have hfiltered :
        (walshSupport f).filter
            (fun u ↦ FABL.f₂Support u ⊆ (Finset.univ : Finset (Fin n))) =
          walshSupport f := by
      ext u
      simp
    rw [hfiltered] at hcard
    have hcard' :
        (walshSupport f).card ≤
          ∑ j ∈ Finset.Icc (m + 1) n, Nat.choose n j := by
      simpa using hcard
    rw [sum_choose_high_tail_eq_sub_low m n hmLt] at hcard'
    exact hcard'
  have hsupportNonempty : (walshSupport f).Nonempty := by
    obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
    exact ⟨a, (mem_walshSupport f a).2 ha⟩
  have hNPos : 0 < N :=
    (Finset.card_pos.mpr hsupportNonempty).trans_le hsupportCard
  have hterm (a : FABL.F₂Cube n) :
      (walshTransform f a : ℝ) ^ 2 ≤
        (maxWalshMagnitude f : ℝ) ^ 2 := by
    have hnat :
        (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
      unfold maxWalshMagnitude
      exact Finset.le_sup'
        (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
        (Finset.mem_univ a)
    have habs :
        |(walshTransform f a : ℝ)| ≤ (maxWalshMagnitude f : ℝ) := by
      have hcast : ((walshTransform f a).natAbs : ℝ) ≤
          (maxWalshMagnitude f : ℝ) := by
        exact_mod_cast hnat
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (walshTransform f a : ℝ))
        (Nat.cast_nonneg (maxWalshMagnitude f))).mpr habs
  have hmoment :
      ((2 : ℝ) ^ n) ^ 2 ≤
        (N : ℝ) * (maxWalshMagnitude f : ℝ) ^ 2 := by
    calc
      ((2 : ℝ) ^ n) ^ 2 =
          ∑ a ∈ walshSupport f, (walshTransform f a : ℝ) ^ 2 :=
        (sum_walshSupport_sq_eq_two_pow_sq f).symm
      _ ≤ ∑ _a ∈ walshSupport f,
          (maxWalshMagnitude f : ℝ) ^ 2 := by
        exact Finset.sum_le_sum fun a _ha ↦ hterm a
      _ = ((walshSupport f).card : ℝ) *
          (maxWalshMagnitude f : ℝ) ^ 2 := by simp
      _ ≤ (N : ℝ) * (maxWalshMagnitude f : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsupportCard)
          (sq_nonneg _)
  have hsqrtPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by
    exact_mod_cast hNPos)
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hrootMul :
      (2 : ℝ) ^ n ≤
        Real.sqrt (N : ℝ) * (maxWalshMagnitude f : ℝ) := by
    apply (sq_le_sq₀ (by positivity)
      (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))).mp
    rw [mul_pow, hsqrtSq]
    exact hmoment
  have hmaxLower :
      (2 : ℝ) ^ n / Real.sqrt (N : ℝ) ≤
        (maxWalshMagnitude f : ℝ) := by
    exact (div_le_iff₀ hsqrtPos).2 (by
      simpa [mul_comm] using hrootMul)
  have hmaxDiv : 2 ^ (m + 2) ∣ maxWalshMagnitude f := by
    unfold maxWalshMagnitude
    obtain ⟨a, _ha, hsup⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      Finset.univ_nonempty
      (fun u ↦ (walshTransform f u).natAbs)
    have haDiv : 2 ^ (m + 2) ∣ (walshTransform f a).natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        two_pow_m_add_two_dvd_walshTransform_of_isResilient
          f m hm hf a
    rwa [hsup]
  obtain ⟨q, hq⟩ := hmaxDiv
  have hpowSplit :
      (2 : ℝ) ^ n =
        (2 : ℝ) ^ (m + 2) * (2 : ℝ) ^ (n - m - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hquotient :
      (2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ) ≤ q := by
    have hscaled :
        (2 : ℝ) ^ (m + 2) *
            ((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ)) ≤
          (2 : ℝ) ^ (m + 2) * (q : ℝ) := by
      calc
        (2 : ℝ) ^ (m + 2) *
            ((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ)) =
            (2 : ℝ) ^ n / Real.sqrt (N : ℝ) := by
          rw [hpowSplit]
          ring
        _ ≤ (maxWalshMagnitude f : ℝ) := hmaxLower
        _ = (2 : ℝ) ^ (m + 2) * (q : ℝ) := by
          exact_mod_cast hq
    exact le_of_mul_le_mul_left hscaled
      (by positivity : 0 < (2 : ℝ) ^ (m + 2))
  have hceil :
      ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ ≤ q :=
    Nat.ceil_le.mpr hquotient
  have hmaxNat :
      2 ^ (m + 2) *
          ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ ≤
        maxWalshMagnitude f := by
    rw [hq]
    exact Nat.mul_le_mul_left _ hceil
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hdimension : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have hamplitude :
      2 ^ (m + 2) *
          ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊ =
        2 * (2 ^ (m + 1) *
          ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    ring
  change nonlinearity f ≤
    2 ^ (n - 1) - 2 ^ (m + 1) *
      ⌈((2 : ℝ) ^ (n - m - 2) / Real.sqrt (N : ℝ))⌉₊
  apply Nat.le_sub_of_add_le
  omega

end CryptBoolean
