/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import CryptBoolean.Carlet.Chapter06.McElieceAx
public import CryptBoolean.Carlet.Chapter07.WalshDivisibility

import CryptBoolean.Carlet.Chapter06.DegreeRelation
import FABL.Chapter05.DegreeOneWeight

/-!
# Degree-sensitive Walsh divisibility

Carlet Theorem 13 and its correlation-immune companion, obtained from
Poisson summation and McEliece--Ax character-sum divisibility.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

attribute [local instance] submoduleFintype

private theorem two_pow_support_card_add_ceilDiv_dvd_walsh_subspace_sum
    (f : BooleanFunction n) (d : ℕ) (hd : 0 < d)
    (hdegree : FABL.functionAlgebraicDegree f ≤ d)
    (S : Finset (Fin n)) :
    (2 : ℤ) ^ (S.card + (n - S.card) ⌈/⌉ d) ∣
      ∑ u : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace S),
        walshTransform f u.1 := by
  classical
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace S
  let E := FABL.perpendicularSubspace Z
  have hfinrank : Module.finrank FABL.𝔽₂ Z = n - S.card := by
    simpa [Z] using finrank_coordinateZeroSubspace S
  let e : FABL.F₂Cube (n - S.card) ≃ₗ[FABL.𝔽₂] Z :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card]
      simpa using hfinrank.symm)
  let L : FABL.F₂Cube (n - S.card) →ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
    Z.subtype.comp e.toLinearMap
  let g : BooleanFunction (n - S.card) := fun y ↦ f (L y)
  have hdegreeRestriction : FABL.functionAlgebraicDegree g ≤ d := by
    apply (functionAlgebraicDegree_comp_affineMap_le_general
      f L.toAffineMap).trans
    simpa [g, L, Function.comp_def] using hdegree
  have hrestriction :=
    two_pow_ceilDiv_dvd_booleanCharacterSum_of_degree_le
      g d hd hdegreeRestriction
  have hrestrictionSum :
      (2 : ℤ) ^ ((n - S.card) ⌈/⌉ d) ∣
        ∑ x : Z, bitSignInt (f x.1) := by
    have hsum : (∑ y, bitSignInt (g y)) =
        ∑ x : Z, bitSignInt (f x.1) := by
      simpa [g, L] using
        (Equiv.sum_comp e.toEquiv (fun x : Z ↦ bitSignInt (f x.1)))
    rwa [hsum] at hrestriction
  have hcardE : Nat.card E = 2 ^ S.card := by
    dsimp [E, Z]
    rw [FABL.card_perpendicularSubspace,
      FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace]
  have hpoisson := sum_walshTransform_submodule_eq f E
  rw [hcardE] at hpoisson
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hpoisson
  rw [show FABL.perpendicularSubspace E = Z by
    dsimp [E]
    exact FABL.perpendicularSubspace_perpendicularSubspace Z] at hpoisson
  obtain ⟨q, hq⟩ := hrestrictionSum
  refine ⟨q, ?_⟩
  change (∑ u : E, walshTransform f u.1) = _
  calc
    (∑ u : E, walshTransform f u.1) =
        (2 : ℤ) ^ S.card * ∑ x : Z, bitSignInt (f x.1) := hpoisson
    _ = (2 : ℤ) ^ S.card *
        ((2 : ℤ) ^ ((n - S.card) ⌈/⌉ d) * q) := by rw [hq]
    _ = (2 : ℤ) ^ (S.card + (n - S.card) ⌈/⌉ d) * q := by
      rw [pow_add]
      ring

private theorem add_ceilDiv_sub_le_add_ceilDiv_sub
    {b k n d : ℕ} (hbk : b ≤ k) (hkn : k ≤ n) (hd : 0 < d) :
    b + (n - b) ⌈/⌉ d ≤ k + (n - k) ⌈/⌉ d := by
  have hceil :
      (n - b) ⌈/⌉ d ≤ (k - b) + (n - k) ⌈/⌉ d := by
    rw [ceilDiv_le_iff_le_mul hd]
    have hleft : k - b ≤ d * (k - b) := by
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left (k - b) hd
    have hright : n - k ≤ d * ((n - k) ⌈/⌉ d) :=
      (ceilDiv_le_iff_le_mul hd).mp le_rfl
    calc
      n - b = (k - b) + (n - k) := by omega
      _ ≤ d * (k - b) + d * ((n - k) ⌈/⌉ d) :=
        Nat.add_le_add hleft hright
      _ = d * ((k - b) + (n - k) ⌈/⌉ d) := by ring
  omega

private theorem one_add_pred_div_eq_ceilDiv
    (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    1 + (N - 1) / d = N ⌈/⌉ d := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hadd : N + d - 1 = (N - 1) + d := by omega
  rw [hadd, Nat.add_div_right _ hd]
  omega

private theorem two_pow_dvd_walshTransform_of_low_weight_zero_of_degree_le
    (f : BooleanFunction n) (m e d : ℕ) (hd : 0 < d)
    (hdegree : FABL.functionAlgebraicDegree f ≤ d)
    (hzero : (2 : ℤ) ^ e ∣ walshTransform f 0)
    (hlow : ∀ a : FABL.F₂Cube n, a ≠ 0 →
      (FABL.f₂Support a).card ≤ m → walshTransform f a = 0)
    (hexponent : ∀ k, m < k → k ≤ n →
      e ≤ k + (n - k) ⌈/⌉ d) :
    ∀ a : FABL.F₂Cube n, (2 : ℤ) ^ e ∣ walshTransform f a := by
  classical
  have hbyWeight : ∀ k : ℕ, ∀ a : FABL.F₂Cube n,
      (FABL.f₂Support a).card = k →
        (2 : ℤ) ^ e ∣ walshTransform f a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro a haCard
        by_cases hk : k ≤ m
        · by_cases ha : a = 0
          · simpa [ha] using hzero
          · rw [hlow a ha (by simpa [haCard] using hk)]
            exact dvd_zero _
        · have hmk : m < k := Nat.lt_of_not_ge hk
          have hkn : k ≤ n := by
            rw [← haCard]
            simpa using Finset.card_le_univ (FABL.f₂Support a)
          let Z := FABL.F₂DecisionTree.coordinateZeroSubspace
            (FABL.f₂Support a)
          let E := FABL.perpendicularSubspace Z
          have haE : a ∈ E := by
            exact (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
              (FABL.f₂Support a) a).2 (by simp)
          let aE : E := ⟨a, haE⟩
          have hsumDiv : (2 : ℤ) ^ e ∣
              ∑ u : E, walshTransform f u.1 := by
            have hdegreeDiv :=
              two_pow_support_card_add_ceilDiv_dvd_walsh_subspace_sum
                f d hd hdegree (FABL.f₂Support a)
            have hpow := pow_dvd_pow (2 : ℤ) (hexponent k hmk hkn)
            apply hpow.trans
            simpa [E, Z, haCard] using hdegreeDiv
          have hrestDiv : (2 : ℤ) ^ e ∣
              ∑ u ∈ (Finset.univ : Finset E).erase aE,
                walshTransform f u.1 := by
            apply Finset.dvd_sum
            intro u hu
            have hua : u ≠ aE := (Finset.mem_erase.mp hu).1
            have husubset : FABL.f₂Support u.1 ⊆ FABL.f₂Support a := by
              exact
                (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
                  (FABL.f₂Support a) u.1).1 u.property
            have hult : (FABL.f₂Support u.1).card < k := by
              have hcardLe := Finset.card_le_card husubset
              rw [haCard] at hcardLe
              apply lt_of_le_of_ne hcardLe
              intro hcardEq
              have hsupportEq :
                  FABL.f₂Support u.1 = FABL.f₂Support a := by
                apply Finset.eq_of_subset_of_card_le husubset
                rw [haCard, hcardEq]
              apply hua
              apply Subtype.ext
              apply (FABL.f₂CubeEquivFinset n).injective
              rw [FABL.f₂CubeEquivFinset_apply,
                FABL.f₂CubeEquivFinset_apply]
              exact hsupportEq
            exact ih (FABL.f₂Support u.1).card hult u.1 rfl
          obtain ⟨q, hq⟩ := hsumDiv
          obtain ⟨r, hr⟩ := hrestDiv
          refine ⟨q - r, ?_⟩
          have hdecompose :=
            Finset.sum_erase_add (Finset.univ : Finset E)
              (fun u : E ↦ walshTransform f u.1) (Finset.mem_univ aE)
          change
            (∑ u ∈ (Finset.univ : Finset E).erase aE,
                walshTransform f u.1) + walshTransform f a =
              ∑ u : E, walshTransform f u.1 at hdecompose
          rw [hq, hr] at hdecompose
          linarith
  intro a
  exact hbyWeight (FABL.f₂Support a).card a rfl

private theorem two_pow_m_add_ceilDiv_dvd_walshTransform_zero_of_isCorrelationImmune
    (f : BooleanFunction n) (m d : ℕ) (hm : m + 1 ≤ n)
    (hd : 0 < d) (hdegree : FABL.functionAlgebraicDegree f ≤ d)
    (hf : IsCorrelationImmune m f) :
    (2 : ℤ) ^ (m + (n - m) ⌈/⌉ d) ∣ walshTransform f 0 := by
  classical
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hlow :=
    theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hmn |>.mp hf
  have hmle : m ≤ Fintype.card (Fin n) := by
    simpa using Nat.le_of_lt hmn
  obtain ⟨S, _hempty, hScard⟩ :=
    Finset.exists_superset_card_eq
      (s := (∅ : Finset (Fin n))) (by simp) hmle
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace S
  let E := FABL.perpendicularSubspace Z
  have hcollapse :
      (∑ u : E, walshTransform f u.1) = walshTransform f 0 := by
    let zE : E := ⟨0, E.zero_mem⟩
    rw [show walshTransform f 0 = walshTransform f zE.1 by rfl]
    apply Finset.sum_eq_single zE
    · intro u _hu huz
      apply hlow u.1
      · intro hu0
        apply huz
        apply Subtype.ext
        exact hu0
      · have husubset : FABL.f₂Support u.1 ⊆ S := by
          exact
            (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
              S u.1).1 u.property
        simpa [hScard] using Finset.card_le_card husubset
    · simp
  have hdiv :=
    two_pow_support_card_add_ceilDiv_dvd_walsh_subspace_sum
      f d hd hdegree S
  rw [hcollapse] at hdiv
  simpa [E, Z, hScard] using hdiv

/-- Carlet Theorem 13: if `f` is `m`-resilient and has positive algebraic
degree, every Walsh coefficient is divisible by the stated degree-sensitive
power of two. -/
theorem two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsResilient m f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f) ∣
          walshTransform f a := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hlow :=
    theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hmn |>.mp hf.1
  have hzero :
      (2 : ℤ) ^ (m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f) ∣
          walshTransform f 0 := by
    rw [(isBalanced_iff_walshTransform_zero_eq_zero f).mp hf.2]
    exact dvd_zero _
  apply two_pow_dvd_walshTransform_of_low_weight_zero_of_degree_le
    f m (m + 2 + (n - m - 2) / FABL.functionAlgebraicDegree f)
      (FABL.functionAlgebraicDegree f) hd le_rfl hzero hlow
  intro k hmk hkn
  have hbase := add_ceilDiv_sub_le_add_ceilDiv_sub
    (b := m + 1) (k := k) (n := n)
    (d := FABL.functionAlgebraicDegree f) (by omega) hkn hd
  have hceil := one_add_pred_div_eq_ceilDiv
    (n - (m + 1)) (FABL.functionAlgebraicDegree f) (by omega) hd
  have hsub : n - (m + 1) - 1 = n - m - 2 := by omega
  calc
    m + 2 + (n - m - 2) / FABL.functionAlgebraicDegree f =
        m + 1 + (n - (m + 1)) ⌈/⌉
          FABL.functionAlgebraicDegree f := by
      rw [← hceil, hsub]
      omega
    _ ≤ k + (n - k) ⌈/⌉ FABL.functionAlgebraicDegree f := hbase

/-- The nonlinearity divisibility consequence of Carlet Theorem 13. -/
theorem two_pow_m_add_one_add_degree_quotient_dvd_nonlinearity_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsResilient m f) :
    2 ^ (m + 1 + (n - m - 2) / FABL.functionAlgebraicDegree f) ∣
      nonlinearity f := by
  let q := m + 1 + (n - m - 2) / FABL.functionAlgebraicDegree f
  have hwalsh :=
    two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isResilient
      f m hm hd hf
  have hqSucc :
      q + 1 = m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f := by
    dsimp [q]
    omega
  have hmax : 2 ^ (q + 1) ∣ maxWalshMagnitude f := by
    unfold maxWalshMagnitude
    obtain ⟨a, _ha, hsup⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube n)))
      Finset.univ_nonempty
      (fun u ↦ (walshTransform f u).natAbs)
    have haDiv : 2 ^ (q + 1) ∣ (walshTransform f a).natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat, hqSucc] using hwalsh a
    rwa [hsup]
  have hqLe : q + 1 ≤ n := by
    have hdivLe :
        (n - m - 2) / FABL.functionAlgebraicDegree f ≤ n - m - 2 :=
      Nat.div_le_self _ _
    dsimp [q]
    omega
  have hpow : (2 : ℤ) ^ (q + 1) ∣ (2 : ℤ) ^ n :=
    pow_dvd_pow (2 : ℤ) hqLe
  have hmaxInt : (2 : ℤ) ^ (q + 1) ∣ (maxWalshMagnitude f : ℤ) := by
    exact_mod_cast hmax
  have htwice : (2 : ℤ) ^ (q + 1) ∣
      2 * (nonlinearity f : ℤ) := by
    have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
    have hrelationInt :
        2 * (nonlinearity f : ℤ) + (maxWalshMagnitude f : ℤ) =
          (2 : ℤ) ^ n := by
      exact_mod_cast hrelation
    have hid : 2 * (nonlinearity f : ℤ) =
        (2 : ℤ) ^ n - (maxWalshMagnitude f : ℤ) := by
      omega
    rw [hid]
    exact hpow.sub hmaxInt
  obtain ⟨r, hr⟩ := htwice
  have hnonlinearityInt :
      (2 : ℤ) ^ q ∣ (nonlinearity f : ℤ) := by
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      2 * (nonlinearity f : ℤ) = (2 : ℤ) ^ (q + 1) * r := hr
      _ = 2 * ((2 : ℤ) ^ q * r) := by rw [pow_succ]; ring
  exact_mod_cast hnonlinearityInt

/-- Correlation-immunity companion to Carlet Theorem 13, including the
endpoint `m = n - 1`. -/
theorem two_pow_m_add_one_add_degree_quotient_dvd_walshTransform_of_isCorrelationImmune
    (f : BooleanFunction n) (m : ℕ) (hm : m + 1 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsCorrelationImmune m f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 1 +
        (n - m - 1) / FABL.functionAlgebraicDegree f) ∣
          walshTransform f a := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hlow :=
    theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hmn |>.mp hf
  have hzeroBase :=
    two_pow_m_add_ceilDiv_dvd_walshTransform_zero_of_isCorrelationImmune
      f m (FABL.functionAlgebraicDegree f) hm hd le_rfl hf
  have hzero :
      (2 : ℤ) ^ (m + 1 +
        (n - m - 1) / FABL.functionAlgebraicDegree f) ∣
          walshTransform f 0 := by
    have hceil := one_add_pred_div_eq_ceilDiv
      (n - m) (FABL.functionAlgebraicDegree f) (by omega) hd
    have hsub : n - m - 1 = (n - m) - 1 := by omega
    have hexponent :
        m + 1 + (n - m - 1) / FABL.functionAlgebraicDegree f =
          m + (n - m) ⌈/⌉ FABL.functionAlgebraicDegree f := by
      rw [hsub, ← hceil]
      omega
    rw [hexponent]
    exact hzeroBase
  apply two_pow_dvd_walshTransform_of_low_weight_zero_of_degree_le
    f m (m + 1 + (n - m - 1) / FABL.functionAlgebraicDegree f)
      (FABL.functionAlgebraicDegree f) hd le_rfl hzero hlow
  intro k hmk hkn
  have hbase := add_ceilDiv_sub_le_add_ceilDiv_sub
    (b := m + 1) (k := k) (n := n)
    (d := FABL.functionAlgebraicDegree f) (by omega) hkn hd
  have hfloor :
      (n - (m + 1)) / FABL.functionAlgebraicDegree f ≤
        (n - (m + 1)) ⌈/⌉ FABL.functionAlgebraicDegree f :=
    by
      simpa only [Nat.floorDiv_eq_div] using
        (floorDiv_le_ceilDiv
          (a := FABL.functionAlgebraicDegree f) (b := n - (m + 1)))
  have hsub : n - (m + 1) = n - m - 1 := by omega
  calc
    m + 1 + (n - m - 1) / FABL.functionAlgebraicDegree f =
        m + 1 + (n - (m + 1)) / FABL.functionAlgebraicDegree f := by
      rw [hsub]
    _ ≤ m + 1 + (n - (m + 1)) ⌈/⌉
        FABL.functionAlgebraicDegree f := Nat.add_le_add_left hfloor _
    _ ≤ k + (n - k) ⌈/⌉ FABL.functionAlgebraicDegree f := hbase

/-- Sharpened correlation-immunity companion to Carlet Theorem 13: the
additional weight divisibility raises the Walsh exponent by one. -/
theorem two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isCorrelationImmune_of_weight
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hd : 0 < FABL.functionAlgebraicDegree f)
    (hf : IsCorrelationImmune m f)
    (hweight :
      2 ^ (m + 1 +
        (n - m - 2) / FABL.functionAlgebraicDegree f) ∣
          hammingWeight f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f) ∣
          walshTransform f a := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hlow :=
    theorem_3_correlationImmune_iff_walshTransform_eq_zero
      m f hn hmn |>.mp hf
  let q := m + 1 +
    (n - m - 2) / FABL.functionAlgebraicDegree f
  have hweightInt : (2 : ℤ) ^ q ∣ (hammingWeight f : ℤ) := by
    exact_mod_cast hweight
  have htwice : (2 : ℤ) ^ (q + 1) ∣
      2 * (hammingWeight f : ℤ) := by
    obtain ⟨r, hr⟩ := hweightInt
    refine ⟨r, ?_⟩
    rw [hr, pow_succ]
    ring
  have hqLe : q + 1 ≤ n := by
    have hdivLe :
        (n - m - 2) / FABL.functionAlgebraicDegree f ≤ n - m - 2 :=
      Nat.div_le_self _ _
    dsimp [q]
    omega
  have hpow : (2 : ℤ) ^ (q + 1) ∣ (2 : ℤ) ^ n :=
    pow_dvd_pow (2 : ℤ) hqLe
  have hzero : (2 : ℤ) ^ (q + 1) ∣ walshTransform f 0 := by
    rw [walshTransform_zero_eq_two_pow_sub_two_weight]
    exact hpow.sub htwice
  have hqSucc :
      q + 1 = m + 2 +
        (n - m - 2) / FABL.functionAlgebraicDegree f := by
    dsimp [q]
    omega
  rw [← hqSucc]
  apply two_pow_dvd_walshTransform_of_low_weight_zero_of_degree_le
    f m (q + 1) (FABL.functionAlgebraicDegree f) hd le_rfl hzero hlow
  intro k hmk hkn
  have hbase := add_ceilDiv_sub_le_add_ceilDiv_sub
    (b := m + 1) (k := k) (n := n)
    (d := FABL.functionAlgebraicDegree f) (by omega) hkn hd
  have hceil := one_add_pred_div_eq_ceilDiv
    (n - (m + 1)) (FABL.functionAlgebraicDegree f) (by omega) hd
  have hsub : n - (m + 1) - 1 = n - m - 2 := by omega
  calc
    q + 1 = m + 1 + (n - (m + 1)) ⌈/⌉
        FABL.functionAlgebraicDegree f := by
      rw [← hceil, hsub]
      dsimp [q]
      omega
    _ ≤ k + (n - k) ⌈/⌉ FABL.functionAlgebraicDegree f := hbase

end CryptBoolean
