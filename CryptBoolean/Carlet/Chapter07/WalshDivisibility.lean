/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter07.NumericalNormalForm

import FABL.Chapter05.DegreeOneWeight

/-!
# Walsh and weight divisibility for resilient functions

The divisibility consequences following Carlet Proposition 32.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

attribute [local instance] submoduleFintype

/-- The Walsh sum over a binary subspace equals its cardinality times the
sign sum over the perpendicular subspace. -/
theorem sum_walshTransform_submodule_eq
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    (∑ u : E, walshTransform f u.1) =
      (Nat.card E : ℤ) *
        ∑ x : FABL.perpendicularSubspace E, bitSignInt (f x.1) := by
  classical
  have hraw (u : FABL.F₂Cube n) :
      rawFourierTransform (realSignView f) u =
        (walshTransform f u : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hpoisson := rawPoissonSummationFormula (realSignView f) E 0 0
  simp_rw [zero_add, FABL.vectorWalshCharacter_zero, AddChar.one_apply,
    one_mul, hraw] at hpoisson
  apply Int.cast_injective (α := ℝ)
  simpa [bitSignInt_cast_eq_realSignView] using hpoisson

private theorem natCard_coordinateZeroSubspace
    (S : Finset (Fin n)) :
    Nat.card (FABL.F₂DecisionTree.coordinateZeroSubspace S) =
      2 ^ (n - S.card) := by
  rw [FABL.card_submodule_eq_two_pow_finrank]
  congr 1
  have hcodimension :=
    FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace S
  rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace] at hcodimension
  have hfinrank :
      Module.finrank FABL.𝔽₂
          (FABL.F₂DecisionTree.coordinateZeroSubspace S) ≤ n := by
    simpa using
      (FABL.F₂DecisionTree.coordinateZeroSubspace S).finrank_le
  omega

private theorem two_dvd_sum_bitSignInt_of_two_dvd_natCard
    {E : Type*} [Fintype E] (g : E → FABL.𝔽₂)
    (hcard : 2 ∣ Nat.card E) :
    (2 : ℤ) ∣ ∑ x : E, bitSignInt (g x) := by
  classical
  choose z hz using fun x : E ↦
    if hx : g x = 1 then
      (⟨(-1 : ℤ), by simp [bitSignInt_eq_if_one, hx]⟩ :
        ∃ q : ℤ, bitSignInt (g x) = 1 + 2 * q)
    else
      (⟨0, by simp [bitSignInt_eq_if_one, hx]⟩ :
        ∃ q : ℤ, bitSignInt (g x) = 1 + 2 * q)
  obtain ⟨q, hq⟩ := hcard
  refine ⟨(q : ℤ) + ∑ x : E, z x, ?_⟩
  calc
    ∑ x : E, bitSignInt (g x) =
        ∑ x : E, (1 + 2 * z x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hz x
    _ = (Nat.card E : ℤ) + 2 * ∑ x : E, z x := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ = 2 * ((q : ℤ) + ∑ x : E, z x) := by
      rw [hq]
      push_cast
      ring

private theorem two_pow_sub_add_one_dvd_walshTransform_of_numericalDegree_le
    (f : BooleanFunction n) (D : ℕ) (hDpos : 1 ≤ D) (hDle : D ≤ n)
    (hdegree :
      FABL.functionNumericalDegree (FABL.booleanRealEmbedding f) ≤ D) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (n - D + 1) ∣ walshTransform f a := by
  intro a
  have hfourierDegree : FABL.fourierDegree (signCubeView f).toReal ≤ D := by
    rw [← functionNumericalDegree_booleanRealEmbedding_eq_fourierDegree_signCubeView]
    exact hdegree
  obtain ⟨z, hz⟩ :=
    FABL.isFourierGranular_signValue_of_fourierDegree_le
      (signCubeView f) hDpos hfourierDegree (FABL.f₂Support a)
  have hcoefficient :
      FABL.vectorFourierCoeff (realSignView f) a =
        (z : ℝ) * (2 * ((2 : ℝ)⁻¹) ^ D) := by
    rw [FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
      ← signCubeView_toReal]
    exact hz
  refine ⟨z, ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff, hcoefficient]
  push_cast
  have hpow :
      (2 : ℝ) ^ n = (2 : ℝ) ^ D * (2 : ℝ) ^ (n - D) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, pow_succ]
  rw [inv_pow]
  field_simp

private theorem coordinateSum_univ_eq_affineFunction :
    (FABL.coordinateSum (Finset.univ : Finset (Fin n)) :
      BooleanFunction n) =
      FABL.affineFunction 0
        (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))) := by
  funext x
  rw [FABL.affineFunction, zero_add,
    FABL.f₂DotProduct_eq_coordinateSum_f₂Support]
  have hsupport :
      FABL.f₂Support
          (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))) =
        Finset.univ :=
    (FABL.f₂CubeEquivFinset n).right_inv Finset.univ
  rw [hsupport]

private theorem two_pow_dvd_walshTransform_of_low_weight_zero
    (f : BooleanFunction n) (m e : ℕ) (hm : m + 2 ≤ n)
    (he : e ≤ m + 2)
    (hzero : (2 : ℤ) ^ e ∣ walshTransform f 0)
    (hlow : ∀ a : FABL.F₂Cube n, a ≠ 0 →
      (FABL.f₂Support a).card ≤ m → walshTransform f a = 0) :
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
          let Z := FABL.F₂DecisionTree.coordinateZeroSubspace
            (FABL.f₂Support a)
          let E := FABL.perpendicularSubspace Z
          have haE : a ∈ E := by
            exact (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
              (FABL.f₂Support a) a).2 (by simp)
          let aE : E := ⟨a, haE⟩
          have hsum := sum_walshTransform_submodule_eq f E
          have hcardE : Nat.card E = 2 ^ k := by
            dsimp [E, Z]
            rw [FABL.card_perpendicularSubspace,
              FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace,
              haCard]
          have hsumDiv : (2 : ℤ) ^ e ∣
              ∑ u : E, walshTransform f u.1 := by
            rw [hsum, hcardE]
            simp only [Nat.cast_pow, Nat.cast_ofNat]
            rw [show FABL.perpendicularSubspace E = Z by
              dsimp [E]
              exact FABL.perpendicularSubspace_perpendicularSubspace Z]
            by_cases hek : e ≤ k
            · exact (pow_dvd_pow (2 : ℤ) hek).mul_right _
            · have heq : e = k + 1 := by omega
              have hklt : k < n := by omega
              have hcardZ :
                  Nat.card Z = 2 ^ (n - k) := by
                dsimp [Z]
                rw [natCard_coordinateZeroSubspace, haCard]
              have htwoCard : 2 ∣ Nat.card Z := by
                rw [hcardZ]
                have hexponent : n - k ≠ 0 :=
                  Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)
                exact
                  (Even.pow_of_ne_zero (by norm_num : Even 2) hexponent).two_dvd
              obtain ⟨q, hq⟩ :=
                two_dvd_sum_bitSignInt_of_two_dvd_natCard
                  (fun x : Z ↦ f x.1) htwoCard
              refine ⟨q, ?_⟩
              rw [heq, pow_succ, hq]
              ring
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

private theorem two_pow_m_add_one_dvd_walshTransform_zero_of_isCorrelationImmune
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsCorrelationImmune m f) :
    (2 : ℤ) ^ (m + 1) ∣ walshTransform f 0 := by
  classical
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hlow :=
    theorem_3_correlationImmune_iff_walshTransform_eq_zero m f hn hmn |>.mp hf
  have hmle : m ≤ Fintype.card (Fin n) := by simpa using (Nat.le_of_lt hmn)
  obtain ⟨S, _hempty, hScard⟩ :=
    Finset.exists_superset_card_eq
      (s := (∅ : Finset (Fin n))) (by simp) hmle
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace S
  let E := FABL.perpendicularSubspace Z
  have hsum := sum_walshTransform_submodule_eq f E
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
  have hcardE : Nat.card E = 2 ^ m := by
    dsimp [E, Z]
    rw [FABL.card_perpendicularSubspace,
      FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace,
      hScard]
  rw [hcollapse, hcardE] at hsum
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hsum
  rw [show FABL.perpendicularSubspace E = Z by
    dsimp [E]
    exact FABL.perpendicularSubspace_perpendicularSubspace Z] at hsum
  have hcardZ : Nat.card Z = 2 ^ (n - m) := by
    dsimp [Z]
    rw [natCard_coordinateZeroSubspace, hScard]
  have htwoCard : 2 ∣ Nat.card Z := by
    rw [hcardZ]
    have hexponent : n - m ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt hmn)
    exact (Even.pow_of_ne_zero (by norm_num : Even 2) hexponent).two_dvd
  obtain ⟨q, hq⟩ :=
    two_dvd_sum_bitSignInt_of_two_dvd_natCard
      (fun x : Z ↦ f x.1) htwoCard
  refine ⟨q, ?_⟩
  calc
    walshTransform f 0 =
        (2 : ℤ) ^ m * ∑ x : Z, bitSignInt (f x.1) := hsum
    _ = (2 : ℤ) ^ m * (2 * q) := by rw [hq]
    _ = (2 : ℤ) ^ (m + 1) * q := by rw [pow_succ]; ring

/-- Carlet's divisibility consequence after Proposition 32: every Walsh
coefficient of an `m`-resilient function is divisible by `2^(m+2)`. -/
theorem two_pow_m_add_two_dvd_walshTransform_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsResilient m f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 2) ∣ walshTransform f a := by
  classical
  let g := f +
    (FABL.coordinateSum (Finset.univ : Finset (Fin n)) : BooleanFunction n)
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hdegree :
      FABL.functionNumericalDegree (FABL.booleanRealEmbedding g) ≤
        n - m - 1 := by
    exact
      (proposition_32_resilient_iff_functionNumericalDegree_le
        m f hn hmn).mp hf
  have hgranular :=
    two_pow_sub_add_one_dvd_walshTransform_of_numericalDegree_le
      g (n - m - 1) (by omega) (by omega) hdegree
  intro a
  let p : FABL.F₂Cube n :=
    FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))
  have hg := hgranular (a + p)
  have hshift : walshTransform g (a + p) = walshTransform f a := by
    dsimp [g]
    rw [coordinateSum_univ_eq_affineFunction,
      walshTransform_add_affineFunction]
    rw [show bitSignInt 0 = 1 by simp [bitSignInt_eq_if_one]]
    simp only [one_mul]
    congr 1
    funext i
    simp only [p, Pi.add_apply, FABL.f₂CubeOfFinset_apply,
      Finset.mem_univ, if_true]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hshift] at hg
  simpa [show n - (n - m - 1) + 1 = m + 2 by omega] using hg

/-- Every Walsh coefficient of an `m`th-order correlation-immune function is
divisible by `2^(m+1)` when `m ≤ n-2`. -/
theorem two_pow_m_add_one_dvd_walshTransform_of_isCorrelationImmune
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsCorrelationImmune m f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 1) ∣ walshTransform f a := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  apply two_pow_dvd_walshTransform_of_low_weight_zero
    f m (m + 1) hm (by omega)
    (two_pow_m_add_one_dvd_walshTransform_zero_of_isCorrelationImmune
      f m hm hf)
  exact theorem_3_correlationImmune_iff_walshTransform_eq_zero
    m f hn hmn |>.mp hf

/-- The Hamming weight of an `m`th-order correlation-immune function is
divisible by `2^m` when `m ≤ n-2`. -/
theorem two_pow_m_dvd_hammingWeight_of_isCorrelationImmune
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsCorrelationImmune m f) :
    2 ^ m ∣ hammingWeight f := by
  have hzero :=
    two_pow_m_add_one_dvd_walshTransform_zero_of_isCorrelationImmune
      f m hm hf
  have hpow : (2 : ℤ) ^ (m + 1) ∣ (2 : ℤ) ^ n :=
    pow_dvd_pow (2 : ℤ) (by omega)
  have htwice : (2 : ℤ) ^ (m + 1) ∣
      2 * (hammingWeight f : ℤ) := by
    have hid :
        2 * (hammingWeight f : ℤ) =
          (2 : ℤ) ^ n - walshTransform f 0 := by
      rw [walshTransform_zero_eq_two_pow_sub_two_weight]
      ring
    rw [hid]
    exact hpow.sub hzero
  obtain ⟨q, hq⟩ := htwice
  have hweightInt :
      (2 : ℤ) ^ m ∣ (hammingWeight f : ℤ) := by
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    calc
      2 * (hammingWeight f : ℤ) = (2 : ℤ) ^ (m + 1) * q := hq
      _ = 2 * ((2 : ℤ) ^ m * q) := by rw [pow_succ]; ring
  exact_mod_cast hweightInt

/-- If an `m`th-order correlation-immune function has weight divisible by
`2^(m+1)`, then every Walsh coefficient is divisible by `2^(m+2)`. -/
theorem two_pow_m_add_two_dvd_walshTransform_of_isCorrelationImmune_of_weight
    (f : BooleanFunction n) (m : ℕ) (hm : m + 2 ≤ n)
    (hf : IsCorrelationImmune m f)
    (hweight : 2 ^ (m + 1) ∣ hammingWeight f) :
    ∀ a : FABL.F₂Cube n,
      (2 : ℤ) ^ (m + 2) ∣ walshTransform f a := by
  have hn : 0 < n := by omega
  have hmn : m < n := by omega
  have hweightInt :
      (2 : ℤ) ^ (m + 1) ∣ (hammingWeight f : ℤ) := by
    exact_mod_cast hweight
  have htwice :
      (2 : ℤ) ^ (m + 2) ∣ 2 * (hammingWeight f : ℤ) := by
    obtain ⟨q, hq⟩ := hweightInt
    refine ⟨q, ?_⟩
    calc
      2 * (hammingWeight f : ℤ) =
          2 * ((2 : ℤ) ^ (m + 1) * q) := by rw [hq]
      _ = (2 : ℤ) ^ (m + 2) * q := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        ring
  have hpow : (2 : ℤ) ^ (m + 2) ∣ (2 : ℤ) ^ n :=
    pow_dvd_pow (2 : ℤ) (by omega)
  have hzero : (2 : ℤ) ^ (m + 2) ∣ walshTransform f 0 := by
    rw [walshTransform_zero_eq_two_pow_sub_two_weight]
    exact hpow.sub htwice
  apply two_pow_dvd_walshTransform_of_low_weight_zero
    f m (m + 2) hm (by omega) hzero
  exact theorem_3_correlationImmune_iff_walshTransform_eq_zero
    m f hn hmn |>.mp hf

end CryptBoolean
