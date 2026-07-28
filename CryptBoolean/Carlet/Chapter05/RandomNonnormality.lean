/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.Normality
public import CryptBoolean.Carlet.Chapter04.DegreeCount
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Random Boolean functions are deeply nonnormal

The finite union bound and asymptotic consequence underlying Carlet's
random-nonnormality statement.
-/

open scoped BooleanCube Topology

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

private noncomputable def fixedOnRangeEquiv
    {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (e : X → Y) (g : Y → Z) :
    {f : Y → Z // ∀ x, f (e x) = g (e x)} ≃
      ({y : Y // y ∉ Set.range e} → Z) where
  toFun f y := f.1 y.1
  invFun h :=
    ⟨fun y ↦ if hy : y ∈ Set.range e then g y else h ⟨y, hy⟩,
      fun x ↦ by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hy
      simp [f.2 x]
    · simp [hy]
  right_inv h := by
    funext y
    simp [y.2]

private theorem card_fixedOnRange
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (e : X → Y) (he : Function.Injective e) (g : Y → Z) :
    Nat.card {f : Y → Z // ∀ x, f (e x) = g (e x)} =
      Fintype.card Z ^ (Fintype.card Y - Fintype.card X) := by
  classical
  rw [Nat.card_congr (fixedOnRangeEquiv e g), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_subtype_compl]
  rw [Fintype.card_congr (Equiv.ofInjective e he).symm]

private abbrev InjectiveBinaryLinearMap (n k : ℕ) :=
  {L : FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube n // Function.Injective L}

private structure WeakNormalCertificate (n k : ℕ) where
  linear : InjectiveBinaryLinearMap n k
  offset : FABL.F₂Cube n
  constant : FABL.𝔽₂
  frequency : FABL.F₂Cube n

private noncomputable instance :
    Fintype (FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube n) :=
  Fintype.ofEquiv (Fin k → FABL.F₂Cube n)
    (Module.piEquiv (Fin k) FABL.𝔽₂ (FABL.F₂Cube n)).toEquiv

private noncomputable instance : Fintype (InjectiveBinaryLinearMap n k) :=
  Fintype.ofFinite _

private def weakNormalCertificateEquiv :
    (InjectiveBinaryLinearMap n k ×
      FABL.F₂Cube n × FABL.𝔽₂ × FABL.F₂Cube n) ≃
        WeakNormalCertificate n k where
  toFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  invFun q := ⟨q.linear, q.offset, q.constant, q.frequency⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance : Fintype (WeakNormalCertificate n k) :=
  Fintype.ofEquiv
    (InjectiveBinaryLinearMap n k ×
      FABL.F₂Cube n × FABL.𝔽₂ × FABL.F₂Cube n)
    weakNormalCertificateEquiv

private def weakNormalCertificateEvent
    (q : WeakNormalCertificate n k) : Set (BooleanFunction n) :=
  {f | ∀ y, f (q.linear.1 y + q.offset) =
    FABL.affineFunction q.constant q.frequency (q.linear.1 y + q.offset)}

private theorem ncard_weakNormalCertificateEvent
    (q : WeakNormalCertificate n k) :
    (weakNormalCertificateEvent q).ncard = 2 ^ (2 ^ n - 2 ^ k) := by
  classical
  let e : FABL.F₂Cube k → FABL.F₂Cube n := fun y ↦ q.linear.1 y + q.offset
  let g : FABL.F₂Cube n → FABL.𝔽₂ :=
    FABL.affineFunction q.constant q.frequency
  have he : Function.Injective e := by
    intro x y hxy
    apply q.linear.2
    exact add_right_cancel hxy
  change Nat.card {f : BooleanFunction n // ∀ y, f (e y) = g (e y)} = _
  rw [card_fixedOnRange e he g]
  simp

private theorem isKWeaklyNormal_subset_certificateUnion :
    {f : BooleanFunction n | IsKWeaklyNormal f k} ⊆
      ⋃ q : WeakNormalCertificate n k, weakNormalCertificateEvent q := by
  intro f hf
  obtain ⟨H, a, hdim, b, c, hflat⟩ := hf
  let e : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] H :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim])
  let L : FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube n :=
    H.subtype.comp e.toLinearMap
  have hL : Function.Injective L := H.subtype_injective.comp e.injective
  let q : WeakNormalCertificate n k :=
    ⟨⟨L, hL⟩, a, b, c⟩
  rw [Set.mem_iUnion]
  refine ⟨q, ?_⟩
  intro y
  apply hflat
  change L y + a ∈ FABL.binaryAffineSubspace H a
  simp [FABL.binaryAffineSubspace, L]

private theorem card_injectiveBinaryLinearMap_le :
    Fintype.card (InjectiveBinaryLinearMap n k) ≤ 2 ^ (n * k) := by
  classical
  calc
    Fintype.card (InjectiveBinaryLinearMap n k) ≤
        Fintype.card (FABL.F₂Cube k →ₗ[FABL.𝔽₂] FABL.F₂Cube n) :=
      Fintype.card_subtype_le _
    _ = Fintype.card (Fin k → FABL.F₂Cube n) := by
      exact Fintype.card_congr
        (Module.piEquiv (Fin k) FABL.𝔽₂ (FABL.F₂Cube n)).toEquiv.symm
    _ = 2 ^ (n * k) := by
      rw [Fintype.card_fun, card_f₂Cube]
      simp [pow_mul]

private theorem card_weakNormalCertificate_le :
    Fintype.card (WeakNormalCertificate n k) ≤ 2 ^ (n * k + 2 * n + 1) := by
  classical
  rw [show Fintype.card (WeakNormalCertificate n k) =
      Fintype.card (InjectiveBinaryLinearMap n k) *
        Fintype.card (FABL.F₂Cube n) * Fintype.card FABL.𝔽₂ *
          Fintype.card (FABL.F₂Cube n) by
    rw [Fintype.card_congr weakNormalCertificateEquiv.symm]
    simp only [Fintype.card_prod]
    ring]
  calc
    Fintype.card (InjectiveBinaryLinearMap n k) *
          Fintype.card (FABL.F₂Cube n) * Fintype.card FABL.𝔽₂ *
        Fintype.card (FABL.F₂Cube n) ≤
      2 ^ (n * k) * 2 ^ n * 2 * 2 ^ n := by
        gcongr
        · exact card_injectiveBinaryLinearMap_le
        · simp
        · norm_num [FABL.𝔽₂]
        · simp
    _ = 2 ^ (n * k + 2 * n + 1) := by ring_nf

private theorem natCard_isKWeaklyNormal_le :
    Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} ≤
      2 ^ (n * k + 2 * n + 1) * 2 ^ (2 ^ n - 2 ^ k) := by
  classical
  have hunion :=
    Set.ncard_iUnion_le_of_fintype
      (fun q : WeakNormalCertificate n k ↦ weakNormalCertificateEvent q)
  calc
    Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} =
        ({f : BooleanFunction n | IsKWeaklyNormal f k} : Set _).ncard := rfl
    _ ≤ (⋃ q : WeakNormalCertificate n k,
          weakNormalCertificateEvent q).ncard :=
      Set.ncard_le_ncard isKWeaklyNormal_subset_certificateUnion
    _ ≤ ∑ q : WeakNormalCertificate n k,
          (weakNormalCertificateEvent q).ncard := hunion
    _ = Fintype.card (WeakNormalCertificate n k) *
          2 ^ (2 ^ n - 2 ^ k) := by
      simp only [ncard_weakNormalCertificateEvent, Finset.sum_const,
        Finset.card_univ, Nat.nsmul_eq_mul]
    _ ≤ 2 ^ (n * k + 2 * n + 1) * 2 ^ (2 ^ n - 2 ^ k) :=
      Nat.mul_le_mul_right _ card_weakNormalCertificate_le

/-- The exact uniform probability that an `n`-variable Boolean function is
`k`-weakly normal. -/
noncomputable def weakNormalityProbability (n k : ℕ) : ℝ :=
  (Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} : ℝ) /
    Nat.card (BooleanFunction n)

/-- A finite union bound for weak normality. -/
theorem weakNormalityProbability_le_of_le (hk : k ≤ n) :
    weakNormalityProbability n k ≤
      (2 : ℝ) ^ (n * k + 2 * n + 1) /
        (2 : ℝ) ^ (2 ^ k) := by
  have hcount := natCard_isKWeaklyNormal_le (n := n) (k := k)
  rw [weakNormalityProbability, natCard_booleanFunction]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hpow : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hk
  have hsplit :
      (2 : ℝ) ^ (2 ^ n) = (2 : ℝ) ^ (2 ^ k) * (2 : ℝ) ^ (2 ^ n - 2 ^ k) := by
    rw [← pow_add, Nat.add_sub_of_le hpow]
  rw [hsplit]
  have hcountR :
      (Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} : ℝ) ≤
        (2 : ℝ) ^ (n * k + 2 * n + 1) *
          (2 : ℝ) ^ (2 ^ n - 2 ^ k) := by
    exact_mod_cast hcount
  calc
    (Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} : ℝ) /
          ((2 : ℝ) ^ (2 ^ k) * (2 : ℝ) ^ (2 ^ n - 2 ^ k)) ≤
        ((2 : ℝ) ^ (n * k + 2 * n + 1) *
          (2 : ℝ) ^ (2 ^ n - 2 ^ k)) /
          ((2 : ℝ) ^ (2 ^ k) * (2 : ℝ) ^ (2 ^ n - 2 ^ k)) :=
      div_le_div_of_nonneg_right hcountR (by positivity)
    _ = (2 : ℝ) ^ (n * k + 2 * n + 1) /
        (2 : ℝ) ^ (2 ^ k) := by field_simp

private theorem not_isKWeaklyNormal_of_lt (hkn : n < k)
    (f : BooleanFunction n) : ¬IsKWeaklyNormal f k := by
  rintro ⟨H, _a, hdim, _⟩
  have hle := Submodule.finrank_le H
  have hambient : Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [hdim, hambient] at hle
  omega

/-- The finite weak-normality union bound is total in `k`; dimensions larger
than the ambient dimension have probability zero. -/
theorem weakNormalityProbability_le (n k : ℕ) :
    weakNormalityProbability n k ≤
      (2 : ℝ) ^ (n * k + 2 * n + 1) /
        (2 : ℝ) ^ (2 ^ k) := by
  by_cases hk : k ≤ n
  · exact weakNormalityProbability_le_of_le hk
  · haveI : IsEmpty {f : BooleanFunction n // IsKWeaklyNormal f k} :=
      ⟨fun f ↦ (not_isKWeaklyNormal_of_lt (by omega) f.1) f.2⟩
    rw [weakNormalityProbability, Nat.card_of_isEmpty]
    norm_num only [Nat.cast_zero, zero_div]
    exact div_nonneg
      (show (0 : ℝ) ≤ (2 : ℝ) ^ (n * k + 2 * n + 1) by positivity)
      (show (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ k) by positivity)

/-- The exact uniform probability that an `n`-variable Boolean function is
`k`-normal. -/
noncomputable def normalityProbability (n k : ℕ) : ℝ :=
  (Nat.card {f : BooleanFunction n // IsKNormal f k} : ℝ) /
    Nat.card (BooleanFunction n)

/-- Normality is no more likely than weak normality. -/
theorem normalityProbability_le_weakNormalityProbability (n k : ℕ) :
    normalityProbability n k ≤ weakNormalityProbability n k := by
  have hcard : Nat.card {f : BooleanFunction n // IsKNormal f k} ≤
      Nat.card {f : BooleanFunction n // IsKWeaklyNormal f k} :=
    Nat.card_le_card_of_injective
      (fun f ↦ ⟨f.1, f.2.isKWeaklyNormal⟩)
      (fun x y h ↦ Subtype.ext
        (congrArg
          (fun z : {f : BooleanFunction n // IsKWeaklyNormal f k} ↦ z.1) h))
  unfold normalityProbability weakNormalityProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private theorem weakNormalityProbability_le_half_pow
    (hn : 0 < n) (hk : 2 < k)
    (hratio : (3 : ℝ) ≤
      (2 : ℝ) ^ k / ((n : ℝ) * (k : ℝ))) :
    weakNormalityProbability n k ≤ ((1 : ℝ) / 2) ^ n := by
  have hdenom : (0 : ℝ) < (n : ℝ) * (k : ℝ) := by positivity
  have hlargeR :
      (3 : ℝ) * ((n : ℝ) * (k : ℝ)) ≤ (2 : ℝ) ^ k :=
    (le_div_iff₀ hdenom).mp hratio
  have hlarge : 3 * (n * k) ≤ 2 ^ k := by
    exact_mod_cast hlargeR
  have hexponent : n * k + 2 * n + 1 ≤ 2 * (n * k) := by nlinarith
  have hgap : n ≤ 2 ^ k - (n * k + 2 * n + 1) := by omega
  have hsplit :
      (2 : ℝ) ^ (2 ^ k) =
        (2 : ℝ) ^ (n * k + 2 * n + 1) *
          (2 : ℝ) ^ (2 ^ k - (n * k + 2 * n + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le (hexponent.trans (by omega))]
  calc
    weakNormalityProbability n k ≤
        (2 : ℝ) ^ (n * k + 2 * n + 1) / (2 : ℝ) ^ (2 ^ k) :=
      weakNormalityProbability_le n k
    _ = ((1 : ℝ) / 2) ^ (2 ^ k - (n * k + 2 * n + 1)) := by
      rw [hsplit, div_eq_iff (by positivity :
        (2 : ℝ) ^ (n * k + 2 * n + 1) *
          (2 : ℝ) ^ (2 ^ k - (n * k + 2 * n + 1)) ≠ 0)]
      rw [div_pow]
      field_simp
      simp
    _ ≤ ((1 : ℝ) / 2) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hgap

/-- The cited general asymptotic theorem: if `k n > 2` eventually and
`2^(k n) / (n * k n)` diverges, then a uniformly random Boolean function is
`k n`-weakly normal with probability tending to zero. -/
theorem tendsto_weakNormalityProbability_zero_of_ratio
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in Filter.atTop, 2 < k n)
    (hratio : Filter.Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ (k n) / ((n : ℝ) * (k n : ℝ)))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ weakNormalityProbability n (k n))
      Filter.atTop (𝓝 0) := by
  have hratio3 : ∀ᶠ n in Filter.atTop,
      (3 : ℝ) ≤ (2 : ℝ) ^ (k n) / ((n : ℝ) * (k n : ℝ)) :=
    hratio.eventually (Filter.eventually_ge_atTop 3)
  have hupper : Filter.Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun n ↦ by
      unfold weakNormalityProbability
      positivity
  · filter_upwards [Filter.eventually_gt_atTop 0, hk, hratio3] with n hn hkn hr
    exact weakNormalityProbability_le_half_pow hn hkn hr

/-- The probability that a uniformly random Boolean function is not
`k`-weakly normal. -/
noncomputable def nonWeakNormalityProbability (n k : ℕ) : ℝ :=
  1 - weakNormalityProbability n k

/-- Under the cited ratio hypothesis, random functions are almost surely not
weakly normal at the prescribed dimensions. -/
theorem tendsto_nonWeakNormalityProbability_one_of_ratio
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in Filter.atTop, 2 < k n)
    (hratio : Filter.Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ (k n) / ((n : ℝ) * (k n : ℝ)))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ nonWeakNormalityProbability n (k n))
      Filter.atTop (𝓝 1) := by
  have hzero := tendsto_weakNormalityProbability_zero_of_ratio k hk hratio
  unfold nonWeakNormalityProbability
  simpa only [sub_zero] using hzero.const_sub 1

/-- The probability that a uniformly random Boolean function is not
`k`-normal. -/
noncomputable def nonnormalityProbability (n k : ℕ) : ℝ :=
  1 - normalityProbability n k

/-- Under the cited ratio hypothesis, random functions are almost surely not
normal at the prescribed dimensions. -/
theorem tendsto_nonnormalityProbability_one_of_ratio
    (k : ℕ → ℕ)
    (hk : ∀ᶠ n in Filter.atTop, 2 < k n)
    (hratio : Filter.Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ (k n) / ((n : ℝ) * (k n : ℝ)))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ nonnormalityProbability n (k n))
      Filter.atTop (𝓝 1) := by
  have hnonweak :=
    tendsto_nonWeakNormalityProbability_one_of_ratio k hk hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hnonweak tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun n ↦ by
      unfold nonWeakNormalityProbability nonnormalityProbability
      linarith [normalityProbability_le_weakNormalityProbability n (k n)]
  · exact Filter.Eventually.of_forall fun n ↦ by
      have hprob : 0 ≤ normalityProbability n (k n) := by
        unfold normalityProbability
        positivity
      unfold nonnormalityProbability
      linarith

private theorem tendsto_natCast_rpow_div_log_atTop
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ δ / Real.log (n : ℝ))
      Filter.atTop Filter.atTop := by
  have hzeroReal : Filter.Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ δ) Filter.atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have hzero : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ) ^ δ)
      Filter.atTop (𝓝 0) :=
    hzeroReal.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in Filter.atTop,
      0 < Real.log (n : ℝ) / (n : ℝ) ^ δ := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hzeroAbove : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ) ^ δ)
      Filter.atTop (𝓝[>] 0) :=
    Filter.tendsto_inf.2 ⟨hzero, Filter.tendsto_principal.2 hpos⟩
  convert hzeroAbove.inv_tendsto_nhdsGT_zero using 1
  funext n
  exact (inv_div (Real.log (n : ℝ)) ((n : ℝ) ^ δ)).symm

/-- Carlet's logarithmic dimension `floor (α log₂ n)`. -/
noncomputable def carletNonnormalityDimension (α : ℝ) (n : ℕ) : ℕ :=
  ⌊α * Real.logb 2 (n : ℝ)⌋₊

private theorem tendsto_carletNonnormalityDimension
    {α : ℝ} (hα : 1 < α) :
    Filter.Tendsto (carletNonnormalityDimension α)
      Filter.atTop Filter.atTop := by
  apply tendsto_nat_floor_atTop.comp
  exact ((Real.tendsto_logb_atTop (b := (2 : ℝ)) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop (by linarith)

private theorem tendsto_carletNonnormalityRatio
    {α : ℝ} (hα : 1 < α) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ carletNonnormalityDimension α n /
          ((n : ℝ) * (carletNonnormalityDimension α n : ℝ)))
      Filter.atTop Filter.atTop := by
  let δ : ℝ := α - 1
  let C : ℝ := Real.log 2 / (2 * α)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (Real.log_pos (by norm_num)) (mul_pos two_pos (by linarith))
  have hcomparison : Filter.Tendsto
      (fun n : ℕ ↦ C * ((n : ℝ) ^ δ / Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_rpow_div_log_atTop hδ).const_mul_atTop hC
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hcomparison
  filter_upwards [Filter.eventually_gt_atTop 1,
    (tendsto_carletNonnormalityDimension hα).eventually
      (Filter.eventually_gt_atTop 2)] with n hn hk
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 < Real.logb 2 (n : ℝ) := by
    rw [Real.logb]
    positivity
  have hx : 0 ≤ α * Real.logb 2 (n : ℝ) :=
    mul_nonneg (by linarith) hlogb.le
  have hkUpper :
      (carletNonnormalityDimension α n : ℝ) ≤
        α * Real.logb 2 (n : ℝ) := by
    exact Nat.floor_le hx
  have hkLower :
      (2 : ℝ) ^ (α * Real.logb 2 (n : ℝ) - 1) ≤
        (2 : ℝ) ^ carletNonnormalityDimension α n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (Nat.sub_one_lt_floor (α * Real.logb 2 (n : ℝ))).le
  have hpower :
      (2 : ℝ) ^ (α * Real.logb 2 (n : ℝ) - 1) =
        (n : ℝ) ^ α / 2 := by
    rw [Real.rpow_sub_one (by norm_num)]
    congr 1
    calc
      (2 : ℝ) ^ (α * Real.logb 2 (n : ℝ)) =
          (2 : ℝ) ^ (Real.logb 2 (n : ℝ) * α) := by
        congr 1
        ring
      _ = ((2 : ℝ) ^ Real.logb 2 (n : ℝ)) ^ α :=
        Real.rpow_mul (by norm_num) _ _
      _ = (n : ℝ) ^ α := by
        rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (2 : ℝ) ≠ 1) hnpos]
  have hnum : (n : ℝ) ^ α / 2 ≤
      (2 : ℝ) ^ carletNonnormalityDimension α n := by
    rw [← hpower]
    exact hkLower
  have hdenom :
      (n : ℝ) * (carletNonnormalityDimension α n : ℝ) ≤
        (n : ℝ) * (α * Real.log (n : ℝ) / Real.log 2) := by
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    simpa [Real.logb, mul_div_assoc] using hkUpper
  have hpowAlpha : (n : ℝ) ^ α = (n : ℝ) ^ δ * n := by
    calc
      (n : ℝ) ^ α = (n : ℝ) ^ (δ + 1) := by
        congr 1
        simp [δ]
      _ = (n : ℝ) ^ δ * (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hnpos _ _
      _ = (n : ℝ) ^ δ * n := by rw [Real.rpow_one]
  have hidentity :
      C * ((n : ℝ) ^ δ / Real.log (n : ℝ)) =
        ((n : ℝ) ^ α / 2) /
          ((n : ℝ) * (α * Real.log (n : ℝ) / Real.log 2)) := by
    dsimp [C]
    rw [hpowAlpha]
    field_simp
  rw [hidentity]
  exact div_le_div₀ (by positivity) hnum (by positivity) hdenom

/-- Carlet's random-nonnormality corollary: for every `α > 1`, the uniform
probability that an `n`-variable Boolean function is not
`floor (α log₂ n)`-normal tends to one. -/
theorem tendsto_carletNonnormalityProbability
    {α : ℝ} (hα : 1 < α) :
    Filter.Tendsto
      (fun n : ℕ ↦
        nonnormalityProbability n (carletNonnormalityDimension α n))
      Filter.atTop (𝓝 1) := by
  apply tendsto_nonnormalityProbability_one_of_ratio
  · exact (tendsto_carletNonnormalityDimension hα).eventually
      (Filter.eventually_gt_atTop 2)
  · exact tendsto_carletNonnormalityRatio hα

end CryptBoolean
