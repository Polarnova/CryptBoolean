/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Resiliency
public import CryptBoolean.Carlet.Chapter06.ThreeFunctionIdentity
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Three-function resilient construction

Carlet Proposition 34 and Relation (68).
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

private theorem walshTransform_threeFunctionSum_eq_zero_iff_pairwiseProductSum_eq_zero
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n)
    (h₁ : walshTransform f₁ a = 0)
    (h₂ : walshTransform f₂ a = 0)
    (h₃ : walshTransform f₃ a = 0) :
    walshTransform (threeFunctionSum f₁ f₂ f₃) a = 0 ↔
      walshTransform (threeFunctionPairwiseProductSum f₁ f₂ f₃) a = 0 := by
  have hidentity := walshTransform_threeFunctionIdentity f₁ f₂ f₃ a
  rw [h₁, h₂, h₃] at hidentity
  constructor <;> intro hzero <;> omega

/-- Carlet Proposition 34, correlation-immune form: under three
correlation-immune inputs, their first and second elementary symmetric
functions are correlation immune simultaneously. -/
theorem isCorrelationImmune_threeFunctionSum_iff_pairwiseProductSum
    (f₁ f₂ f₃ : BooleanFunction n)
    (hn : 0 < n) (hk : k < n)
    (h₁ : IsCorrelationImmune k f₁)
    (h₂ : IsCorrelationImmune k f₂)
    (h₃ : IsCorrelationImmune k f₃) :
    IsCorrelationImmune k (threeFunctionSum f₁ f₂ f₃) ↔
      IsCorrelationImmune k
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
  have h₁Walsh :=
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      k f₁ hn hk).mp h₁
  have h₂Walsh :=
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      k f₂ hn hk).mp h₂
  have h₃Walsh :=
    (theorem_3_correlationImmune_iff_walshTransform_eq_zero
      k f₃ hn hk).mp h₃
  rw [theorem_3_correlationImmune_iff_walshTransform_eq_zero
      k (threeFunctionSum f₁ f₂ f₃) hn hk,
    theorem_3_correlationImmune_iff_walshTransform_eq_zero
      k (threeFunctionPairwiseProductSum f₁ f₂ f₃) hn hk]
  constructor
  · intro hsum a ha hweight
    exact
      (walshTransform_threeFunctionSum_eq_zero_iff_pairwiseProductSum_eq_zero
        f₁ f₂ f₃ a
        (h₁Walsh a ha hweight)
        (h₂Walsh a ha hweight)
        (h₃Walsh a ha hweight)).mp
          (hsum a ha hweight)
  · intro hpair a ha hweight
    exact
      (walshTransform_threeFunctionSum_eq_zero_iff_pairwiseProductSum_eq_zero
        f₁ f₂ f₃ a
        (h₁Walsh a ha hweight)
        (h₂Walsh a ha hweight)
        (h₃Walsh a ha hweight)).mpr
          (hpair a ha hweight)

/-- Carlet Proposition 34, resilient form: under three resilient inputs,
their first and second elementary symmetric functions are resilient
simultaneously. -/
theorem isResilient_threeFunctionSum_iff_pairwiseProductSum
    (f₁ f₂ f₃ : BooleanFunction n)
    (hn : 0 < n) (hk : k < n)
    (h₁ : IsResilient k f₁)
    (h₂ : IsResilient k f₂)
    (h₃ : IsResilient k f₃) :
    IsResilient k (threeFunctionSum f₁ f₂ f₃) ↔
      IsResilient k
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
  have h₁Walsh :=
    (theorem_3_resilient_iff_walshTransform_eq_zero
      k f₁ hn hk).mp h₁
  have h₂Walsh :=
    (theorem_3_resilient_iff_walshTransform_eq_zero
      k f₂ hn hk).mp h₂
  have h₃Walsh :=
    (theorem_3_resilient_iff_walshTransform_eq_zero
      k f₃ hn hk).mp h₃
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
      k (threeFunctionSum f₁ f₂ f₃) hn hk,
    theorem_3_resilient_iff_walshTransform_eq_zero
      k (threeFunctionPairwiseProductSum f₁ f₂ f₃) hn hk]
  constructor
  · intro hsum a hweight
    exact
      (walshTransform_threeFunctionSum_eq_zero_iff_pairwiseProductSum_eq_zero
        f₁ f₂ f₃ a
        (h₁Walsh a hweight)
        (h₂Walsh a hweight)
        (h₃Walsh a hweight)).mp
          (hsum a hweight)
  · intro hpair a hweight
    exact
      (walshTransform_threeFunctionSum_eq_zero_iff_pairwiseProductSum_eq_zero
        f₁ f₂ f₃ a
        (h₁Walsh a hweight)
        (h₂Walsh a hweight)
        (h₃Walsh a hweight)).mpr
          (hpair a hweight)

private theorem two_mul_walshTransform_pairwiseProductSum_natAbs_le
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n) :
    2 * (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs ≤
      (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs +
        (walshTransform f₁ a).natAbs +
        (walshTransform f₂ a).natAbs +
        (walshTransform f₃ a).natAbs := by
  have hidentity := walshTransform_threeFunctionIdentity f₁ f₂ f₃ a
  have heq :
      2 * walshTransform
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) a =
        walshTransform f₁ a + walshTransform f₂ a + walshTransform f₃ a -
          walshTransform (threeFunctionSum f₁ f₂ f₃) a := by
    omega
  calc
    2 * (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs =
        (2 * walshTransform
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs := by
      rw [Int.natAbs_mul]
      norm_num
    _ = (walshTransform f₁ a + walshTransform f₂ a + walshTransform f₃ a -
        walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs := by
      rw [heq]
    _ ≤ (walshTransform f₁ a + walshTransform f₂ a +
          walshTransform f₃ a).natAbs +
          (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ ((walshTransform f₁ a).natAbs +
          (walshTransform f₂ a).natAbs +
          (walshTransform f₃ a).natAbs) +
          (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs := by
      gcongr
      exact (Int.natAbs_add_le _ _).trans
        (Nat.add_le_add_right (Int.natAbs_add_le _ _) _)
    _ = (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs +
          (walshTransform f₁ a).natAbs +
          (walshTransform f₂ a).natAbs +
          (walshTransform f₃ a).natAbs := by omega

/-- Spectral maximum inequality underlying Carlet Relation (68). -/
theorem two_mul_maxWalshMagnitude_pairwiseProductSum_le
    (f₁ f₂ f₃ : BooleanFunction n) :
    2 * maxWalshMagnitude
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) ≤
      maxWalshMagnitude (threeFunctionSum f₁ f₂ f₃) +
        maxWalshMagnitude f₁ +
        maxWalshMagnitude f₂ +
        maxWalshMagnitude f₃ := by
  unfold maxWalshMagnitude
  obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun u ↦
      (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) u).natAbs)
  rw [hmax]
  refine (two_mul_walshTransform_pairwiseProductSum_natAbs_le
    f₁ f₂ f₃ a).trans ?_
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (walshTransform_natAbs_le_maxWalshMagnitude
          (threeFunctionSum f₁ f₂ f₃) a)
        (walshTransform_natAbs_le_maxWalshMagnitude f₁ a))
      (walshTransform_natAbs_le_maxWalshMagnitude f₂ a))
    (walshTransform_natAbs_le_maxWalshMagnitude f₃ a)

/-- Division-free natural-number form of Carlet Relation (68). -/
theorem relation_68_threeFunctionConstruction
    (f₁ f₂ f₃ : BooleanFunction n) :
    nonlinearity (threeFunctionSum f₁ f₂ f₃) +
        nonlinearity f₁ + nonlinearity f₂ + nonlinearity f₃ ≤
      2 ^ n +
        2 * nonlinearity
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
  have hmax :=
    two_mul_maxWalshMagnitude_pairwiseProductSum_le f₁ f₂ f₃
  have hsum :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      (threeFunctionSum f₁ f₂ f₃)
  have hpair :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      (threeFunctionPairwiseProductSum f₁ f₂ f₃)
  have h₁ := two_mul_nonlinearity_add_maxWalshMagnitude f₁
  have h₂ := two_mul_nonlinearity_add_maxWalshMagnitude f₂
  have h₃ := two_mul_nonlinearity_add_maxWalshMagnitude f₃
  omega

/-- Carlet Relation (68) in the source's real-valued half-factor form. -/
theorem nonlinearity_pairwiseProductSum_cast_lower_bound
    (f₁ f₂ f₃ : BooleanFunction n) (hn : 0 < n) :
    (nonlinearity
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) : ℝ) ≥
      (1 / 2 : ℝ) *
        ((nonlinearity (threeFunctionSum f₁ f₂ f₃) : ℝ) +
          nonlinearity f₁ + nonlinearity f₂ + nonlinearity f₃) -
        (2 : ℝ) ^ (n - 1) := by
  have h := relation_68_threeFunctionConstruction f₁ f₂ f₃
  have hcast :
      (nonlinearity (threeFunctionSum f₁ f₂ f₃) : ℝ) +
          nonlinearity f₁ + nonlinearity f₂ + nonlinearity f₃ ≤
        (2 : ℝ) ^ n +
          2 * nonlinearity
            (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
    exact_mod_cast h
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpow] at hcast
  linarith

private theorem two_mul_walshTransform_pairwiseProductSum_natAbs_le_of_disjoint
    (f₁ f₂ f₃ : BooleanFunction n) (a : FABL.F₂Cube n)
    (h₁₂ : walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (h₁₃ : walshTransform f₁ a = 0 ∨ walshTransform f₃ a = 0)
    (h₂₃ : walshTransform f₂ a = 0 ∨ walshTransform f₃ a = 0) :
    2 * (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs ≤
      (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs +
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) := by
  have hidentity := walshTransform_threeFunctionIdentity f₁ f₂ f₃ a
  have heq :
      2 * walshTransform
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) a =
        walshTransform f₁ a + walshTransform f₂ a + walshTransform f₃ a -
          walshTransform (threeFunctionSum f₁ f₂ f₃) a := by
    omega
  have h₁max :
      (walshTransform f₁ a).natAbs ≤
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) :=
    (walshTransform_natAbs_le_maxWalshMagnitude f₁ a).trans
      (Nat.le_max_left _ _)
  have h₂max :
      (walshTransform f₂ a).natAbs ≤
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) :=
    (walshTransform_natAbs_le_maxWalshMagnitude f₂ a).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have h₃max :
      (walshTransform f₃ a).natAbs ≤
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) :=
    (walshTransform_natAbs_le_maxWalshMagnitude f₃ a).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hinput :
      (walshTransform f₁ a + walshTransform f₂ a +
        walshTransform f₃ a).natAbs ≤
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) := by
    rcases h₁₂ with h₁zero | h₂zero
    · rcases h₂₃ with h₂zero | h₃zero
      · simpa [h₁zero, h₂zero] using h₃max
      · simpa [h₁zero, h₃zero] using h₂max
    · rcases h₁₃ with h₁zero | h₃zero
      · simpa [h₁zero, h₂zero] using h₃max
      · simpa [h₂zero, h₃zero] using h₁max
  calc
    2 * (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs =
        (2 * walshTransform
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) a).natAbs := by
      rw [Int.natAbs_mul]
      norm_num
    _ = (walshTransform f₁ a + walshTransform f₂ a + walshTransform f₃ a -
        walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs := by
      rw [heq]
    _ ≤ (walshTransform f₁ a + walshTransform f₂ a +
          walshTransform f₃ a).natAbs +
          (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ (walshTransform (threeFunctionSum f₁ f₂ f₃) a).natAbs +
          max (maxWalshMagnitude f₁)
            (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) := by
      omega

/-- Spectral maximum inequality for Proposition 34 under pairwise disjoint
input Walsh supports. -/
theorem two_mul_maxWalshMagnitude_pairwiseProductSum_le_of_pairwiseDisjoint
    (f₁ f₂ f₃ : BooleanFunction n)
    (h₁₂ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (h₁₃ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₃ a = 0)
    (h₂₃ : ∀ a, walshTransform f₂ a = 0 ∨ walshTransform f₃ a = 0) :
    2 * maxWalshMagnitude
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) ≤
      maxWalshMagnitude (threeFunctionSum f₁ f₂ f₃) +
        max (maxWalshMagnitude f₁)
          (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) := by
  unfold maxWalshMagnitude
  obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun u ↦
      (walshTransform
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) u).natAbs)
  rw [hmax]
  refine
    (two_mul_walshTransform_pairwiseProductSum_natAbs_le_of_disjoint
      f₁ f₂ f₃ a (h₁₂ a) (h₁₃ a) (h₂₃ a)).trans ?_
  exact Nat.add_le_add_right
    (walshTransform_natAbs_le_maxWalshMagnitude
      (threeFunctionSum f₁ f₂ f₃) a) _

/-- Division-free natural-number form of Carlet Relation (69). -/
theorem relation_69_threeFunctionConstruction
    (f₁ f₂ f₃ : BooleanFunction n)
    (h₁₂ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (h₁₃ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₃ a = 0)
    (h₂₃ : ∀ a, walshTransform f₂ a = 0 ∨ walshTransform f₃ a = 0) :
    nonlinearity (threeFunctionSum f₁ f₂ f₃) +
        min (nonlinearity f₁) (min (nonlinearity f₂) (nonlinearity f₃)) ≤
      2 * nonlinearity
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
  have hmax :=
    two_mul_maxWalshMagnitude_pairwiseProductSum_le_of_pairwiseDisjoint
      f₁ f₂ f₃ h₁₂ h₁₃ h₂₃
  have hsum :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      (threeFunctionSum f₁ f₂ f₃)
  have hpair :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      (threeFunctionPairwiseProductSum f₁ f₂ f₃)
  have h₁ := two_mul_nonlinearity_add_maxWalshMagnitude f₁
  have h₂ := two_mul_nonlinearity_add_maxWalshMagnitude f₂
  have h₃ := two_mul_nonlinearity_add_maxWalshMagnitude f₃
  rcases le_total (nonlinearity f₁) (nonlinearity f₂) with h₁₂n | h₂₁n
  · rcases le_total (nonlinearity f₁) (nonlinearity f₃) with h₁₃n | h₃₁n
    · have hmaxInputs :
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
            maxWalshMagnitude f₁ :=
        Nat.max_eq_left (max_le (by omega) (by omega))
      have hminInputs :
          min (nonlinearity f₁)
              (min (nonlinearity f₂) (nonlinearity f₃)) =
            nonlinearity f₁ :=
        Nat.min_eq_left (le_min h₁₂n h₁₃n)
      rw [hmaxInputs] at hmax
      rw [hminInputs]
      omega
    · have hmaxInputs :
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
            maxWalshMagnitude f₃ := by
        calc
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
              max (maxWalshMagnitude f₁) (maxWalshMagnitude f₃) := by
            exact congrArg (fun z ↦ max (maxWalshMagnitude f₁) z)
              (Nat.max_eq_right (by omega))
          _ = maxWalshMagnitude f₃ := Nat.max_eq_right (by omega)
      have hminInputs :
          min (nonlinearity f₁)
              (min (nonlinearity f₂) (nonlinearity f₃)) =
            nonlinearity f₃ := by
        rw [Nat.min_eq_right (h₃₁n.trans h₁₂n),
          Nat.min_eq_right h₃₁n]
      rw [hmaxInputs] at hmax
      rw [hminInputs]
      omega
  · rcases le_total (nonlinearity f₂) (nonlinearity f₃) with h₂₃n | h₃₂n
    · have hmaxInputs :
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
            maxWalshMagnitude f₂ := by
        calc
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
              max (maxWalshMagnitude f₁) (maxWalshMagnitude f₂) := by
            exact congrArg (fun z ↦ max (maxWalshMagnitude f₁) z)
              (Nat.max_eq_left (by omega))
          _ = maxWalshMagnitude f₂ := Nat.max_eq_right (by omega)
      have hminInputs :
          min (nonlinearity f₁)
              (min (nonlinearity f₂) (nonlinearity f₃)) =
            nonlinearity f₂ := by
        rw [Nat.min_eq_left h₂₃n, Nat.min_eq_right h₂₁n]
      rw [hmaxInputs] at hmax
      rw [hminInputs]
      omega
    · have hmaxInputs :
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
            maxWalshMagnitude f₃ := by
        calc
          max (maxWalshMagnitude f₁)
              (max (maxWalshMagnitude f₂) (maxWalshMagnitude f₃)) =
              max (maxWalshMagnitude f₁) (maxWalshMagnitude f₃) := by
            exact congrArg (fun z ↦ max (maxWalshMagnitude f₁) z)
              (Nat.max_eq_right (by omega))
          _ = maxWalshMagnitude f₃ := Nat.max_eq_right (by omega)
      have hminInputs :
          min (nonlinearity f₁)
              (min (nonlinearity f₂) (nonlinearity f₃)) =
            nonlinearity f₃ := by
        rw [Nat.min_eq_right h₃₂n,
          Nat.min_eq_right (h₃₂n.trans h₂₁n)]
      rw [hmaxInputs] at hmax
      rw [hminInputs]
      omega

/-- Carlet Relation (69) in the source's real-valued half-factor form. -/
theorem nonlinearity_pairwiseProductSum_cast_lower_bound_of_pairwiseDisjoint
    (f₁ f₂ f₃ : BooleanFunction n)
    (h₁₂ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₂ a = 0)
    (h₁₃ : ∀ a, walshTransform f₁ a = 0 ∨ walshTransform f₃ a = 0)
    (h₂₃ : ∀ a, walshTransform f₂ a = 0 ∨ walshTransform f₃ a = 0) :
    (nonlinearity
        (threeFunctionPairwiseProductSum f₁ f₂ f₃) : ℝ) ≥
      (1 / 2 : ℝ) *
        ((nonlinearity (threeFunctionSum f₁ f₂ f₃) : ℝ) +
          min (nonlinearity f₁)
            (min (nonlinearity f₂) (nonlinearity f₃))) := by
  have h := relation_69_threeFunctionConstruction f₁ f₂ f₃ h₁₂ h₁₃ h₂₃
  have hcast :
      (nonlinearity (threeFunctionSum f₁ f₂ f₃) : ℝ) +
          min (nonlinearity f₁)
            (min (nonlinearity f₂) (nonlinearity f₃)) ≤
        2 * nonlinearity
          (threeFunctionPairwiseProductSum f₁ f₂ f₃) := by
    exact_mod_cast h
  linarith

end CryptBoolean
