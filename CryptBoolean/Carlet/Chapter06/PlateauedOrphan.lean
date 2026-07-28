/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight
public import CryptBoolean.Carlet.Chapter04.KthNonhomomorphicity
public import CryptBoolean.Carlet.Chapter04.ReedMullerCosetDistance
public import CryptBoolean.Carlet.Chapter06.DualIsometry
public import CryptBoolean.Carlet.Chapter06.Plateaued

/-!
# Plateaued cosets and orphans

The support order on first-order Reed--Muller cosets and Langevin's maximality
theorem for non-affine plateaued functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A first-order coset leader is a representative whose weight realizes its
nonlinearity. -/
def IsFirstOrderCosetLeader (f : BooleanFunction n) : Prop :=
  hammingWeight f = nonlinearity f

/-- The support order on first-order Reed--Muller cosets. -/
def FirstOrderCosetBelow (f g : BooleanFunction n) : Prop :=
  ∃ f₁ g₁ : BooleanFunction n,
    f₁ + f ∈ reedMuller 1 n ∧
      g₁ + g ∈ reedMuller 1 n ∧
      IsFirstOrderCosetLeader f₁ ∧
      IsFirstOrderCosetLeader g₁ ∧
      support f₁ ⊆ support g₁

/-- A first-order Reed--Muller coset is an orphan when it is maximal in the
coset-leader support order. -/
def IsFirstOrderOrphan (f : BooleanFunction n) : Prop :=
  ∀ g : BooleanFunction n,
    FirstOrderCosetBelow f g → f + g ∈ reedMuller 1 n

/-- Adding an affine function preserves plateauedness. -/
theorem IsPlateaued.add_affineFunction
    {f : BooleanFunction n} (hf : IsPlateaued f)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    IsPlateaued (f + FABL.affineFunction b a) := by
  rcases hf with ⟨amplitude, hpositive, hspectrum⟩
  refine ⟨amplitude, hpositive, fun u ↦ ?_⟩
  rcases hspectrum (u + a) with hzero | hmagnitude
  · left
    rw [walshTransform_add_affineFunction]
    simp [hzero]
  · right
    simpa only [walshTransform_add_affineFunction_natAbs] using hmagnitude

private theorem walshTransform_zero_cast_eq_maxWalshMagnitude_of_leader
    (f : BooleanFunction n) (hf : IsFirstOrderCosetLeader f) :
    (walshTransform f 0 : ℝ) = (maxWalshMagnitude f : ℝ) := by
  have hrelation := congrArg (fun k : ℕ ↦ (k : ℝ))
    (two_mul_nonlinearity_add_maxWalshMagnitude f)
  have hzero := congrArg (fun z : ℤ ↦ (z : ℝ))
    (walshTransform_zero_eq_two_pow_sub_two_weight f)
  push_cast at hrelation hzero
  rw [hf] at hzero
  linarith

private theorem amplitude_eq_maxWalshMagnitude_of_leader
    (f : BooleanFunction n) (amplitude : ℕ)
    (hf : HasPlateauedWalshAmplitude f amplitude)
    (hleader : IsFirstOrderCosetLeader f) :
    amplitude = maxWalshMagnitude f := by
  have hzeroMax :=
    walshTransform_zero_cast_eq_maxWalshMagnitude_of_leader f hleader
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  have hmaxPositive : 0 < (maxWalshMagnitude f : ℝ) := by
    have habsPositive : 0 < |(walshTransform f u : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast hu)
    exact habsPositive.trans_le (abs_walshTransform_le_maxWalshMagnitude f u)
  have hzeroNe : walshTransform f 0 ≠ 0 := by
    intro hzero
    rw [hzero, Int.cast_zero] at hzeroMax
    linarith
  have hmagnitude : (walshTransform f 0).natAbs = amplitude := by
    rcases hf.2 0 with hzero | hmagnitude
    · exact (hzeroNe hzero).elim
    · exact hmagnitude
  apply Nat.cast_injective (R := ℝ)
  have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmagnitude
  have hmaxAmplitude :
      (maxWalshMagnitude f : ℝ) = (amplitude : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, abs_of_pos
      (hzeroMax.trans_gt hmaxPositive), hzeroMax,
      abs_of_nonneg (by positivity : 0 ≤ (maxWalshMagnitude f : ℝ))] using hcast
  exact hmaxAmplitude.symm

/-- A non-affine plateaued coset leader cannot have its support properly
contained in the support of another first-order coset leader. -/
theorem eq_of_plateaued_cosetLeaders_of_support_subset
    (f g : BooleanFunction n)
    (hf : IsPlateaued f)
    (hnonlinearity : 0 < nonlinearity f)
    (hleaderF : IsFirstOrderCosetLeader f)
    (hleaderG : IsFirstOrderCosetLeader g)
    (hsubset : support f ⊆ support g) :
    g = f := by
  classical
  by_contra hne
  rcases hf with ⟨amplitude, hfAmplitude⟩
  have hamplitudeMax : amplitude = maxWalshMagnitude f :=
    amplitude_eq_maxWalshMagnitude_of_leader f amplitude hfAmplitude hleaderF
  have hrelationF := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hamplitudeLt : amplitude < 2 ^ n := by
    rw [hamplitudeMax]
    omega
  let k := hammingWeight (f + g)
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    have hfgzero : f + g = 0 := hammingNorm_eq_zero.mp hkzero
    apply hne
    funext x
    have hx := congrFun hfgzero x
    simp only [Pi.add_apply, Pi.zero_apply] at hx
    by_cases hfx : f x = 0
    · simp only [hfx, zero_add] at hx ⊢
      exact hx
    · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
      by_cases hgx : g x = 0
      · simp [hfxOne, hgx] at hx
      · exact (Fin.eq_one_of_ne_zero _ hgx).trans hfxOne.symm
  have hinter : support f ∩ support g = support f :=
    Finset.inter_eq_left.mpr hsubset
  have hweight := hammingWeight_add_add_two_mul_card_inter f g
  rw [hinter, ← hammingWeight_eq_card_support] at hweight
  have hzeroF :=
    walshTransform_zero_cast_eq_maxWalshMagnitude_of_leader f hleaderF
  have hzeroG :=
    walshTransform_zero_cast_eq_maxWalshMagnitude_of_leader g hleaderG
  have hmaxG :
      (maxWalshMagnitude g : ℝ) =
        (amplitude : ℝ) - 2 * (k : ℝ) := by
    have hzF := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_zero_eq_two_pow_sub_two_weight f)
    have hzG := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_zero_eq_two_pow_sub_two_weight g)
    have hw := congrArg (fun q : ℕ ↦ (q : ℝ)) hweight
    push_cast at hzF hzG hw
    rw [← hamplitudeMax] at hzeroF
    dsimp [k] at hw ⊢
    linarith
  have hraw (h : BooleanFunction n) (u : FABL.F₂Cube n) :
      rawFourierTransform (realSignView h) u =
        (walshTransform h u : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hinner :
      (∑ x, realSignView f x * realSignView g x) =
        (2 : ℝ) ^ n - 2 * (k : ℝ) := by
    calc
      (∑ x, realSignView f x * realSignView g x) =
          ∑ x, realSignView (f + g) x := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact (realSignView_add f g x).symm
      _ = (walshTransform (f + g) 0 : ℝ) := by
        rw [walshTransform_cast_eq_sum_realSignView_mul_character]
        simp
      _ = (2 : ℝ) ^ n - 2 * (k : ℝ) := by
        have hz := congrArg (fun z : ℤ ↦ (z : ℝ))
          (walshTransform_zero_eq_two_pow_sub_two_weight (f + g))
        push_cast at hz
        exact hz
  have hplancherel :=
    sum_rawFourierTransform_mul (realSignView f) (realSignView g)
  simp_rw [hraw] at hplancherel
  rw [hinner] at hplancherel
  have hsumBound :
      (∑ u, (walshTransform f u : ℝ) * (walshTransform g u : ℝ)) ≤
        ((walshSupport f).card : ℝ) * (amplitude : ℝ) *
          (maxWalshMagnitude g : ℝ) := by
    calc
      (∑ u, (walshTransform f u : ℝ) * (walshTransform g u : ℝ)) =
          ∑ u ∈ walshSupport f,
            (walshTransform f u : ℝ) * (walshTransform g u : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro u _hu hnot
        have hzero : walshTransform f u = 0 := by
          simpa only [mem_walshSupport, not_ne_iff] using hnot
        simp [hzero]
      _ ≤ ∑ _u ∈ walshSupport f,
          (amplitude : ℝ) * (maxWalshMagnitude g : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        have hneF : walshTransform f u ≠ 0 :=
          (mem_walshSupport f u).mp hu
        have hmagnitudeF :
            |(walshTransform f u : ℝ)| = (amplitude : ℝ) := by
          rcases hfAmplitude.2 u with hzero | hmagnitude
          · exact (hneF hzero).elim
          · have hcast := congrArg (fun q : ℕ ↦ (q : ℝ)) hmagnitude
            simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
        calc
          (walshTransform f u : ℝ) * (walshTransform g u : ℝ) ≤
              |(walshTransform f u : ℝ) * (walshTransform g u : ℝ)| :=
            le_abs_self _
          _ = |(walshTransform f u : ℝ)| *
              |(walshTransform g u : ℝ)| := abs_mul _ _
          _ ≤ (amplitude : ℝ) * (maxWalshMagnitude g : ℝ) := by
            rw [hmagnitudeF]
            exact mul_le_mul_of_nonneg_left
              (abs_walshTransform_le_maxWalshMagnitude g u)
              (by positivity)
      _ = ((walshSupport f).card : ℝ) * (amplitude : ℝ) *
          (maxWalshMagnitude g : ℝ) := by simp [mul_assoc]
  have hcard :=
    card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul
      f amplitude hfAmplitude
  have hcardReal := congrArg (fun q : ℕ ↦ (q : ℝ)) hcard
  push_cast at hcardReal
  rw [hplancherel, hmaxG] at hsumBound
  have hamplitudePositive : 0 < (amplitude : ℝ) := by
    exact_mod_cast hfAmplitude.1
  have hpowPositive : 0 < (2 : ℝ) ^ n := by positivity
  have hpowSquare : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by
    rw [mul_comm 2 n, pow_mul]
  rw [hpowSquare] at hcardReal
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsupportAmplitudeLe :
      ((walshSupport f).card : ℝ) * (amplitude : ℝ) ≤
        (2 : ℝ) ^ n := by
    nlinarith [hsumBound, hcardReal, hkReal]
  have hmul := mul_le_mul_of_nonneg_right hsupportAmplitudeLe
    (le_of_lt hamplitudePositive)
  have hpowLeAmplitude : (2 : ℝ) ^ n ≤ (amplitude : ℝ) := by
    nlinarith [hmul, hcardReal]
  exact (not_lt_of_ge hpowLeAmplitude) (by exact_mod_cast hamplitudeLt)

/-- Langevin's corrected orphan theorem: every non-affine plateaued function
represents a maximal first-order Reed--Muller coset. -/
theorem isFirstOrderOrphan_of_isPlateaued
    (f : BooleanFunction n) (hf : IsPlateaued f)
    (hnonaffine : f ∉ reedMuller 1 n) :
    IsFirstOrderOrphan f := by
  have hnonlinearity : 0 < nonlinearity f := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rcases (isAffineBooleanFunction_iff_nonlinearity_eq_zero f).2 hzero with
      ⟨b, a, hfa⟩
    apply hnonaffine
    rw [hfa]
    exact affineFunction_mem_reedMuller_one b a
  intro g hbelow
  rcases hbelow with
    ⟨f₁, g₁, hf₁Coset, hg₁Coset, hf₁Leader, hg₁Leader, hsupport⟩
  obtain ⟨b, a, haffine⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (f₁ + f) hf₁Coset
  have hf₁Eq : f₁ = f + FABL.affineFunction b a := by
    funext x
    have hx := congrFun haffine x
    simp only [Pi.add_apply] at hx ⊢
    rw [← hx]
    by_cases hf₁x : f₁ x = 0
    · by_cases hfx : f x = 0
      · simp [hf₁x, hfx]
      · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
        simp [hf₁x, hfxOne]
    · have hf₁xOne : f₁ x = 1 := Fin.eq_one_of_ne_zero _ hf₁x
      by_cases hfx : f x = 0
      · simp [hf₁xOne, hfx]
      · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
        simp [hf₁xOne, hfxOne]
  have hf₁Plateaued : IsPlateaued f₁ := by
    rw [hf₁Eq]
    exact hf.add_affineFunction b a
  have hf₁Nonlinearity : 0 < nonlinearity f₁ := by
    rw [hf₁Eq, nonlinearity_add_affineFunction]
    exact hnonlinearity
  have hleadersEqual : g₁ = f₁ :=
    eq_of_plateaued_cosetLeaders_of_support_subset
      f₁ g₁ hf₁Plateaued hf₁Nonlinearity hf₁Leader hg₁Leader hsupport
  have hsum := (reedMuller 1 n).add_mem hf₁Coset hg₁Coset
  have hfunctions : (f₁ + f) + (g₁ + g) = f + g := by
    rw [hleadersEqual]
    funext x
    simp only [Pi.add_apply]
    by_cases hf₁x : f₁ x = 0
    · simp [hf₁x]
    · have hf₁xOne : f₁ x = 1 := Fin.eq_one_of_ne_zero _ hf₁x
      by_cases hfx : f x = 0
      · by_cases hgx : g x = 0
        · simp [hf₁xOne, hfx, hgx]
        · have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
          simp [hf₁xOne, hfx, hgxOne]
      · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
        by_cases hgx : g x = 0
        · simp [hf₁xOne, hfxOne, hgx]
        · have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
          simp [hf₁xOne, hfxOne, hgxOne]
  rwa [hfunctions] at hsum

end CryptBoolean
