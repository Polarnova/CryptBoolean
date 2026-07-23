/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderGeneralBounds
public import CryptBoolean.Carlet.Chapter02.Fourier
public import CryptBoolean.Carlet.Chapter03.ReedMullerDuality
public import FABL.Chapter05.KrawtchoukPolynomials

/-!
# Carlet--Mesnager's second-order power-sum bridge

The finite moment argument reducing the covering radius of `RM(2,n)` to a
uniform lower bound for consecutive correlation power sums.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- The raw correlation of `f` with a Reed--Muller approximant `g`. -/
def orderTwoCorrelation
    (f g : BooleanFunction n) : ℝ :=
  (walshTransform (f + g) 0 : ℝ)

/-- Raw correlation is cube size minus twice Hamming distance. -/
theorem orderTwoCorrelation_eq_two_pow_sub_two_hammingDistance
    (f g : BooleanFunction n) :
    orderTwoCorrelation f g =
      (2 ^ n : ℝ) - 2 * hammingDistance f g := by
  rw [orderTwoCorrelation, walshTransform_zero_eq_two_pow_sub_two_weight,
    hammingDistance_eq_hammingWeight_add]
  push_cast
  ring

/-- Carlet--Mesnager's `A₂(f)`, expressed through the exact distance--
correlation relation. -/
noncomputable def maximumOrderTwoCorrelation
    (f : BooleanFunction n) : ℝ :=
  (2 ^ n : ℝ) - 2 * higherOrderNonlinearity 2 f

/-- The definition of `A₂(f)` is the complement of twice the second-order
nonlinearity. -/
theorem maximumOrderTwoCorrelation_eq
    (f : BooleanFunction n) :
    maximumOrderTwoCorrelation f =
      (2 ^ n : ℝ) - 2 * higherOrderNonlinearity 2 f := by
  rfl

/-- Every second-order Reed--Muller correlation is at most `A₂(f)`. -/
theorem orderTwoCorrelation_le_maximum
    (f g : BooleanFunction n) (hg : g ∈ reedMuller 2 n) :
    orderTwoCorrelation f g ≤ maximumOrderTwoCorrelation f := by
  rw [orderTwoCorrelation_eq_two_pow_sub_two_hammingDistance,
    maximumOrderTwoCorrelation_eq]
  have hdistance :
      (higherOrderNonlinearity 2 f : ℝ) ≤
        (hammingDistance f g : ℝ) := by
    exact_mod_cast higherOrderNonlinearity_le_hammingDistance 2 f g hg
  linarith

/-- A closest second-order Reed--Muller word attains `A₂(f)`. -/
theorem exists_orderTwoCorrelation_eq_maximum
    (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, g ∈ reedMuller 2 n ∧
      orderTwoCorrelation f g = maximumOrderTwoCorrelation f := by
  obtain ⟨g, hg, hdistance⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity 2 f
  refine ⟨g, hg, ?_⟩
  rw [orderTwoCorrelation_eq_two_pow_sub_two_hammingDistance,
    maximumOrderTwoCorrelation_eq, hdistance]

/-- The maximum second-order correlation is nonnegative. -/
theorem maximumOrderTwoCorrelation_nonneg
    (f : BooleanFunction n) :
    0 ≤ maximumOrderTwoCorrelation f := by
  rw [maximumOrderTwoCorrelation_eq]
  have hbound := two_mul_higherOrderNonlinearity_le_two_pow 2 (by omega) f
  have hboundReal :
      2 * (higherOrderNonlinearity 2 f : ℝ) ≤ (2 ^ n : ℝ) := by
    exact_mod_cast hbound
  linarith

private theorem orderTwoCorrelation_add_one
    (f g : BooleanFunction n) :
    orderTwoCorrelation f (g + 1) = -orderTwoCorrelation f g := by
  classical
  have hbit (b : FABL.𝔽₂) : bitSignInt (b + 1) = -bitSignInt b := by
    rw [bitSignInt, bitSignInt, FABL.signEncode_add, FABL.signEncode_one]
    norm_num
  unfold orderTwoCorrelation
  norm_cast
  unfold walshTransform
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [walshTerm_zero, walshTerm_zero]
  simp only [Pi.add_apply, Pi.one_apply]
  rw [show f x + (g x + 1) = (f x + g x) + 1 by abel]
  exact hbit (f x + g x)

/-- Every second-order correlation has absolute value at most `A₂(f)`. -/
theorem abs_orderTwoCorrelation_le_maximum
    (f g : BooleanFunction n) (hg : g ∈ reedMuller 2 n) :
    |orderTwoCorrelation f g| ≤ maximumOrderTwoCorrelation f := by
  have hupper := orderTwoCorrelation_le_maximum f g hg
  have hone : (1 : BooleanFunction n) ∈ reedMuller 2 n := by
    rw [mem_reedMuller_iff]
    simp
  have hcomplement : g + 1 ∈ reedMuller 2 n :=
    (reedMuller 2 n).add_mem hg hone
  have hlower' :
      orderTwoCorrelation f (g + 1) ≤ maximumOrderTwoCorrelation f := by
    exact orderTwoCorrelation_le_maximum f (g + 1) hcomplement
  rw [orderTwoCorrelation_add_one] at hlower'
  rw [abs_le]
  constructor <;> linarith

/-- The even `2k`-th correlation power sum over `RM(2,n)`. -/
noncomputable def orderTwoCorrelationPowerSum
    (k : ℕ) (f : BooleanFunction n) : ℝ :=
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  ∑ g : reedMuller 2 n, (orderTwoCorrelation f g.1) ^ (2 * k)

private theorem evenPower_nonneg (x : ℝ) (k : ℕ) :
    0 ≤ x ^ (2 * k) := by
  rw [show 2 * k = k * 2 by omega, pow_mul]
  exact sq_nonneg (x ^ k)

/-- Correlation power sums are nonnegative. -/
theorem orderTwoCorrelationPowerSum_nonneg
    (k : ℕ) (f : BooleanFunction n) :
    0 ≤ orderTwoCorrelationPowerSum k f := by
  classical
  rw [orderTwoCorrelationPowerSum]
  exact Finset.sum_nonneg fun g _hg ↦ evenPower_nonneg _ _

private theorem exists_walshTransform_ne_zero
    (f : BooleanFunction n) :
    ∃ a : FABL.F₂Cube n, walshTransform f a ≠ 0 := by
  by_contra h
  push Not at h
  have hsum : ∑ a : FABL.F₂Cube n, (walshTransform f a : ℝ) ^ 2 = 0 := by
    simp [h]
  have hparseval := sum_walshTransform_sq_eq_two_pow_sq f
  rw [hsum] at hparseval
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  nlinarith

private theorem orderTwoCorrelation_affine_zero
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    orderTwoCorrelation f (FABL.affineFunction 0 a) =
      walshTransform f a := by
  classical
  unfold orderTwoCorrelation walshTransform walshTerm
  push_cast
  apply Finset.sum_congr rfl
  intro x _hx
  simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]

/-- Every correlation power sum has a nonzero affine-correlation summand. -/
theorem orderTwoCorrelationPowerSum_pos
    (k : ℕ) (f : BooleanFunction n) :
    0 < orderTwoCorrelationPowerSum k f := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  obtain ⟨a, ha⟩ := exists_walshTransform_ne_zero f
  let g : reedMuller 2 n :=
    ⟨FABL.affineFunction 0 a,
      reedMuller_mono (by omega : 1 ≤ 2)
        (affineFunction_mem_reedMuller_one 0 a)⟩
  have hg : orderTwoCorrelation f g.1 ≠ 0 := by
    change orderTwoCorrelation f (FABL.affineFunction 0 a) ≠ 0
    rw [orderTwoCorrelation_affine_zero]
    exact_mod_cast ha
  have hterm : 0 < (orderTwoCorrelation f g.1) ^ (2 * k) := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
    exact sq_pos_of_ne_zero (pow_ne_zero k hg)
  rw [orderTwoCorrelationPowerSum]
  exact Finset.sum_pos'
    (fun h _hh ↦ evenPower_nonneg _ _)
    ⟨g, Finset.mem_univ g, hterm⟩

/-- The consecutive power sums satisfy the finite maximum-moment inequality
used in Carlet--Mesnager Relation (9.9). -/
theorem orderTwoCorrelationPowerSum_succ_le
    (k : ℕ) (f : BooleanFunction n) :
    orderTwoCorrelationPowerSum (k + 1) f ≤
      (maximumOrderTwoCorrelation f) ^ 2 *
        orderTwoCorrelationPowerSum k f := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  rw [orderTwoCorrelationPowerSum, orderTwoCorrelationPowerSum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _hg
  have habs := abs_orderTwoCorrelation_le_maximum f g.1 g.2
  have hmaximum := maximumOrderTwoCorrelation_nonneg f
  have hsquare :
      (orderTwoCorrelation f g.1) ^ 2 ≤
        (maximumOrderTwoCorrelation f) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hmaximum]
    exact habs
  have hpow : 0 ≤ (orderTwoCorrelation f g.1) ^ (2 * k) := by
    exact evenPower_nonneg _ _
  calc
    (orderTwoCorrelation f g.1) ^ (2 * (k + 1)) =
        (orderTwoCorrelation f g.1) ^ 2 *
          (orderTwoCorrelation f g.1) ^ (2 * k) := by
      rw [Nat.mul_succ, pow_add]
      ring
    _ ≤ (maximumOrderTwoCorrelation f) ^ 2 *
          (orderTwoCorrelation f g.1) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hsquare hpow

/-- Carlet--Mesnager Relation (9.9): the square root of a consecutive
power-sum ratio is bounded by the maximum second-order correlation. -/
theorem sqrt_orderTwoCorrelationPowerSum_ratio_le
    (k : ℕ) (f : BooleanFunction n) :
    Real.sqrt
        (orderTwoCorrelationPowerSum (k + 1) f /
          orderTwoCorrelationPowerSum k f) ≤
      maximumOrderTwoCorrelation f := by
  have hden := orderTwoCorrelationPowerSum_pos k f
  have hnum := orderTwoCorrelationPowerSum_nonneg (k + 1) f
  have hratio :
      orderTwoCorrelationPowerSum (k + 1) f /
          orderTwoCorrelationPowerSum k f ≤
        (maximumOrderTwoCorrelation f) ^ 2 := by
    rw [div_le_iff₀ hden]
    exact orderTwoCorrelationPowerSum_succ_le k f
  have hratioNonneg :
      0 ≤ orderTwoCorrelationPowerSum (k + 1) f /
        orderTwoCorrelationPowerSum k f :=
    div_nonneg hnum hden.le
  have hsqrt := Real.sq_sqrt hratioNonneg
  have hsqrtNonneg := Real.sqrt_nonneg
    (orderTwoCorrelationPowerSum (k + 1) f /
      orderTwoCorrelationPowerSum k f)
  have hmaximum := maximumOrderTwoCorrelation_nonneg f
  nlinarith

/-- The minimum consecutive moment ratio appearing in Relation (9.10). -/
noncomputable def minimumOrderTwoMomentRatio
    (k n : ℕ) : ℝ :=
  (Finset.univ : Finset (BooleanFunction n)).inf'
    Finset.univ_nonempty fun f ↦
      Real.sqrt
        (orderTwoCorrelationPowerSum (k + 1) f /
          orderTwoCorrelationPowerSum k f)

/-- Carlet--Mesnager Relation (9.10), before inserting the low-weight
dual-code character-sum estimate. -/
theorem maximumHigherOrderNonlinearity_two_cast_le_momentRatio
    (k n : ℕ) :
    (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
      (2 ^ n : ℝ) / 2 - minimumOrderTwoMomentRatio k n / 2 := by
  classical
  obtain ⟨f, hmaximum⟩ :=
    exists_higherOrderNonlinearity_eq_maximum 2 n
  have hratioLeMaximum :=
    sqrt_orderTwoCorrelationPowerSum_ratio_le k f
  have hsourceRelation := maximumOrderTwoCorrelation_eq f
  have hminimum : minimumOrderTwoMomentRatio k n ≤
      Real.sqrt
        (orderTwoCorrelationPowerSum (k + 1) f /
          orderTwoCorrelationPowerSum k f) := by
    rw [minimumOrderTwoMomentRatio]
    exact Finset.inf'_le _ (Finset.mem_univ f)
  rw [← hmaximum]
  linarith

/-- The parity of the multiset of points in an ordered tuple, viewed as a
Boolean function. -/
def tuplePointParity
    (x : Fin m → FABL.F₂Cube n) : BooleanFunction n :=
  fun y ↦ ∑ i, if x i = y then 1 else 0

/-- Pairing with the tuple point-parity function evaluates a Boolean function
on every entry of the tuple and adds the results. -/
theorem booleanFunctionPairing_tuplePointParity
    (f : BooleanFunction n) (x : Fin m → FABL.F₂Cube n) :
    booleanFunctionPairing n f (tuplePointParity x) =
      ∑ i, f (x i) := by
  classical
  rw [booleanFunctionPairing_apply]
  simp_rw [tuplePointParity, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

/-- The ordered `2k`-tuples whose point-parity function belongs to the dual
Reed--Muller code occurring in Carlet--Mesnager Lemma 9.2.2. -/
noncomputable def orderTwoAdmissibleTuples
    (k n : ℕ) : Finset (Fin (2 * k) → FABL.F₂Cube n) := by
  classical
  exact (Finset.univ : Finset (Fin (2 * k) → FABL.F₂Cube n)).filter fun x ↦
    tuplePointParity x ∈ reedMuller (n - 3) n

/-- The dual Reed--Muller words used to group the admissible tuples. -/
noncomputable def orderTwoDualWords
    (n : ℕ) : Finset (BooleanFunction n) := by
  classical
  exact (Finset.univ : Finset (BooleanFunction n)).filter fun h ↦
    h ∈ reedMuller (n - 3) n

/-- The fiber of ordered tuples having a prescribed point-parity word. -/
noncomputable def tuplePointParityFiber
    (k : ℕ) (h : BooleanFunction n) :
    Finset (Fin (2 * k) → FABL.F₂Cube n) := by
  classical
  exact (Finset.univ : Finset (Fin (2 * k) → FABL.F₂Cube n)).filter fun x ↦
    tuplePointParity x = h

/-- The number of ordered tuples having a prescribed point-parity word. -/
noncomputable def tuplePointParityMultiplicity
    (k : ℕ) (h : BooleanFunction n) : ℕ :=
  (tuplePointParityFiber k h).card

private def tupleRelabelEquiv
    (m : ℕ) (σ : Equiv.Perm (FABL.F₂Cube n)) :
    (Fin m → FABL.F₂Cube n) ≃ (Fin m → FABL.F₂Cube n) :=
  Equiv.piCongrRight fun _ ↦ σ

private theorem tuplePointParity_tupleRelabelEquiv
    (x : Fin m → FABL.F₂Cube n) (σ : Equiv.Perm (FABL.F₂Cube n)) :
    tuplePointParity (tupleRelabelEquiv m σ x) =
      tuplePointParity x ∘ σ.symm := by
  classical
  funext y
  simp only [tuplePointParity, tupleRelabelEquiv,
    Equiv.piCongrRight_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.map_apply, σ.apply_eq_iff_eq_symm_apply]

/-- Relabeling all cube points by a permutation preserves point-parity fiber
cardinality. -/
theorem tuplePointParityMultiplicity_comp_perm
    (k : ℕ) (h : BooleanFunction n)
    (σ : Equiv.Perm (FABL.F₂Cube n)) :
    tuplePointParityMultiplicity k h =
      tuplePointParityMultiplicity k (h ∘ σ.symm) := by
  classical
  rw [tuplePointParityMultiplicity, tuplePointParityMultiplicity]
  apply Finset.card_equiv (tupleRelabelEquiv (2 * k) σ)
  intro x
  simp only [tuplePointParityFiber, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [tuplePointParity_tupleRelabelEquiv]
  constructor
  · intro hx
    rw [hx]
  · intro hx
    funext y
    have hy := congrFun hx (σ y)
    simpa using hy

/-- Point-parity fiber cardinality depends only on the Hamming weight of the
prescribed word. -/
theorem tuplePointParityMultiplicity_eq_of_hammingWeight_eq
    (k : ℕ) (h₁ h₂ : BooleanFunction n)
    (hweight : hammingWeight h₁ = hammingWeight h₂) :
    tuplePointParityMultiplicity k h₁ =
      tuplePointParityMultiplicity k h₂ := by
  classical
  have hcard : (support h₁).card = (support h₂).card := by
    rw [← hammingWeight_eq_card_support,
      ← hammingWeight_eq_card_support]
    exact hweight
  obtain ⟨σ, hσ⟩ :=
    Equiv.Perm.exists_map_finset_eq (support h₁) (support h₂) hcard
  have hcomp : h₁ ∘ σ.symm = h₂ := by
    funext y
    have hmem : σ.symm y ∈ support h₁ ↔ y ∈ support h₂ := by
      rw [← hσ]
      simp
    have hone : h₁ (σ.symm y) = 1 ↔ h₂ y = 1 := by
      simpa using hmem
    by_cases hleft : h₁ (σ.symm y) = 0
    · have hright : h₂ y = 0 := by
        by_contra hright
        have hrightOne : h₂ y = 1 :=
          Fin.eq_one_of_ne_zero _ hright
        have hleftOne := hone.mpr hrightOne
        exact zero_ne_one (hleft.symm.trans hleftOne)
      exact hleft.trans hright.symm
    · have hleftOne : h₁ (σ.symm y) = 1 :=
        Fin.eq_one_of_ne_zero _ hleft
      exact hleftOne.trans (hone.mp hleftOne).symm
  rw [← hcomp]
  exact tuplePointParityMultiplicity_comp_perm k h₁ σ

/-- The common point-parity multiplicity of words of Hamming weight `w`, or
zero when no such word exists. -/
noncomputable def tuplePointParityMultiplicityByWeight
    (k n w : ℕ) : ℕ :=
  if hweight : ∃ h : BooleanFunction n, hammingWeight h = w then
    tuplePointParityMultiplicity k (Classical.choose hweight)
  else
    0

/-- A point-parity fiber multiplicity is its weight-indexed multiplicity. -/
theorem tuplePointParityMultiplicity_eq_byWeight
    (k : ℕ) (h : BooleanFunction n) :
    tuplePointParityMultiplicity k h =
      tuplePointParityMultiplicityByWeight k n (hammingWeight h) := by
  classical
  rw [tuplePointParityMultiplicityByWeight,
    dif_pos (⟨h, rfl⟩ : ∃ g : BooleanFunction n,
      hammingWeight g = hammingWeight h)]
  apply tuplePointParityMultiplicity_eq_of_hammingWeight_eq
  exact (Classical.choose_spec
    (⟨h, rfl⟩ : ∃ g : BooleanFunction n,
      hammingWeight g = hammingWeight h)).symm

private noncomputable def booleanFunctionPairingCharacter
    (h : BooleanFunction n) : AddChar (BooleanFunction n) ℝ :=
  FABL.binarySign.compAddMonoidHom
    { toFun := fun g ↦ booleanFunctionPairing n g h
      map_zero' := by simp
      map_add' := by simp }

private noncomputable def reedMullerPairingCharacter
    (h : BooleanFunction n) : AddChar (reedMuller 2 n) ℝ :=
  (booleanFunctionPairingCharacter h).compAddMonoidHom
    (reedMuller 2 n).subtype.toAddMonoidHom

private theorem booleanFunctionPairingCharacter_eq_zero_iff
    (h : BooleanFunction n) :
    booleanFunctionPairingCharacter h = 0 ↔ h = 0 := by
  classical
  constructor
  · intro hzero
    apply (booleanFunctionPairing_nondegenerate (n := n)).2 h
    intro g
    have happ := DFunLike.congr_fun hzero g
    change FABL.binarySign (booleanFunctionPairing n g h) = 1 at happ
    exact (FABL.binarySign_eq_one_iff _).mp happ
  · rintro rfl
    ext g
    rw [AddChar.zero_apply]
    simp [booleanFunctionPairingCharacter]

private theorem sum_booleanFunctionPairingCharacter
    (h : BooleanFunction n) :
    ∑ g : BooleanFunction n,
        FABL.binarySign (booleanFunctionPairing n g h) =
      if h = 0 then (2 : ℝ) ^ (2 ^ n) else 0 := by
  classical
  change (∑ g : BooleanFunction n,
    booleanFunctionPairingCharacter h g) = _
  rw [AddChar.sum_eq_ite]
  by_cases hh : h = 0
  · rw [if_pos ((booleanFunctionPairingCharacter_eq_zero_iff h).2 hh),
      if_pos hh,
      show Fintype.card (BooleanFunction n) = 2 ^ (2 ^ n) by simp]
    norm_cast
  · rw [if_neg (mt (booleanFunctionPairingCharacter_eq_zero_iff h).mp hh),
      if_neg hh]

private theorem sum_booleanFunctionPairingCharacter_add
    (p h : BooleanFunction n) :
    ∑ g : BooleanFunction n,
        FABL.binarySign (booleanFunctionPairing n g (p + h)) =
      if p = h then (2 : ℝ) ^ (2 ^ n) else 0 := by
  rw [sum_booleanFunctionPairingCharacter]
  congr 1
  rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self]

/-- The character sum over `RM(2,n)` induced by pairing with `h`. -/
noncomputable def reedMullerTwoPairingCharacterSum
    (h : BooleanFunction n) : ℝ :=
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  ∑ g : reedMuller 2 n,
    FABL.binarySign (booleanFunctionPairing n g.1 h)

private theorem reedMullerPairingCharacter_eq_zero_iff
    (h : BooleanFunction n) :
    reedMullerPairingCharacter h = 0 ↔ h ∈ reedMullerDual 2 n := by
  classical
  constructor
  · intro hzero
    rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff]
    intro g hg
    have happ := DFunLike.congr_fun hzero
      (⟨g, hg⟩ : reedMuller 2 n)
    change FABL.binarySign (booleanFunctionPairing n g h) = 1 at happ
    exact (FABL.binarySign_eq_one_iff _).mp happ
  · intro hdual
    ext g
    rw [AddChar.zero_apply]
    apply (FABL.binarySign_eq_one_iff _).2
    rw [reedMullerDual, LinearMap.BilinForm.mem_orthogonal_iff] at hdual
    exact hdual g.1 g.2

/-- Character orthogonality on `RM(2,n)` at a word in the dual code. -/
theorem reedMullerTwoPairingCharacterSum_eq_card_of_mem_dual
    (h : BooleanFunction n) (hdual : h ∈ reedMullerDual 2 n) :
    reedMullerTwoPairingCharacterSum h =
      (Nat.card (reedMuller 2 n) : ℝ) := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  rw [reedMullerTwoPairingCharacterSum]
  change (∑ g : reedMuller 2 n, reedMullerPairingCharacter h g) = _
  rw [AddChar.sum_eq_ite,
    if_pos ((reedMullerPairingCharacter_eq_zero_iff h).2 hdual),
    Nat.card_eq_fintype_card]

/-- Character orthogonality on `RM(2,n)` away from the dual code. -/
theorem reedMullerTwoPairingCharacterSum_eq_zero_of_not_mem_dual
    (h : BooleanFunction n) (hdual : h ∉ reedMullerDual 2 n) :
    reedMullerTwoPairingCharacterSum h = 0 := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  rw [reedMullerTwoPairingCharacterSum]
  change (∑ g : reedMuller 2 n, reedMullerPairingCharacter h g) = 0
  rw [AddChar.sum_eq_ite,
    if_neg (mt (reedMullerPairingCharacter_eq_zero_iff h).mp hdual)]

private theorem orderTwoCorrelation_eq_sum_realSignView
    (f g : BooleanFunction n) :
    orderTwoCorrelation f g = ∑ y, realSignView (f + g) y := by
  rw [orderTwoCorrelation,
    walshTransform_cast_eq_sum_realSignView_mul_character]
  simp

private theorem product_realSignView_eq_pairing_tuplePointParity
    (f : BooleanFunction n) (x : Fin m → FABL.F₂Cube n) :
    ∏ i, realSignView f (x i) =
      FABL.binarySign (booleanFunctionPairing n f (tuplePointParity x)) := by
  rw [booleanFunctionPairing_tuplePointParity]
  simp only [realSignView, FABL.realSignEncodedFunction,
    FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
  symm
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, ih]

private theorem sum_realSignView_eq_two_pow_sub_two_weight
    (g : BooleanFunction n) :
    ∑ y, realSignView g y =
      (2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ) := by
  calc
    (∑ y, realSignView g y) = (walshTransform g 0 : ℝ) := by
      symm
      rw [walshTransform_cast_eq_sum_realSignView_mul_character]
      simp
    _ = (2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ) := by
      exact_mod_cast walshTransform_zero_eq_two_pow_sub_two_weight g

private noncomputable def cubePointEquivFin
    (n : ℕ) : FABL.F₂Cube n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (card_f₂Cube n)

private noncomputable def booleanFunctionVectorEquiv
    (n : ℕ) : BooleanFunction n ≃ FABL.F₂Cube (2 ^ n) :=
  Equiv.arrowCongr (cubePointEquivFin n) (Equiv.refl FABL.𝔽₂)

private theorem f₂Support_card_booleanFunctionVectorEquiv
    (g : BooleanFunction n) :
    (FABL.f₂Support (booleanFunctionVectorEquiv n g)).card =
      hammingWeight g := by
  classical
  rw [hammingWeight_eq_card_support]
  symm
  apply Finset.card_equiv (cubePointEquivFin n)
  intro y
  rw [mem_support, FABL.mem_f₂Support]
  change g y = 1 ↔
    g ((cubePointEquivFin n).symm (cubePointEquivFin n y)) ≠ 0
  rw [(cubePointEquivFin n).symm_apply_apply]
  constructor
  · intro hy
    rw [hy]
    exact one_ne_zero
  · exact Fin.eq_one_of_ne_zero _

private theorem vectorWalshCharacter_booleanFunctionVectorEquiv
    (g h : BooleanFunction n) :
    FABL.vectorWalshCharacter (booleanFunctionVectorEquiv n g)
        (booleanFunctionVectorEquiv n h) =
      FABL.binarySign (booleanFunctionPairing n g h) := by
  rw [FABL.vectorWalshCharacter_apply, booleanFunctionPairing_apply]
  congr 1
  unfold FABL.f₂DotProduct dotProduct
  symm
  apply Fintype.sum_equiv (cubePointEquivFin n)
  intro y
  simp [booleanFunctionVectorEquiv, Equiv.arrowCongr,
    Function.comp_apply]

private theorem negativeCoordinateCount_binaryCubeSignEquiv
    (q : ℕ) (x : FABL.F₂Cube q) :
    FABL.negativeCoordinateCount (FABL.binaryCubeSignEquiv q x) =
      (FABL.f₂Support x).card := by
  classical
  unfold FABL.negativeCoordinateCount FABL.f₂Support
  congr 1
  ext i
  by_cases hi : x i = 0
  · simp [hi]
  · have hiOne : x i = 1 := Fin.eq_one_of_ne_zero _ hi
    simp [hiOne]

private theorem sum_vectorWalshCharacter_supportCard_eq_krawtchoukValue
    (q j : ℕ) (x : FABL.F₂Cube q) :
    ∑ γ ∈ (Finset.univ : Finset (FABL.F₂Cube q)).filter
        (fun γ ↦ (FABL.f₂Support γ).card = j),
      FABL.vectorWalshCharacter γ x =
        FABL.krawtchoukValue j (FABL.binaryCubeSignEquiv q x) := by
  classical
  rw [Finset.sum_filter, FABL.krawtchoukValue]
  calc
    (∑ γ : FABL.F₂Cube q,
        if (FABL.f₂Support γ).card = j then
          FABL.vectorWalshCharacter γ x else 0) =
        ∑ S : Finset (Fin q),
          if S.card = j then
            FABL.monomial S (FABL.binaryCubeSignEquiv q x) else 0 := by
      apply Fintype.sum_equiv (FABL.f₂CubeEquivFinset q)
      intro γ
      rw [FABL.f₂CubeEquivFinset_apply]
      by_cases hcard : (FABL.f₂Support γ).card = j
      · rw [if_pos hcard, if_pos hcard, FABL.vectorWalshCharacter,
          FABL.monomial_binaryCubeSignEquiv]
      · rw [if_neg hcard, if_neg hcard]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin q)).powersetCard j,
          FABL.monomial S (FABL.binaryCubeSignEquiv q x) := by
      rw [← Finset.sum_filter]
      congr 1
      ext S
      simp [eq_comm]

private theorem sum_booleanFunctionPairing_weightLayer_eq_eval_krawtchouk
    (j : ℕ) (hj : j ≤ 2 ^ n) (h : BooleanFunction n) :
    ∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
        (fun g ↦ hammingWeight g = j),
      FABL.binarySign (booleanFunctionPairing n g h) =
        Polynomial.eval (hammingWeight h : ℝ)
          (FABL.krawtchoukPolynomial (2 ^ n) j) := by
  classical
  calc
    (∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
        (fun g ↦ hammingWeight g = j),
      FABL.binarySign (booleanFunctionPairing n g h)) =
        ∑ γ ∈ (Finset.univ : Finset (FABL.F₂Cube (2 ^ n))).filter
            (fun γ ↦ (FABL.f₂Support γ).card = j),
          FABL.vectorWalshCharacter γ (booleanFunctionVectorEquiv n h) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Fintype.sum_equiv (booleanFunctionVectorEquiv n)
      intro g
      have hweight := f₂Support_card_booleanFunctionVectorEquiv g
      have hcharacter :=
        vectorWalshCharacter_booleanFunctionVectorEquiv g h
      by_cases hg : hammingWeight g = j
      · rw [if_pos hg, if_pos (hweight.trans hg), hcharacter]
      · rw [if_neg hg, if_neg (by rw [hweight]; exact hg)]
    _ = FABL.krawtchoukValue j
          (FABL.binaryCubeSignEquiv (2 ^ n)
            (booleanFunctionVectorEquiv n h)) :=
      sum_vectorWalshCharacter_supportCard_eq_krawtchoukValue
        (2 ^ n) j (booleanFunctionVectorEquiv n h)
    _ = Polynomial.eval (hammingWeight h : ℝ)
          (FABL.krawtchoukPolynomial (2 ^ n) j) := by
      have hrepresentation :=
        (FABL.krawtchoukPolynomial_represents j hj
          (FABL.binaryCubeSignEquiv (2 ^ n)
            (booleanFunctionVectorEquiv n h))).2
      rw [negativeCoordinateCount_binaryCubeSignEquiv,
        f₂Support_card_booleanFunctionVectorEquiv] at hrepresentation
      exact hrepresentation.symm

private theorem hammingWeight_le_two_pow
    (g : BooleanFunction n) : hammingWeight g ≤ 2 ^ n := by
  rw [← card_f₂Cube n]
  exact hammingNorm_le_card_fintype

private theorem two_pow_mul_tuplePointParityMultiplicity_eq_fourierSum
    (k : ℕ) (h : BooleanFunction n) :
    (2 : ℝ) ^ (2 ^ n) * (tuplePointParityMultiplicity k h : ℝ) =
      ∑ g : BooleanFunction n,
        FABL.binarySign (booleanFunctionPairing n g h) *
          ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k) := by
  classical
  rw [tuplePointParityMultiplicity]
  calc
    (2 : ℝ) ^ (2 ^ n) * ((tuplePointParityFiber k h).card : ℝ) =
        ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          if tuplePointParity x = h then (2 : ℝ) ^ (2 ^ n) else 0 := by
      rw [show ((tuplePointParityFiber k h).card : ℝ) =
          ∑ _x ∈ tuplePointParityFiber k h, (1 : ℝ) by simp,
        Finset.mul_sum, tuplePointParityFiber, Finset.sum_filter]
      simp
    _ = ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          ∑ g : BooleanFunction n,
            FABL.binarySign
              (booleanFunctionPairing n g (tuplePointParity x + h)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (sum_booleanFunctionPairingCharacter_add
        (tuplePointParity x) h).symm
    _ = ∑ g : BooleanFunction n,
          ∑ x : Fin (2 * k) → FABL.F₂Cube n,
            FABL.binarySign (booleanFunctionPairing n g h) *
              FABL.binarySign
                (booleanFunctionPairing n g (tuplePointParity x)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _hg
      apply Finset.sum_congr rfl
      intro x _hx
      have hadd := map_add (booleanFunctionPairing n g)
        (tuplePointParity x) h
      rw [hadd, AddChar.map_add_eq_mul, mul_comm]
    _ = ∑ g : BooleanFunction n,
          ∑ x : Fin (2 * k) → FABL.F₂Cube n,
            FABL.binarySign (booleanFunctionPairing n g h) *
              ∏ i, realSignView g (x i) := by
      apply Finset.sum_congr rfl
      intro g _hg
      apply Finset.sum_congr rfl
      intro x _hx
      rw [product_realSignView_eq_pairing_tuplePointParity]
    _ = ∑ g : BooleanFunction n,
          FABL.binarySign (booleanFunctionPairing n g h) *
            (∑ y, realSignView g y) ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [← Finset.mul_sum, Fintype.sum_pow]
    _ = ∑ g : BooleanFunction n,
          FABL.binarySign (booleanFunctionPairing n g h) *
            ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [sum_realSignView_eq_two_pow_sub_two_weight]

private theorem booleanFunctionFourierSum_eq_krawtchoukSum
    (k : ℕ) (h : BooleanFunction n) :
    (∑ g : BooleanFunction n,
        FABL.binarySign (booleanFunctionPairing n g h) *
          ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k)) =
      ∑ j ∈ Finset.range (2 ^ n + 1),
        Polynomial.eval (hammingWeight h : ℝ)
            (FABL.krawtchoukPolynomial (2 ^ n) j) *
          ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k) := by
  classical
  calc
    (∑ g : BooleanFunction n,
        FABL.binarySign (booleanFunctionPairing n g h) *
          ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k)) =
        ∑ j ∈ Finset.range (2 ^ n + 1),
          ∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
              (fun g ↦ hammingWeight g = j),
            FABL.binarySign (booleanFunctionPairing n g h) *
              ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro g _hg
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (hammingWeight_le_two_pow g)
    _ = ∑ j ∈ Finset.range (2 ^ n + 1),
          (∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
              (fun g ↦ hammingWeight g = j),
            FABL.binarySign (booleanFunctionPairing n g h)) *
              ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        (∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
            (fun g ↦ hammingWeight g = j),
          FABL.binarySign (booleanFunctionPairing n g h) *
            ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k)) =
            ∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
                (fun g ↦ hammingWeight g = j),
              FABL.binarySign (booleanFunctionPairing n g h) *
                ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k) := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [(Finset.mem_filter.mp hg).2]
        _ = (∑ g ∈ (Finset.univ : Finset (BooleanFunction n)).filter
              (fun g ↦ hammingWeight g = j),
            FABL.binarySign (booleanFunctionPairing n g h)) *
              ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k) := by
          rw [Finset.sum_mul]
    _ = ∑ j ∈ Finset.range (2 ^ n + 1),
        Polynomial.eval (hammingWeight h : ℝ)
            (FABL.krawtchoukPolynomial (2 ^ n) j) *
          ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sum_booleanFunctionPairing_weightLayer_eq_eval_krawtchouk
        j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) h]

/-- Mesnager HDR Lemma 9.2.7 in finite Fourier form: the ordered-tuple
multiplicity at a realizable weight is the inverse Fourier transform of the
`2k`-th powers of the one-point character sums. -/
theorem tuplePointParityMultiplicityByWeight_eq_fourierSum
    (k : ℕ) (h : BooleanFunction n) :
    (tuplePointParityMultiplicityByWeight k n (hammingWeight h) : ℝ) =
      (∑ g : BooleanFunction n,
          FABL.binarySign (booleanFunctionPairing n g h) *
            ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k)) /
        (2 : ℝ) ^ (2 ^ n) := by
  rw [← tuplePointParityMultiplicity_eq_byWeight k h,
    eq_div_iff (by positivity)]
  simpa [mul_comm] using
    two_pow_mul_tuplePointParityMultiplicity_eq_fourierSum k h

/-- The finite Krawtchouk sum equal to Mesnager's exponential-generating
coefficient `[z^(2k)] sinh(z)^w cosh(z)^(2^n-w)`. Here `w` is the actual
Hamming weight, rather than Mesnager's half-weight parameter. -/
noncomputable def tuplePointParityKrawtchoukMultiplicity
    (k n w : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2 ^ n + 1),
      Polynomial.eval (w : ℝ)
          (FABL.krawtchoukPolynomial (2 ^ n) j) *
        ((2 ^ n : ℝ) - 2 * (j : ℝ)) ^ (2 * k)) /
    (2 : ℝ) ^ (2 ^ n)

/-- Mesnager HDR Lemma 9.2.7 in explicit finite Krawtchouk form. -/
theorem tuplePointParityMultiplicityByWeight_eq_krawtchoukSum
    (k : ℕ) (h : BooleanFunction n) :
    (tuplePointParityMultiplicityByWeight k n (hammingWeight h) : ℝ) =
      tuplePointParityKrawtchoukMultiplicity k n (hammingWeight h) := by
  rw [tuplePointParityMultiplicityByWeight_eq_fourierSum,
    tuplePointParityKrawtchoukMultiplicity,
    booleanFunctionFourierSum_eq_krawtchoukSum]

private noncomputable def orderTwoDualTuples
    (k n : ℕ) : Finset (Fin (2 * k) → FABL.F₂Cube n) := by
  classical
  exact (Finset.univ : Finset (Fin (2 * k) → FABL.F₂Cube n)).filter fun x ↦
    tuplePointParity x ∈ reedMullerDual 2 n

private theorem orderTwoCorrelationPowerSum_eq_dualTupleCharacterSum
    (k : ℕ) (f : BooleanFunction n) :
    orderTwoCorrelationPowerSum k f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        ∑ x ∈ orderTwoDualTuples k n,
          FABL.binarySign
            (booleanFunctionPairing n f (tuplePointParity x)) := by
  classical
  letI : Fintype (reedMuller 2 n) := Fintype.ofFinite (reedMuller 2 n)
  rw [orderTwoCorrelationPowerSum]
  calc
    ∑ g : reedMuller 2 n, (orderTwoCorrelation f g.1) ^ (2 * k) =
        ∑ g : reedMuller 2 n,
          ∑ x : Fin (2 * k) → FABL.F₂Cube n,
            ∏ i, realSignView (f + g.1) (x i) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [orderTwoCorrelation_eq_sum_realSignView, Fintype.sum_pow]
    _ = ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          ∑ g : reedMuller 2 n,
            FABL.binarySign
                (booleanFunctionPairing n f (tuplePointParity x)) *
              FABL.binarySign
                (booleanFunctionPairing n g.1 (tuplePointParity x)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro g _hg
      rw [product_realSignView_eq_pairing_tuplePointParity]
      have hpairing :
          booleanFunctionPairing n (f + g.1) (tuplePointParity x) =
            booleanFunctionPairing n f (tuplePointParity x) +
              booleanFunctionPairing n g.1 (tuplePointParity x) := by
        have hadd := congrArg
          (fun L : BooleanFunction n →ₗ[FABL.𝔽₂] FABL.𝔽₂ ↦
            L (tuplePointParity x))
          (map_add (booleanFunctionPairing n) f g.1)
        exact hadd
      rw [hpairing, AddChar.map_add_eq_mul]
    _ = ∑ x : Fin (2 * k) → FABL.F₂Cube n,
          FABL.binarySign
              (booleanFunctionPairing n f (tuplePointParity x)) *
            reedMullerTwoPairingCharacterSum (tuplePointParity x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.mul_sum]
      rfl
    _ = (Nat.card (reedMuller 2 n) : ℝ) *
          ∑ x ∈ orderTwoDualTuples k n,
            FABL.binarySign
              (booleanFunctionPairing n f (tuplePointParity x)) := by
      rw [orderTwoDualTuples, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : tuplePointParity x ∈ reedMullerDual 2 n <;>
        simp [hx,
          reedMullerTwoPairingCharacterSum_eq_card_of_mem_dual,
          reedMullerTwoPairingCharacterSum_eq_zero_of_not_mem_dual,
          mul_comm]

/-- Carlet--Mesnager Lemma 9.2.2: the `2k`-th correlation power sum is the
cardinality of `RM(2,n)` times the character sum over the ordered tuples whose
point-parity function belongs to `RM(n-3,n)`. -/
theorem orderTwoCorrelationPowerSum_eq_admissibleTupleCharacterSum
    (k : ℕ) (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoCorrelationPowerSum k f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        ∑ x ∈ orderTwoAdmissibleTuples k n,
          FABL.binarySign
            (booleanFunctionPairing n f (tuplePointParity x)) := by
  classical
  rw [orderTwoCorrelationPowerSum_eq_dualTupleCharacterSum]
  rw [orderTwoDualTuples, orderTwoAdmissibleTuples,
    reedMullerDual_eq (r := 2) (n := n) (by omega)]
  rw [show n - 2 - 1 = n - 3 by omega]

private theorem admissibleTupleCharacterSum_eq_weightGrouped
    (k : ℕ) (f : BooleanFunction n) :
    (∑ x ∈ orderTwoAdmissibleTuples k n,
        FABL.binarySign
          (booleanFunctionPairing n f (tuplePointParity x))) =
      ∑ h ∈ orderTwoDualWords n,
        (tuplePointParityMultiplicityByWeight k n (hammingWeight h) : ℝ) *
          FABL.binarySign (booleanFunctionPairing n f h) := by
  classical
  calc
    (∑ x ∈ orderTwoAdmissibleTuples k n,
        FABL.binarySign
          (booleanFunctionPairing n f (tuplePointParity x))) =
        ∑ h ∈ orderTwoDualWords n,
          ∑ x ∈ (orderTwoAdmissibleTuples k n).filter
              (fun x ↦ tuplePointParity x = h),
            FABL.binarySign
              (booleanFunctionPairing n f (tuplePointParity x)) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro x hx
      simpa only [orderTwoAdmissibleTuples, orderTwoDualWords,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    _ = ∑ h ∈ orderTwoDualWords n,
        (tuplePointParityMultiplicityByWeight k n (hammingWeight h) : ℝ) *
          FABL.binarySign (booleanFunctionPairing n f h) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hdual : h ∈ reedMuller (n - 3) n := by
        simpa only [orderTwoDualWords, Finset.mem_filter,
          Finset.mem_univ, true_and] using hh
      have hfiber :
          (orderTwoAdmissibleTuples k n).filter
              (fun x ↦ tuplePointParity x = h) =
            tuplePointParityFiber k h := by
        ext x
        simp only [orderTwoAdmissibleTuples, tuplePointParityFiber,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hx ↦ hx.2
        · intro hx
          exact ⟨by simpa only [hx] using hdual, hx⟩
      rw [hfiber]
      calc
        (∑ x ∈ tuplePointParityFiber k h,
            FABL.binarySign
              (booleanFunctionPairing n f (tuplePointParity x))) =
            ∑ _x ∈ tuplePointParityFiber k h,
              FABL.binarySign (booleanFunctionPairing n f h) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxparity : tuplePointParity x = h := by
            simpa [tuplePointParityFiber] using hx
          rw [hxparity]
        _ = ((tuplePointParityFiber k h).card : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h) := by
          simp
        _ = (tuplePointParityMultiplicityByWeight k n
                (hammingWeight h) : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h) := by
          change (tuplePointParityMultiplicity k h : ℝ) *
              FABL.binarySign (booleanFunctionPairing n f h) = _
          rw [tuplePointParityMultiplicity_eq_byWeight]

/-- Carlet--Mesnager Proposition 9.2.5, first grouping layer: the correlation
power sum is grouped by dual Reed--Muller words, with a tuple multiplicity that
depends only on the word's Hamming weight. -/
theorem orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum
    (k : ℕ) (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoCorrelationPowerSum k f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        ∑ h ∈ orderTwoDualWords n,
          (tuplePointParityMultiplicityByWeight k n (hammingWeight h) : ℝ) *
            FABL.binarySign (booleanFunctionPairing n f h) := by
  rw [orderTwoCorrelationPowerSum_eq_admissibleTupleCharacterSum k f hn,
    admissibleTupleCharacterSum_eq_weightGrouped]

/-- Proposition 9.2.5 with each tuple multiplicity replaced by its exact finite
Fourier inversion formula. -/
theorem orderTwoCorrelationPowerSum_eq_dualFourierMultiplicityCharacterSum
    (k : ℕ) (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoCorrelationPowerSum k f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        ∑ h ∈ orderTwoDualWords n,
          ((∑ g : BooleanFunction n,
              FABL.binarySign (booleanFunctionPairing n g h) *
                ((2 ^ n : ℝ) - 2 * (hammingWeight g : ℝ)) ^ (2 * k)) /
            (2 : ℝ) ^ (2 ^ n)) *
              FABL.binarySign (booleanFunctionPairing n f h) := by
  rw [orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum k f hn]
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  rw [tuplePointParityMultiplicityByWeight_eq_fourierSum]

/-- Proposition 9.2.5 with each tuple multiplicity replaced by the explicit
finite Krawtchouk sum equivalent to Mesnager's generating-function formula. -/
theorem orderTwoCorrelationPowerSum_eq_dualKrawtchoukMultiplicityCharacterSum
    (k : ℕ) (f : BooleanFunction n) (hn : 3 ≤ n) :
    orderTwoCorrelationPowerSum k f =
      (Nat.card (reedMuller 2 n) : ℝ) *
        ∑ h ∈ orderTwoDualWords n,
          tuplePointParityKrawtchoukMultiplicity k n (hammingWeight h) *
            FABL.binarySign (booleanFunctionPairing n f h) := by
  rw [orderTwoCorrelationPowerSum_eq_dualFourierMultiplicityCharacterSum
    k f hn]
  congr 1
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← tuplePointParityMultiplicityByWeight_eq_fourierSum,
    tuplePointParityMultiplicityByWeight_eq_krawtchoukSum]

end CryptBoolean
