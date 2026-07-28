/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.TracePairing
public import CryptBoolean.Carlet.Chapter05.QuadraticTraceRepresentation
public import CryptBoolean.Carlet.Chapter06.Bentness

import Mathlib.GroupTheory.OrderOfElement

/-!
# Hyper-bent functions

Carlet Section 6.7: finite-field Walsh transforms and the power-reindexing
definition of hyper-bent functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance hyperBentFieldFintype :
    Fintype (BinaryGaloisField n) :=
  Fintype.ofFinite (BinaryGaloisField n)

/-- The raw Walsh transform of a Boolean function represented on `GF(2^n)`,
using the absolute-trace pairing for its linear characters. -/
noncomputable def fieldWalshTransform
    (f : FieldBooleanFunction n) (a : BinaryGaloisField n) : ℤ :=
  ∑ x : BinaryGaloisField n,
    bitSignInt (f x + absoluteTrace n (a * x))

/-- Bentness in finite-field coordinates. -/
def IsFieldBent (f : FieldBooleanFunction n) : Prop :=
  ∀ a : BinaryGaloisField n,
    (fieldWalshTransform f a).natAbs = 2 ^ (n / 2)

/-- Reindex a finite-field Boolean function by a power map. -/
noncomputable def fieldPowerReindex (f : FieldBooleanFunction n) (i : ℕ) :
    FieldBooleanFunction n :=
  fun x ↦ f (x ^ i)

/-- A power map with exponent coprime to the order of the multiplicative
group is a permutation of `GF(2^n)`. -/
theorem fieldPowerMap_bijective {i : ℕ} (hn : 2 ≤ n)
    (hi : Nat.Coprime i (2 ^ n - 1)) :
    Function.Bijective
      (fun x : BinaryGaloisField n ↦ x ^ i) := by
  have hcard : Nat.card (BinaryGaloisField n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n (by omega)]
  have hcop : (Nat.card (BinaryGaloisField n)ˣ).Coprime i := by
    rw [hcard]
    exact hi.symm
  have hunit : Function.Bijective
      (fun z : (BinaryGaloisField n)ˣ ↦ z ^ i) :=
    Nat.Coprime.pow_left_bijective hcop
  have hmodulus : 1 < 2 ^ n - 1 := by
    have hpower : 2 ^ 2 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by omega) hn
    norm_num at hpower ⊢
    omega
  have hiPos : 0 < i := by
    by_contra hnot
    have hizero : i = 0 := by omega
    subst i
    simp only [Nat.coprime_zero_left] at hi
    omega
  constructor
  · intro x y hxy
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 :=
        (pow_eq_zero_iff hiPos.ne').mp
          (by simpa [zero_pow hiPos.ne'] using hxy.symm)
      exact hy.symm
    · by_cases hy : y = 0
      · subst y
        have hxzero : x = 0 :=
          (pow_eq_zero_iff hiPos.ne').mp
            (by simpa [zero_pow hiPos.ne'] using hxy)
        exact (hx hxzero).elim
      · have hu : (Units.mk0 x hx : (BinaryGaloisField n)ˣ) ^ i =
            (Units.mk0 y hy : (BinaryGaloisField n)ˣ) ^ i := by
          apply Units.val_injective
          exact hxy
        exact congrArg Units.val (hunit.1 hu)
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy, zero_pow hiPos.ne']⟩
    · obtain ⟨u, hu⟩ := hunit.2 (Units.mk0 y hy)
      refine ⟨(u : BinaryGaloisField n), ?_⟩
      exact congrArg Units.val hu

/-- The power permutation attached to a coprime exponent. -/
noncomputable def fieldPowerEquiv {i : ℕ} (hn : 2 ≤ n)
    (hi : Nat.Coprime i (2 ^ n - 1)) :
    BinaryGaloisField n ≃ BinaryGaloisField n :=
  Equiv.ofBijective (fun x ↦ x ^ i) (fieldPowerMap_bijective hn hi)

@[simp] theorem fieldPowerEquiv_apply {i : ℕ} (hn : 2 ≤ n)
    (hi : Nat.Coprime i (2 ^ n - 1)) (x : BinaryGaloisField n) :
    fieldPowerEquiv hn hi x = x ^ i := rfl

/-- Power reindexing is precomposition by the corresponding field
permutation. -/
theorem fieldPowerReindex_eq_comp_fieldPowerEquiv
    (f : FieldBooleanFunction n) {i : ℕ} (hn : 2 ≤ n)
    (hi : Nat.Coprime i (2 ^ n - 1)) :
    fieldPowerReindex f i = f ∘ fieldPowerEquiv hn hi := by
  rfl

/-- Carlet's hyper-bent predicate: in even dimension, every power reindexing
whose exponent is coprime to `2^n-1` is bent. -/
def IsHyperBent (f : FieldBooleanFunction n) : Prop :=
  Even n ∧ ∀ i : ℕ, Nat.Coprime i (2 ^ n - 1) →
    IsFieldBent (fieldPowerReindex f i)

/-- Every cube frequency has a unique finite-field trace coefficient, so its
raw Walsh coefficient is a field Walsh coefficient. -/
theorem exists_fieldWalshTransform_eq_walshTransform
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FieldBooleanFunction n) (u : FABL.F₂Cube n) :
    ∃ a : BinaryGaloisField n,
      fieldWalshTransform f a = walshTransform (f ∘ theta) u := by
  obtain ⟨a, ha, _haUnique⟩ := existsUnique_tracePairingCoefficient theta u
  refine ⟨a, ?_⟩
  unfold fieldWalshTransform walshTransform
  symm
  apply Fintype.sum_equiv theta.toEquiv
  intro x
  unfold walshTerm
  change bitSignInt (f (theta x) + FABL.f₂DotProduct u x) = _
  rw [ha x]
  rfl

/-- Conversely, every finite-field trace coefficient is represented by a
cube frequency under any linear choice of field coordinates. -/
theorem exists_walshTransform_eq_fieldWalshTransform
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FieldBooleanFunction n) (a : BinaryGaloisField n) :
    ∃ u : FABL.F₂Cube n,
      walshTransform (f ∘ theta) u = fieldWalshTransform f a := by
  let ell : FABL.F₂Cube n →ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
    { toFun := fun x ↦ absoluteTrace n (a * theta x)
      map_add' := by
        intro x y
        simp only [map_add, mul_add]
      map_smul' := by
        intro c x
        rw [theta.map_smul]
        have hmul : a * (c • theta x) = c • (a * theta x) := by
          simp only [Algebra.smul_def]
          ring
        rw [hmul, map_smul]
        rfl }
  let u : FABL.F₂Cube n :=
    (dotProductEquiv FABL.𝔽₂ (Fin n)).symm ell
  have hu (x : FABL.F₂Cube n) :
      FABL.f₂DotProduct u x = absoluteTrace n (a * theta x) := by
    change (dotProductEquiv FABL.𝔽₂ (Fin n) u) x = ell x
    rw [LinearEquiv.apply_symm_apply]
  refine ⟨u, ?_⟩
  unfold fieldWalshTransform walshTransform
  apply Fintype.sum_equiv theta.toEquiv
  intro x
  unfold walshTerm
  change bitSignInt (f (theta x) + FABL.f₂DotProduct u x) = _
  rw [hu x]
  rfl

/-- Finite-field bentness agrees with canonical cube bentness under every
linear coordinate identification. -/
theorem isFieldBent_iff_isBent_comp_linearEquiv
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FieldBooleanFunction n) :
    IsFieldBent f ↔ IsBent (f ∘ theta) := by
  rw [isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half]
  constructor
  · intro hf u
    obtain ⟨a, ha⟩ :=
      exists_fieldWalshTransform_eq_walshTransform theta f u
    rw [← ha]
    exact hf a
  · intro hf a
    obtain ⟨u, hu⟩ :=
      exists_walshTransform_eq_fieldWalshTransform theta f a
    rw [← hu]
    exact hf u

/-- The power exponent `1` shows that every hyper-bent function is bent. -/
theorem IsHyperBent.isFieldBent {f : FieldBooleanFunction n}
    (hf : IsHyperBent f) : IsFieldBent f := by
  have h := hf.2 1 (by simp)
  have heq : fieldPowerReindex f 1 = f := by
    funext x
    simp [fieldPowerReindex]
  rw [heq] at h
  exact h

/-- Coordinate form of the hyper-bent definition. -/
theorem isHyperBent_iff_forall_isBent_powerReindex_comp_linearEquiv
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : FieldBooleanFunction n) :
    IsHyperBent f ↔
      Even n ∧ ∀ i : ℕ, Nat.Coprime i (2 ^ n - 1) →
        IsBent (fieldPowerReindex f i ∘ theta) := by
  unfold IsHyperBent
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨hn, fun i hi ↦ ?_⟩
    exact (isFieldBent_iff_isBent_comp_linearEquiv theta _).1 (hf i hi)
  · rintro ⟨hn, hf⟩
    refine ⟨hn, fun i hi ↦ ?_⟩
    exact (isFieldBent_iff_isBent_comp_linearEquiv theta _).2 (hf i hi)

/-- The two directions `1` and `c` span the quadratic extension when `c`
does not lie in the embedded subfield. -/
theorem quadraticSubfieldBasisMap_bijective {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (c : BinaryGaloisField (2 * m)) (hc : c ∉ Set.range iota) :
    Function.Bijective
      (fun p : BinaryGaloisField m × BinaryGaloisField m ↦
        iota p.1 + c * iota p.2) := by
  let coord : BinaryGaloisField m × BinaryGaloisField m →
      BinaryGaloisField (2 * m) :=
    fun p ↦ iota p.1 + c * iota p.2
  have hcoordInjective : Function.Injective coord := by
    rintro ⟨z, r⟩ ⟨z', r'⟩ hcoord
    change iota z + c * iota r = iota z' + c * iota r' at hcoord
    have hdiff : c * iota (r - r') = iota (z' - z) := by
      rw [map_sub, map_sub]
      linear_combination hcoord
    have hr : r = r' := by
      by_contra hrNe
      have hrDiff : r - r' ≠ 0 := sub_ne_zero.mpr hrNe
      apply hc
      refine ⟨(z' - z) / (r - r'), ?_⟩
      symm
      calc
        c = iota (z' - z) / iota (r - r') :=
          (eq_div_iff ((map_ne_zero iota).mpr hrDiff)).2 hdiff
        _ = iota ((z' - z) / (r - r')) := by
          exact (map_div₀ iota (z' - z) (r - r')).symm
    subst r'
    have hz : z = z' := by
      apply iota.toRingHom.injective
      exact add_right_cancel hcoord
    subst z'
    rfl
  have hcoordCard : Nat.card
        (BinaryGaloisField m × BinaryGaloisField m) =
      Nat.card (BinaryGaloisField (2 * m)) := by
    rw [Nat.card_prod,
      GaloisField.card 2 m hm.ne',
      GaloisField.card 2 (2 * m) (mul_ne_zero (by omega) hm.ne')]
    rw [← pow_add]
    congr 1
    omega
  exact (Nat.bijective_iff_injective_and_card coord).2
    ⟨hcoordInjective, hcoordCard⟩

/-- Coordinates in a quadratic binary extension relative to the basis
formed by `1` and an element outside the embedded subfield. -/
noncomputable def quadraticSubfieldBasisEquiv {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (c : BinaryGaloisField (2 * m)) (hc : c ∉ Set.range iota) :
    BinaryGaloisField m × BinaryGaloisField m ≃
      BinaryGaloisField (2 * m) :=
  Equiv.ofBijective
    (fun p ↦ iota p.1 + c * iota p.2)
    (quadraticSubfieldBasisMap_bijective hm iota c hc)

@[simp] theorem quadraticSubfieldBasisEquiv_apply {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (c : BinaryGaloisField (2 * m)) (hc : c ∉ Set.range iota)
    (p : BinaryGaloisField m × BinaryGaloisField m) :
    quadraticSubfieldBasisEquiv hm iota c hc p =
      iota p.1 + c * iota p.2 := rfl

/-- A coprime power permutation of the quadratic extension restricts to a
power permutation of its embedded middle field. -/
theorem quadraticSubfield_powerMap_bijective {m i : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (hi : Nat.Coprime i (2 ^ (2 * m) - 1)) :
    Function.Bijective (fun r : BinaryGaloisField m ↦ r ^ i) := by
  have hpowerInjective : Function.Injective
      (fun x : BinaryGaloisField (2 * m) ↦ x ^ i) :=
    (fieldPowerMap_bijective (by omega) hi).1
  have hrestrictedInjective : Function.Injective
      (fun r : BinaryGaloisField m ↦ r ^ i) := by
    intro r s hrs
    have hmap : (iota r) ^ i = (iota s) ^ i := by
      simpa only [map_pow] using congrArg iota hrs
    exact iota.toRingHom.injective (hpowerInjective hmap)
  exact ⟨hrestrictedInjective,
    (Finite.injective_iff_surjective).mp hrestrictedInjective⟩

/-- Membership in the quadratic subfield is invariant under every coprime
power permutation of the ambient field. -/
theorem pow_mem_quadraticSubfield_iff {m i : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (hi : Nat.Coprime i (2 ^ (2 * m) - 1))
    (x : BinaryGaloisField (2 * m)) :
    x ^ i ∈ Set.range iota ↔ x ∈ Set.range iota := by
  have hpowerInjective : Function.Injective
      (fun y : BinaryGaloisField (2 * m) ↦ y ^ i) :=
    (fieldPowerMap_bijective (by omega) hi).1
  have hrestricted := quadraticSubfield_powerMap_bijective hm iota hi
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨r, hr⟩ := hrestricted.2 k
    change r ^ i = k at hr
    refine ⟨r, hpowerInjective ?_⟩
    change (iota r) ^ i = x ^ i
    rw [← map_pow, hr, hk]
  · rintro ⟨r, rfl⟩
    exact ⟨r ^ i, map_pow iota r i⟩

/-- Carlet Lemma 4: a coprime power of a translated quadratic-subfield
line meets every non-subfield scalar multiple of the subfield exactly once. -/
theorem existsUnique_subfield_power_intersection {m i : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (a omega : BinaryGaloisField (2 * m))
    (ha : a ∉ Set.range iota)
    (_homega : omega ∉ Set.range iota)
    (hi : Nat.Coprime i (2 ^ (2 * m) - 1)) :
    ∃! z : BinaryGaloisField m,
      ∃ k : BinaryGaloisField m,
        a * (iota z + omega) ^ i = iota k := by
  let power : BinaryGaloisField (2 * m) ≃ BinaryGaloisField (2 * m) :=
    fieldPowerEquiv (by omega) hi
  let c : BinaryGaloisField (2 * m) := power.symm a⁻¹
  have hpowerInjective : Function.Injective
      (fun x : BinaryGaloisField (2 * m) ↦ x ^ i) := by
    intro x y hxy
    apply power.injective
    exact hxy
  have hcPower : c ^ i = a⁻¹ := by
    change power c = a⁻¹
    exact power.apply_symm_apply a⁻¹
  have ha0 : a ≠ 0 := by
    intro haZero
    apply ha
    refine ⟨0, ?_⟩
    simp [haZero]
  have hcOutside : c ∉ Set.range iota := by
    rintro ⟨r, hr⟩
    have hinv : a⁻¹ = iota (r ^ i) := by
      calc
        a⁻¹ = c ^ i := hcPower.symm
        _ = (iota r) ^ i := by rw [hr]
        _ = iota (r ^ i) := by rw [map_pow]
    apply ha
    refine ⟨(r ^ i)⁻¹, ?_⟩
    simpa only [inv_inv, map_inv₀] using (congrArg Inv.inv hinv).symm
  have hrestrictedPowerSurjective : Function.Surjective
      (fun r : BinaryGaloisField m ↦ r ^ i) :=
    (quadraticSubfield_powerMap_bijective hm iota hi).2
  have hcondition (z : BinaryGaloisField m) :
      (∃ k : BinaryGaloisField m,
          a * (iota z + omega) ^ i = iota k) ↔
        ∃ r : BinaryGaloisField m,
          iota z + omega = c * iota r := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨r, hr⟩ := hrestrictedPowerSurjective k
      change r ^ i = k at hr
      refine ⟨r, hpowerInjective ?_⟩
      calc
        (iota z + omega) ^ i = a⁻¹ * (a * (iota z + omega) ^ i) := by
          rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
        _ = a⁻¹ * iota k := by rw [hk]
        _ = c ^ i * iota (r ^ i) := by rw [hcPower, hr]
        _ = (c * iota r) ^ i := by rw [mul_pow, map_pow]
    · rintro ⟨r, hr⟩
      refine ⟨r ^ i, ?_⟩
      rw [hr, mul_pow, map_pow, hcPower, ← mul_assoc,
        mul_inv_cancel₀ ha0, one_mul]
  let coord := quadraticSubfieldBasisEquiv hm iota c hcOutside
  obtain ⟨p, hp⟩ := coord.surjective omega
  refine ⟨-p.1, ?_, ?_⟩
  · change ∃ k : BinaryGaloisField m,
      a * (iota (-p.1) + omega) ^ i = iota k
    rw [hcondition]
    refine ⟨p.2, ?_⟩
    change iota p.1 + c * iota p.2 = omega at hp
    rw [← hp, map_neg]
    ring
  · intro z hz
    rw [hcondition] at hz
    obtain ⟨r, hr⟩ := hz
    have hzr : coord (-z, r) = omega := by
      change iota (-z) + c * iota r = omega
      rw [map_neg, ← hr]
      ring
    have hpairs := coord.injective (hzr.trans hp.symm)
    simpa using congrArg (fun q ↦ -q.1) hpairs

end CryptBoolean
