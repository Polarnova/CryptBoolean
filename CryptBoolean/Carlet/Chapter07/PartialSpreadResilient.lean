/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.TracePairing
public import CryptBoolean.Carlet.Chapter04.Resiliency
public import CryptBoolean.Carlet.Chapter06.HyperBentPartialSpread
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Partial-spread resilient functions

Carlet Relation (63): a partial-spread quotient construction whose adjoint
coset avoids every low-weight frequency is resilient.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable local instance partialSpreadResilientFieldFintype {r : ℕ} :
    Fintype (BinaryGaloisField r) :=
  Fintype.ofFinite (BinaryGaloisField r)

/-- The partial-spread quotient construction in explicit field and cube
coordinates. -/
noncomputable def partialSpreadResilientFunction {r s : ℕ}
    (theta : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (g : FieldBooleanFunction r)
    (phi : FABL.F₂Cube s →ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (a : BinaryGaloisField r) (b : FABL.F₂Cube s) :
    BooleanFunction (r + s) :=
  fun z ↦
    let p := (cubeSplitLinearEquiv r s) z
    g (theta p.1 / (a + phi p.2)) + FABL.f₂DotProduct b p.2

@[simp] theorem partialSpreadResilientFunction_append {r s : ℕ}
    (theta : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (g : FieldBooleanFunction r)
    (phi : FABL.F₂Cube s →ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (a : BinaryGaloisField r) (b : FABL.F₂Cube s)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    partialSpreadResilientFunction theta g phi a b (Fin.append x y) =
      g (theta x / (a + phi y)) + FABL.f₂DotProduct b y := by
  simp [partialSpreadResilientFunction, cubeSplitLinearEquiv]

private theorem sum_bitSignInt_dotProduct_eq_zero {s : ℕ}
    (u : FABL.F₂Cube s) (hu : u ≠ 0) :
    ∑ y, bitSignInt (FABL.f₂DotProduct u y) = 0 := by
  apply Int.cast_injective (α := ℝ)
  norm_num only [Int.cast_zero]
  calc
    ((∑ y, bitSignInt (FABL.f₂DotProduct u y) : ℤ) : ℝ) =
        rawFourierTransform (fun _ : FABL.F₂Cube s ↦ (1 : ℝ)) u := by
      rw [rawFourierTransform]
      simp_rw [FABL.vectorWalshCharacter_apply, ← bitSignInt_cast]
      push_cast
      simp
    _ = 0 := by rw [rawFourierTransform_one, if_neg hu]

/-- The Walsh transform of the partial-spread quotient construction is a sum
of cube characters indexed by the quotient variable. -/
theorem walshTransform_partialSpreadResilientFunction_append {r s : ℕ}
    (theta : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (g : FieldBooleanFunction r)
    (phi : FABL.F₂Cube s →ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (phiStar : BinaryGaloisField r →ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (hphiStar : ∀ z y,
      FABL.f₂DotProduct (phiStar z) y =
        absoluteTrace r (z * phi y))
    (a : BinaryGaloisField r) (b : FABL.F₂Cube s)
    (hdenom : ∀ y, a + phi y ≠ 0)
    (u : FABL.F₂Cube r) (v : FABL.F₂Cube s)
    (z : BinaryGaloisField r)
    (hz : ∀ x, FABL.f₂DotProduct u x =
      absoluteTrace r (z * theta x)) :
    walshTransform (partialSpreadResilientFunction theta g phi a b)
        (Fin.append u v) =
      ∑ t : BinaryGaloisField r,
        bitSignInt (g t + absoluteTrace r (z * a * t)) *
          ∑ y : FABL.F₂Cube s,
            bitSignInt
              (FABL.f₂DotProduct (phiStar (z * t) + b + v) y) := by
  classical
  unfold walshTransform
  calc
    (∑ w : FABL.F₂Cube (r + s),
        walshTerm (partialSpreadResilientFunction theta g phi a b)
          (Fin.append u v) w) =
      ∑ p : FABL.F₂Cube r × FABL.F₂Cube s,
        walshTerm (partialSpreadResilientFunction theta g phi a b)
          (Fin.append u v) (Fin.append p.1 p.2) := by
        exact (Fintype.sum_equiv (Fin.appendEquiv r s)
          (fun p ↦ walshTerm
            (partialSpreadResilientFunction theta g phi a b)
            (Fin.append u v) (Fin.append p.1 p.2))
          (fun w ↦ walshTerm
            (partialSpreadResilientFunction theta g phi a b)
            (Fin.append u v) w)
          (fun _ ↦ rfl)).symm
    _ = ∑ y : FABL.F₂Cube s, ∑ x : FABL.F₂Cube r,
        walshTerm (partialSpreadResilientFunction theta g phi a b)
          (Fin.append u v) (Fin.append x y) := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = ∑ y : FABL.F₂Cube s, ∑ t : BinaryGaloisField r,
        bitSignInt
          (g t + FABL.f₂DotProduct b y +
            absoluteTrace r (z * ((a + phi y) * t)) +
              FABL.f₂DotProduct v y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      let d : BinaryGaloisField r := a + phi y
      let e : BinaryGaloisField r ≃ BinaryGaloisField r :=
        (Equiv.mulRight₀ d (hdenom y)).symm
      apply Fintype.sum_equiv (theta.toEquiv.trans e)
      intro x
      simp only [walshTerm, partialSpreadResilientFunction_append,
        FABL.f₂DotProduct_append]
      change bitSignInt
          (g (theta x / d) + FABL.f₂DotProduct b y +
            (FABL.f₂DotProduct u x + FABL.f₂DotProduct v y)) =
        bitSignInt
          (g (e (theta x)) + FABL.f₂DotProduct b y +
            absoluteTrace r (z * (d * e (theta x))) +
              FABL.f₂DotProduct v y)
      simp only [e, Equiv.mulRight₀_symm_apply]
      rw [hz x]
      have hd : d * (theta x * d⁻¹) = theta x := by
        calc
          d * (theta x * d⁻¹) = theta x * (d * d⁻¹) := by ring
          _ = theta x := by rw [mul_inv_cancel₀ (hdenom y), mul_one]
      rw [hd]
      rw [div_eq_mul_inv]
      simp only [add_assoc]
    _ = ∑ t : BinaryGaloisField r, ∑ y : FABL.F₂Cube s,
        bitSignInt (g t + absoluteTrace r (z * a * t)) *
          bitSignInt
            (FABL.f₂DotProduct (phiStar (z * t) + b + v) y) := by
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro t _ht
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← bitSignInt_add]
      congr 1
      rw [show z * ((a + phi y) * t) =
          z * a * t + (z * t) * phi y by ring, map_add,
        ← hphiStar (z * t) y]
      simp only [FABL.f₂DotProduct, add_dotProduct]
      abel
    _ = ∑ t : BinaryGaloisField r,
        bitSignInt (g t + absoluteTrace r (z * a * t)) *
          ∑ y : FABL.F₂Cube s,
            bitSignInt
              (FABL.f₂DotProduct (phiStar (z * t) + b + v) y) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]

/-- Carlet Relation (63): if every adjoint translate lies outside the
weight-`k` ball, the partial-spread quotient construction is `k`-resilient.
The avoidance hypothesis itself implies `k < s`, so separate positivity
hypotheses on the parameters are unnecessary. -/
theorem isResilient_partialSpreadResilientFunction {r s k : ℕ}
    (theta : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (g : FieldBooleanFunction r)
    (phi : FABL.F₂Cube s →ₗ[FABL.𝔽₂] BinaryGaloisField r)
    (phiStar : BinaryGaloisField r →ₗ[FABL.𝔽₂] FABL.F₂Cube s)
    (hphiStar : ∀ z y,
      FABL.f₂DotProduct (phiStar z) y =
        absoluteTrace r (z * phi y))
    (a : BinaryGaloisField r) (b : FABL.F₂Cube s)
    (hdenom : ∀ y, a + phi y ≠ 0)
    (hweight : ∀ z,
      k < (FABL.f₂Support (phiStar z + b)).card) :
    IsResilient k (partialSpreadResilientFunction theta g phi a b) := by
  have hks : k < s := by
    have h := hweight 0
    apply h.trans_le
    calc
      (FABL.f₂Support (phiStar 0 + b)).card ≤
          (Finset.univ : Finset (Fin s)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = s := Fintype.card_fin s
  have hrs : 0 < r + s := by omega
  have hkrs : k < r + s := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    k (partialSpreadResilientFunction theta g phi a b) hrs hkrs]
  intro w hw
  let p := (Fin.appendEquiv r s).symm w
  have hp : Fin.append p.1 p.2 = w :=
    (Fin.appendEquiv r s).apply_symm_apply w
  obtain ⟨z, hz, _hzUnique⟩ :=
    existsUnique_tracePairingCoefficient theta p.1
  rw [← hp,
    walshTransform_partialSpreadResilientFunction_append
      theta g phi phiStar hphiStar a b hdenom p.1 p.2 z hz]
  apply Finset.sum_eq_zero
  intro t _ht
  rw [show (∑ y : FABL.F₂Cube s,
      bitSignInt
        (FABL.f₂DotProduct (phiStar (z * t) + b + p.2) y)) = 0 by
    apply sum_bitSignInt_dotProduct_eq_zero
    intro hzero
    have heq : phiStar (z * t) + b = p.2 := by
      have hpSelf : p.2 + p.2 = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero (p.2 i)
      calc
        phiStar (z * t) + b = phiStar (z * t) + b + 0 :=
          (add_zero _).symm
        _ = phiStar (z * t) + b + (p.2 + p.2) := by rw [hpSelf]
        _ = (phiStar (z * t) + b + p.2) + p.2 := by abel
        _ = 0 + p.2 := by rw [hzero]
        _ = p.2 := zero_add _
    have hpWeight : (FABL.f₂Support p.2).card ≤ k := by
      apply (Nat.le_add_left (FABL.f₂Support p.2).card _).trans
      rw [← card_f₂Support_append, hp]
      exact hw
    have hfar := hweight (z * t)
    rw [heq] at hfar
    omega, mul_zero]

end CryptBoolean
