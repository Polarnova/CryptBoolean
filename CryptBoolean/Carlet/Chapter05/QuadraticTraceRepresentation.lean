/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.TraceMonomialDegree
public import CryptBoolean.Carlet.Chapter02.TracePairing
public import CryptBoolean.Carlet.Chapter05.QuadraticNormalForm
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Finite.Extension

/-!
# Quadratic trace representations

Odd- and even-dimensional quadratic Boolean functions in finite-field coordinates.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The `i`th binary Frobenius power as a linear endomorphism. -/
noncomputable def binaryFrobeniusLinear (n i : ℕ) :
    BinaryGaloisField n →ₗ[FABL.𝔽₂] BinaryGaloisField n :=
  (FiniteField.frobeniusAlgHom FABL.𝔽₂ (BinaryGaloisField n) ^ i).toLinearMap

private noncomputable def binaryFrobeniusEquiv (n : ℕ) :
    BinaryGaloisField n ≃ₐ[FABL.𝔽₂] BinaryGaloisField n :=
  FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
    (BinaryGaloisField n)

/-- Evaluation of the linear Frobenius endomorphism is the corresponding
binary power. -/
theorem binaryFrobeniusLinear_apply (n i : ℕ)
    (x : BinaryGaloisField n) :
    binaryFrobeniusLinear n i x = x ^ (2 ^ i) := by
  change (FiniteField.frobeniusAlgHom FABL.𝔽₂
    (BinaryGaloisField n) ^ i) x = x ^ (2 ^ i)
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
  simp [ZMod.card]

private theorem absoluteTrace_frobeniusAlgEquiv_pow (n i : ℕ)
    (x : BinaryGaloisField n) :
    absoluteTrace n
        ((FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
          (BinaryGaloisField n) ^ i) x) =
      absoluteTrace n x := by
  simpa [absoluteTrace] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
        (BinaryGaloisField n) ^ i) x

private theorem binaryFrobeniusAlgEquiv_pow_complement_apply
    (n i : ℕ) (hn : n ≠ 0) (hi : i ≤ n)
    (x : BinaryGaloisField n) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
        (BinaryGaloisField n) ^ (n - i))
        ((FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
          (BinaryGaloisField n) ^ i) x) = x := by
  rw [← AlgEquiv.mul_apply, ← pow_add, Nat.sub_add_cancel hi]
  have hpow :
      (FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
        (BinaryGaloisField n)) ^ n = 1 := by
    letI : Fintype (BinaryGaloisField n) := Fintype.ofFinite _
    apply DFunLike.ext _ _
    intro y
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    change y ^ Fintype.card FABL.𝔽₂ ^ n = y
    rw [show Fintype.card FABL.𝔽₂ = 2 by exact ZMod.card 2]
    rw [← show Fintype.card (BinaryGaloisField n) = 2 ^ n by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn]]
    exact FiniteField.pow_card y
  rw [hpow]
  rfl

private theorem binaryFrobeniusLinear_eq_algEquiv_pow_apply (n i : ℕ)
    (x : BinaryGaloisField n) :
    binaryFrobeniusLinear n i x =
      (FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
        (BinaryGaloisField n) ^ i) x := by
  rw [binaryFrobeniusLinear_apply, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp [ZMod.card]

private theorem absoluteTrace_mul_binaryFrobeniusLinear
    (n i : ℕ) (hn : n ≠ 0) (hi : i ≤ n)
    (a y : BinaryGaloisField n) :
    absoluteTrace n (a * binaryFrobeniusLinear n i y) =
      absoluteTrace n
        ((FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
          (BinaryGaloisField n) ^ (n - i)) a * y) := by
  let E := FiniteField.frobeniusAlgEquivOfAlgebraic FABL.𝔽₂
    (BinaryGaloisField n)
  calc
    absoluteTrace n (a * binaryFrobeniusLinear n i y) =
        absoluteTrace n ((E ^ (n - i))
          (a * binaryFrobeniusLinear n i y)) := by
      rw [absoluteTrace_frobeniusAlgEquiv_pow]
    _ = absoluteTrace n ((E ^ (n - i)) a *
          (E ^ (n - i)) ((E ^ i) y)) := by
      rw [map_mul]
      rw [binaryFrobeniusLinear_eq_algEquiv_pow_apply]
    _ = absoluteTrace n ((E ^ (n - i)) a * y) := by
      rw [binaryFrobeniusAlgEquiv_pow_complement_apply n i hn hi]
    _ = _ := rfl

/-- The adjoint of the `i`th binary Frobenius power under the absolute-trace
pairing is the complementary Frobenius power. -/
theorem absoluteTrace_mul_frobeniusPow
    (n i : ℕ) (hn : n ≠ 0) (hi : i ≤ n)
    (a y : BinaryGaloisField n) :
    absoluteTrace n (a * y ^ (2 ^ i)) =
      absoluteTrace n (a ^ (2 ^ (n - i)) * y) := by
  rw [← binaryFrobeniusLinear_apply n i y,
    absoluteTrace_mul_binaryFrobeniusLinear n i hn hi]
  rw [← binaryFrobeniusLinear_eq_algEquiv_pow_apply n (n - i) a,
    binaryFrobeniusLinear_apply]

private noncomputable def alternatingMapOfBilinForm
    {V : Type*} [AddCommGroup V] [Module FABL.𝔽₂ V]
    (B : LinearMap.BilinForm FABL.𝔽₂ V) (hB : B.IsAlt) :
    V [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂ where
  toFun v := B (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;>
      simp [Function.update, LinearMap.BilinForm.add_right]
  map_update_smul' v i c x := by
    fin_cases i <;>
      simp [Function.update]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h01 : v 0 = v 1 := by simpa using hij
      rw [h01]
      exact hB.self_eq_zero (v 1)
    · have h10 : v 1 = v 0 := by simpa using hij
      rw [h10]
      exact hB.self_eq_zero (v 0)
    · exact (hne rfl).elim

private noncomputable def transportedQuadraticPolar {n : ℕ}
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    BinaryGaloisField n [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
  (alternatingMapOfBilinForm
    (quadraticPolar f hdegree) (quadraticPolar_isAlt f hdegree)).compLinearMap
      theta.symm.toLinearMap

@[simp] private theorem transportedQuadraticPolar_apply {n : ℕ}
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (x y : BinaryGaloisField n) :
    transportedQuadraticPolar theta f hdegree ![x, y] =
      quadraticPolar f hdegree (theta.symm x) (theta.symm y) := by
  rfl

private noncomputable def oddQuadraticPolarAlternating (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1)) :
    BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂ where
  toFun v := ∑ i, absoluteTrace (2 * m + 1)
    (beta i *
      (binaryFrobeniusLinear (2 * m + 1) (i + 1) (v 0) * v 1 +
        v 0 * binaryFrobeniusLinear (2 * m + 1) (i + 1) (v 1)))
  map_update_add' v j x y := by
    fin_cases j <;>
      simp [Function.update, map_add, add_mul, mul_add,
        Finset.sum_add_distrib] <;> ring
  map_update_smul' v j c x := by
    fin_cases j <;>
      simp [Function.update, map_smul, ← smul_add, Finset.mul_sum]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h01 : v 0 = v 1 := by simpa using hij
      simp [h01, mul_comm, ZModModule.add_self]
    · have h10 : v 1 = v 0 := by simpa using hij
      simp [h10, mul_comm, ZModModule.add_self]
    · exact (hne rfl).elim

@[simp] private theorem oddQuadraticPolarAlternating_apply (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1))
    (x y : BinaryGaloisField (2 * m + 1)) :
    oddQuadraticPolarAlternating m beta ![x, y] =
      ∑ i, absoluteTrace (2 * m + 1)
        (beta i *
          (binaryFrobeniusLinear (2 * m + 1) (i + 1) x * y +
            x * binaryFrobeniusLinear (2 * m + 1) (i + 1) y)) := by
  rfl

/-- The homogeneous quadratic part in Carlet's odd-dimensional trace
representation. -/
noncomputable def oddQuadraticTracePart (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1)) :
    FieldBooleanFunction (2 * m + 1) :=
  fun x ↦ absoluteTrace (2 * m + 1)
    (∑ i, beta i * (binaryFrobeniusLinear (2 * m + 1) (i + 1) x * x))

private theorem oddQuadraticTracePart_polar (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1))
    (x y : BinaryGaloisField (2 * m + 1)) :
    oddQuadraticTracePart m beta (x + y) +
        oddQuadraticTracePart m beta x +
        oddQuadraticTracePart m beta y +
        oddQuadraticTracePart m beta 0 =
      oddQuadraticPolarAlternating m beta ![x, y] := by
  rw [oddQuadraticPolarAlternating_apply]
  simp only [oddQuadraticTracePart, map_add, map_zero, mul_zero,
    Finset.sum_const_zero]
  rw [map_sum, map_sum, map_sum]
  rw [add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← map_add, ← map_add]
  congr 1
  simp [add_mul, mul_add]
  ring_nf
  rw [show (2 : BinaryGaloisField (2 * m + 1)) = 0 from
    CharP.cast_eq_zero (BinaryGaloisField (2 * m + 1)) 2]
  simp

/-- The polar form of the odd-dimensional quadratic trace part, written as
the explicit sum of paired Frobenius monomials. -/
theorem oddQuadraticTracePart_polar_eq_sum (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1))
    (x y : BinaryGaloisField (2 * m + 1)) :
    oddQuadraticTracePart m beta (x + y) +
        oddQuadraticTracePart m beta x +
        oddQuadraticTracePart m beta y +
        oddQuadraticTracePart m beta 0 =
      ∑ i, absoluteTrace (2 * m + 1)
        (beta i *
          (x ^ (2 ^ ((i : ℕ) + 1)) * y +
            x * y ^ (2 ^ ((i : ℕ) + 1)))) := by
  rw [oddQuadraticTracePart_polar,
    oddQuadraticPolarAlternating_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [binaryFrobeniusLinear_apply, binaryFrobeniusLinear_apply]

private noncomputable def oddQuadraticPolarMap (m : ℕ) :
    (Fin m → BinaryGaloisField (2 * m + 1)) →ₗ[FABL.𝔽₂]
      (BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) where
  toFun := oddQuadraticPolarAlternating m
  map_add' beta gamma := by
    ext v
    simp [oddQuadraticPolarAlternating, add_mul, Finset.sum_add_distrib]
  map_smul' c beta := by
    ext v
    simp [oddQuadraticPolarAlternating, map_smul, Finset.mul_sum]

private noncomputable def oddPolarLinearized (m : ℕ)
    (beta : Fin m → BinaryGaloisField (2 * m + 1)) :
    BinaryGaloisField (2 * m + 1) →ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * m + 1) :=
  ∑ i, (beta i • binaryFrobeniusLinear (2 * m + 1) (i + 1) +
    (((binaryFrobeniusEquiv (2 * m + 1)) ^
        ((2 * m + 1) - (i + 1))) (beta i)) •
      binaryFrobeniusLinear (2 * m + 1) ((2 * m + 1) - (i + 1)))

private def oddPolarFrobeniusIndex (m : ℕ) :
    Fin m ⊕ Fin m → Fin (2 * m + 1)
  | Sum.inl i => ⟨i + 1, by omega⟩
  | Sum.inr i => ⟨(2 * m + 1) - (i + 1), by omega⟩

private theorem oddPolarFrobeniusIndex_injective (m : ℕ) :
    Function.Injective (oddPolarFrobeniusIndex m) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [oddPolarFrobeniusIndex, Fin.mk.injEq] at hij
          congr 1
          omega
      | inr j =>
          simp only [oddPolarFrobeniusIndex, Fin.mk.injEq] at hij
          have hi := i.isLt
          have hj := j.isLt
          omega
  | inr i =>
      cases j with
      | inl j =>
          simp only [oddPolarFrobeniusIndex, Fin.mk.injEq] at hij
          have hi := i.isLt
          have hj := j.isLt
          omega
      | inr j =>
          simp only [oddPolarFrobeniusIndex, Fin.mk.injEq] at hij
          congr 1
          omega

private theorem binaryFrobeniusLinear_linearIndependent (n : ℕ) (hn : n ≠ 0) :
    LinearIndependent (BinaryGaloisField n)
      (fun i : Fin n ↦ binaryFrobeniusLinear n i) := by
  have hLI := (linearIndependent_algHom_toLinearMap FABL.𝔽₂
    (BinaryGaloisField n) (BinaryGaloisField n)).comp _
      (FiniteField.bijective_frobeniusAlgHom_pow FABL.𝔽₂
        (BinaryGaloisField n)).1
  rw [GaloisField.finrank 2 hn] at hLI
  exact hLI

private theorem oddPolarLinearized_injective (m : ℕ) :
    Function.Injective (oddPolarLinearized m) := by
  intro beta gamma h
  let coeff : Fin m ⊕ Fin m → BinaryGaloisField (2 * m + 1)
    | Sum.inl i => beta i - gamma i
    | Sum.inr i =>
        ((binaryFrobeniusEquiv (2 * m + 1)) ^
          ((2 * m + 1) - (i + 1))) (beta i) -
        ((binaryFrobeniusEquiv (2 * m + 1)) ^
          ((2 * m + 1) - (i + 1))) (gamma i)
  have hLI : LinearIndependent (BinaryGaloisField (2 * m + 1))
      (fun s : Fin m ⊕ Fin m ↦
        binaryFrobeniusLinear (2 * m + 1) (oddPolarFrobeniusIndex m s)) :=
    (binaryFrobeniusLinear_linearIndependent (2 * m + 1) (by omega)).comp _
      (oddPolarFrobeniusIndex_injective m)
  have hzero : ∑ s, coeff s •
      binaryFrobeniusLinear (2 * m + 1) (oddPolarFrobeniusIndex m s) = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [coeff, oddPolarFrobeniusIndex]
    rw [show (∑ i : Fin m, (beta i - gamma i) •
          binaryFrobeniusLinear (2 * m + 1) (i + 1)) =
        (∑ i : Fin m, beta i • binaryFrobeniusLinear (2 * m + 1) (i + 1)) -
          ∑ i : Fin m, gamma i • binaryFrobeniusLinear (2 * m + 1) (i + 1) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      exact sub_smul (beta i) (gamma i)
        (binaryFrobeniusLinear (2 * m + 1) (i + 1))]
    rw [show (∑ i : Fin m,
          (((binaryFrobeniusEquiv (2 * m + 1)) ^
                ((2 * m + 1) - (i + 1))) (beta i) -
            ((binaryFrobeniusEquiv (2 * m + 1)) ^
                ((2 * m + 1) - (i + 1))) (gamma i)) •
            binaryFrobeniusLinear (2 * m + 1) ((2 * m + 1) - (i + 1))) =
        (∑ i : Fin m, ((binaryFrobeniusEquiv (2 * m + 1)) ^
                ((2 * m + 1) - (i + 1))) (beta i) •
            binaryFrobeniusLinear (2 * m + 1) ((2 * m + 1) - (i + 1))) -
          ∑ i : Fin m, ((binaryFrobeniusEquiv (2 * m + 1)) ^
                ((2 * m + 1) - (i + 1))) (gamma i) •
            binaryFrobeniusLinear (2 * m + 1) ((2 * m + 1) - (i + 1)) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      exact sub_smul
        (((binaryFrobeniusEquiv (2 * m + 1)) ^
          ((2 * m + 1) - (i + 1))) (beta i))
        (((binaryFrobeniusEquiv (2 * m + 1)) ^
          ((2 * m + 1) - (i + 1))) (gamma i))
        (binaryFrobeniusLinear (2 * m + 1) ((2 * m + 1) - (i + 1)))]
    have hdiff : oddPolarLinearized m beta - oddPolarLinearized m gamma = 0 :=
      sub_eq_zero.mpr h
    rw [oddPolarLinearized, oddPolarLinearized, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at hdiff
    rw [← hdiff]
    abel
  apply funext
  intro i
  have hi := Fintype.linearIndependent_iff.mp hLI coeff hzero (Sum.inl i)
  exact sub_eq_zero.mp hi

private theorem oddQuadraticPolarAlternating_eq_trace_linearized_mul
    (m : ℕ) (beta : Fin m → BinaryGaloisField (2 * m + 1))
    (x y : BinaryGaloisField (2 * m + 1)) :
    oddQuadraticPolarAlternating m beta ![x, y] =
      absoluteTrace (2 * m + 1) (oddPolarLinearized m beta x * y) := by
  rw [oddQuadraticPolarAlternating_apply]
  rw [show oddPolarLinearized m beta x =
      ∑ i, (beta i * binaryFrobeniusLinear (2 * m + 1) (i + 1) x +
        ((binaryFrobeniusEquiv (2 * m + 1)) ^
            ((2 * m + 1) - (i + 1))) (beta i) *
          binaryFrobeniusLinear (2 * m + 1)
            ((2 * m + 1) - (i + 1)) x) by
    simp [oddPolarLinearized, LinearMap.sum_apply, smul_eq_mul]]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  let E := binaryFrobeniusEquiv (2 * m + 1)
  let Fi := binaryFrobeniusLinear (2 * m + 1) (i + 1)
  let Fj := binaryFrobeniusLinear (2 * m + 1)
    ((2 * m + 1) - (i + 1))
  have hadjoint : absoluteTrace (2 * m + 1)
      (beta i * (x * Fi y)) =
      absoluteTrace (2 * m + 1)
        (((E ^ ((2 * m + 1) - (i + 1))) (beta i) * Fj x) * y) := by
    calc
      absoluteTrace (2 * m + 1) (beta i * (x * Fi y)) =
          absoluteTrace (2 * m + 1) ((beta i * x) * Fi y) := by
        rw [mul_assoc]
      _ = absoluteTrace (2 * m + 1)
          ((E ^ ((2 * m + 1) - (i + 1))) (beta i * x) * y) := by
        apply absoluteTrace_mul_binaryFrobeniusLinear
        · omega
        · omega
      _ = absoluteTrace (2 * m + 1)
          (((E ^ ((2 * m + 1) - (i + 1))) (beta i) * Fj x) * y) := by
        have hFj : Fj x =
            (E ^ ((2 * m + 1) - (i + 1))) x := by
          simpa [E, Fj, binaryFrobeniusEquiv] using
            binaryFrobeniusLinear_eq_algEquiv_pow_apply
              (2 * m + 1) ((2 * m + 1) - (i + 1)) x
        apply congrArg (fun z : BinaryGaloisField (2 * m + 1) ↦
          absoluteTrace (2 * m + 1) (z * y))
        calc
          (E ^ ((2 * m + 1) - (i + 1))) (beta i * x) =
              (E ^ ((2 * m + 1) - (i + 1))) (beta i) *
                (E ^ ((2 * m + 1) - (i + 1))) x :=
            (E ^ ((2 * m + 1) - (i + 1))).map_mul (beta i) x
          _ = (E ^ ((2 * m + 1) - (i + 1))) (beta i) * Fj x := by
            rw [hFj]
  calc
    absoluteTrace (2 * m + 1)
        (beta i * (Fi x * y + x * Fi y)) =
      absoluteTrace (2 * m + 1) (beta i * (Fi x * y)) +
        absoluteTrace (2 * m + 1) (beta i * (x * Fi y)) := by
      rw [mul_add, map_add]
    _ = absoluteTrace (2 * m + 1) (beta i * (Fi x * y)) +
        absoluteTrace (2 * m + 1)
          (((E ^ ((2 * m + 1) - (i + 1))) (beta i) * Fj x) * y) := by
      rw [hadjoint]
    _ = absoluteTrace (2 * m + 1)
        ((beta i * Fi x +
          (E ^ ((2 * m + 1) - (i + 1))) (beta i) * Fj x) * y) := by
      rw [add_mul, map_add]
      congr 1
      rw [mul_assoc]

private theorem oddQuadraticPolarMap_injective (m : ℕ) :
    Function.Injective (oddQuadraticPolarMap m) := by
  letI : Fintype (BinaryGaloisField (2 * m + 1)) := Fintype.ofFinite _
  letI : Algebra.IsAlgebraic FABL.𝔽₂
      (BinaryGaloisField (2 * m + 1)) := Algebra.IsIntegral.isAlgebraic
  letI : Algebra.IsSeparable FABL.𝔽₂
      (BinaryGaloisField (2 * m + 1)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  intro beta gamma hpolar
  apply oddPolarLinearized_injective m
  ext x
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate FABL.𝔽₂
    (BinaryGaloisField (2 * m + 1))).1
  intro y
  rw [Algebra.traceForm_apply]
  change absoluteTrace (2 * m + 1)
    ((oddPolarLinearized m beta x - oddPolarLinearized m gamma x) * y) = 0
  rw [sub_mul, map_sub, sub_eq_zero]
  calc
    absoluteTrace (2 * m + 1) (oddPolarLinearized m beta x * y) =
        oddQuadraticPolarAlternating m beta ![x, y] :=
      (oddQuadraticPolarAlternating_eq_trace_linearized_mul m beta x y).symm
    _ = oddQuadraticPolarAlternating m gamma ![x, y] := by
      exact congrArg (fun A ↦ A ![x, y]) hpolar
    _ = absoluteTrace (2 * m + 1) (oddPolarLinearized m gamma x * y) :=
      oddQuadraticPolarAlternating_eq_trace_linearized_mul m gamma x y

private theorem oddQuadraticPolarMap_finrank_eq (m : ℕ) :
    Module.finrank FABL.𝔽₂
        (Fin m → BinaryGaloisField (2 * m + 1)) =
      Module.finrank FABL.𝔽₂
        (BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) := by
  have hn : 2 * m + 1 ≠ 0 := by omega
  rw [Module.finrank_pi_fintype]
  simp only [GaloisField.finrank 2 hn, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    m * (2 * m + 1) = Nat.choose (2 * m + 1) 2 := by
      rw [Nat.choose_two_right]
      rw [show 2 * m + 1 - 1 = 2 * m by omega]
      rw [show (2 * m + 1) * (2 * m) =
        2 * (m * (2 * m + 1)) by ring]
      rw [Nat.mul_div_cancel_left _ zero_lt_two]
    _ = Module.finrank FABL.𝔽₂
        (BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) := by
      symm
      calc
        Module.finrank FABL.𝔽₂
            (BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) =
          Module.finrank FABL.𝔽₂
            ((⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m + 1))) →ₗ[FABL.𝔽₂]
              FABL.𝔽₂) :=
          exteriorPower.alternatingMapLinearEquiv.finrank_eq
        _ = Module.finrank FABL.𝔽₂
            (⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m + 1))) := by
          exact Module.finrank_linearMap_self FABL.𝔽₂ FABL.𝔽₂
            (⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m + 1)))
        _ = Nat.choose
            (Module.finrank FABL.𝔽₂ (BinaryGaloisField (2 * m + 1))) 2 :=
          exteriorPower.finrank_eq FABL.𝔽₂ 2
        _ = Nat.choose (2 * m + 1) 2 := by
          rw [GaloisField.finrank 2 hn]

private theorem oddQuadraticPolarMap_surjective (m : ℕ) :
    Function.Surjective (oddQuadraticPolarMap m) := by
  letI : FiniteDimensional FABL.𝔽₂
      (BinaryGaloisField (2 * m + 1) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) :=
    exteriorPower.alternatingMapLinearEquiv.symm.finiteDimensional
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (oddQuadraticPolarMap_finrank_eq m)).mp
      (oddQuadraticPolarMap_injective m)

private theorem exists_oddQuadraticTracePart_polar_eq (m : ℕ)
    (theta : FABL.F₂Cube (2 * m + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * m + 1))
    (f : BooleanFunction (2 * m + 1))
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ beta : Fin m → BinaryGaloisField (2 * m + 1),
      ∀ x y, quadraticPolarKernel
          (fun u ↦ oddQuadraticTracePart m beta (theta u)) x y =
        quadraticPolarKernel f x y := by
  obtain ⟨beta, hbeta⟩ :=
    oddQuadraticPolarMap_surjective m
      (transportedQuadraticPolar theta f hdegree)
  refine ⟨beta, ?_⟩
  intro x y
  have hvalue := congrArg
    (fun A ↦ A ![theta x, theta y]) hbeta
  rw [oddQuadraticPolarMap, transportedQuadraticPolar_apply] at hvalue
  simp only [theta.symm_apply_apply] at hvalue
  rw [quadraticPolar_apply] at hvalue
  rw [quadraticPolarKernel_eq]
  change oddQuadraticTracePart m beta (theta (x + y)) +
      oddQuadraticTracePart m beta (theta x) +
      oddQuadraticTracePart m beta (theta y) +
      oddQuadraticTracePart m beta (theta 0) = _
  rw [theta.map_add, theta.map_zero, oddQuadraticTracePart_polar]
  exact hvalue

private theorem absoluteTrace_mul_eq_frobeniusLinear_mul_self
    (n : ℕ) (a x : BinaryGaloisField n) :
    absoluteTrace n (a * x) =
      absoluteTrace n
        (binaryFrobeniusLinear n 1 a * (x * x)) := by
  calc
    absoluteTrace n (a * x) =
        absoluteTrace n ((binaryFrobeniusEquiv n) (a * x)) := by
      simpa [binaryFrobeniusEquiv] using
        (absoluteTrace_frobeniusAlgEquiv_pow n 1 (a * x)).symm
    _ = absoluteTrace n
        (binaryFrobeniusLinear n 1 a *
          binaryFrobeniusLinear n 1 x) := by
      have ha : binaryFrobeniusLinear n 1 a = binaryFrobeniusEquiv n a := by
        simpa [binaryFrobeniusEquiv] using
          binaryFrobeniusLinear_eq_algEquiv_pow_apply n 1 a
      have hx : binaryFrobeniusLinear n 1 x = binaryFrobeniusEquiv n x := by
        simpa [binaryFrobeniusEquiv] using
          binaryFrobeniusLinear_eq_algEquiv_pow_apply n 1 x
      apply congrArg (absoluteTrace n)
      calc
        binaryFrobeniusEquiv n (a * x) =
            binaryFrobeniusEquiv n a * binaryFrobeniusEquiv n x :=
          (binaryFrobeniusEquiv n).map_mul a x
        _ = binaryFrobeniusLinear n 1 a *
            binaryFrobeniusLinear n 1 x := by rw [ha, hx]
    _ = absoluteTrace n
        (binaryFrobeniusLinear n 1 a * (x * x)) := by
      simp [binaryFrobeniusLinear_apply, pow_two]

private noncomputable def oddQuadraticTraceRepresentation (m : ℕ)
    (betaEmpty : BinaryGaloisField (2 * m + 1))
    (beta : Fin (m + 1) → BinaryGaloisField (2 * m + 1)) :
    FieldBooleanFunction (2 * m + 1) :=
  fun x ↦ absoluteTrace (2 * m + 1)
    (betaEmpty + ∑ i,
      beta i * (binaryFrobeniusLinear (2 * m + 1) i x * x))

private theorem oddQuadraticTraceRepresentation_eq_power_sum (m : ℕ)
    (betaEmpty : BinaryGaloisField (2 * m + 1))
    (beta : Fin (m + 1) → BinaryGaloisField (2 * m + 1))
    (x : BinaryGaloisField (2 * m + 1)) :
    oddQuadraticTraceRepresentation m betaEmpty beta x =
      absoluteTrace (2 * m + 1)
        (betaEmpty + ∑ i, beta i * x ^ (2 ^ (i : ℕ) + 1)) := by
  simp [oddQuadraticTraceRepresentation, binaryFrobeniusLinear_apply,
    pow_succ]

private theorem exists_oddQuadraticTraceRepresentation_of_degree_le (m : ℕ)
    (theta : FABL.F₂Cube (2 * m + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * m + 1))
    (f : BooleanFunction (2 * m + 1))
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ betaEmpty : BinaryGaloisField (2 * m + 1),
      ∃ beta : Fin (m + 1) → BinaryGaloisField (2 * m + 1),
        ∀ u, f u = oddQuadraticTraceRepresentation m betaEmpty beta (theta u) := by
  obtain ⟨quadraticBeta, hpolar⟩ :=
    exists_oddQuadraticTracePart_polar_eq m theta f hdegree
  let q : BooleanFunction (2 * m + 1) :=
    fun u ↦ oddQuadraticTracePart m quadraticBeta (theta u)
  let h : BooleanFunction (2 * m + 1) := fun u ↦ f u + q u
  have hzero : ∀ x y, quadraticPolarKernel h x y = 0 := by
    intro x y
    calc
      quadraticPolarKernel h x y =
          quadraticPolarKernel f x y + quadraticPolarKernel q x y := by
        simp only [quadraticPolarKernel_eq, h]
        abel
      _ = quadraticPolarKernel f x y + quadraticPolarKernel f x y := by
        rw [hpolar x y]
      _ = 0 := ZModModule.add_self _
  obtain ⟨c, a, haffine⟩ :=
    exists_affineFunction_of_quadraticPolarKernel_eq_zero h hzero
  obtain ⟨linearBeta, hlinear, _hlinearUnique⟩ :=
    existsUnique_tracePairingCoefficient theta a
  obtain ⟨traceOne, htraceOne⟩ :=
    exists_absoluteTrace_eq_one (2 * m + 1)
  let betaEmpty : BinaryGaloisField (2 * m + 1) := c • traceOne
  let beta : Fin (m + 1) → BinaryGaloisField (2 * m + 1) :=
    Fin.cases (binaryFrobeniusLinear (2 * m + 1) 1 linearBeta) quadraticBeta
  refine ⟨betaEmpty, beta, ?_⟩
  intro u
  have hu := congrFun haffine u
  have hf : f u = FABL.affineFunction c a u + q u := by
    calc
      f u = (f u + q u) + q u := by
        rw [add_assoc, ZModModule.add_self, add_zero]
      _ = FABL.affineFunction c a u + q u := by
        rw [← hu]
  rw [hf]
  rw [show FABL.affineFunction c a u =
      c + absoluteTrace (2 * m + 1) (linearBeta * theta u) by
    rw [FABL.affineFunction, hlinear u]]
  rw [absoluteTrace_mul_eq_frobeniusLinear_mul_self]
  change c + absoluteTrace (2 * m + 1)
      (binaryFrobeniusLinear (2 * m + 1) 1 linearBeta *
        (theta u * theta u)) +
      oddQuadraticTracePart m quadraticBeta (theta u) =
    oddQuadraticTraceRepresentation m betaEmpty beta (theta u)
  rw [oddQuadraticTraceRepresentation]
  rw [Fin.sum_univ_succ]
  simp only [beta, Fin.cases_zero, Fin.cases_succ]
  rw [map_add, map_add]
  rw [show absoluteTrace (2 * m + 1) betaEmpty = c by
    simp [betaEmpty, htraceOne]]
  simp [oddQuadraticTracePart, binaryFrobeniusLinear_apply, add_assoc]

private theorem binaryWeight_two_pow_add_one_le_two (i : ℕ) :
    binaryWeight (2 ^ i + 1) ≤ 2 := by
  cases i with
  | zero => decide
  | succ i =>
      rw [show 2 ^ (i + 1) + 1 = 2 * 2 ^ i + 1 by
        rw [pow_succ']]
      simp [binaryWeight]

private theorem functionAlgebraicDegree_constant_le_two {n : ℕ} (c : FABL.𝔽₂) :
    FABL.functionAlgebraicDegree (fun _ : FABL.F₂Cube n ↦ c) ≤ 2 := by
  by_cases hc : c = 0
  · have hconstant : (fun _ : FABL.F₂Cube n ↦ c) = 0 := by
      funext x
      simp [hc]
    rw [hconstant]
    simp
  · have hcOne : c = 1 := Fin.eq_one_of_ne_zero c hc
    have hconstant : (fun _ : FABL.F₂Cube n ↦ c) = 1 := by
      funext x
      simp [hcOne]
    rw [hconstant]
    simp

/-- A binary trace monomial with exponent `2^i + 1` has algebraic degree at
most two whenever the exponent lies below the field modulus. -/
theorem functionAlgebraicDegree_traceMonomial_two_pow_add_one_le_two
    {n i : ℕ} (hn : 0 < n) (hk : 2 ^ i + 1 < 2 ^ n - 1)
    (theta : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) :
    FABL.functionAlgebraicDegree
        (fun x ↦ absoluteTrace n (a * (theta x) ^ (2 ^ i + 1))) ≤ 2 := by
  by_cases hzero : (fun x : FABL.F₂Cube n ↦
      absoluteTrace n (a * (theta x) ^ (2 ^ i + 1))) = 0
  · rw [hzero]
    simp
  · rw [functionAlgebraicDegree_traceMonomial hn hk theta a hzero]
    exact binaryWeight_two_pow_add_one_le_two i

/-- The quadratic exponents in the odd-dimensional trace representation lie
strictly below the multiplicative field modulus. -/
theorem two_pow_add_one_lt_odd_modulus
    (m : ℕ) (hm : 0 < m) (i : Fin (m + 1)) :
    2 ^ (i : ℕ) + 1 < 2 ^ (2 * m + 1) - 1 := by
  have hi : (i : ℕ) ≤ m := Nat.le_of_lt_succ i.isLt
  have hipow : 2 ^ (i : ℕ) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by omega) hi
  have hfour : 4 ≤ 2 ^ (m + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2)
      (show 2 ≤ m + 1 by omega)
  have hmPow : 1 < 2 ^ m := Nat.one_lt_two_pow hm.ne'
  rw [show 2 * m + 1 = m + (m + 1) by omega, pow_add]
  have hmul : 2 ^ m * 4 ≤ 2 ^ m * 2 ^ (m + 1) :=
    Nat.mul_le_mul_left _ hfour
  omega

/-- Carlet's finite-field trace representation of odd-dimensional quadratic Boolean functions. -/
theorem functionAlgebraicDegree_le_two_iff_exists_odd_quadraticTraceRepresentation
    (m : ℕ)
    (theta : FABL.F₂Cube (2 * m + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * m + 1))
    (f : BooleanFunction (2 * m + 1)) :
    FABL.functionAlgebraicDegree f ≤ 2 ↔
      ∃ betaEmpty : BinaryGaloisField (2 * m + 1),
        ∃ beta : Fin (m + 1) → BinaryGaloisField (2 * m + 1),
          ∀ x, f x = absoluteTrace (2 * m + 1)
            (betaEmpty + ∑ i, beta i * (theta x) ^ (2 ^ (i : ℕ) + 1)) := by
  constructor
  · intro hdegree
    obtain ⟨betaEmpty, beta, hrepresentation⟩ :=
      exists_oddQuadraticTraceRepresentation_of_degree_le m theta f hdegree
    refine ⟨betaEmpty, beta, ?_⟩
    intro x
    rw [hrepresentation x,
      oddQuadraticTraceRepresentation_eq_power_sum]
  · rintro ⟨betaEmpty, beta, hrepresentation⟩
    by_cases hm : m = 0
    · subst m
      exact (FABL.functionAlgebraicDegree_le_dimension f).trans (by omega)
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let constant : BooleanFunction (2 * m + 1) :=
        fun _ ↦ absoluteTrace (2 * m + 1) betaEmpty
      let term (i : Fin (m + 1)) : BooleanFunction (2 * m + 1) :=
        fun x ↦ absoluteTrace (2 * m + 1)
          (beta i * (theta x) ^ (2 ^ (i : ℕ) + 1))
      have hdecomposition : f = constant + ∑ i, term i := by
        funext x
        rw [hrepresentation x, map_add, map_sum]
        simp only [Pi.add_apply, Finset.sum_apply, constant, term]
      rw [hdecomposition]
      apply (FABL.functionAlgebraicDegree_add_le_max constant
        (∑ i, term i)).trans
      apply max_le
      · simpa [constant] using
          functionAlgebraicDegree_constant_le_two
            (n := 2 * m + 1) (absoluteTrace (2 * m + 1) betaEmpty)
      · apply FABL.functionAlgebraicDegree_finset_sum_le Finset.univ term 2
        intro i _hi
        exact functionAlgebraicDegree_traceMonomial_two_pow_add_one_le_two
          (by omega : 0 < 2 * m + 1)
          (two_pow_add_one_lt_odd_modulus m hmpos i) theta (beta i)

variable {m : ℕ}

/-- The relative norm determined by an explicitly supplied copy of `GF(2^m)` inside
`GF(2^(2m))`. -/
noncomputable def quadraticTraceMiddleNorm
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) : BinaryGaloisField m := by
  letI := iota.toAlgebra
  exact Algebra.norm (BinaryGaloisField m) x

/-- The explicitly embedded middle field has relative degree two in the
quadratic binary extension. -/
theorem quadraticTraceMiddle_finrank (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    letI := iota.toAlgebra
    Module.finrank (BinaryGaloisField m) (BinaryGaloisField (2 * m)) = 2 := by
  letI := iota.toAlgebra
  letI : IsScalarTower FABL.𝔽₂ (BinaryGaloisField m) (BinaryGaloisField (2 * m)) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have h := Module.finrank_mul_finrank FABL.𝔽₂
    (BinaryGaloisField m) (BinaryGaloisField (2 * m))
  rw [GaloisField.finrank 2 hm,
    GaloisField.finrank 2 (mul_ne_zero (by omega) hm)] at h
  have h' : m * Module.finrank (BinaryGaloisField m) (BinaryGaloisField (2 * m)) =
      m * 2 := by simpa [Nat.mul_comm] using h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h'

/-- Re-embedding the relative norm gives the middle Frobenius monomial. -/
theorem quadraticTraceMiddleNorm_map_eq_pow (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) :
    iota (quadraticTraceMiddleNorm iota x) = x ^ (2 ^ m + 1) := by
  letI := iota.toAlgebra
  change algebraMap (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (Algebra.norm (BinaryGaloisField m) x) = x ^ (2 ^ m + 1)
  rw [FiniteField.algebraMap_norm_eq_pow_sum,
    quadraticTraceMiddle_finrank hm iota, GaloisField.card 2 m hm]
  simp [Nat.add_comm]

private theorem quadraticTraceMiddleNorm_polar_map (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (x y : BinaryGaloisField (2 * m)) :
    iota (quadraticTraceMiddleNorm iota (x + y) +
        quadraticTraceMiddleNorm iota x + quadraticTraceMiddleNorm iota y) =
      x ^ (2 ^ m) * y + x * y ^ (2 ^ m) := by
  rw [map_add, map_add, quadraticTraceMiddleNorm_map_eq_pow hm,
    quadraticTraceMiddleNorm_map_eq_pow hm, quadraticTraceMiddleNorm_map_eq_pow hm]
  rw [show (x + y) ^ (2 ^ m + 1) = (x + y) ^ (2 ^ m) * (x + y) by
    rw [pow_add, pow_one]]
  rw [add_pow_char_pow x y 2 m]
  ring_nf
  have htwo : (2 : BinaryGaloisField (2 * m)) = 0 := by
    change ((2 : ℕ) : BinaryGaloisField (2 * m)) = 0
    exact CharP.cast_eq_zero (BinaryGaloisField (2 * m)) 2
  simp only [htwo, mul_zero, add_zero, zero_add]

private theorem quadraticTraceMiddle_trace_frobenius_mul_map
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (x y : BinaryGaloisField (2 * m)) :
    letI := iota.toAlgebra
    iota (Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
        (x ^ (2 ^ m) * y)) =
      x ^ (2 ^ m) * y + x * y ^ (2 ^ m) := by
  letI := iota.toAlgebra
  change algebraMap (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
        (x ^ (2 ^ m) * y)) = _
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    quadraticTraceMiddle_finrank hm iota, GaloisField.card 2 m hm]
  simp only [sum_range_succ, sum_range_zero, pow_zero, zero_add, pow_one]
  rw [mul_pow]
  have hx : (x ^ (2 ^ m)) ^ (2 ^ m) = x := by
    rw [← pow_mul, ← pow_add]
    have hcard : x ^ (2 ^ (2 * m)) = x := by
      letI := Fintype.ofFinite (BinaryGaloisField (2 * m))
      have h := FiniteField.pow_card x
      rw [Fintype.card_eq_nat_card,
        GaloisField.card 2 (2 * m) (mul_ne_zero (by omega) hm)] at h
      exact h
    simpa [two_mul] using hcard
  rw [hx]

private theorem quadraticTraceMiddleNorm_polar_eq_trace
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (x y : BinaryGaloisField (2 * m)) :
    letI := iota.toAlgebra
    quadraticTraceMiddleNorm iota (x + y) + quadraticTraceMiddleNorm iota x +
        quadraticTraceMiddleNorm iota y =
      Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
        (x ^ (2 ^ m) * y) := by
  letI := iota.toAlgebra
  apply iota.injective
  exact (quadraticTraceMiddleNorm_polar_map hm iota x y).trans
    (quadraticTraceMiddle_trace_frobenius_mul_map hm iota x y).symm

private noncomputable def quadraticTraceMiddleTerm
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (gamma : BinaryGaloisField m) (x : BinaryGaloisField (2 * m)) : FABL.𝔽₂ :=
  absoluteTrace m (gamma * quadraticTraceMiddleNorm iota x)

private theorem quadraticTraceMiddleTerm_polar
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (gamma : BinaryGaloisField m) (x y : BinaryGaloisField (2 * m)) :
    quadraticTraceMiddleTerm iota gamma (x + y) +
        quadraticTraceMiddleTerm iota gamma x + quadraticTraceMiddleTerm iota gamma y =
      absoluteTrace (2 * m) (iota gamma * x ^ (2 ^ m) * y) := by
  letI := iota.toAlgebra
  letI : IsScalarTower FABL.𝔽₂ (BinaryGaloisField m) (BinaryGaloisField (2 * m)) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  unfold quadraticTraceMiddleTerm
  rw [← map_add, ← map_add]
  rw [← mul_add, ← mul_add, quadraticTraceMiddleNorm_polar_eq_trace hm iota]
  change Algebra.trace FABL.𝔽₂ (BinaryGaloisField m)
      (gamma * Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
        (x ^ (2 ^ m) * y)) =
    Algebra.trace FABL.𝔽₂ (BinaryGaloisField (2 * m))
      (iota gamma * x ^ (2 ^ m) * y)
  rw [← Algebra.trace_trace (R := FABL.𝔽₂) (S := BinaryGaloisField m)
    (T := BinaryGaloisField (2 * m))]
  congr 1
  rw [mul_assoc (iota gamma) (x ^ (2 ^ m)) y]
  change gamma * Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (x ^ (2 ^ m) * y) =
    Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (gamma • (x ^ (2 ^ m) * y))
  rw [map_smul]
  rfl

private noncomputable def evenQuadraticPolarAlternating
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m) :
    BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂ where
  toFun v :=
    (∑ i, absoluteTrace (2 * m)
      (p.1 i *
        (binaryFrobeniusLinear (2 * m) (i + 1) (v 0) * v 1 +
          v 0 * binaryFrobeniusLinear (2 * m) (i + 1) (v 1)))) +
    absoluteTrace (2 * m)
      (iota p.2 * binaryFrobeniusLinear (2 * m) m (v 0) * v 1)
  map_update_add' v j x y := by
    fin_cases j <;>
      simp [Function.update, map_add, add_mul, mul_add,
        Finset.sum_add_distrib] <;> ring
  map_update_smul' v j c x := by
    fin_cases j <;>
      simp [Function.update, map_smul, ← smul_add, mul_add, Finset.mul_sum]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h01 : v 0 = v 1 := by simpa using hij
      rw [h01]
      have hmiddle := quadraticTraceMiddleTerm_polar hm iota p.2 (v 1) (v 1)
      have hmiddleLeft :
          quadraticTraceMiddleTerm iota p.2 (v 1 + v 1) +
              quadraticTraceMiddleTerm iota p.2 (v 1) +
              quadraticTraceMiddleTerm iota p.2 (v 1) = 0 := by
        letI := iota.toAlgebra
        rw [ZModModule.add_self]
        have htermZero : quadraticTraceMiddleTerm iota p.2 0 = 0 := by
          simp [quadraticTraceMiddleTerm, quadraticTraceMiddleNorm]
        rw [htermZero, zero_add, ZModModule.add_self]
      have hmiddleZero : absoluteTrace (2 * m)
          (iota p.2 * binaryFrobeniusLinear (2 * m) m (v 1) * v 1) = 0 := by
        rw [binaryFrobeniusLinear_apply]
        exact hmiddle.symm.trans hmiddleLeft
      have hordinary : (∑ i, absoluteTrace (2 * m)
          (p.1 i *
            (binaryFrobeniusLinear (2 * m) (i + 1) (v 1) * v 1 +
              v 1 * binaryFrobeniusLinear (2 * m) (i + 1) (v 1)))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _hi
        simp [mul_comm, ZModModule.add_self]
      rw [hordinary, zero_add]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmiddleZero
    · have h10 : v 1 = v 0 := by simpa using hij
      rw [h10]
      have hmiddle := quadraticTraceMiddleTerm_polar hm iota p.2 (v 0) (v 0)
      have hmiddleLeft :
          quadraticTraceMiddleTerm iota p.2 (v 0 + v 0) +
              quadraticTraceMiddleTerm iota p.2 (v 0) +
              quadraticTraceMiddleTerm iota p.2 (v 0) = 0 := by
        letI := iota.toAlgebra
        rw [ZModModule.add_self]
        have htermZero : quadraticTraceMiddleTerm iota p.2 0 = 0 := by
          simp [quadraticTraceMiddleTerm, quadraticTraceMiddleNorm]
        rw [htermZero, zero_add, ZModModule.add_self]
      have hmiddleZero : absoluteTrace (2 * m)
          (iota p.2 * binaryFrobeniusLinear (2 * m) m (v 0) * v 0) = 0 := by
        rw [binaryFrobeniusLinear_apply]
        exact hmiddle.symm.trans hmiddleLeft
      have hordinary : (∑ i, absoluteTrace (2 * m)
          (p.1 i *
            (binaryFrobeniusLinear (2 * m) (i + 1) (v 0) * v 0 +
              v 0 * binaryFrobeniusLinear (2 * m) (i + 1) (v 0)))) = 0 := by
        apply Finset.sum_eq_zero
        intro i _hi
        simp [mul_comm, ZModModule.add_self]
      rw [hordinary, zero_add]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmiddleZero
    · exact (hne rfl).elim

private theorem evenQuadraticPolarAlternating_apply
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m)
    (x y : BinaryGaloisField (2 * m)) :
    evenQuadraticPolarAlternating hm iota p ![x, y] =
      (∑ i, absoluteTrace (2 * m)
        (p.1 i *
          (binaryFrobeniusLinear (2 * m) (i + 1) x * y +
            x * binaryFrobeniusLinear (2 * m) (i + 1) y))) +
      absoluteTrace (2 * m)
        (iota p.2 * binaryFrobeniusLinear (2 * m) m x * y) := by
  rfl

private noncomputable def evenQuadraticPolarMap
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    ((Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m) →ₗ[FABL.𝔽₂]
      (BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) where
  toFun := evenQuadraticPolarAlternating hm iota
  map_add' p q := by
    ext v
    simp [evenQuadraticPolarAlternating, add_mul, Finset.sum_add_distrib, map_add]
    ring
  map_smul' c p := by
    ext v
    simp [evenQuadraticPolarAlternating, map_smul, mul_add, Finset.mul_sum]

private noncomputable def evenPolarLinearized
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m) :
    BinaryGaloisField (2 * m) →ₗ[FABL.𝔽₂] BinaryGaloisField (2 * m) :=
  (∑ i, (p.1 i • binaryFrobeniusLinear (2 * m) (i + 1) +
    (((binaryFrobeniusEquiv (2 * m)) ^
        ((2 * m) - (i + 1))) (p.1 i)) •
      binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1)))) +
    (iota p.2) • binaryFrobeniusLinear (2 * m) m

private def evenPolarFrobeniusIndex (hm : m ≠ 0) :
    ((Fin m.pred ⊕ Fin m.pred) ⊕ Fin 1) → Fin (2 * m)
  | Sum.inl (Sum.inl i) => ⟨i + 1, by
      have hi := i.isLt
      have hpred : m.pred = m - 1 := Nat.pred_eq_sub_one
      have hmpos := Nat.pos_of_ne_zero hm
      omega⟩
  | Sum.inl (Sum.inr i) => ⟨(2 * m) - (i + 1), by
      have hi := i.isLt
      have hpred : m.pred = m - 1 := Nat.pred_eq_sub_one
      have hmpos := Nat.pos_of_ne_zero hm
      omega⟩
  | Sum.inr _ => ⟨m, by
      have hmpos := Nat.pos_of_ne_zero hm
      omega⟩

private theorem evenPolarFrobeniusIndex_injective (hm : m ≠ 0) :
    Function.Injective (evenPolarFrobeniusIndex hm) := by
  have hpred : m.pred = m - 1 := Nat.pred_eq_sub_one
  intro i j hij
  cases i with
  | inl i =>
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              cases j with
              | inl j =>
                  simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
                  congr 2
                  omega
              | inr j =>
                  simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
                  have hi := i.isLt
                  have hj := j.isLt
                  have hmpos := Nat.pos_of_ne_zero hm
                  omega
          | inr j =>
              simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
              have hi := i.isLt
              have hmpos := Nat.pos_of_ne_zero hm
              omega
      | inr i =>
          cases j with
          | inl j =>
              cases j with
              | inl j =>
                  simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
                  have hi := i.isLt
                  have hj := j.isLt
                  have hmpos := Nat.pos_of_ne_zero hm
                  omega
              | inr j =>
                  simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
                  congr 2
                  omega
          | inr j =>
              simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
              have hi := i.isLt
              have hmpos := Nat.pos_of_ne_zero hm
              omega
  | inr i =>
      cases j with
      | inl j =>
          cases j with
          | inl j =>
              simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
              have hj := j.isLt
              have hmpos := Nat.pos_of_ne_zero hm
              omega
          | inr j =>
              simp only [evenPolarFrobeniusIndex, Fin.mk.injEq] at hij
              have hj := j.isLt
              have hmpos := Nat.pos_of_ne_zero hm
              omega
      | inr j =>
          exact congrArg Sum.inr (Subsingleton.elim i j)

private theorem evenPolarLinearized_injective (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    Function.Injective (evenPolarLinearized iota) := by
  intro p q hpq
  let coeff : ((Fin m.pred ⊕ Fin m.pred) ⊕ Fin 1) →
      BinaryGaloisField (2 * m)
    | Sum.inl (Sum.inl i) => p.1 i - q.1 i
    | Sum.inl (Sum.inr i) =>
        ((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (p.1 i) -
          ((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (q.1 i)
    | Sum.inr _ => iota p.2 - iota q.2
  have hLI : LinearIndependent (BinaryGaloisField (2 * m))
      (fun s : ((Fin m.pred ⊕ Fin m.pred) ⊕ Fin 1) ↦
        binaryFrobeniusLinear (2 * m) (evenPolarFrobeniusIndex hm s)) :=
    (binaryFrobeniusLinear_linearIndependent (2 * m)
      (mul_ne_zero (by omega) hm)).comp _ (evenPolarFrobeniusIndex_injective hm)
  have hzero : ∑ s, coeff s •
      binaryFrobeniusLinear (2 * m) (evenPolarFrobeniusIndex hm s) = 0 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_one]
    simp only [coeff, evenPolarFrobeniusIndex]
    rw [show (∑ i : Fin m.pred, (p.1 i - q.1 i) •
          binaryFrobeniusLinear (2 * m) (i + 1)) =
        (∑ i : Fin m.pred, p.1 i • binaryFrobeniusLinear (2 * m) (i + 1)) -
          ∑ i : Fin m.pred, q.1 i • binaryFrobeniusLinear (2 * m) (i + 1) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      exact sub_smul (p.1 i) (q.1 i) (binaryFrobeniusLinear (2 * m) (i + 1))]
    rw [show (∑ i : Fin m.pred,
          (((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (p.1 i) -
            ((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (q.1 i)) •
            binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1))) =
        (∑ i : Fin m.pred,
          ((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (p.1 i) •
            binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1))) -
          ∑ i : Fin m.pred,
          ((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (q.1 i) •
            binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1)) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      exact sub_smul
        (((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (p.1 i))
        (((binaryFrobeniusEquiv (2 * m)) ^ ((2 * m) - (i + 1))) (q.1 i))
        (binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1)))]
    rw [sub_smul (iota p.2) (iota q.2) (binaryFrobeniusLinear (2 * m) m)]
    have hdiff : evenPolarLinearized iota p - evenPolarLinearized iota q = 0 :=
      sub_eq_zero.mpr hpq
    rw [evenPolarLinearized, evenPolarLinearized, Finset.sum_add_distrib,
      Finset.sum_add_distrib] at hdiff
    rw [← hdiff]
    abel
  apply Prod.ext
  · funext i
    have hi := Fintype.linearIndependent_iff.mp hLI coeff hzero (Sum.inl (Sum.inl i))
    exact sub_eq_zero.mp hi
  · apply iota.injective
    have hmiddle := Fintype.linearIndependent_iff.mp hLI coeff hzero
      (Sum.inr (0 : Fin 1))
    exact sub_eq_zero.mp hmiddle

private theorem evenQuadraticPolarAlternating_eq_trace_linearized_mul
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m)
    (x y : BinaryGaloisField (2 * m)) :
    evenQuadraticPolarAlternating hm iota p ![x, y] =
      absoluteTrace (2 * m) (evenPolarLinearized iota p x * y) := by
  rw [evenQuadraticPolarAlternating_apply]
  rw [show evenPolarLinearized iota p x =
      (∑ i, (p.1 i * binaryFrobeniusLinear (2 * m) (i + 1) x +
        ((binaryFrobeniusEquiv (2 * m)) ^
            ((2 * m) - (i + 1))) (p.1 i) *
          binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1)) x)) +
        iota p.2 * binaryFrobeniusLinear (2 * m) m x by
    simp [evenPolarLinearized, LinearMap.sum_apply, smul_eq_mul]]
  rw [add_mul, map_add, Finset.sum_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  let E := binaryFrobeniusEquiv (2 * m)
  let Fi := binaryFrobeniusLinear (2 * m) (i + 1)
  let Fj := binaryFrobeniusLinear (2 * m) ((2 * m) - (i + 1))
  have hadjoint : absoluteTrace (2 * m) (p.1 i * (x * Fi y)) =
      absoluteTrace (2 * m)
        (((E ^ ((2 * m) - (i + 1))) (p.1 i) * Fj x) * y) := by
    calc
      absoluteTrace (2 * m) (p.1 i * (x * Fi y)) =
          absoluteTrace (2 * m) ((p.1 i * x) * Fi y) := by
        rw [mul_assoc]
      _ = absoluteTrace (2 * m)
          ((E ^ ((2 * m) - (i + 1))) (p.1 i * x) * y) := by
        apply absoluteTrace_mul_binaryFrobeniusLinear
        · exact mul_ne_zero (by omega) hm
        · have hi := i.isLt
          have hpred : m.pred = m - 1 := Nat.pred_eq_sub_one
          omega
      _ = absoluteTrace (2 * m)
          (((E ^ ((2 * m) - (i + 1))) (p.1 i) * Fj x) * y) := by
        have hFj : Fj x = (E ^ ((2 * m) - (i + 1))) x := by
          simpa [E, Fj, binaryFrobeniusEquiv] using
            binaryFrobeniusLinear_eq_algEquiv_pow_apply
              (2 * m) ((2 * m) - (i + 1)) x
        apply congrArg (fun z : BinaryGaloisField (2 * m) ↦
          absoluteTrace (2 * m) (z * y))
        calc
          (E ^ ((2 * m) - (i + 1))) (p.1 i * x) =
              (E ^ ((2 * m) - (i + 1))) (p.1 i) *
                (E ^ ((2 * m) - (i + 1))) x :=
            (E ^ ((2 * m) - (i + 1))).map_mul (p.1 i) x
          _ = (E ^ ((2 * m) - (i + 1))) (p.1 i) * Fj x := by
            rw [hFj]
  calc
    absoluteTrace (2 * m) (p.1 i * (Fi x * y + x * Fi y)) =
        absoluteTrace (2 * m) (p.1 i * (Fi x * y)) +
          absoluteTrace (2 * m) (p.1 i * (x * Fi y)) := by
      rw [mul_add, map_add]
    _ = absoluteTrace (2 * m) (p.1 i * (Fi x * y)) +
        absoluteTrace (2 * m)
          (((E ^ ((2 * m) - (i + 1))) (p.1 i) * Fj x) * y) := by
      rw [hadjoint]
    _ = absoluteTrace (2 * m)
        ((p.1 i * Fi x +
          (E ^ ((2 * m) - (i + 1))) (p.1 i) * Fj x) * y) := by
      rw [add_mul, map_add]
      congr 1
      rw [mul_assoc]

private theorem evenQuadraticPolarMap_injective (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    Function.Injective (evenQuadraticPolarMap hm iota) := by
  letI : Fintype (BinaryGaloisField (2 * m)) := Fintype.ofFinite _
  letI : Algebra.IsAlgebraic FABL.𝔽₂ (BinaryGaloisField (2 * m)) :=
    Algebra.IsIntegral.isAlgebraic
  letI : Algebra.IsSeparable FABL.𝔽₂ (BinaryGaloisField (2 * m)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  intro p q hpq
  apply evenPolarLinearized_injective hm iota
  ext x
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate FABL.𝔽₂ (BinaryGaloisField (2 * m))).1
  intro y
  rw [Algebra.traceForm_apply]
  change absoluteTrace (2 * m)
    ((evenPolarLinearized iota p x - evenPolarLinearized iota q x) * y) = 0
  rw [sub_mul, map_sub, sub_eq_zero]
  calc
    absoluteTrace (2 * m) (evenPolarLinearized iota p x * y) =
        evenQuadraticPolarAlternating hm iota p ![x, y] :=
      (evenQuadraticPolarAlternating_eq_trace_linearized_mul hm iota p x y).symm
    _ = evenQuadraticPolarAlternating hm iota q ![x, y] := by
      exact congrArg (fun A ↦ A ![x, y]) hpq
    _ = absoluteTrace (2 * m) (evenPolarLinearized iota q x * y) :=
      evenQuadraticPolarAlternating_eq_trace_linearized_mul hm iota q x y

private theorem evenQuadraticPolarMap_finrank_eq (hm : m ≠ 0)
    (_iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    Module.finrank FABL.𝔽₂
        ((Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m) =
      Module.finrank FABL.𝔽₂
        (BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.pred_eq_sub_one]
  rw [GaloisField.finrank 2 hm,
    GaloisField.finrank 2 (mul_ne_zero (by omega) hm)]
  calc
    (m - 1) * (2 * m) + m = Nat.choose (2 * m) 2 := by
      rw [Nat.choose_two_right]
      have hmpos := Nat.pos_of_ne_zero hm
      rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega]
      rw [show (2 * m) * (2 * (m - 1) + 1) =
        2 * ((m - 1) * (2 * m) + m) by ring]
      rw [Nat.mul_div_cancel_left _ zero_lt_two]
    _ = Module.finrank FABL.𝔽₂
        (BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) := by
      symm
      calc
        Module.finrank FABL.𝔽₂
            (BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) =
          Module.finrank FABL.𝔽₂
            ((⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m))) →ₗ[FABL.𝔽₂] FABL.𝔽₂) :=
          exteriorPower.alternatingMapLinearEquiv.finrank_eq
        _ = Module.finrank FABL.𝔽₂
            (⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m))) := by
          exact Module.finrank_linearMap_self FABL.𝔽₂ FABL.𝔽₂
            (⋀[FABL.𝔽₂]^2 (BinaryGaloisField (2 * m)))
        _ = Nat.choose
            (Module.finrank FABL.𝔽₂ (BinaryGaloisField (2 * m))) 2 :=
          exteriorPower.finrank_eq FABL.𝔽₂ 2
        _ = Nat.choose (2 * m) 2 := by
          rw [GaloisField.finrank 2 (mul_ne_zero (by omega) hm)]

private theorem evenQuadraticPolarMap_surjective (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    Function.Surjective (evenQuadraticPolarMap hm iota) := by
  letI : FiniteDimensional FABL.𝔽₂
      (BinaryGaloisField (2 * m) [⋀^Fin 2]→ₗ[FABL.𝔽₂] FABL.𝔽₂) :=
    exteriorPower.alternatingMapLinearEquiv.symm.finiteDimensional
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (evenQuadraticPolarMap_finrank_eq hm iota)).mp
      (evenQuadraticPolarMap_injective hm iota)

private noncomputable def evenQuadraticTracePart
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m) :
    FieldBooleanFunction (2 * m) :=
  fun x ↦ absoluteTrace (2 * m)
      (∑ i, p.1 i *
        (binaryFrobeniusLinear (2 * m) (i + 1) x * x)) +
    quadraticTraceMiddleTerm iota p.2 x

private theorem evenQuadraticTracePart_polar (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m)
    (x y : BinaryGaloisField (2 * m)) :
    evenQuadraticTracePart iota p (x + y) + evenQuadraticTracePart iota p x +
        evenQuadraticTracePart iota p y + evenQuadraticTracePart iota p 0 =
      evenQuadraticPolarAlternating hm iota p ![x, y] := by
  rw [evenQuadraticPolarAlternating_apply]
  let ordinary : BinaryGaloisField (2 * m) → FABL.𝔽₂ := fun z ↦
    absoluteTrace (2 * m)
      (∑ i, p.1 i * (binaryFrobeniusLinear (2 * m) (i + 1) z * z))
  have hordinary : ordinary (x + y) + ordinary x + ordinary y + ordinary 0 =
      ∑ i, absoluteTrace (2 * m)
        (p.1 i *
          (binaryFrobeniusLinear (2 * m) (i + 1) x * y +
            x * binaryFrobeniusLinear (2 * m) (i + 1) y)) := by
    simp only [ordinary, map_add, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero]
    rw [map_sum, map_sum, map_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← map_add, ← map_add]
    congr 1
    simp [add_mul, mul_add]
    ring_nf
    rw [show (2 : BinaryGaloisField (2 * m)) = 0 from
      CharP.cast_eq_zero (BinaryGaloisField (2 * m)) 2]
    simp
  have hmiddleZero : quadraticTraceMiddleTerm iota p.2 0 = 0 := by
    letI := iota.toAlgebra
    simp [quadraticTraceMiddleTerm, quadraticTraceMiddleNorm]
  have hmiddle :
      quadraticTraceMiddleTerm iota p.2 (x + y) +
          quadraticTraceMiddleTerm iota p.2 x +
          quadraticTraceMiddleTerm iota p.2 y +
          quadraticTraceMiddleTerm iota p.2 0 =
        absoluteTrace (2 * m)
          (iota p.2 * binaryFrobeniusLinear (2 * m) m x * y) := by
    rw [hmiddleZero, add_zero, binaryFrobeniusLinear_apply]
    exact quadraticTraceMiddleTerm_polar hm iota p.2 x y
  change (ordinary (x + y) + quadraticTraceMiddleTerm iota p.2 (x + y)) +
      (ordinary x + quadraticTraceMiddleTerm iota p.2 x) +
      (ordinary y + quadraticTraceMiddleTerm iota p.2 y) +
      (ordinary 0 + quadraticTraceMiddleTerm iota p.2 0) = _
  rw [show (ordinary (x + y) + quadraticTraceMiddleTerm iota p.2 (x + y)) +
      (ordinary x + quadraticTraceMiddleTerm iota p.2 x) +
      (ordinary y + quadraticTraceMiddleTerm iota p.2 y) +
      (ordinary 0 + quadraticTraceMiddleTerm iota p.2 0) =
    (ordinary (x + y) + ordinary x + ordinary y + ordinary 0) +
      (quadraticTraceMiddleTerm iota p.2 (x + y) +
        quadraticTraceMiddleTerm iota p.2 x +
        quadraticTraceMiddleTerm iota p.2 y +
        quadraticTraceMiddleTerm iota p.2 0) by abel]
  rw [hordinary, hmiddle]

private theorem exists_evenQuadraticTracePart_polar_eq (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (theta : FABL.F₂Cube (2 * m) ≃ₗ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (f : BooleanFunction (2 * m))
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ p : (Fin m.pred → BinaryGaloisField (2 * m)) × BinaryGaloisField m,
      ∀ x y, quadraticPolarKernel
          (fun u ↦ evenQuadraticTracePart iota p (theta u)) x y =
        quadraticPolarKernel f x y := by
  obtain ⟨p, hp⟩ := evenQuadraticPolarMap_surjective hm iota
    (transportedQuadraticPolar theta f hdegree)
  refine ⟨p, ?_⟩
  intro x y
  have hvalue := congrArg (fun A ↦ A ![theta x, theta y]) hp
  rw [evenQuadraticPolarMap, transportedQuadraticPolar_apply] at hvalue
  simp only [theta.symm_apply_apply] at hvalue
  rw [quadraticPolar_apply] at hvalue
  rw [quadraticPolarKernel_eq]
  change evenQuadraticTracePart iota p (theta (x + y)) +
      evenQuadraticTracePart iota p (theta x) +
      evenQuadraticTracePart iota p (theta y) +
      evenQuadraticTracePart iota p (theta 0) = _
  rw [theta.map_add, theta.map_zero, evenQuadraticTracePart_polar hm iota]
  exact hvalue

private theorem exists_evenQuadraticTraceRepresentation_of_degree_le
    (r : ℕ)
    (iota : BinaryGaloisField (r + 1) →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * (r + 1)))
    (theta : FABL.F₂Cube (2 * (r + 1)) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * (r + 1)))
    (f : BooleanFunction (2 * (r + 1)))
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ betaEmpty : BinaryGaloisField (2 * (r + 1)),
      ∃ beta : Fin (r + 1) → BinaryGaloisField (2 * (r + 1)),
      ∃ gamma : BinaryGaloisField (r + 1),
        ∀ u, f u =
          absoluteTrace (2 * (r + 1))
            (betaEmpty + ∑ i, beta i * (theta u) ^ (2 ^ (i : ℕ) + 1)) +
          absoluteTrace (r + 1)
            (gamma * quadraticTraceMiddleNorm iota (theta u)) := by
  have hm : r + 1 ≠ 0 := by omega
  obtain ⟨p, hpolar⟩ :=
    exists_evenQuadraticTracePart_polar_eq hm iota theta f hdegree
  simp only [Nat.pred_succ] at p hpolar
  let q : BooleanFunction (2 * (r + 1)) :=
    fun u ↦ evenQuadraticTracePart iota p (theta u)
  let h : BooleanFunction (2 * (r + 1)) := fun u ↦ f u + q u
  have hzero : ∀ x y, quadraticPolarKernel h x y = 0 := by
    intro x y
    calc
      quadraticPolarKernel h x y =
          quadraticPolarKernel f x y + quadraticPolarKernel q x y := by
        simp only [quadraticPolarKernel_eq, h]
        abel
      _ = quadraticPolarKernel f x y + quadraticPolarKernel f x y := by
        rw [hpolar x y]
      _ = 0 := ZModModule.add_self _
  obtain ⟨c, a, haffine⟩ :=
    exists_affineFunction_of_quadraticPolarKernel_eq_zero h hzero
  obtain ⟨linearBeta, hlinear, _hlinearUnique⟩ :=
    existsUnique_tracePairingCoefficient theta a
  obtain ⟨traceOne, htraceOne⟩ := exists_absoluteTrace_eq_one (2 * (r + 1))
  let betaEmpty : BinaryGaloisField (2 * (r + 1)) := c • traceOne
  let beta : Fin (r + 1) → BinaryGaloisField (2 * (r + 1)) :=
    Fin.cons (binaryFrobeniusLinear (2 * (r + 1)) 1 linearBeta) p.1
  refine ⟨betaEmpty, beta, p.2, ?_⟩
  intro u
  have hu := congrFun haffine u
  have hf : f u = FABL.affineFunction c a u + q u := by
    calc
      f u = (f u + q u) + q u := by
        rw [add_assoc, ZModModule.add_self, add_zero]
      _ = FABL.affineFunction c a u + q u := by
        rw [← hu]
  rw [hf]
  rw [show FABL.affineFunction c a u =
      c + absoluteTrace (2 * (r + 1)) (linearBeta * theta u) by
    rw [FABL.affineFunction, hlinear u]]
  rw [absoluteTrace_mul_eq_frobeniusLinear_mul_self]
  change c + absoluteTrace (2 * (r + 1))
      (binaryFrobeniusLinear (2 * (r + 1)) 1 linearBeta *
        (theta u * theta u)) +
      evenQuadraticTracePart iota p (theta u) = _
  rw [Fin.sum_univ_succ]
  simp only [beta, Fin.cons_zero, Fin.cons_succ]
  simp only [evenQuadraticTracePart, quadraticTraceMiddleTerm]
  rw [map_add, map_sum]
  rw [show absoluteTrace (2 * (r + 1)) betaEmpty = c by
    simp [betaEmpty, htraceOne]]
  simp_rw [binaryFrobeniusLinear_apply]
  have hpower (z : BinaryGaloisField (2 * (r + 1))) (i : ℕ) :
      z ^ (2 ^ i + 1) = z ^ (2 ^ i) * z := by
    rw [pow_add, pow_one]
  simp_rw [hpower]
  simp only [pow_one, Nat.pred_eq_sub_one, Nat.add_one_sub_one,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, Fin.val_succ, map_add,
    map_sum]
  exact (show ∀ a b c d : FABL.𝔽₂,
      a + b + (c + d) = a + (b + c) + d by
    intro a b c d
    abel) _ _ _ _

private noncomputable def explicitRelativeTraceOne
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    BinaryGaloisField (2 * m) := by
  letI := iota.toAlgebra
  exact (Algebra.trace_surjective (BinaryGaloisField m)
    (BinaryGaloisField (2 * m)) (1 : BinaryGaloisField m)).choose

private theorem trace_explicitRelativeTraceOne
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m)) :
    letI := iota.toAlgebra
    Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (explicitRelativeTraceOne iota) = 1 := by
  letI := iota.toAlgebra
  exact (Algebra.trace_surjective (BinaryGaloisField m)
    (BinaryGaloisField (2 * m)) (1 : BinaryGaloisField m)).choose_spec

private theorem absoluteTrace_explicitRelativeTraceOne_mul_iota
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (z : BinaryGaloisField m) :
    absoluteTrace (2 * m) (explicitRelativeTraceOne iota * iota z) =
      absoluteTrace m z := by
  letI := iota.toAlgebra
  letI : IsScalarTower FABL.𝔽₂ (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  change Algebra.trace FABL.𝔽₂ (BinaryGaloisField (2 * m))
      (explicitRelativeTraceOne iota *
        algebraMap (BinaryGaloisField m) (BinaryGaloisField (2 * m)) z) =
    Algebra.trace FABL.𝔽₂ (BinaryGaloisField m) z
  rw [← Algebra.trace_trace (R := FABL.𝔽₂) (S := BinaryGaloisField m)
    (T := BinaryGaloisField (2 * m))]
  congr 1
  rw [mul_comm (explicitRelativeTraceOne iota), ← Algebra.smul_def, map_smul,
    trace_explicitRelativeTraceOne iota]
  simp

private theorem absoluteTrace_middleNorm_eq_explicitRelativeTraceOne_mul_pow
    (hm : m ≠ 0)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (gamma : BinaryGaloisField m) (x : BinaryGaloisField (2 * m)) :
    absoluteTrace m (gamma * quadraticTraceMiddleNorm iota x) =
      absoluteTrace (2 * m)
        ((explicitRelativeTraceOne iota * iota gamma) * x ^ (2 ^ m + 1)) := by
  letI := iota.toAlgebra
  rw [← absoluteTrace_explicitRelativeTraceOne_mul_iota iota
    (gamma * quadraticTraceMiddleNorm iota x)]
  congr 1
  rw [map_mul, quadraticTraceMiddleNorm_map_eq_pow hm iota]
  ac_rfl

private theorem two_pow_add_one_lt_even_modulus (hm : m ≠ 0)
    (i : Fin m) :
    2 ^ (i : ℕ) + 1 < 2 ^ (2 * m) - 1 := by
  by_cases hmOne : m = 1
  · subst m
    fin_cases i
    norm_num
  · have hmTwo : 1 < m := by omega
    have hiPow : 2 ^ (i : ℕ) < 2 ^ m :=
      Nat.pow_lt_pow_right (by omega) i.isLt
    have ha : 4 ≤ 2 ^ m := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hmTwo
    have hmul : 4 * 2 ^ m ≤ 2 ^ m * 2 ^ m := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2 ^ m) ha
    rw [show 2 * m = m + m by omega, pow_add]
    omega

private theorem middle_two_pow_add_one_lt_even_modulus
    (hm : m ≠ 0) (hmOne : m ≠ 1) :
    2 ^ m + 1 < 2 ^ (2 * m) - 1 := by
  have hmTwo : 1 < m := by omega
  have ha : 4 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hmTwo
  have hmul : 4 * 2 ^ m ≤ 2 ^ m * 2 ^ m := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2 ^ m) ha
  rw [show 2 * m = m + m by omega, pow_add]
  omega

/-- Carlet's finite-field trace representation of even-dimensional quadratic Boolean
functions, with the middle coefficient taken in an explicitly embedded half-degree subfield. -/
theorem functionAlgebraicDegree_le_two_iff_exists_even_quadraticTraceRepresentation
    (m : ℕ) (hm : m ≠ 0)
    (theta : FABL.F₂Cube (2 * m) ≃ₗ[FABL.𝔽₂] BinaryGaloisField (2 * m))
    (f : BooleanFunction (2 * m)) :
    FABL.functionAlgebraicDegree f ≤ 2 ↔
      ∃ iota : BinaryGaloisField m →ₐ[FABL.𝔽₂] BinaryGaloisField (2 * m),
      ∃ betaEmpty : BinaryGaloisField (2 * m),
      ∃ beta : Fin m → BinaryGaloisField (2 * m),
      ∃ gamma : BinaryGaloisField m,
        ∀ x, f x =
          absoluteTrace (2 * m)
            (betaEmpty + ∑ i, beta i * (theta x) ^ (2 ^ (i : ℕ) + 1)) +
          absoluteTrace m
            (gamma * quadraticTraceMiddleNorm iota (theta x)) := by
  constructor
  · intro hdegree
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hmSucc : r + 1 ≠ 0 := by omega
    let iota : BinaryGaloisField (r + 1) →ₐ[FABL.𝔽₂]
        BinaryGaloisField (2 * (r + 1)) :=
      (FiniteField.nonempty_algHom_of_finrank_dvd
        (F := FABL.𝔽₂) (K := BinaryGaloisField (r + 1))
        (L := BinaryGaloisField (2 * (r + 1))) (by
          rw [GaloisField.finrank 2 hmSucc,
            GaloisField.finrank 2 (mul_ne_zero (by omega) hmSucc)]
          exact dvd_mul_left (r + 1) 2)).some
    obtain ⟨betaEmpty, beta, gamma, hrepresentation⟩ :=
      exists_evenQuadraticTraceRepresentation_of_degree_le
        r iota theta f hdegree
    exact ⟨iota, betaEmpty, beta, gamma, hrepresentation⟩
  · rintro ⟨iota, betaEmpty, beta, gamma, hrepresentation⟩
    by_cases hmOne : m = 1
    · subst m
      exact (FABL.functionAlgebraicDegree_le_dimension f).trans (by omega)
    · let constant : BooleanFunction (2 * m) :=
        fun _ ↦ absoluteTrace (2 * m) betaEmpty
      let term (i : Fin m) : BooleanFunction (2 * m) :=
        fun x ↦ absoluteTrace (2 * m)
          (beta i * (theta x) ^ (2 ^ (i : ℕ) + 1))
      let middle : BooleanFunction (2 * m) :=
        fun x ↦ absoluteTrace m
          (gamma * quadraticTraceMiddleNorm iota (theta x))
      have hdecomposition : f = constant + ∑ i, term i + middle := by
        funext x
        rw [hrepresentation x, map_add, map_sum]
        simp only [Pi.add_apply, Finset.sum_apply, constant, term, middle]
      rw [hdecomposition]
      apply (FABL.functionAlgebraicDegree_add_le_max
        (constant + ∑ i, term i) middle).trans
      apply max_le
      · apply (FABL.functionAlgebraicDegree_add_le_max constant
          (∑ i, term i)).trans
        apply max_le
        · simpa [constant] using
            functionAlgebraicDegree_constant_le_two
              (n := 2 * m) (absoluteTrace (2 * m) betaEmpty)
        · apply FABL.functionAlgebraicDegree_finset_sum_le Finset.univ term 2
          intro i _hi
          exact functionAlgebraicDegree_traceMonomial_two_pow_add_one_le_two
            (by omega) (two_pow_add_one_lt_even_modulus hm i)
            theta (beta i)
      · have hmiddleFunction : middle = fun x : FABL.F₂Cube (2 * m) ↦
            absoluteTrace (2 * m)
              ((explicitRelativeTraceOne iota * iota gamma) *
                (theta x) ^ (2 ^ m + 1)) := by
          funext x
          exact absoluteTrace_middleNorm_eq_explicitRelativeTraceOne_mul_pow
            hm iota gamma (theta x)
        rw [hmiddleFunction]
        exact functionAlgebraicDegree_traceMonomial_two_pow_add_one_le_two
          (by omega) (middle_two_pow_add_one_lt_even_modulus hm hmOne)
          theta (explicitRelativeTraceOne iota * iota gamma)


end CryptBoolean
