/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter09.CarletFeng
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import CryptBoolean.Carlet.Chapter02.TracePairing
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.GaussSum

/-!
# Nonlinearity of the Carlet--Feng function

The logarithmic incomplete-character-sum estimate and the resulting
nonlinearity bound from Carlet Chapter 9.
-/

open Finset
open scoped BigOperators

@[expose] public section

namespace CryptBoolean

noncomputable section

private theorem harmonic_sum_le_log_odd (m : ℕ) :
    (∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1)) ≤
      Real.log (2 * (m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      let x : ℝ := 2 / (2 * (m : ℝ) + 1)
      have hx : 0 ≤ x := by positivity
      have hlog := Real.le_log_one_add_of_nonneg hx
      have hstep :
          (1 : ℝ) / (m + 1) ≤
            Real.log (2 * ((m + 1 : ℕ) : ℝ) + 1) -
              Real.log (2 * (m : ℝ) + 1) := by
        have hden : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
        have hmden : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hxform :
            2 * x / (x + 2) = (1 : ℝ) / (m + 1) := by
          dsimp [x]
          field_simp
          ring_nf
        have honeAdd :
            1 + x =
              (2 * ((m + 1 : ℕ) : ℝ) + 1) /
                (2 * (m : ℝ) + 1) := by
          dsimp [x]
          norm_num only [Nat.cast_add, Nat.cast_one]
          field_simp
          ring_nf
        rw [hxform, honeAdd] at hlog
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        exact hlog
      have := add_le_add ih hstep
      norm_num only [Nat.cast_add, Nat.cast_one] at this ⊢
      linarith

private theorem norm_gaussSum_eq_sqrt_card
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hproduct := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq χ ψ] at hproduct
  have hnorm := congrArg norm hproduct
  simp only [norm_mul, norm_star, norm_natCast] at hnorm
  calc
    ‖gaussSum χ ψ‖ = Real.sqrt (‖gaussSum χ ψ‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt (Fintype.card F : ℝ) := by
      rw [pow_two, hnorm]

private noncomputable def primitivePowerEquiv
    {F : Type*} [Field F] [Fintype F]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1)) :
    ZMod (Fintype.card F - 1) ≃+ Additive Fˣ := by
  let N := Fintype.card F - 1
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.sub_pos_of_lt Fintype.one_lt_card
  letI : NeZero N := ⟨hN.ne'⟩
  have hαNe : α ≠ 0 := by
    exact (hα.isUnit hN.ne').ne_zero
  let αu : Fˣ := Units.mk0 α hαNe
  have hαu : IsPrimitiveRoot αu N := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [N, αu] using hα
  have hzp : Subgroup.zpowers αu = ⊤ := by
    rw [hαu.zpowers_eq]
    apply top_unique
    intro u _hu
    rw [mem_rootsOfUnity']
    simpa [N] using FiniteField.pow_card_sub_one_eq_one (u : F) (Units.ne_zero u)
  exact hαu.zmodEquivZPowers.trans
    (((MulEquiv.subgroupCongr hzp).trans Subgroup.topEquiv).toAdditive)

private theorem primitivePowerEquiv_natCast
    {F : Type*} [Field F] [Fintype F]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    (i : ℕ) :
    ((primitivePowerEquiv α hα (i : ZMod (Fintype.card F - 1))).toMul : Fˣ) =
      Units.mk0 (α ^ i) (pow_ne_zero i ((hα.isUnit (by
        exact (Nat.sub_pos_of_lt Fintype.one_lt_card).ne')).ne_zero)) := by
  let N := Fintype.card F - 1
  have hN : 0 < N := Nat.sub_pos_of_lt Fintype.one_lt_card
  letI : NeZero N := ⟨hN.ne'⟩
  let hαNe : α ≠ 0 := (hα.isUnit hN.ne').ne_zero
  let αu : Fˣ := Units.mk0 α hαNe
  have hαu : IsPrimitiveRoot αu N := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [N, αu] using hα
  apply Units.ext
  change ((primitivePowerEquiv α hα (i : ZMod N)).toMul : F) = α ^ i
  simp only [primitivePowerEquiv, AddEquiv.trans_apply,
    IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  rfl

private noncomputable def primitivePowerMulChar
    {F : Type*} [Field F] [Fintype F]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    (μ : ZMod (Fintype.card F - 1)) : MulChar F ℂ := by
  let N := Fintype.card F - 1
  have hN : 0 < N := Nat.sub_pos_of_lt Fintype.one_lt_card
  letI : NeZero N := ⟨hN.ne'⟩
  let logEquiv : Additive Fˣ ≃+ ZMod N := (primitivePowerEquiv α hα).symm
  let ψ : AddChar (Additive Fˣ) Circle :=
    (AddChar.zmod N μ).compAddMonoidHom logEquiv.toAddMonoidHom
  let unitCircleHom : Fˣ →* Circle :=
    { toFun := fun u => ψ (Additive.ofMul u)
      map_one' := ψ.map_zero_eq_one
      map_mul' := fun u v =>
        ψ.map_add_eq_mul (Additive.ofMul u) (Additive.ofMul v) }
  exact MulChar.ofUnitHom (Circle.toUnits.comp unitCircleHom)

private theorem primitivePowerMulChar_apply_powerEquiv
    {F : Type*} [Field F] [Fintype F] [NeZero (Fintype.card F - 1)]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    (μ j : ZMod (Fintype.card F - 1)) :
    primitivePowerMulChar α hα μ
        (((primitivePowerEquiv α hα j).toMul : Fˣ) : F) =
      ((AddChar.zmod (Fintype.card F - 1) μ j : Circle) : ℂ) := by
  let N := Fintype.card F - 1
  have hN : 0 < N := Nat.sub_pos_of_lt Fintype.one_lt_card
  letI : NeZero N := ⟨hN.ne'⟩
  rw [primitivePowerMulChar]
  rw [MulChar.ofUnitHom_coe]
  change (((AddChar.zmod N μ)
      ((primitivePowerEquiv α hα).symm (primitivePowerEquiv α hα j)) : Circle) : ℂ) = _
  rw [AddEquiv.symm_apply_apply]

private theorem primitivePowerMulChar_apply_natPow
    {F : Type*} [Field F] [Fintype F] [NeZero (Fintype.card F - 1)]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    (μ : ZMod (Fintype.card F - 1)) (i : ℕ) :
    primitivePowerMulChar α hα μ (α ^ i) =
      ((AddChar.zmod (Fintype.card F - 1) μ
        (i : ZMod (Fintype.card F - 1)) : Circle) : ℂ) := by
  have h := primitivePowerMulChar_apply_powerEquiv α hα μ
    (i : ZMod (Fintype.card F - 1))
  rw [primitivePowerEquiv_natCast] at h
  simpa using h

private noncomputable def cyclicDFT {N : ℕ} [NeZero N]
    (a : ZMod N → ℂ) (μ : ZMod N) : ℂ :=
  ∑ j : ZMod N, AddChar.zmodAddEquiv μ j * a j

private theorem cyclicDFT_inversion {N : ℕ} [NeZero N]
    (a : ZMod N → ℂ) (j : ZMod N) :
    a j = (N : ℂ)⁻¹ *
      ∑ μ : ZMod N, AddChar.zmodAddEquiv μ (-j) * cyclicDFT a μ := by
  classical
  simp only [cyclicDFT]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have hcombine (μ k : ZMod N) :
      (N : ℂ)⁻¹ * AddChar.zmodAddEquiv μ (-j) *
          AddChar.zmodAddEquiv μ k =
        (N : ℂ)⁻¹ * AddChar.zmodAddEquiv μ (k + -j) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul, add_comm]
  simp_rw [hcombine, ← Finset.mul_sum]
  have horth (k : ZMod N) :
      (∑ μ : ZMod N, AddChar.zmodAddEquiv μ (k + -j)) =
        if k = j then (N : ℂ) else 0 := by
    calc
      _ = ∑ ψ : AddChar (ZMod N) ℂ, ψ (k + -j) := by
        apply Fintype.sum_equiv AddChar.zmodAddEquiv.toEquiv
        intro μ
        rfl
      _ = if k + -j = 0 then (Fintype.card (ZMod N) : ℂ) else 0 :=
        AddChar.sum_apply_eq_ite (k + -j)
      _ = if k = j then (N : ℂ) else 0 := by
        rw [ZMod.card]
        congr 1
        simp only [add_neg_eq_zero]
  simp_rw [horth]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp [hN]

private theorem gaussSum_eq_sum_units
    {F : Type*} [Field F] [Fintype F] [Fintype Fˣ]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ u : Fˣ, χ (u : F) * ψ (u : F) := by
  classical
  rw [gaussSum]
  calc
    (∑ x : F, χ x * ψ x) =
        ∑ x ∈ (Finset.univ.erase 0), χ x * ψ x := by
      have h := Finset.sum_erase_add (Finset.univ : Finset F)
        (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))
      rw [χ.map_zero, zero_mul, add_zero] at h
      exact h.symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x.1 * ψ x.1 := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ u : Fˣ, χ (u : F) * ψ (u : F) := by
      symm
      apply Fintype.sum_equiv unitsEquivNeZero
      intro u
      rfl

private theorem cyclicDFT_primitivePower_eq_gaussSum
    {F : Type*} [Field F] [Fintype F] [NeZero (Fintype.card F - 1)]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    (ψ : AddChar F ℂ) (μ : ZMod (Fintype.card F - 1)) :
    cyclicDFT (fun j => ψ
      (((primitivePowerEquiv α hα j).toMul : Fˣ) : F)) μ =
        gaussSum (primitivePowerMulChar α hα μ) ψ := by
  letI := Fintype.ofFinite Fˣ
  letI := Fintype.ofFinite (Additive Fˣ)
  rw [gaussSum_eq_sum_units]
  simp only [cyclicDFT]
  apply Fintype.sum_equiv
    ((primitivePowerEquiv α hα).toEquiv.trans Additive.toMul)
  intro j
  change (((AddChar.zmod (Fintype.card F - 1) μ j : Circle) : ℂ) * _) =
    primitivePowerMulChar α hα μ
      (((primitivePowerEquiv α hα j).toMul : Fˣ) : F) * _
  rw [primitivePowerMulChar_apply_powerEquiv]
  rfl

private theorem primitivePowerMulChar_zero
    {F : Type*} [Field F] [Fintype F] [NeZero (Fintype.card F - 1)]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1)) :
    primitivePowerMulChar α hα 0 = 1 := by
  apply MulChar.ext
  intro u
  let j := (primitivePowerEquiv α hα).symm (Additive.ofMul u)
  have h := primitivePowerMulChar_apply_powerEquiv α hα 0 j
  simp only [AddChar.zmod_zero, AddChar.one_apply] at h
  simpa [j] using h

private theorem primitivePowerMulChar_ne_one_of_ne_zero
    {F : Type*} [Field F] [Fintype F] [NeZero (Fintype.card F - 1)]
    (α : F) (hα : IsPrimitiveRoot α (Fintype.card F - 1))
    {μ : ZMod (Fintype.card F - 1)} (hμ : μ ≠ 0) :
    primitivePowerMulChar α hα μ ≠ 1 := by
  intro hχ
  have hz : AddChar.zmodAddEquiv μ = AddChar.zmodAddEquiv 0 := by
    apply AddChar.ext
    intro j
    have hval := DFunLike.congr_fun hχ
      ((((primitivePowerEquiv α hα j).toMul : Fˣ) : F))
    rw [primitivePowerMulChar_apply_powerEquiv] at hval
    change (((AddChar.zmod (Fintype.card F - 1) μ j : Circle) : ℂ)) =
      (((AddChar.zmod (Fintype.card F - 1) 0 j : Circle) : ℂ))
    simpa using hval
  exact hμ (AddChar.zmodAddEquiv.injective hz)

private theorem cyclicInterval_eq_phase_mul_geom
    {N : ℕ} [NeZero N] (μ start : ZMod N) (H : ℕ) :
    (∑ k ∈ Finset.range H,
      AddChar.zmodAddEquiv μ (-(start + (k : ZMod N)))) =
      AddChar.zmodAddEquiv μ (-start) *
        ∑ k ∈ Finset.range H,
          (AddChar.zmodAddEquiv μ (-1)) ^ k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    AddChar.zmodAddEquiv μ (-(start + (k : ZMod N))) =
        AddChar.zmodAddEquiv μ (-start + -(k : ZMod N)) := by
      congr 2
      simp only [neg_add_rev]
      ac_rfl
    _ = AddChar.zmodAddEquiv μ (-start) *
        AddChar.zmodAddEquiv μ (-(k : ZMod N)) :=
      (AddChar.zmodAddEquiv μ).map_add_eq_mul _ _
    _ = AddChar.zmodAddEquiv μ (-start) *
        (AddChar.zmodAddEquiv μ (-1)) ^ k := by
      rw [show -(k : ZMod N) = k • (-1 : ZMod N) by simp [nsmul_eq_mul],
        AddChar.map_nsmul_eq_pow]

private theorem norm_one_sub_zmod_natCast_neg_one
    (N r : ℕ) [NeZero N] (hr : r ≤ N / 2) :
    ‖(1 : ℂ) - AddChar.zmodAddEquiv (r : ZMod N) (-1)‖ =
      2 * Real.sin (Real.pi * r / N) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hangle0 : 0 ≤ Real.pi * (r : ℝ) / N := by positivity
  have hangleHalf : Real.pi * (r : ℝ) / N ≤ Real.pi / 2 := by
    have htwice : 2 * r ≤ N := by omega
    have hcast : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast htwice
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin (Real.pi * (r : ℝ) / N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hangle0 (hangleHalf.trans (by linarith [Real.pi_pos]))
  change ‖(1 : ℂ) -
    (((AddChar.zmod N (r : ZMod N) (-1 : ZMod N) : Circle) : ℂ))‖ = _
  have hzCircle := AddChar.zmod_intCast N (r : ℤ) (-1 : ℤ)
  have hzComplex := congrArg (fun z : Circle => (z : ℂ)) hzCircle
  simp only [Circle.coe_exp, Int.cast_natCast, Int.cast_neg, Int.cast_one] at hzComplex
  rw [hzComplex]
  rw [norm_sub_rev]
  have hform :
      ((2 * Real.pi * ((r : ℝ) * (-1 : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I =
        Complex.I * ((-(2 * Real.pi * (r : ℝ) / N) : ℝ) : ℂ) := by
    ring_nf
  rw [hform, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : -(2 * Real.pi * (r : ℝ) / N) / 2 =
      -(Real.pi * (r : ℝ) / N) := by ring_nf
  rw [hhalf, Real.sin_neg]
  rw [show 2 * -Real.sin (Real.pi * (r : ℝ) / N) =
    -(2 * Real.sin (Real.pi * (r : ℝ) / N)) by ring_nf]
  rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]

private theorem four_mul_div_le_norm_one_sub_zmod_natCast_neg_one
    (N r : ℕ) [NeZero N] (hr : r ≤ N / 2) :
    4 * (r : ℝ) / N ≤
      ‖(1 : ℂ) - AddChar.zmodAddEquiv (r : ZMod N) (-1)‖ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have htwice : 2 * r ≤ N := by omega
  have hangle0 : 0 ≤ Real.pi * (r : ℝ) / N := by positivity
  have hangleHalf : Real.pi * (r : ℝ) / N ≤ Real.pi / 2 := by
    have hcast : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast htwice
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
    nlinarith [Real.pi_pos]
  rw [norm_one_sub_zmod_natCast_neg_one N r hr]
  have hjordan := Real.mul_le_sin hangle0 hangleHalf
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hjordan ⊢
  nlinarith [Real.pi_pos]

private theorem cyclicInterval_norm_le_natCast
    (N r H : ℕ) [NeZero N] (hr0 : 0 < r) (hr : r ≤ N / 2)
    (start : ZMod N) :
    ‖∑ k ∈ Finset.range H,
      AddChar.zmodAddEquiv (r : ZMod N) (-(start + (k : ZMod N)))‖ ≤
        (N : ℝ) / (2 * r) := by
  let z : ℂ := AddChar.zmodAddEquiv (r : ZMod N) (-1)
  let G : ℂ := ∑ k ∈ Finset.range H, z ^ k
  have hphase := cyclicInterval_eq_phase_mul_geom (r : ZMod N) start H
  have hnormPhase :
      ‖∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv (r : ZMod N) (-(start + (k : ZMod N)))‖ = ‖G‖ := by
    rw [hphase, norm_mul, AddChar.norm_apply, one_mul]
  rw [hnormPhase]
  have hgeom := geom_sum_mul_neg z H
  change G * (1 - z) = 1 - z ^ H at hgeom
  have hnormGeom := congrArg norm hgeom
  rw [norm_mul] at hnormGeom
  have hzNorm : ‖z‖ = 1 := by
    exact AddChar.norm_apply _ _
  have hnum : ‖(1 : ℂ) - z ^ H‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - z ^ H‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ H‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, norm_pow, hzNorm, one_pow]; norm_num
  have hdenLower : 4 * (r : ℝ) / N ≤ ‖(1 : ℂ) - z‖ := by
    exact four_mul_div_le_norm_one_sub_zmod_natCast_neg_one N r hr
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hNReal : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbasePos : 0 < 4 * (r : ℝ) / N := by positivity
  have hdenPos : 0 < ‖(1 : ℂ) - z‖ :=
    lt_of_lt_of_le hbasePos hdenLower
  have hG : ‖G‖ ≤ 2 / ‖(1 : ℂ) - z‖ := by
    rw [le_div_iff₀ hdenPos]
    rw [hnormGeom]
    exact hnum
  calc
    ‖G‖ ≤ 2 / ‖(1 : ℂ) - z‖ := hG
    _ ≤ 2 / (4 * (r : ℝ) / N) := by
      exact div_le_div_of_nonneg_left (by norm_num) hbasePos hdenLower
    _ = (N : ℝ) / (2 * r) := by
      field_simp
      ring_nf

private theorem cyclicInterval_norm_le_neg_natCast
    (N r H : ℕ) [NeZero N] (hr0 : 0 < r) (hr : r ≤ N / 2)
    (start : ZMod N) :
    ‖∑ k ∈ Finset.range H,
      AddChar.zmodAddEquiv (-(r : ZMod N)) (-(start + (k : ZMod N)))‖ ≤
        (N : ℝ) / (2 * r) := by
  have hsum :
      (∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv (-(r : ZMod N)) (-(start + (k : ZMod N)))) =
      starRingEnd ℂ (∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv (r : ZMod N) (-(start + (k : ZMod N)))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hchar : AddChar.zmodAddEquiv (-(r : ZMod N)) =
        -(AddChar.zmodAddEquiv (r : ZMod N)) :=
      AddEquiv.map_neg AddChar.zmodAddEquiv (r : ZMod N)
    rw [hchar, AddChar.neg_apply]
    exact AddChar.map_neg_eq_conj
      (AddChar.zmodAddEquiv (r : ZMod N)) (-(start + (k : ZMod N)))
  rw [hsum, Complex.norm_conj]
  exact cyclicInterval_norm_le_natCast N r H hr0 hr start

private def oddNonzeroZModParam (m : ℕ) :
    Fin m ⊕ Fin m → {μ : ZMod (2 * m + 1) // μ ≠ 0}
  | Sum.inl i => ⟨((i.1 + 1 : ℕ) : ZMod (2 * m + 1)), by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < 2 * m + 1)] at hv
      simp at hv⟩
  | Sum.inr i => ⟨-((i.1 + 1 : ℕ) : ZMod (2 * m + 1)), by
      exact neg_ne_zero.mpr (by
        intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < 2 * m + 1)] at hv
        simp at hv)⟩

private theorem oddNonzeroZModParam_bijective (m : ℕ) :
    Function.Bijective (oddNonzeroZModParam m) := by
  let N := 2 * m + 1
  have hN : 0 < N := by omega
  letI : NeZero N := ⟨hN.ne'⟩
  have hcastNe (i : Fin m) : ((i.1 + 1 : ℕ) : ZMod N) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < N)] at hv
    simp at hv
  have hnegVal (i : Fin m) : (-((i.1 + 1 : ℕ) : ZMod N)).val = N - (i.1 + 1) := by
    rw [ZMod.neg_val, if_neg (hcastNe i),
      ZMod.val_cast_of_lt (by omega : i.1 + 1 < N)]
  constructor
  · intro a b hab
    apply Subtype.ext_iff.mp at hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            congr 1
            have hv := congrArg ZMod.val hab
            simp only [oddNonzeroZModParam] at hv
            rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < N),
              ZMod.val_cast_of_lt (by omega : j.1 + 1 < N)] at hv
            omega
        | inr j =>
            have hv := congrArg ZMod.val hab
            simp only [oddNonzeroZModParam] at hv
            rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < N), hnegVal j] at hv
            exfalso
            omega
    | inr i =>
        cases b with
        | inl j =>
            have hv := congrArg ZMod.val hab
            simp only [oddNonzeroZModParam] at hv
            rw [hnegVal i, ZMod.val_cast_of_lt (by omega : j.1 + 1 < N)] at hv
            exfalso
            omega
        | inr j =>
            congr 1
            have hv := congrArg ZMod.val hab
            simp only [oddNonzeroZModParam] at hv
            rw [hnegVal i, hnegVal j] at hv
            omega
  · intro μ
    let v := μ.1.val
    have hvPos : 0 < v := by
      exact Nat.pos_of_ne_zero fun hv => μ.2 ((ZMod.val_eq_zero μ.1).mp hv)
    have hvLt : v < N := ZMod.val_lt μ.1
    by_cases hv : v ≤ m
    · let i : Fin m := ⟨v - 1, by omega⟩
      refine ⟨Sum.inl i, ?_⟩
      apply Subtype.ext
      apply ZMod.val_injective
      simp only [oddNonzeroZModParam]
      rw [ZMod.val_cast_of_lt (by omega : i.1 + 1 < N)]
      simp only [i, v]
      omega
    · let r := N - v
      have hrPos : 0 < r := by omega
      have hrLe : r ≤ m := by omega
      let i : Fin m := ⟨r - 1, by omega⟩
      refine ⟨Sum.inr i, ?_⟩
      apply Subtype.ext
      apply ZMod.val_injective
      simp only [oddNonzeroZModParam]
      rw [hnegVal i]
      simp only [i, r, v]
      omega

private noncomputable def oddNonzeroZModEquiv (m : ℕ) :
    Fin m ⊕ Fin m ≃ {μ : ZMod (2 * m + 1) // μ ≠ 0} :=
  Equiv.ofBijective (oddNonzeroZModParam m) (oddNonzeroZModParam_bijective m)

private theorem sum_nonzero_cyclicInterval_norm_le_harmonic
    (m H : ℕ) (start : ZMod (2 * m + 1)) :
    (∑ μ : {μ : ZMod (2 * m + 1) // μ ≠ 0},
      ‖∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv μ.1 (-(start + (k : ZMod (2 * m + 1))))‖) ≤
      (2 * m + 1 : ℝ) *
        ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
  let N := 2 * m + 1
  have hN : 0 < N := by omega
  letI : NeZero N := ⟨hN.ne'⟩
  let bound : Fin m → ℝ := fun i => (N : ℝ) / (2 * (i.1 + 1))
  calc
    (∑ μ : {μ : ZMod N // μ ≠ 0},
      ‖∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv μ.1 (-(start + (k : ZMod N)))‖) =
        ∑ s : Fin m ⊕ Fin m,
          ‖∑ k ∈ Finset.range H,
            AddChar.zmodAddEquiv (oddNonzeroZModEquiv m s).1
              (-(start + (k : ZMod N)))‖ := by
      symm
      apply Fintype.sum_equiv (oddNonzeroZModEquiv m)
      intro s
      rfl
    _ = (∑ i : Fin m,
          ‖∑ k ∈ Finset.range H,
            AddChar.zmodAddEquiv ((i.1 + 1 : ℕ) : ZMod N)
              (-(start + (k : ZMod N)))‖) +
        ∑ i : Fin m,
          ‖∑ k ∈ Finset.range H,
            AddChar.zmodAddEquiv (-((i.1 + 1 : ℕ) : ZMod N))
              (-(start + (k : ZMod N)))‖ := by
      rw [Fintype.sum_sum_type]
      rfl
    _ ≤ (∑ i : Fin m, bound i) + ∑ i : Fin m, bound i := by
      apply add_le_add <;> apply Finset.sum_le_sum <;> intro i hi
      · simpa [bound, Nat.cast_add, Nat.cast_one] using
          cyclicInterval_norm_le_natCast N (i.1 + 1) H (by omega)
            (by simp [N]; omega) start
      · simpa [bound, Nat.cast_add, Nat.cast_one] using
          cyclicInterval_norm_le_neg_natCast N (i.1 + 1) H (by omega)
            (by simp [N]; omega) start
    _ = (2 * m + 1 : ℝ) *
        ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
      have hsumFin :
          (∑ i : Fin m, bound i) =
            ∑ k ∈ Finset.range m, (N : ℝ) / (2 * ((k : ℝ) + 1)) := by
        simpa [bound, Nat.cast_add, Nat.cast_one] using
          Fin.sum_univ_eq_sum_range
            (fun k : ℕ => (N : ℝ) / (2 * ((k : ℝ) + 1))) m
      rw [hsumFin]
      have hfactor :
          (∑ k ∈ Finset.range m, (N : ℝ) / (2 * ((k : ℝ) + 1))) =
            (N : ℝ) / 2 *
              ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        field_simp
      rw [hfactor]
      dsimp [N]
      push_cast
      ring_nf

private theorem sum_nonzero_cyclicInterval_norm_le_harmonic_of_eq
    {N : ℕ} [NeZero N] (m H : ℕ) (hN : N = 2 * m + 1)
    (start : ZMod N) :
    (∑ μ : {μ : ZMod N // μ ≠ 0},
      ‖∑ k ∈ Finset.range H,
        AddChar.zmodAddEquiv μ.1 (-(start + (k : ZMod N)))‖) ≤
      (N : ℝ) * ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
  subst N
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    sum_nonzero_cyclicInterval_norm_le_harmonic m H start

private theorem cyclicInterval_sum_eq_dft
    {N H : ℕ} [NeZero N] (a : ZMod N → ℂ) (start : ZMod N) :
    (∑ k ∈ Finset.range H, a (start + (k : ZMod N))) =
      (N : ℂ)⁻¹ * ∑ μ : ZMod N,
        cyclicDFT a μ *
          ∑ k ∈ Finset.range H,
            AddChar.zmodAddEquiv μ (-(start + (k : ZMod N))) := by
  calc
    (∑ k ∈ Finset.range H, a (start + (k : ZMod N))) =
        ∑ k ∈ Finset.range H,
          (N : ℂ)⁻¹ * ∑ μ : ZMod N,
            AddChar.zmodAddEquiv μ (-(start + (k : ZMod N))) * cyclicDFT a μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact cyclicDFT_inversion a (start + (k : ZMod N))
    _ = (N : ℂ)⁻¹ * ∑ k ∈ Finset.range H,
          ∑ μ : ZMod N,
            AddChar.zmodAddEquiv μ (-(start + (k : ZMod N))) * cyclicDFT a μ := by
      rw [Finset.mul_sum]
    _ = (N : ℂ)⁻¹ * ∑ μ : ZMod N,
          cyclicDFT a μ *
            ∑ k ∈ Finset.range H,
              AddChar.zmodAddEquiv μ (-(start + (k : ZMod N))) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring_nf

private theorem binaryField_incompleteCharacterSum_norm_le_harmonic
    {n : ℕ} (hn : 2 ≤ n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1))
    {ψ : AddChar (BinaryGaloisField n) ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ k ∈ Finset.range (2 ^ (n - 1)),
      ψ (α ^ ((2 ^ (n - 1) - 1) + k))‖ ≤
      1 + Real.sqrt (2 ^ n : ℝ) *
        ∑ k ∈ Finset.range (2 ^ (n - 1) - 1), (1 : ℝ) / (k + 1) := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  let F := BinaryGaloisField n
  letI : Fintype F := Fintype.ofFinite F
  let H := 2 ^ (n - 1)
  let m := H - 1
  let N := 2 ^ n - 1
  have hn0 : n ≠ 0 := by omega
  have hHPos : 0 < H := Nat.two_pow_pos (n - 1)
  have hpow : 2 ^ n = 2 * H := by
    have hnSplit : n = (n - 1) + 1 := by omega
    rw [hnSplit, pow_succ]
    simp [H, Nat.mul_comm]
  have hN : N = 2 * m + 1 := by omega
  have hfieldCard : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]
  have hcardOrder : Fintype.card F - 1 = N := by omega
  letI := Fintype.ofFinite Fˣ
  letI := Fintype.ofFinite (Additive Fˣ)
  letI : NeZero (Fintype.card F - 1) :=
    ⟨by rw [hcardOrder, hN]; omega⟩
  have hαCard : IsPrimitiveRoot α (Fintype.card F - 1) := by
    simpa [hcardOrder] using hα
  let a : ZMod (Fintype.card F - 1) → ℂ := fun j =>
    ψ ((((primitivePowerEquiv α hαCard j).toMul : Fˣ) : F))
  let start : ZMod (Fintype.card F - 1) := (m : ℕ)
  let C : ZMod (Fintype.card F - 1) → ℂ := fun μ =>
    ∑ k ∈ Finset.range H,
      AddChar.zmodAddEquiv μ (-(start + (k : ZMod (Fintype.card F - 1))))
  have hinterval :
      (∑ k ∈ Finset.range H, ψ (α ^ (m + k))) =
        ∑ k ∈ Finset.range H, a (start + (k : ZMod (Fintype.card F - 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hp := primitivePowerEquiv_natCast α hαCard (m + k)
    change ψ (α ^ (m + k)) = ψ
      ((((primitivePowerEquiv α hαCard
        (start + (k : ZMod (Fintype.card F - 1)))).toMul : Fˣ) : F))
    rw [show start + (k : ZMod (Fintype.card F - 1)) =
      ((m + k : ℕ) : ZMod (Fintype.card F - 1)) by
        change (m : ZMod (Fintype.card F - 1)) + (k : ZMod (Fintype.card F - 1)) = _
        norm_num]
    exact (congrArg (fun u : Fˣ => ψ (u : F)) hp).symm
  have hDFT :
      (∑ k ∈ Finset.range H, a (start + (k : ZMod (Fintype.card F - 1)))) =
        (((Fintype.card F - 1 : ℕ) : ℂ))⁻¹ *
          ∑ μ : ZMod (Fintype.card F - 1), cyclicDFT a μ * C μ := by
    exact cyclicInterval_sum_eq_dft a start
  rw [show 2 ^ (n - 1) = H by rfl, show 2 ^ (n - 1) - 1 = m by rfl]
  rw [hinterval, hDFT, norm_mul]
  have horderReal : (0 : ℝ) < ((Fintype.card F - 1 : ℕ) : ℝ) := by
    rw [hcardOrder, hN]
    positivity
  have hscale : ‖((((Fintype.card F - 1 : ℕ) : ℂ))⁻¹)‖ =
      (((Fintype.card F - 1 : ℕ) : ℝ))⁻¹ := by
    simp
  rw [hscale]
  have hψNe : ψ ≠ 1 := by
    simpa using hψ (one_ne_zero : (1 : F) ≠ 0)
  have hDZero : cyclicDFT a 0 = -1 := by
    rw [cyclicDFT_primitivePower_eq_gaussSum α hαCard ψ]
    rw [primitivePowerMulChar_zero, gaussSum_one_left hψNe]
  have hCZero : C 0 = H := by
    have hz : AddChar.zmodAddEquiv
        (0 : ZMod (Fintype.card F - 1)) = 0 :=
      AddEquiv.map_zero
        (AddChar.zmodAddEquiv : ZMod (Fintype.card F - 1) ≃+
          AddChar (ZMod (Fintype.card F - 1)) ℂ)
    change (∑ k ∈ Finset.range H,
      AddChar.zmodAddEquiv (0 : ZMod (Fintype.card F - 1))
        (-(start + (k : ZMod (Fintype.card F - 1))))) = (H : ℂ)
    rw [hz]
    simp
  have hDNonzero (μ : {μ : ZMod (Fintype.card F - 1) // μ ≠ 0}) :
      ‖cyclicDFT a μ.1‖ = Real.sqrt (Fintype.card F : ℝ) := by
    rw [cyclicDFT_primitivePower_eq_gaussSum α hαCard ψ]
    exact norm_gaussSum_eq_sqrt_card _
      (primitivePowerMulChar_ne_one_of_ne_zero α hαCard μ.2) _ hψ
  have hsumSplit :
      (∑ μ : ZMod (Fintype.card F - 1), ‖cyclicDFT a μ * C μ‖) =
        H + ∑ μ : {μ : ZMod (Fintype.card F - 1) // μ ≠ 0},
          ‖cyclicDFT a μ.1 * C μ.1‖ := by
    have herase := Finset.sum_erase_add
      (Finset.univ : Finset (ZMod (Fintype.card F - 1)))
      (fun μ => ‖cyclicDFT a μ * C μ‖) (Finset.mem_univ 0)
    have hsubtype :
        (∑ μ ∈ (Finset.univ.erase 0), ‖cyclicDFT a μ * C μ‖) =
          ∑ μ : {μ : ZMod (Fintype.card F - 1) // μ ≠ 0},
            ‖cyclicDFT a μ.1 * C μ.1‖ := by
      apply Finset.sum_subtype
      intro μ
      simp
    rw [hsubtype] at herase
    have hzeroTerm : ‖cyclicDFT a 0 * C 0‖ = (H : ℝ) := by
      simp [hDZero, hCZero]
    rw [hzeroTerm] at herase
    simpa [add_comm] using herase.symm
  have htriangle :
      ‖∑ μ : ZMod (Fintype.card F - 1), cyclicDFT a μ * C μ‖ ≤
        ∑ μ : ZMod (Fintype.card F - 1), ‖cyclicDFT a μ * C μ‖ := by
    simpa using norm_sum_le (Finset.univ : Finset (ZMod (Fintype.card F - 1)))
      (fun μ => cyclicDFT a μ * C μ)
  calc
    (((Fintype.card F - 1 : ℕ) : ℝ))⁻¹ *
        ‖∑ μ : ZMod (Fintype.card F - 1), cyclicDFT a μ * C μ‖ ≤
      (((Fintype.card F - 1 : ℕ) : ℝ))⁻¹ *
        ∑ μ : ZMod (Fintype.card F - 1), ‖cyclicDFT a μ * C μ‖ :=
      mul_le_mul_of_nonneg_left htriangle (by positivity)
    _ = (((Fintype.card F - 1 : ℕ) : ℝ))⁻¹ *
        (H + Real.sqrt (Fintype.card F : ℝ) *
          ∑ μ : {μ : ZMod (Fintype.card F - 1) // μ ≠ 0}, ‖C μ.1‖) := by
      rw [hsumSplit]
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [norm_mul, hDNonzero]
    _ ≤ (((Fintype.card F - 1 : ℕ) : ℝ))⁻¹ *
        (H + Real.sqrt (Fintype.card F : ℝ) *
          (((Fintype.card F - 1 : ℕ) : ℝ) *
            ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1))) := by
      apply mul_le_mul_of_nonneg_left
      · gcongr
        simpa [C] using
          sum_nonzero_cyclicInterval_norm_le_harmonic_of_eq m H
            (hcardOrder.trans hN) start
      · positivity
    _ ≤ 1 + Real.sqrt (2 ^ n : ℝ) *
        ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
      rw [hcardOrder, hfieldCard]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      have hNReal : (0 : ℝ) < N := by rw [hN]; positivity
      have hHle : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : H ≤ N)
      have hcancel :
          (N : ℝ)⁻¹ * (H + Real.sqrt (2 ^ n : ℝ) *
            ((N : ℝ) * ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1))) =
          (H : ℝ) / N + Real.sqrt (2 ^ n : ℝ) *
            ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := by
        let S : ℝ := ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1)
        change (N : ℝ)⁻¹ * (H + Real.sqrt (2 ^ n : ℝ) * ((N : ℝ) * S)) =
          (H : ℝ) / N + Real.sqrt (2 ^ n : ℝ) * S
        field_simp [ne_of_gt hNReal]
      rw [hcancel]
      simpa [add_comm] using
        add_le_add_right ((div_le_one hNReal).mpr hHle)
          (Real.sqrt (2 ^ n : ℝ) *
            ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1))

private theorem binaryField_incompleteCharacterSum_norm_le
    {n : ℕ} (hn : 2 ≤ n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1))
    {ψ : AddChar (BinaryGaloisField n) ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ k ∈ Finset.range (2 ^ (n - 1)),
      ψ (α ^ ((2 ^ (n - 1) - 1) + k))‖ ≤
      1 + (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ) := by
  let H := 2 ^ (n - 1)
  let m := H - 1
  let N := 2 ^ n - 1
  have hHPos : 0 < H := Nat.two_pow_pos (n - 1)
  have hpow : 2 ^ n = 2 * H := by
    have hnSplit : n = (n - 1) + 1 := by omega
    rw [hnSplit, pow_succ]
    simp [H, Nat.mul_comm]
  have hN : N = 2 * m + 1 := by omega
  have hsum := binaryField_incompleteCharacterSum_norm_le_harmonic hn hα hψ
  rw [show 2 ^ (n - 1) = H by rfl, show 2 ^ (n - 1) - 1 = m by rfl] at hsum ⊢
  have hharm := harmonic_sum_le_log_odd m
  have hNPos : 0 < N := by rw [hN]; omega
  have hNLe : N ≤ 2 ^ n := by omega
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hNPos)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact_mod_cast hNLe
  rw [Real.log_pow] at hlogN
  have hharmN :
      (∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1)) ≤
        (n : ℝ) * Real.log 2 := by
    calc
      _ ≤ Real.log (2 * (m : ℝ) + 1) := hharm
      _ = Real.log (N : ℝ) := by
        congr 2
        rw [hN]
        push_cast
        rfl
      _ ≤ (n : ℝ) * Real.log 2 := hlogN
  calc
    _ ≤ 1 + Real.sqrt (2 ^ n : ℝ) *
        ∑ k ∈ Finset.range m, (1 : ℝ) / (k + 1) := hsum
    _ ≤ 1 + Real.sqrt (2 ^ n : ℝ) * ((n : ℝ) * Real.log 2) := by
      gcongr
    _ = 1 + (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ) := by ring_nf

private noncomputable def absoluteTraceAddChar (n : ℕ) :
    AddChar (BinaryGaloisField n) ℂ where
  toFun x := (bitSignInt (absoluteTrace n x) : ℂ)
  map_zero_eq_one' := by simp [bitSignInt]
  map_add_eq_mul' x y := by
    rw [map_add, bitSignInt_add]
    norm_num

@[simp] private theorem absoluteTraceAddChar_apply (n : ℕ)
    (x : BinaryGaloisField n) :
    absoluteTraceAddChar n x = (bitSignInt (absoluteTrace n x) : ℂ) := rfl

private theorem absoluteTraceAddChar_isPrimitive (n : ℕ) :
    (absoluteTraceAddChar n).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  obtain ⟨x, hx⟩ := exists_absoluteTrace_eq_one n
  intro h
  have hval := DFunLike.congr_fun h x
  simp [absoluteTraceAddChar, hx, bitSignInt] at hval
  norm_num at hval

private noncomputable def carletFengComplement {n : ℕ}
    (α : BinaryGaloisField n) : Finset (BinaryGaloisField n) := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  exact Finset.univ \ carletFengSupport α

private noncomputable def carletFengComplementInterval {n : ℕ}
    (α : BinaryGaloisField n) : Finset (BinaryGaloisField n) := by
  classical
  exact (Finset.range (2 ^ (n - 1))).image
    (fun k => α ^ ((2 ^ (n - 1) - 1) + k))

private theorem carletFengSupport_compl_eq_image_interval
    {n : ℕ} (hn : 2 ≤ n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1)) :
    carletFengComplement α =
      carletFengComplementInterval α := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  change (Finset.univ \ carletFengSupport α) =
    (Finset.range (2 ^ (n - 1))).image
      (fun k => α ^ ((2 ^ (n - 1) - 1) + k))
  let H := 2 ^ (n - 1)
  let m := H - 1
  let N := 2 ^ n - 1
  have hn0 : n ≠ 0 := by omega
  have hHPos : 0 < H := Nat.two_pow_pos (n - 1)
  have hpow : 2 ^ n = 2 * H := by
    have hnSplit : n = (n - 1) + 1 := by omega
    rw [hnSplit, pow_succ]
    simp [H, Nat.mul_comm]
  have hsubset :
      (Finset.range H).image (fun k => α ^ (m + k)) ⊆
        Finset.univ \ carletFengSupport α := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact pow_not_mem_carletFengSupport_of_mem_interval hn hα
      (by simp only [Finset.mem_range] at hk; omega)
      (by simp only [Finset.mem_range] at hk; omega)
  have hinj : Set.InjOn (fun k : ℕ => α ^ (m + k)) (Finset.range H : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    have hmi : m + i < N := by omega
    have hmj : m + j < N := by omega
    exact Nat.add_left_cancel (hα.pow_inj hmi hmj hij)
  have hImageCard :
      ((Finset.range H).image (fun k => α ^ (m + k))).card = H := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hComplCard : (Finset.univ \ carletFengSupport α).card = H := by
    have hfieldCard : Fintype.card (BinaryGaloisField n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      hfieldCard, carletFengSupport_card hn hα]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hComplCard, hImageCard])
  simpa [H, m] using heq.symm

private theorem cast_walshTransform_carletFeng_eq_two_mul_complementSum
    {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (α : BinaryGaloisField n)
    (u : FABL.F₂Cube n) (b : BinaryGaloisField n) (hb : b ≠ 0)
    (hpair : ∀ x, FABL.f₂DotProduct u x = absoluteTrace n (b * θ x)) :
    ((walshTransform (carletFengBooleanFunction θ α) u : ℤ) : ℂ) =
      2 * ∑ y ∈ carletFengComplement α,
        (absoluteTraceAddChar n).mulShift b y := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  let ψ := (absoluteTraceAddChar n).mulShift b
  have hψNe : ψ ≠ 1 := (absoluteTraceAddChar_isPrimitive n) hb
  have htotal : ∑ y : BinaryGaloisField n, ψ y = 0 :=
    AddChar.sum_eq_zero_of_ne_one hψNe
  have hpoint (y : BinaryGaloisField n) :
      (bitSignInt (carletFengFieldFunction α y + absoluteTrace n (b * y)) : ℂ) =
        if y ∈ carletFengSupport α then -ψ y else ψ y := by
    rw [bitSignInt_add]
    by_cases hy : y ∈ carletFengSupport α
    · simp [carletFengFieldFunction, hy, ψ, absoluteTraceAddChar, bitSignInt]
    · simp [carletFengFieldFunction, hy, ψ, absoluteTraceAddChar, bitSignInt]
  have htransport :
      ((walshTransform (carletFengBooleanFunction θ α) u : ℤ) : ℂ) =
        ∑ y : BinaryGaloisField n,
          if y ∈ carletFengSupport α then -ψ y else ψ y := by
    simp only [walshTransform, walshTerm, Int.cast_sum]
    calc
      (∑ x : FABL.F₂Cube n,
          (bitSignInt
            (carletFengBooleanFunction θ α x + FABL.f₂DotProduct u x) : ℂ)) =
          ∑ x : FABL.F₂Cube n,
            (bitSignInt
              (carletFengFieldFunction α (θ x) + absoluteTrace n (b * θ x)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hpair]
        rfl
      _ = ∑ x : FABL.F₂Cube n,
          if θ x ∈ carletFengSupport α then -ψ (θ x) else ψ (θ x) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint (θ x)
      _ = ∑ y : BinaryGaloisField n,
          if y ∈ carletFengSupport α then -ψ y else ψ y :=
        Equiv.sum_comp θ.toEquiv
          (fun y : BinaryGaloisField n =>
            if y ∈ carletFengSupport α then -ψ y else ψ y)
  rw [htransport]
  have hpartition := Finset.sum_compl_add_sum (carletFengSupport α) ψ
  rw [htotal] at hpartition
  change (∑ y : BinaryGaloisField n,
      if y ∈ carletFengSupport α then -ψ y else ψ y) = _
  rw [Finset.sum_ite]
  have hmemFilter :
      (Finset.univ.filter fun y : BinaryGaloisField n => y ∈ carletFengSupport α) =
        carletFengSupport α := by
    ext y
    simp
  have hnotMemFilter :
      (Finset.univ.filter fun y : BinaryGaloisField n => y ∉ carletFengSupport α) =
        carletFengComplement α := by
    ext y
    simp [carletFengComplement]
  rw [hmemFilter, hnotMemFilter, Finset.sum_neg_distrib]
  change -(∑ y ∈ carletFengSupport α, ψ y) +
      ∑ y ∈ carletFengComplement α, ψ y =
    2 * ∑ y ∈ carletFengComplement α, ψ y
  have hpartition' :
      (∑ y ∈ carletFengComplement α, ψ y) +
        ∑ y ∈ carletFengSupport α, ψ y = 0 := by
    have hcompl : carletFengComplement α = (carletFengSupport α)ᶜ := by
      ext y
      simp [carletFengComplement]
    rw [hcompl]
    exact hpartition
  have hnegSupport :
      -(∑ y ∈ carletFengSupport α, ψ y) =
        ∑ y ∈ carletFengComplement α, ψ y :=
    neg_eq_of_add_eq_zero_left hpartition'
  rw [hnegSupport, two_mul]

private theorem sum_carletFengComplement_eq_interval
    {n : ℕ} (hn : 2 ≤ n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1))
    (g : BinaryGaloisField n → ℂ) :
    (∑ y ∈ carletFengComplement α, g y) =
      ∑ k ∈ Finset.range (2 ^ (n - 1)),
        g (α ^ ((2 ^ (n - 1) - 1) + k)) := by
  classical
  rw [carletFengSupport_compl_eq_image_interval hn hα]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hnSplit : n = (n - 1) + 1 := by omega
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hnSplit
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  apply Finset.sum_image
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  apply Nat.add_left_cancel
  exact hα.pow_inj (by omega) (by omega) hij

private theorem cast_walshTransform_carletFeng_eq_two_mul_intervalSum
    {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1))
    (u : FABL.F₂Cube n) (b : BinaryGaloisField n) (hb : b ≠ 0)
    (hpair : ∀ x, FABL.f₂DotProduct u x = absoluteTrace n (b * θ x)) :
    ((walshTransform (carletFengBooleanFunction θ α) u : ℤ) : ℂ) =
      2 * ∑ k ∈ Finset.range (2 ^ (n - 1)),
        (absoluteTraceAddChar n).mulShift b
          (α ^ ((2 ^ (n - 1) - 1) + k)) := by
  rw [cast_walshTransform_carletFeng_eq_two_mul_complementSum θ α u b hb hpair]
  rw [sum_carletFengComplement_eq_interval hn hα]

private theorem abs_walshTransform_carletFengBooleanFunction_le
    {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1))
    (u : FABL.F₂Cube n) :
    |(walshTransform (carletFengBooleanFunction θ α) u : ℝ)| ≤
      2 * (1 + (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ)) := by
  obtain ⟨b, hpair, _⟩ := existsUnique_tracePairingCoefficient θ u
  by_cases hb : b = 0
  · subst b
    have hu : u = 0 := by
      apply (dotProductEquiv FABL.𝔽₂ (Fin n)).injective
      apply LinearMap.ext
      intro x
      change FABL.f₂DotProduct u x = FABL.f₂DotProduct 0 x
      rw [hpair x]
      simp [FABL.f₂DotProduct, zero_dotProduct]
    have hzero : walshTransform (carletFengBooleanFunction θ α) 0 = 0 :=
      (isBalanced_iff_walshTransform_zero_eq_zero _).mp
        (isBalanced_carletFengBooleanFunction hn θ hα)
    rw [hu, hzero]
    have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    simpa only [Int.cast_zero, abs_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg n) hlog)
            (Real.sqrt_nonneg (2 ^ n : ℝ))))
  · have hψNe : (absoluteTraceAddChar n).mulShift b ≠ 1 :=
      (absoluteTraceAddChar_isPrimitive n) hb
    have hψPrimitive : ((absoluteTraceAddChar n).mulShift b).IsPrimitive :=
      AddChar.IsPrimitive.of_ne_one hψNe
    have hsum := binaryField_incompleteCharacterSum_norm_le hn hα hψPrimitive
    have hwalsh :=
      cast_walshTransform_carletFeng_eq_two_mul_intervalSum
        hn θ hα u b hb hpair
    calc
      |(walshTransform (carletFengBooleanFunction θ α) u : ℝ)| =
          ‖((walshTransform (carletFengBooleanFunction θ α) u : ℤ) : ℂ)‖ :=
        (Complex.norm_intCast _).symm
      _ = ‖2 * ∑ k ∈ Finset.range (2 ^ (n - 1)),
          (absoluteTraceAddChar n).mulShift b
            (α ^ ((2 ^ (n - 1) - 1) + k))‖ := congrArg norm hwalsh
      _ = 2 * ‖∑ k ∈ Finset.range (2 ^ (n - 1)),
          (absoluteTraceAddChar n).mulShift b
            (α ^ ((2 ^ (n - 1) - 1) + k))‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 2 * (1 + (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ)) := by
        gcongr

/-- The real embedding of every Walsh magnitude of the Carlet--Feng function is bounded by
the logarithmic incomplete-character-sum estimate. -/
theorem maxWalshMagnitude_carletFengBooleanFunction_cast_le
    {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1)) :
    (maxWalshMagnitude (carletFengBooleanFunction θ α) : ℝ) ≤
      2 * (1 + (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ)) := by
  classical
  rw [maxWalshMagnitude, Nat.cast_finsetSup']
  apply Finset.sup'_le
  intro u _hu
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact abs_walshTransform_carletFengBooleanFunction_le hn θ hα u

/-- The survey's logarithmic lower bound for the nonlinearity of the Carlet--Feng function. -/
theorem nonlinearity_carletFengBooleanFunction_lower_bound
    {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {α : BinaryGaloisField n} (hα : IsPrimitiveRoot α (2 ^ n - 1)) :
    (2 ^ (n - 1) : ℝ) -
        (n : ℝ) * Real.log 2 * Real.sqrt (2 ^ n : ℝ) - 1 ≤
      (nonlinearity (carletFengBooleanFunction θ α) : ℝ) := by
  have hmax := maxWalshMagnitude_carletFengBooleanFunction_cast_le hn θ hα
  have hnSplit : n = (n - 1) + 1 := by omega
  have hpowNat : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hnSplit
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
  have hpowReal : (2 ^ n : ℝ) / 2 = (2 ^ (n - 1) : ℝ) := by
    rw [show (2 ^ n : ℝ) = (2 ^ (n - 1) * 2 : ℕ) by exact_mod_cast hpowNat]
    push_cast
    ring_nf
  rw [nonlinearity_cast_eq_relation_35, hpowReal]
  linarith

end

end CryptBoolean
