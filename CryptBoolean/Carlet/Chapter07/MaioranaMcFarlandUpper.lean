/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.DirectSum
public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarland

/-!
# Upper nonlinearity bound for general Maiorana--McFarland functions

Carlet Relation (62), obtained from Parseval on the fibers of the frequency
map.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

private def maioranaMcFarlandFiberSignedIndicator
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    FABL.F₂Cube s → ℝ :=
  fun y ↦ if φ y = a then (bitSignInt (g y) : ℝ) else 0

private theorem rawFourierTransform_maioranaMcFarlandFiberSignedIndicator
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    rawFourierTransform
        (maioranaMcFarlandFiberSignedIndicator φ g a) b =
      (maioranaMcFarlandFiberCharacterSum φ g a b : ℝ) := by
  classical
  rw [rawFourierTransform, maioranaMcFarlandFiberCharacterSum,
    Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hφ : φ y = a
  · simp only [hφ, if_true,
      maioranaMcFarlandFiberSignedIndicator,
      FABL.vectorWalshCharacter_apply]
    rw [← bitSignInt_cast, ← Int.cast_mul, ← bitSignInt_add]
  · simp [hφ, maioranaMcFarlandFiberSignedIndicator]

private theorem expect_sq_maioranaMcFarlandFiberSignedIndicator
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    (𝔼 y : FABL.F₂Cube s,
        maioranaMcFarlandFiberSignedIndicator φ g a y ^ 2) =
      (maioranaMcFarlandFiberCardinality φ a : ℝ) / 2 ^ s := by
  classical
  rw [Fintype.expect_eq_sum_div_card, card_f₂Cube,
    maioranaMcFarlandFiberCardinality]
  push_cast
  congr 1
  calc
    (∑ y : FABL.F₂Cube s,
        maioranaMcFarlandFiberSignedIndicator φ g a y ^ 2) =
        ∑ y with φ y = a, (1 : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hφ : φ y = a
      · simp [hφ, maioranaMcFarlandFiberSignedIndicator,
          bitSignInt_eq_if_one]
      · simp [hφ, maioranaMcFarlandFiberSignedIndicator]
    _ = (((Finset.univ : Finset (FABL.F₂Cube s)).filter
        fun y ↦ φ y = a).card : ℝ) := by simp

/-- Parseval on a fiber: the square mass of all fiber character sums is the
cube size times the fiber cardinality. -/
theorem sum_sq_maioranaMcFarlandFiberCharacterSum
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    (∑ b : FABL.F₂Cube s,
        (maioranaMcFarlandFiberCharacterSum φ g a b : ℝ) ^ 2) =
      (2 ^ s : ℝ) * maioranaMcFarlandFiberCardinality φ a := by
  let F := maioranaMcFarlandFiberSignedIndicator φ g a
  have hparseval := FABL.vector_plancherel F F
  have hscale (b : FABL.F₂Cube s) :
      rawFourierTransform F b =
        (2 ^ s : ℝ) * FABL.vectorFourierCoeff F b :=
    rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff F b
  calc
    (∑ b : FABL.F₂Cube s,
        (maioranaMcFarlandFiberCharacterSum φ g a b : ℝ) ^ 2) =
        ∑ b : FABL.F₂Cube s, rawFourierTransform F b ^ 2 := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [rawFourierTransform_maioranaMcFarlandFiberSignedIndicator]
    _ = (2 ^ s : ℝ) ^ 2 *
        ∑ b : FABL.F₂Cube s, FABL.vectorFourierCoeff F b ^ 2 := by
      simp_rw [hscale]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (2 ^ s : ℝ) ^ 2 * (𝔼 y : FABL.F₂Cube s, F y ^ 2) := by
      congr 1
      calc
        (∑ b : FABL.F₂Cube s, FABL.vectorFourierCoeff F b ^ 2) =
            ∑ b : FABL.F₂Cube s,
              FABL.vectorFourierCoeff F b *
                FABL.vectorFourierCoeff F b := by
          apply Finset.sum_congr rfl
          intro b _hb
          ring
        _ = 𝔼 y : FABL.F₂Cube s, F y * F y := hparseval.symm
        _ = 𝔼 y : FABL.F₂Cube s, F y ^ 2 := by
          apply Finset.expect_congr rfl
          intro y _hy
          ring
    _ = (2 ^ s : ℝ) * maioranaMcFarlandFiberCardinality φ a := by
      rw [expect_sq_maioranaMcFarlandFiberSignedIndicator]
      field_simp

private theorem exists_sqrt_fiberCardinality_le_abs_characterSum
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    ∃ b : FABL.F₂Cube s,
      Real.sqrt (maioranaMcFarlandFiberCardinality φ a : ℝ) ≤
        |(maioranaMcFarlandFiberCharacterSum φ g a b : ℝ)| := by
  let values := fun b : FABL.F₂Cube s ↦
    |(maioranaMcFarlandFiberCharacterSum φ g a b : ℝ)| ^ 2
  let maximum :=
    (Finset.univ : Finset (FABL.F₂Cube s)).sup'
      Finset.univ_nonempty values
  obtain ⟨b, _hb, hb⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube s)))
      Finset.univ_nonempty values
  have hsumLe :
      (∑ b : FABL.F₂Cube s, values b) ≤
        (2 ^ s : ℝ) * maximum := by
    have h :=
      Finset.sum_le_card_nsmul
        (Finset.univ : Finset (FABL.F₂Cube s))
        values maximum
        (fun b _hb ↦ Finset.le_sup' values (Finset.mem_univ b))
    simpa [card_f₂Cube, nsmul_eq_mul] using h
  have hsum :
      (∑ b : FABL.F₂Cube s, values b) =
        (2 ^ s : ℝ) * maioranaMcFarlandFiberCardinality φ a := by
    simpa [values, sq_abs] using
      sum_sq_maioranaMcFarlandFiberCharacterSum φ g a
  have hmaximum :
      (maioranaMcFarlandFiberCardinality φ a : ℝ) ≤ maximum := by
    rw [hsum] at hsumLe
    nlinarith [show (0 : ℝ) < 2 ^ s by positivity]
  refine ⟨b, (Real.sqrt_le_iff).2 ⟨abs_nonneg _, ?_⟩⟩
  change maximum = values b at hb
  rw [hb] at hmaximum
  simpa [values, sq_abs] using hmaximum

private theorem exists_ceil_sqrt_fiberCardinality_le_natAbs_characterSum
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    ∃ b : FABL.F₂Cube s,
      ⌈Real.sqrt (maioranaMcFarlandFiberCardinality φ a : ℝ)⌉₊ ≤
        (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs := by
  obtain ⟨b, hb⟩ :=
    exists_sqrt_fiberCardinality_le_abs_characterSum φ g a
  refine ⟨b, Nat.ceil_le.mpr ?_⟩
  simpa only [Int.cast_abs, Nat.cast_natAbs] using hb

/-- Some Walsh coefficient has magnitude at least `2^r` times the ceiling of
the square root of the largest fiber. -/
theorem two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    2 ^ r *
        ⌈Real.sqrt
          (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ ≤
      maxWalshMagnitude (booleanMaioranaMcFarlandGeneral φ g) := by
  obtain ⟨a, _ha, ha⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FABL.F₂Cube r)))
      Finset.univ_nonempty
      (maioranaMcFarlandFiberCardinality φ)
  obtain ⟨b, hb⟩ :=
    exists_ceil_sqrt_fiberCardinality_le_natAbs_characterSum φ g a
  have hwalsh :=
    walshTransform_natAbs_le_maxWalshMagnitude
      (booleanMaioranaMcFarlandGeneral φ g) (Fin.append a b)
  rw [walshTransform_booleanMaioranaMcFarlandGeneral,
    Int.natAbs_mul] at hwalsh
  norm_num at hwalsh
  have ha' :
      maxMaioranaMcFarlandFiberCardinality φ =
        maioranaMcFarlandFiberCardinality φ a := by
    simpa [maxMaioranaMcFarlandFiberCardinality] using ha
  rw [ha']
  exact (Nat.mul_le_mul_left (2 ^ r) hb).trans hwalsh

/-- Carlet Relation (62): the largest fiber forces an upper bound on the
nonlinearity of a general Maiorana--McFarland function. -/
theorem nonlinearity_booleanMaioranaMcFarlandGeneral_upper_bound
    (hr : 0 < r)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    nonlinearity (booleanMaioranaMcFarlandGeneral φ g) ≤
      2 ^ (r + s - 1) -
        2 ^ (r - 1) *
          ⌈Real.sqrt
            (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ := by
  have hmax :=
    two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude φ g
  have hrelation :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      (booleanMaioranaMcFarlandGeneral φ g)
  have htotal : 2 ^ (r + s) = 2 * 2 ^ (r + s - 1) := by
    calc
      2 ^ (r + s) = 2 ^ ((r + s - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (r + s - 1) := by
        rw [pow_succ]
        omega
  have hleft : 2 ^ r = 2 * 2 ^ (r - 1) := by
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (r - 1) := by
        rw [pow_succ]
        omega
  rw [htotal] at hrelation
  rw [hleft] at hmax
  have hmax' :
      2 * (2 ^ (r - 1) *
        ⌈Real.sqrt
          (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊) ≤
        maxWalshMagnitude (booleanMaioranaMcFarlandGeneral φ g) := by
    simpa [mul_assoc] using hmax
  have hadd :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) +
          2 ^ (r - 1) *
            ⌈Real.sqrt
              (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ ≤
        2 ^ (r + s - 1) := by
    omega
  exact Nat.le_sub_of_add_le hadd

end CryptBoolean
