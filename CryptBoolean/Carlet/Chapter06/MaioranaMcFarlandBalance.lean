/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandGeneral

/-!
# Balance of the Maiorana--McFarland frequency map

The fiber character sums in Relation (49), together with raw Plancherel,
force the frequency map in every bent representation to be uniformly
distributed.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- A map between binary cubes is balanced when all output fibers have the
cardinality forced by the two cube dimensions. -/
def IsBalancedCubeMap
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) : Prop :=
  ∀ a : FABL.F₂Cube r,
    ((Finset.univ : Finset (FABL.F₂Cube s)).filter fun y ↦ φ y = a).card =
      2 ^ (s - r)

private noncomputable def maioranaMcFarlandFiberSign
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    FABL.F₂Cube s → ℝ :=
  fun y ↦ if φ y = a then realSignView g y else 0

private theorem rawFourierTransform_maioranaMcFarlandFiberSign
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r)
    (b : FABL.F₂Cube s) :
    rawFourierTransform (maioranaMcFarlandFiberSign φ g a) b =
      (maioranaMcFarlandFiberCharacterSum φ g a b : ℝ) := by
  classical
  rw [rawFourierTransform, maioranaMcFarlandFiberCharacterSum]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hφ : φ y = a
  · simp only [maioranaMcFarlandFiberSign, hφ, if_pos]
    rw [bitSignInt_add]
    norm_num only [Int.cast_mul]
    rw [bitSignInt_cast, bitSignInt_cast]
    simp [realSignView, FABL.realSignEncodedFunction,
      FABL.signEncodedFunction, FABL.vectorWalshCharacter_apply,
      FABL.signValue_signEncode_eq_binarySign]
  · simp [hφ, maioranaMcFarlandFiberSign]

private theorem sum_sq_maioranaMcFarlandFiberSign
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (a : FABL.F₂Cube r) :
    (∑ y, maioranaMcFarlandFiberSign φ g a y ^ 2) =
      (((Finset.univ : Finset (FABL.F₂Cube s)).filter
        fun y ↦ φ y = a).card : ℝ) := by
  classical
  calc
    (∑ y, maioranaMcFarlandFiberSign φ g a y ^ 2) =
        ∑ y, if φ y = a then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hφ : φ y = a
      · simp [maioranaMcFarlandFiberSign, hφ, realSignView_mul_self,
          pow_two]
      · simp [maioranaMcFarlandFiberSign, hφ]
    _ = (((Finset.univ : Finset (FABL.F₂Cube s)).filter
        fun y ↦ φ y = a).card : ℝ) := by
      simp

/-- If a general Maiorana--McFarland representation is bent, then its
frequency map is uniformly distributed over the output cube. -/
theorem isBalancedCubeMap_of_isBent_maioranaMcFarlandGeneral
    (f : BooleanFunction (r + s))
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hf : ∀ x y,
      f (Fin.append x y) = FABL.f₂DotProduct x (φ y) + g y)
    (heven : Even (r + s)) (hbent : IsBent f) :
    IsBalancedCubeMap φ := by
  classical
  have hcriterion :=
    (isBent_iff_maioranaMcFarlandFiberCharacterSum_natAbs
      f φ g hf heven).1 hbent
  have hrs : r ≤ s := by omega
  intro a
  let ψ := maioranaMcFarlandFiberSign φ g a
  let e := (r + s) / 2 - r
  have habs (b : FABL.F₂Cube s) :
      |rawFourierTransform ψ b| = (2 : ℝ) ^ e := by
    change
      |rawFourierTransform (maioranaMcFarlandFiberSign φ g a) b| = _
    rw [rawFourierTransform_maioranaMcFarlandFiberSign]
    have hmag := hcriterion.2 a b
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hmag
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
      Nat.cast_ofNat, e] using hcast
  have hplancherel := sum_rawFourierTransform_mul ψ ψ
  have hleft :
      (∑ b : FABL.F₂Cube s,
          rawFourierTransform ψ b * rawFourierTransform ψ b) =
        (2 : ℝ) ^ s * ((2 : ℝ) ^ e) ^ 2 := by
    calc
      (∑ b : FABL.F₂Cube s,
          rawFourierTransform ψ b * rawFourierTransform ψ b) =
          ∑ _b : FABL.F₂Cube s, ((2 : ℝ) ^ e) ^ 2 := by
        apply Finset.sum_congr rfl
        intro b _hb
        have hsquare := congrArg (fun z : ℝ ↦ z ^ 2) (habs b)
        rw [sq_abs] at hsquare
        simpa [pow_two] using hsquare
      _ = (2 : ℝ) ^ s * ((2 : ℝ) ^ e) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul]
        norm_num
  have hcardReal :
      ((((Finset.univ : Finset (FABL.F₂Cube s)).filter
          fun y ↦ φ y = a).card : ℕ) : ℝ) =
        ((2 : ℝ) ^ e) ^ 2 := by
    rw [hleft] at hplancherel
    dsimp [ψ] at hplancherel
    simp_rw [← pow_two] at hplancherel
    rw [sum_sq_maioranaMcFarlandFiberSign] at hplancherel
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ s ≠ 0)
    exact hplancherel.symm
  have hexponent : 2 * e = s - r := by
    rcases heven with ⟨k, hk⟩
    dsimp [e]
    omega
  apply Nat.cast_injective (R := ℝ)
  rw [hcardReal]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, show e * 2 = s - r by omega]

end CryptBoolean
