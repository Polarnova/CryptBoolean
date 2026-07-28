/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Dual

/-!
# Nested construction of bent functions

Carlet Theorem 10: bent slices whose pointwise dual slices are bent.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- Appending binary-cube blocks commutes with addition. -/
@[simp] theorem finAppend_add
    (u₁ u₂ : FABL.F₂Cube n) (v₁ v₂ : FABL.F₂Cube m) :
    Fin.append (u₁ + u₂) (v₁ + v₂) =
      Fin.append u₁ v₁ + Fin.append u₂ v₂ := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- The restriction of a block Boolean function at a fixed second-block input. -/
def firstBlockSlice
    (f : BooleanFunction (n + m)) (y : FABL.F₂Cube m) : BooleanFunction n :=
  fun x ↦ f (Fin.append x y)

/-- The restriction of a block Boolean function at a fixed first-block input. -/
def secondBlockSlice
    (f : BooleanFunction (n + m)) (x : FABL.F₂Cube n) : BooleanFunction m :=
  fun y ↦ f (Fin.append x y)

/-- At fixed first-block frequency, the ambient Walsh transform is the raw
Fourier transform of the Walsh coefficients of the first-block slices. -/
theorem walshTransform_append_cast_eq_rawFourierTransform_sliceWalsh
    (f : BooleanFunction (n + m))
    (s : FABL.F₂Cube n) (t : FABL.F₂Cube m) :
    (walshTransform f (Fin.append s t) : ℝ) =
      rawFourierTransform
        (fun y ↦ (walshTransform (firstBlockSlice f y) s : ℝ)) t := by
  classical
  rw [walshTransform_cast_eq_sum_realSignView_mul_character,
    rawFourierTransform]
  calc
    (∑ z : FABL.F₂Cube (n + m),
        realSignView f z * FABL.vectorWalshCharacter (Fin.append s t) z) =
        ∑ p : FABL.F₂Cube n × FABL.F₂Cube m,
          realSignView f (Fin.append p.1 p.2) *
            FABL.vectorWalshCharacter (Fin.append s t) (Fin.append p.1 p.2) := by
      let summand := fun z : FABL.F₂Cube (n + m) ↦
        realSignView f z * FABL.vectorWalshCharacter (Fin.append s t) z
      calc
        (∑ z : FABL.F₂Cube (n + m), summand z) =
            ∑ z : FABL.F₂Cube (n + m),
              summand (Fin.append
                ((Fin.appendEquiv n m).symm z).1
                ((Fin.appendEquiv n m).symm z).2) := by
          apply Finset.sum_congr rfl
          intro z _hz
          have hz : Fin.append
              ((Fin.appendEquiv n m).symm z).1
              ((Fin.appendEquiv n m).symm z).2 = z :=
            (Fin.appendEquiv n m).apply_symm_apply z
          exact congrArg summand hz |>.symm
        _ = ∑ p : FABL.F₂Cube n × FABL.F₂Cube m,
            summand (Fin.append p.1 p.2) :=
          Equiv.sum_comp (Fin.appendEquiv n m).symm
            (fun p : FABL.F₂Cube n × FABL.F₂Cube m ↦
              summand (Fin.append p.1 p.2))
    _ = ∑ y : FABL.F₂Cube m,
        (∑ x : FABL.F₂Cube n,
          realSignView (firstBlockSlice f y) x *
            FABL.vectorWalshCharacter s x) *
          FABL.vectorWalshCharacter t y := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [FABL.vectorWalshCharacter_append]
      simp [firstBlockSlice, realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction]
      ring
    _ = ∑ y : FABL.F₂Cube m,
        (walshTransform (firstBlockSlice f y) s : ℝ) *
          FABL.vectorWalshCharacter t y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [walshTransform_cast_eq_sum_realSignView_mul_character]

/-- At a first-block frequency, collect the dual values of all bent first-block slices. -/
noncomputable def dualSliceFunction
    (f : BooleanFunction (n + m)) (s : FABL.F₂Cube n) : BooleanFunction m :=
  fun y ↦ bentDual (firstBlockSlice f y) s

/-- The raw Walsh transform of nested bent slices factors through their dual slice. -/
theorem walshTransform_eq_two_pow_half_mul_walshTransform_dualSliceFunction
    (f : BooleanFunction (n + m))
    (hslices : ∀ y, IsBent (firstBlockSlice f y))
    (s : FABL.F₂Cube n) (t : FABL.F₂Cube m) :
    walshTransform f (Fin.append s t) =
      (2 ^ (n / 2) : ℤ) * walshTransform (dualSliceFunction f s) t := by
  classical
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [walshTransform_append_cast_eq_rawFourierTransform_sliceWalsh,
    rawFourierTransform,
    walshTransform_cast_eq_sum_realSignView_mul_character
      (dualSliceFunction f s) t]
  calc
    (∑ y : FABL.F₂Cube m,
        (walshTransform (firstBlockSlice f y) s : ℝ) *
          FABL.vectorWalshCharacter t y) =
      ∑ y : FABL.F₂Cube m,
        ((2 : ℝ) ^ (n / 2) *
          (bitSignInt (dualSliceFunction f s y) : ℝ)) *
          FABL.vectorWalshCharacter t y := by
      apply Finset.sum_congr rfl
      intro y _hy
      have hdual := congrArg (fun z : ℤ ↦ (z : ℝ))
        (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
          (firstBlockSlice f y) (hslices y) s)
      simpa only [dualSliceFunction, Int.cast_mul, Int.cast_pow,
        Int.cast_ofNat] using congrArg
          (fun z : ℝ ↦ z * FABL.vectorWalshCharacter t y) hdual
    _ = (2 : ℝ) ^ (n / 2) *
        ∑ y : FABL.F₂Cube m,
          realSignView (dualSliceFunction f s) y *
            FABL.vectorWalshCharacter t y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      have hsign :
          (bitSignInt (dualSliceFunction f s y) : ℝ) =
            realSignView (dualSliceFunction f s) y := by
        rw [bitSignInt_cast]
        simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
      rw [hsign]
      ring

/-- Carlet Theorem 10: with bent first-block slices, the whole function is
bent exactly when every function of their dual values is bent. -/
theorem isBent_iff_forall_isBent_dualSliceFunction
    (f : BooleanFunction (n + m))
    (hn : Even n) (hm : Even m)
    (hslices : ∀ y, IsBent (firstBlockSlice f y)) :
    IsBent f ↔ ∀ s, IsBent (dualSliceFunction f s) := by
  have hhalf : (n + m) / 2 = n / 2 + m / 2 := by
    rcases hn with ⟨r, hr⟩
    rcases hm with ⟨q, hq⟩
    omega
  constructor
  · intro hf s
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
      (dualSliceFunction f s)).mpr
    intro t
    have hfactor :=
      walshTransform_eq_two_pow_half_mul_walshTransform_dualSliceFunction
        f hslices s t
    have hmagnitude :=
      natAbs_walshTransform_eq_two_pow_half_of_isBent
        f hf (Fin.append s t)
    rw [hfactor, Int.natAbs_mul, Int.natAbs_pow, hhalf, pow_add] at hmagnitude
    norm_num at hmagnitude
    exact hmagnitude
  · intro hdual
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half f).mpr
    intro u
    let s := ((Fin.appendEquiv n m).symm u).1
    let t := ((Fin.appendEquiv n m).symm u).2
    have hu : Fin.append s t = u :=
      (Fin.appendEquiv n m).apply_symm_apply u
    rw [← hu,
      walshTransform_eq_two_pow_half_mul_walshTransform_dualSliceFunction
        f hslices s t,
      Int.natAbs_mul, Int.natAbs_pow]
    rw [natAbs_walshTransform_eq_two_pow_half_of_isBent
        (dualSliceFunction f s) (hdual s) t,
      hhalf, pow_add]
    norm_num

/-- Under Theorem 10's hypotheses, the dual is obtained by dualizing the
second-block function of first-slice dual values. -/
theorem bentDual_append_eq_bentDual_dualSliceFunction
    (f : BooleanFunction (n + m))
    (hn : Even n) (hm : Even m)
    (hslices : ∀ y, IsBent (firstBlockSlice f y))
    (hdualSlices : ∀ s, IsBent (dualSliceFunction f s))
    (s : FABL.F₂Cube n) (t : FABL.F₂Cube m) :
    bentDual f (Fin.append s t) = bentDual (dualSliceFunction f s) t := by
  have hf := (isBent_iff_forall_isBent_dualSliceFunction
    f hn hm hslices).mpr hdualSlices
  have hfactor :=
    walshTransform_eq_two_pow_half_mul_walshTransform_dualSliceFunction
      f hslices s t
  have hdualF :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      f hf (Fin.append s t)
  have hdualInner :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      (dualSliceFunction f s) (hdualSlices s) t
  have hhalf : (n + m) / 2 = n / 2 + m / 2 := by
    rcases hn with ⟨r, hr⟩
    rcases hm with ⟨q, hq⟩
    omega
  rw [hdualInner] at hfactor
  rw [hdualF, hhalf, pow_add] at hfactor
  have hsign :
      bitSignInt (bentDual f (Fin.append s t)) =
        bitSignInt (bentDual (dualSliceFunction f s) t) := by
    exact mul_left_cancel₀
      (by positivity : (2 ^ (n / 2) : ℤ) * 2 ^ (m / 2) ≠ 0)
      (by simpa [mul_assoc] using hfactor)
  exact bitSignInt_injective hsign

end CryptBoolean
