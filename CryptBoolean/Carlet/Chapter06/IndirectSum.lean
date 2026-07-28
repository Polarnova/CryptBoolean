/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.NestedBent
public import CryptBoolean.Carlet.Chapter06.DualAffine

/-!
# The indirect sum of bent functions

Carlet Section 6.4.2: the four-function indirect-sum construction and its dual.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- The indirect sum of two pairs of Boolean functions on disjoint blocks. -/
def indirectSum
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m) :
    BooleanFunction (n + m) :=
  fun z ↦
    let p := (Fin.appendEquiv n m).symm z
    f₁ p.1 + g₁ p.2 + (f₁ p.1 + f₂ p.1) * (g₁ p.2 + g₂ p.2)

@[simp] theorem indirectSum_append
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (x : FABL.F₂Cube n) (y : FABL.F₂Cube m) :
    indirectSum f₁ f₂ g₁ g₂ (Fin.append x y) =
      f₁ x + g₁ y + (f₁ x + f₂ x) * (g₁ y + g₂ y) := by
  simp [indirectSum]

private theorem xor_cancel_left (a b c : FABL.𝔽₂) :
    a + c + (a + b) = b + c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private theorem bentDual_add_constant
    (f : BooleanFunction n) (hf : IsBent f) (c : FABL.𝔽₂)
    (a : FABL.F₂Cube n) :
    bentDual (f + FABL.affineFunction c 0) a = bentDual f a + c := by
  have hg : IsBent (f + FABL.affineFunction c 0) :=
    (isBent_add_affineFunction_iff f c 0).2 hf
  have hdualG :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
      (f + FABL.affineFunction c 0) hg a
  have hshift := walshTransform_add_affineFunction f c 0 a
  have hdualF :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf a
  apply bitSignInt_injective
  apply mul_left_cancel₀ (by positivity : (2 ^ (n / 2) : ℤ) ≠ 0)
  calc
    (2 ^ (n / 2) : ℤ) *
        bitSignInt (bentDual (f + FABL.affineFunction c 0) a) =
        walshTransform (f + FABL.affineFunction c 0) a := hdualG.symm
    _ = bitSignInt c * walshTransform f (a + 0) := hshift
    _ = bitSignInt c *
        ((2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f a)) := by
      rw [add_zero, hdualF]
    _ = (2 ^ (n / 2) : ℤ) *
        (bitSignInt (bentDual f a) * bitSignInt c) := by ring
    _ = (2 ^ (n / 2) : ℤ) * bitSignInt (bentDual f a + c) := by
      rw [bitSignInt_add]

private theorem firstBlockSlice_indirectSum
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (y : FABL.F₂Cube m) :
    firstBlockSlice (indirectSum f₁ f₂ g₁ g₂) y =
      if g₁ y + g₂ y = 0 then f₁ + FABL.affineFunction (g₁ y) 0
      else f₂ + FABL.affineFunction (g₁ y) 0 := by
  funext x
  by_cases h : g₁ y + g₂ y = 0
  · rw [if_pos h]
    simp [firstBlockSlice, h, FABL.affineFunction, FABL.f₂DotProduct]
  · have hone : g₁ y + g₂ y = 1 := Fin.eq_one_of_ne_zero _ h
    rw [if_neg h]
    simp only [firstBlockSlice, indirectSum_append, Pi.add_apply,
      FABL.affineFunction, FABL.f₂DotProduct, zero_dotProduct]
    rw [hone, mul_one, add_zero]
    exact xor_cancel_left (f₁ x) (f₂ x) (g₁ y)

private theorem dualSliceFunction_indirectSum
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂)
    (s : FABL.F₂Cube n) :
    dualSliceFunction (indirectSum f₁ f₂ g₁ g₂) s =
      fun y ↦ bentDual f₁ s + g₁ y +
        (bentDual f₁ s + bentDual f₂ s) * (g₁ y + g₂ y) := by
  funext y
  rw [dualSliceFunction, firstBlockSlice_indirectSum]
  by_cases h : g₁ y + g₂ y = 0
  · rw [if_pos h, bentDual_add_constant f₁ hf₁]
    simp [h]
  · have hone : g₁ y + g₂ y = 1 := Fin.eq_one_of_ne_zero _ h
    rw [if_neg h, bentDual_add_constant f₂ hf₂]
    rw [hone]
    simpa [add_comm, add_left_comm, add_assoc] using
      (xor_cancel_left (bentDual f₁ s) (bentDual f₂ s) (g₁ y)).symm

private theorem isBent_dualSliceFunction_indirectSum
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂)
    (hg₁ : IsBent g₁) (hg₂ : IsBent g₂)
    (s : FABL.F₂Cube n) :
    IsBent (dualSliceFunction (indirectSum f₁ f₂ g₁ g₂) s) := by
  rw [dualSliceFunction_indirectSum f₁ f₂ g₁ g₂ hf₁ hf₂ s]
  by_cases h : bentDual f₁ s + bentDual f₂ s = 0
  · have heq :
        (fun y ↦ bentDual f₁ s + g₁ y +
          (bentDual f₁ s + bentDual f₂ s) * (g₁ y + g₂ y)) =
          g₁ + FABL.affineFunction (bentDual f₁ s) 0 := by
      funext y
      simp [h, FABL.affineFunction, FABL.f₂DotProduct]
      ring
    rw [heq]
    exact (isBent_add_affineFunction_iff g₁ (bentDual f₁ s) 0).2 hg₁
  · have hone : bentDual f₁ s + bentDual f₂ s = 1 :=
      Fin.eq_one_of_ne_zero _ h
    have heq :
        (fun y ↦ bentDual f₁ s + g₁ y +
          (bentDual f₁ s + bentDual f₂ s) * (g₁ y + g₂ y)) =
          g₂ + FABL.affineFunction (bentDual f₁ s) 0 := by
      funext y
      simp only [Pi.add_apply, FABL.affineFunction, FABL.f₂DotProduct,
        zero_dotProduct, add_zero]
      rw [hone, one_mul]
      simpa [add_comm, add_left_comm, add_assoc] using
        xor_cancel_left (g₁ y) (g₂ y) (bentDual f₁ s)
    rw [heq]
    exact (isBent_add_affineFunction_iff g₂ (bentDual f₁ s) 0).2 hg₂

/-- The indirect sum of four bent functions is bent. -/
theorem isBent_indirectSum
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (hn : Even n) (hm : Even m) (_hnPositive : 0 < n) (_hmPositive : 0 < m)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂)
    (hg₁ : IsBent g₁) (hg₂ : IsBent g₂) :
    IsBent (indirectSum f₁ f₂ g₁ g₂) := by
  have hslices :
      ∀ y, IsBent (firstBlockSlice (indirectSum f₁ f₂ g₁ g₂) y) := by
    intro y
    rw [firstBlockSlice_indirectSum]
    split
    · exact (isBent_add_affineFunction_iff f₁ (g₁ y) 0).2 hf₁
    · exact (isBent_add_affineFunction_iff f₂ (g₁ y) 0).2 hf₂
  apply (isBent_iff_forall_isBent_dualSliceFunction
    (indirectSum f₁ f₂ g₁ g₂) hn hm hslices).2
  exact isBent_dualSliceFunction_indirectSum
    f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂

/-- The dual of an indirect sum is the indirect sum of the four duals. -/
theorem bentDual_indirectSum_append
    (f₁ f₂ : BooleanFunction n) (g₁ g₂ : BooleanFunction m)
    (hn : Even n) (hm : Even m) (_hnPositive : 0 < n) (_hmPositive : 0 < m)
    (hf₁ : IsBent f₁) (hf₂ : IsBent f₂)
    (hg₁ : IsBent g₁) (hg₂ : IsBent g₂)
    (s : FABL.F₂Cube n) (t : FABL.F₂Cube m) :
    bentDual (indirectSum f₁ f₂ g₁ g₂) (Fin.append s t) =
      indirectSum (bentDual f₁) (bentDual f₂) (bentDual g₁) (bentDual g₂)
        (Fin.append s t) := by
  let h := indirectSum f₁ f₂ g₁ g₂
  have hslices : ∀ y, IsBent (firstBlockSlice h y) := by
    intro y
    dsimp [h]
    rw [firstBlockSlice_indirectSum]
    split
    · exact (isBent_add_affineFunction_iff f₁ (g₁ y) 0).2 hf₁
    · exact (isBent_add_affineFunction_iff f₂ (g₁ y) 0).2 hf₂
  have hdualSlices : ∀ u, IsBent (dualSliceFunction h u) := by
    intro u
    exact isBent_dualSliceFunction_indirectSum
      f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ u
  rw [bentDual_append_eq_bentDual_dualSliceFunction
    h hn hm hslices hdualSlices s t]
  rw [indirectSum_append]
  dsimp [h]
  rw [dualSliceFunction_indirectSum f₁ f₂ g₁ g₂ hf₁ hf₂ s]
  by_cases hd : bentDual f₁ s + bentDual f₂ s = 0
  · have hfunction :
        (fun y ↦ bentDual f₁ s + g₁ y +
          (bentDual f₁ s + bentDual f₂ s) * (g₁ y + g₂ y)) =
          g₁ + FABL.affineFunction (bentDual f₁ s) 0 := by
      funext y
      simp [hd, FABL.affineFunction, FABL.f₂DotProduct]
      ring
    rw [hfunction, bentDual_add_constant g₁ hg₁]
    simp [hd]
    abel
  · have hdOne : bentDual f₁ s + bentDual f₂ s = 1 :=
      Fin.eq_one_of_ne_zero _ hd
    have hfunction :
        (fun y ↦ bentDual f₁ s + g₁ y +
          (bentDual f₁ s + bentDual f₂ s) * (g₁ y + g₂ y)) =
          g₂ + FABL.affineFunction (bentDual f₁ s) 0 := by
      funext y
      simp only [Pi.add_apply, FABL.affineFunction, FABL.f₂DotProduct,
        zero_dotProduct, add_zero]
      rw [hdOne, one_mul]
      simpa [add_comm, add_left_comm, add_assoc] using
        xor_cancel_left (g₁ y) (g₂ y) (bentDual f₁ s)
    rw [hfunction, bentDual_add_constant g₂ hg₂]
    rw [hdOne]
    simpa [add_comm, add_left_comm, add_assoc] using
      (xor_cancel_left (bentDual g₁ t) (bentDual g₂ t) (bentDual f₁ s)).symm

end CryptBoolean
