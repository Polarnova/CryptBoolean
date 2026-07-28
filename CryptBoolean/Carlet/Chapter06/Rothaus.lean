/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.NestedBent
public import CryptBoolean.Carlet.Chapter06.ThreeFunctionBent

/-!
# The Dillon--Rothaus construction

Carlet Section 6.4.2: the two-variable secondary construction from four bent
functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The Dillon--Rothaus function, with the two new coordinates forming the
first block. -/
def rothausConstruction
    (g h k : BooleanFunction n) : BooleanFunction (2 + n) :=
  fun z ↦
    let p := (Fin.appendEquiv 2 n).symm z
    let u := p.1
    let x := p.2
    g x * h x + g x * k x + h x * k x +
      (g x + h x) * u 0 + (g x + k x) * u 1 + u 0 * u 1

@[simp] theorem rothausConstruction_append
    (g h k : BooleanFunction n)
    (u : FABL.F₂Cube 2) (x : FABL.F₂Cube n) :
    rothausConstruction g h k (Fin.append u x) =
      g x * h x + g x * k x + h x * k x +
        (g x + h x) * u 0 + (g x + k x) * u 1 + u 0 * u 1 := by
  simp [rothausConstruction]

private def rothausTwoBitQuadratic
    (c a b : FABL.𝔽₂) : BooleanFunction 2 :=
  fun u ↦ c + a * u 0 + b * u 1 + u 0 * u 1

private theorem sum_bitSignInt_rothausTwoBitQuadratic
    (c a b p q : FABL.𝔽₂) :
    (∑ x₁ : FABL.𝔽₂, ∑ x₂ : FABL.𝔽₂,
      bitSignInt
        (c + a * x₁ + b * x₂ + x₁ * x₂ + p * x₁ + q * x₂)) =
      2 * bitSignInt (c + (a + p) * (b + q)) := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;>
    fin_cases p <;> fin_cases q <;> decide

private theorem walshTransform_rothausTwoBitQuadratic
    (c a b : FABL.𝔽₂) (s : FABL.F₂Cube 2) :
    walshTransform (rothausTwoBitQuadratic c a b) s =
      2 * bitSignInt (c + (a + s 0) * (b + s 1)) := by
  rw [walshTransform]
  calc
    ∑ u : FABL.F₂Cube 2,
        walshTerm (rothausTwoBitQuadratic c a b) s u =
        ∑ p : FABL.𝔽₂ × FABL.𝔽₂,
          walshTerm (rothausTwoBitQuadratic c a b) s ![p.1, p.2] := by
      exact Fintype.sum_equiv (finTwoArrowEquiv FABL.𝔽₂)
        (fun u ↦ walshTerm (rothausTwoBitQuadratic c a b) s u)
        (fun p ↦ walshTerm
          (rothausTwoBitQuadratic c a b) s ![p.1, p.2])
        (fun u ↦ by
          have hu :
              ![((finTwoArrowEquiv FABL.𝔽₂) u).1,
                ((finTwoArrowEquiv FABL.𝔽₂) u).2] = u := by
            simpa only [finTwoArrowEquiv_symm_apply] using
              (finTwoArrowEquiv FABL.𝔽₂).symm_apply_apply u
          rw [hu])
    _ = ∑ x₁ : FABL.𝔽₂, ∑ x₂ : FABL.𝔽₂,
          bitSignInt
            (c + a * x₁ + b * x₂ + x₁ * x₂ +
              s 0 * x₁ + s 1 * x₂) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x₁ _hx₁
      apply Finset.sum_congr rfl
      intro x₂ _hx₂
      simp [walshTerm, rothausTwoBitQuadratic,
        FABL.f₂DotProduct, dotProduct, Fin.sum_univ_two]
      congr 1
      abel
    _ = 2 * bitSignInt (c + (a + s 0) * (b + s 1)) :=
      sum_bitSignInt_rothausTwoBitQuadratic c a b (s 0) (s 1)

private theorem isBent_rothausTwoBitQuadratic
    (c a b : FABL.𝔽₂) :
    IsBent (rothausTwoBitQuadratic c a b) := by
  apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half _).mpr
  intro s
  rw [walshTransform_rothausTwoBitQuadratic, Int.natAbs_mul]
  have hsign :
      (bitSignInt (c + (a + s 0) * (b + s 1))).natAbs = 1 := by
    rw [bitSignInt_eq_if_one]
    split <;> simp
  rw [hsign]
  norm_num

private theorem bentDual_rothausTwoBitQuadratic
    (c a b : FABL.𝔽₂) (s : FABL.F₂Cube 2) :
    bentDual (rothausTwoBitQuadratic c a b) s =
      c + (a + s 0) * (b + s 1) := by
  rw [bentDual, walshTransform_rothausTwoBitQuadratic]
  by_cases hvalue : c + (a + s 0) * (b + s 1) = 1
  · rw [hvalue]
    norm_num [bitSignInt_eq_if_one]
  · have hzero : c + (a + s 0) * (b + s 1) = 0 := by
      by_contra hne
      exact hvalue (Fin.eq_one_of_ne_zero _ hne)
    rw [hzero]
    norm_num [bitSignInt_eq_if_one]

private theorem firstBlockSlice_rothausConstruction
    (g h k : BooleanFunction n) (x : FABL.F₂Cube n) :
    firstBlockSlice (rothausConstruction g h k) x =
      rothausTwoBitQuadratic
        (g x * h x + g x * k x + h x * k x)
        (g x + h x) (g x + k x) := by
  funext u
  simp [firstBlockSlice, rothausTwoBitQuadratic]

private theorem dualSliceFunction_rothausConstruction
    (g h k : BooleanFunction n) (s : FABL.F₂Cube 2) :
    dualSliceFunction (rothausConstruction g h k) s =
      fun x ↦
        g x * h x + g x * k x + h x * k x +
          (g x + h x + s 0) * (g x + k x + s 1) := by
  funext x
  rw [dualSliceFunction, firstBlockSlice_rothausConstruction,
    bentDual_rothausTwoBitQuadratic]

private theorem rothausDual_zero_zero
    (g h k : FABL.𝔽₂) :
    g * h + g * k + h * k + (g + h) * (g + k) = g := by
  fin_cases g <;> fin_cases h <;> fin_cases k <;> decide

private theorem rothausDual_one_zero
    (g h k : FABL.𝔽₂) :
    g * h + g * k + h * k + (g + h + 1) * (g + k) = k := by
  fin_cases g <;> fin_cases h <;> fin_cases k <;> decide

private theorem rothausDual_zero_one
    (g h k : FABL.𝔽₂) :
    g * h + g * k + h * k + (g + h) * (g + k + 1) = h := by
  fin_cases g <;> fin_cases h <;> fin_cases k <;> decide

private theorem rothausDual_one_one
    (g h k : FABL.𝔽₂) :
    g * h + g * k + h * k + (g + h + 1) * (g + k + 1) =
      g + h + k + 1 := by
  fin_cases g <;> fin_cases h <;> fin_cases k <;> decide

private theorem isBent_dualSliceFunction_rothausConstruction
    (g h k : BooleanFunction n)
    (hg : IsBent g) (hh : IsBent h) (hk : IsBent k)
    (hsum : IsBent (threeFunctionSum g h k))
    (s : FABL.F₂Cube 2) :
    IsBent (dualSliceFunction (rothausConstruction g h k) s) := by
  rw [dualSliceFunction_rothausConstruction]
  by_cases hs₀ : s 0 = 0
  · by_cases hs₁ : s 1 = 0
    · have heq :
          (fun x ↦
            g x * h x + g x * k x + h x * k x +
              (g x + h x + s 0) * (g x + k x + s 1)) = g := by
          funext x
          rw [hs₀, hs₁]
          simpa using rothausDual_zero_zero (g x) (h x) (k x)
      rw [heq]
      exact hg
    · have hs₁One : s 1 = 1 := Fin.eq_one_of_ne_zero _ hs₁
      have heq :
          (fun x ↦
            g x * h x + g x * k x + h x * k x +
              (g x + h x + s 0) * (g x + k x + s 1)) = h := by
          funext x
          rw [hs₀, hs₁One]
          simpa using rothausDual_zero_one (g x) (h x) (k x)
      rw [heq]
      exact hh
  · have hs₀One : s 0 = 1 := Fin.eq_one_of_ne_zero _ hs₀
    by_cases hs₁ : s 1 = 0
    · have heq :
          (fun x ↦
            g x * h x + g x * k x + h x * k x +
              (g x + h x + s 0) * (g x + k x + s 1)) = k := by
          funext x
          rw [hs₀One, hs₁]
          simpa using rothausDual_one_zero (g x) (h x) (k x)
      rw [heq]
      exact hk
    · have hs₁One : s 1 = 1 := Fin.eq_one_of_ne_zero _ hs₁
      have heq :
          (fun x ↦
            g x * h x + g x * k x + h x * k x +
              (g x + h x + s 0) * (g x + k x + s 1)) =
            threeFunctionSum g h k + FABL.affineFunction 1 0 := by
          funext x
          rw [hs₀One, hs₁One]
          simp only [threeFunctionSum, Pi.add_apply, FABL.affineFunction,
            FABL.f₂DotProduct, zero_dotProduct, add_zero]
          exact rothausDual_one_one (g x) (h x) (k x)
      rw [heq]
      exact (isBent_add_affineFunction_iff
        (threeFunctionSum g h k) 1 0).mpr hsum

/-- The Dillon--Rothaus secondary construction is bent when `g`, `h`, `k`,
and `g + h + k` are bent. -/
theorem isBent_rothausConstruction
    (g h k : BooleanFunction n)
    (hnEven : Even n) (_hnTwo : 2 ≤ n)
    (hg : IsBent g) (hh : IsBent h) (hk : IsBent k)
    (hsum : IsBent (threeFunctionSum g h k)) :
    IsBent (rothausConstruction g h k) := by
  have hslices :
      ∀ x, IsBent (firstBlockSlice (rothausConstruction g h k) x) := by
    intro x
    rw [firstBlockSlice_rothausConstruction]
    exact isBent_rothausTwoBitQuadratic _ _ _
  apply (isBent_iff_forall_isBent_dualSliceFunction
    (rothausConstruction g h k) (by norm_num) hnEven hslices).mpr
  exact isBent_dualSliceFunction_rothausConstruction
    g h k hg hh hk hsum

end CryptBoolean
