/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.ExtremalOrderCompleteQuadratic
public import CryptBoolean.Carlet.Chapter08.ExtremalPropagation

/-!
# Coordinate rigidity of the complete quadratic function

Constant mixed coordinate derivatives characterize the complete quadratic
function up to an affine summand.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem completeQuadraticBit_eq_full_sum
    {m : ℕ} (x : FABL.F₂Cube m) :
    FABL.completeQuadraticBit x =
      ∑ i : Fin m, ∑ j : Fin m, if i < j then x i * x j else 0 := by
  rw [FABL.completeQuadraticBit]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j _
    rfl

/-- The complete quadratic function on appended coordinate blocks is the sum
of the two block quadratics and their coordinate-sum product. -/
theorem completeQuadraticBit_finAppend
    {r s : ℕ} (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    FABL.completeQuadraticBit (Fin.append x y) =
      FABL.completeQuadraticBit x + FABL.completeQuadraticBit y +
        (∑ i, x i) * (∑ j, y j) := by
  classical
  rw [completeQuadraticBit_eq_full_sum, completeQuadraticBit_eq_full_sum,
    completeQuadraticBit_eq_full_sum]
  have hleft (i j : Fin r) :
      Fin.castAdd s i < Fin.castAdd s j ↔ i < j :=
    (Fin.strictMono_castAdd s).lt_iff_lt
  have hright (i j : Fin s) :
      Fin.natAdd r i < Fin.natAdd r j ↔ i < j :=
    Fin.natAdd_lt_natAdd_iff r
  have hcross (i : Fin r) (j : Fin s) :
      Fin.castAdd s i < Fin.natAdd r j := by
    change i.val < r + j.val
    omega
  have hcross' (i : Fin s) (j : Fin r) :
      ¬Fin.natAdd r i < Fin.castAdd s j := by
    change ¬r + i.val < j.val
    omega
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    hleft, hright, hcross, hcross', if_true, if_false, Finset.sum_const_zero,
    Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- A second derivative in the same direction vanishes. -/
theorem secondBooleanDerivative_same_direction
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    secondBooleanDerivative f a a = 0 := by
  funext x
  rw [secondBooleanDerivative_apply]
  rw [show x + a + a = x by
    rw [add_assoc, ZModModule.add_self, add_zero]]
  abel_nf
  simp [two_smul, ZModModule.add_self]

/-- Second differentiation distributes over pointwise addition. -/
theorem secondBooleanDerivative_add
    (f g : BooleanFunction n) (a e : FABL.F₂Cube n) :
    secondBooleanDerivative (f + g) a e =
      secondBooleanDerivative f a e + secondBooleanDerivative g a e := by
  funext x
  simp only [secondBooleanDerivative_apply, Pi.add_apply]
  abel

/-- Distinct coordinate directions have constant mixed derivative one for
the complete quadratic function. -/
theorem secondBooleanDerivative_completeQuadraticBit_coordinateDirections_eq_one
    (i j : Fin n) (hij : i ≠ j) :
    secondBooleanDerivative
        (FABL.completeQuadraticBit : BooleanFunction n)
        (coordinateDirection i) (coordinateDirection j) = 1 := by
  rw [secondBooleanDerivative,
    booleanDerivative_completeQuadraticBit_eq_affineFunction]
  have hdot : FABL.f₂DotProduct
      (completeQuadraticPolarFrequency (coordinateDirection j))
      (coordinateDirection i) = 1 := by
    rw [FABL.f₂DotProduct, dotProduct_comm]
    rw [show dotProduct (coordinateDirection i)
        (completeQuadraticPolarFrequency (coordinateDirection j)) =
        completeQuadraticPolarFrequency (coordinateDirection j) i by
      rw [coordinateDirection]
      simp [FABL.f₂CubeOfFinset_apply, dotProduct]]
    rw [completeQuadraticPolarFrequency_apply_eq_sum_add]
    simp [coordinateDirection, FABL.f₂CubeOfFinset_apply, hij]
  funext x
  simp only [FABL.booleanDerivative, FABL.affineFunction]
  rw [show FABL.f₂DotProduct
      (completeQuadraticPolarFrequency (coordinateDirection j))
      (x + coordinateDirection i) =
      FABL.f₂DotProduct (completeQuadraticPolarFrequency (coordinateDirection j)) x +
        FABL.f₂DotProduct (completeQuadraticPolarFrequency (coordinateDirection j))
          (coordinateDirection i) by
    exact dotProduct_add _ _ _]
  rw [hdot]
  abel_nf
  simp [two_smul, ZModModule.add_self]

/-- A Boolean function whose mixed derivatives in every pair of distinct
coordinate directions equal one is the complete quadratic function plus an
affine function. -/
theorem exists_completeQuadraticBit_add_affineFunction_of_coordinateSecondDerivatives_eq_one
    (f : BooleanFunction n)
    (hpairs : ∀ i j : Fin n, i ≠ j →
      secondBooleanDerivative f (coordinateDirection i)
        (coordinateDirection j) = 1) :
    ∃ c u, f =
      (FABL.completeQuadraticBit : BooleanFunction n) +
        FABL.affineFunction c u := by
  let q : BooleanFunction n := FABL.completeQuadraticBit
  let h : BooleanFunction n := f + q
  have hsecond (i j : Fin n) :
      secondBooleanDerivative h (coordinateDirection i)
        (coordinateDirection j) = 0 := by
    by_cases hij : i = j
    · subst j
      exact secondBooleanDerivative_same_direction h (coordinateDirection i)
    · change secondBooleanDerivative (f + q) (coordinateDirection i)
          (coordinateDirection j) = 0
      rw [secondBooleanDerivative_add, hpairs i j hij]
      rw [secondBooleanDerivative_completeQuadraticBit_coordinateDirections_eq_one
        i j hij]
      funext x
      exact ZModModule.add_self 1
  let u : FABL.F₂Cube n := fun i =>
    FABL.booleanDerivative h (coordinateDirection i) 0
  have hfirst (i : Fin n) :
      FABL.booleanDerivative h (coordinateDirection i) = fun _ => u i := by
    funext x
    exact eq_constant_of_coordinateDerivatives_eq_zero
      (FABL.booleanDerivative h (coordinateDirection i))
      (fun j => hsecond j i) x
  let c : FABL.𝔽₂ := h 0
  let r : BooleanFunction n := h + FABL.affineFunction c u
  have hdotCoordinate (i : Fin n) :
      FABL.f₂DotProduct u (coordinateDirection i) = u i := by
    rw [FABL.f₂DotProduct, dotProduct_comm, coordinateDirection]
    simp [FABL.f₂CubeOfFinset_apply, dotProduct]
  have hrDerivative (i : Fin n) :
      FABL.booleanDerivative r (coordinateDirection i) = 0 := by
    funext x
    change FABL.booleanDerivative (h + FABL.affineFunction c u)
      (coordinateDirection i) x = 0
    rw [booleanDerivative_add]
    change FABL.booleanDerivative h (coordinateDirection i) x +
      FABL.booleanDerivative (FABL.affineFunction c u)
        (coordinateDirection i) x = 0
    rw [congrFun (hfirst i) x]
    simp only [FABL.booleanDerivative, FABL.affineFunction]
    rw [show FABL.f₂DotProduct u (x + coordinateDirection i) =
        FABL.f₂DotProduct u x +
          FABL.f₂DotProduct u (coordinateDirection i) by
      exact dotProduct_add _ _ _]
    rw [hdotCoordinate]
    abel_nf
    simp [two_smul, ZModModule.add_self]
  have hrConstant := eq_constant_of_coordinateDerivatives_eq_zero r hrDerivative
  have hrZero : r = 0 := by
    funext x
    rw [hrConstant]
    change h 0 + (h 0 + FABL.f₂DotProduct u 0) = 0
    rw [show FABL.f₂DotProduct u 0 = 0 by
      simp [FABL.f₂DotProduct]]
    rw [add_zero]
    exact ZModModule.add_self (h 0)
  have hhAffine : h = FABL.affineFunction c u := by
    funext x
    have hzero := congrFun hrZero x
    change h x + FABL.affineFunction c u x = 0 at hzero
    calc
      h x = (h x + FABL.affineFunction c u x) +
          FABL.affineFunction c u x := by
        rw [add_assoc, ZModModule.add_self, add_zero]
      _ = FABL.affineFunction c u x := by rw [hzero, zero_add]
  refine ⟨c, u, ?_⟩
  funext x
  have hvalue := congrFun hhAffine x
  change f x + q x = FABL.affineFunction c u x at hvalue
  calc
    f x = (f x + q x) + q x := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    _ = FABL.affineFunction c u x + q x := by rw [hvalue]
    _ = q x + FABL.affineFunction c u x := add_comm _ _

/-- Every two-coordinate-block slice of the complete quadratic function plus
an affine function is again a complete quadratic function plus an affine
function. -/
theorem exists_firstBlockSlice_completeQuadraticBit_add_affineFunction
    {r s : ℕ} (c : FABL.𝔽₂) (u : FABL.F₂Cube (r + s))
    (y : FABL.F₂Cube s) :
    ∃ c' u',
      firstBlockSlice
          ((FABL.completeQuadraticBit : BooleanFunction (r + s)) +
            FABL.affineFunction c u) y =
        (FABL.completeQuadraticBit : BooleanFunction r) +
          FABL.affineFunction c' u' := by
  let ySum : FABL.𝔽₂ := ∑ j, y j
  let uLeft : FABL.F₂Cube r := fun i => u (Fin.castAdd s i)
  let uRight : FABL.F₂Cube s := fun j => u (Fin.natAdd r j)
  let cross : FABL.F₂Cube r := fun _ => ySum
  refine ⟨FABL.completeQuadraticBit y + c + FABL.f₂DotProduct uRight y,
    uLeft + cross, ?_⟩
  funext x
  rw [firstBlockSlice, Pi.add_apply, completeQuadraticBit_finAppend]
  have huAppend : Fin.append uLeft uRight = u := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [uLeft, uRight]
  have hdotSplit :
      FABL.f₂DotProduct u (Fin.append x y) =
        FABL.f₂DotProduct uLeft x + FABL.f₂DotProduct uRight y := by
    rw [← huAppend, FABL.f₂DotProduct_append]
  have hcrossDot : FABL.f₂DotProduct cross x = (∑ i, x i) * ySum := by
    simp only [FABL.f₂DotProduct, dotProduct, cross]
    simp_rw [mul_comm ySum]
    rw [← Finset.sum_mul]
  have haddDot : FABL.f₂DotProduct (uLeft + cross) x =
      FABL.f₂DotProduct uLeft x + FABL.f₂DotProduct cross x := by
    exact add_dotProduct uLeft cross x
  rw [FABL.affineFunction, hdotSplit, Pi.add_apply, FABL.affineFunction,
    haddDot]
  change
    FABL.completeQuadraticBit x + FABL.completeQuadraticBit y +
        (∑ i, x i) * ySum +
          (c + (FABL.f₂DotProduct uLeft x + FABL.f₂DotProduct uRight y)) =
      FABL.completeQuadraticBit x +
        (FABL.completeQuadraticBit y + c + FABL.f₂DotProduct uRight y +
          (FABL.f₂DotProduct uLeft x + FABL.f₂DotProduct cross x))
  rw [hcrossDot]
  ring

/-- In even first-block dimension, all first-block slices of the complete
quadratic function plus an affine function are bent. -/
theorem isBent_firstBlockSlice_completeQuadraticBit_add_affineFunction
    {r s : ℕ} (hr : Even r) (c : FABL.𝔽₂)
    (u : FABL.F₂Cube (r + s)) (y : FABL.F₂Cube s) :
    IsBent
      (firstBlockSlice
        ((FABL.completeQuadraticBit : BooleanFunction (r + s)) +
          FABL.affineFunction c u) y) := by
  obtain ⟨c', u', hslice⟩ :=
    exists_firstBlockSlice_completeQuadraticBit_add_affineFunction c u y
  rw [hslice, isBent_add_affineFunction_iff]
  exact isBent_completeQuadraticBit hr

end CryptBoolean
