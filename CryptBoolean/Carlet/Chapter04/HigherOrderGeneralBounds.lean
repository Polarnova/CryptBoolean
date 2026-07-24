/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
import FABL.Chapter03.LearningTheory.FourierEstimation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Powerset

/-!
# Carlet Chapter 4 general higher-order nonlinearity bounds

The exact finite sphere-covering count underlying Carlet's asymptotic
existence bound for higher-order nonlinearity.
-/

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators BooleanCube ENNReal Topology NNReal

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private def firstCoordinateTailLinearMap (n : ℕ) :
    FABL.F₂Cube (n + 1) →ₗ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def firstCoordinateLift
    (f : BooleanFunction n) : BooleanFunction (n + 1) :=
  f ∘ (firstCoordinateTailLinearMap n).toAffineMap

private def firstCoordinatePlotkinCombine
    (g h : BooleanFunction n) : BooleanFunction (n + 1) :=
  firstCoordinateLift g +
    (fun x ↦ x 0) * firstCoordinateLift h

private theorem firstCoordinatePlotkinCombine_zero
    (g h : BooleanFunction n) (x : FABL.F₂Cube n) :
    firstCoordinatePlotkinCombine g h (Fin.cons 0 x) = g x := by
  simp [firstCoordinatePlotkinCombine, firstCoordinateLift,
    firstCoordinateTailLinearMap]

private theorem firstCoordinatePlotkinCombine_one
    (g h : BooleanFunction n) (x : FABL.F₂Cube n) :
    firstCoordinatePlotkinCombine g h (Fin.cons 1 x) = g x + h x := by
  simp [firstCoordinatePlotkinCombine, firstCoordinateLift,
    firstCoordinateTailLinearMap]

private theorem firstCoordinatePlotkinCombine_degree_le
    (r : ℕ) (hr : 1 ≤ r) (g h : BooleanFunction n)
    (hg : FABL.functionAlgebraicDegree g ≤ r)
    (hh : FABL.functionAlgebraicDegree h ≤ r - 1) :
    FABL.functionAlgebraicDegree (firstCoordinatePlotkinCombine g h) ≤ r := by
  have hgLift :
      FABL.functionAlgebraicDegree (firstCoordinateLift g) ≤ r :=
    (functionAlgebraicDegree_comp_affineMap_le_general g
      (firstCoordinateTailLinearMap n).toAffineMap).trans hg
  have hhLift :
      FABL.functionAlgebraicDegree (firstCoordinateLift h) ≤ r - 1 :=
    (functionAlgebraicDegree_comp_affineMap_le_general h
      (firstCoordinateTailLinearMap n).toAffineMap).trans hh
  have hcoordinate :
      FABL.functionAlgebraicDegree
          (fun x : FABL.F₂Cube (n + 1) ↦ x 0) ≤ 1 := by
    simpa using functionAlgebraicDegree_affineMap_coordinate_le_one_general
      (AffineMap.id FABL.𝔽₂ (FABL.F₂Cube (n + 1))) (0 : Fin (n + 1))
  apply (FABL.functionAlgebraicDegree_add_le_max
    (firstCoordinateLift g)
    ((fun x : FABL.F₂Cube (n + 1) ↦ x 0) * firstCoordinateLift h)).trans
  apply max_le hgLift
  exact (FABL.functionAlgebraicDegree_mul_le_add _ _).trans
    ((Nat.add_le_add hcoordinate hhLift).trans (by omega))

private def firstCoordinateSlice
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂) : BooleanFunction n :=
  fun x ↦ f (Fin.cons b x)

private theorem hammingDistance_firstCoordinateSlices
    (f g : BooleanFunction (n + 1)) :
    hammingDistance f g =
      hammingDistance (firstCoordinateSlice f 0) (firstCoordinateSlice g 0) +
        hammingDistance (firstCoordinateSlice f 1) (firstCoordinateSlice g 1) := by
  classical
  unfold hammingDistance hammingDist
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  change (∑ x : FABL.F₂Cube (n + 1), if f x ≠ g x then 1 else 0) = _
  rw [← Equiv.sum_comp (Fin.consEquiv
    (fun _ : Fin (n + 1) ↦ FABL.𝔽₂)), Fintype.sum_prod_type]
  change (∑ b : FABL.𝔽₂, ∑ x : FABL.F₂Cube n,
    if f (Fin.cons b x) ≠ g (Fin.cons b x) then 1 else 0) = _
  rw [show (Finset.univ : Finset FABL.𝔽₂) = {0, 1} by rfl]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton]
  rfl

private theorem hammingDistance_add_left_add_right
    (f g h : BooleanFunction n) :
    hammingDistance f (g + h) = hammingDistance (f + g) h := by
  simp only [hammingDistance_eq_hammingWeight_add]
  rw [add_assoc]

/-- The covering radius `ρ(r,n)`: the largest order-`r` nonlinearity in
dimension `n`. -/
noncomputable def maximumHigherOrderNonlinearity (r n : ℕ) : ℕ :=
  (Finset.univ : Finset (BooleanFunction n)).sup'
    Finset.univ_nonempty (higherOrderNonlinearity r)

/-- Every order-`r` nonlinearity is bounded by the Reed--Muller covering radius. -/
theorem higherOrderNonlinearity_le_maximum
    (r : ℕ) (f : BooleanFunction n) :
    higherOrderNonlinearity r f ≤ maximumHigherOrderNonlinearity r n := by
  exact Finset.le_sup' (higherOrderNonlinearity r) (Finset.mem_univ f)

/-- The finite Boolean-function space contains a word attaining the
order-`r` Reed--Muller covering radius. -/
theorem exists_higherOrderNonlinearity_eq_maximum (r n : ℕ) :
    ∃ f : BooleanFunction n,
      higherOrderNonlinearity r f = maximumHigherOrderNonlinearity r n := by
  classical
  unfold maximumHigherOrderNonlinearity
  obtain ⟨f, _hf, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (BooleanFunction n)))
    Finset.univ_nonempty (higherOrderNonlinearity r)
  exact ⟨f, hmax.symm⟩

private theorem higherOrderNonlinearity_succ_le_maximum_add_maximum
    (r : ℕ) (hr : 1 ≤ r) (f : BooleanFunction (n + 1)) :
    higherOrderNonlinearity r f ≤
      maximumHigherOrderNonlinearity r n +
        maximumHigherOrderNonlinearity (r - 1) n := by
  let fzero : BooleanFunction n := firstCoordinateSlice f 0
  let fone : BooleanFunction n := firstCoordinateSlice f 1
  obtain ⟨g, hg, hdistanceG⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r fzero
  obtain ⟨h, hh, hdistanceH⟩ :=
    exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity
      (r - 1) (fone + g)
  let q : BooleanFunction (n + 1) := firstCoordinatePlotkinCombine g h
  have hq : q ∈ reedMuller r (n + 1) := by
    exact firstCoordinatePlotkinCombine_degree_le r hr g h hg hh
  have hqzero : firstCoordinateSlice q 0 = g := by
    funext x
    exact firstCoordinatePlotkinCombine_zero g h x
  have hqone : firstCoordinateSlice q 1 = g + h := by
    funext x
    exact firstCoordinatePlotkinCombine_one g h x
  calc
    higherOrderNonlinearity r f ≤ hammingDistance f q :=
      higherOrderNonlinearity_le_hammingDistance r f q hq
    _ = hammingDistance fzero g + hammingDistance fone (g + h) := by
      rw [hammingDistance_firstCoordinateSlices, hqzero, hqone]
    _ = hammingDistance fzero g + hammingDistance (fone + g) h := by
      rw [hammingDistance_add_left_add_right]
    _ = higherOrderNonlinearity r fzero +
        higherOrderNonlinearity (r - 1) (fone + g) := by
      rw [hdistanceG, hdistanceH]
    _ ≤ maximumHigherOrderNonlinearity r n +
        maximumHigherOrderNonlinearity (r - 1) n :=
      Nat.add_le_add
        (higherOrderNonlinearity_le_maximum r fzero)
        (higherOrderNonlinearity_le_maximum (r - 1) (fone + g))

/-- The Reed--Muller covering radii satisfy the Plotkin recurrence
`ρ(r,n+1) ≤ ρ(r,n) + ρ(r-1,n)`. -/
theorem maximumHigherOrderNonlinearity_succ_le
    (r n : ℕ) (hr : 1 ≤ r) :
    maximumHigherOrderNonlinearity r (n + 1) ≤
      maximumHigherOrderNonlinearity r n +
        maximumHigherOrderNonlinearity (r - 1) n := by
  obtain ⟨f, hf⟩ := exists_higherOrderNonlinearity_eq_maximum r (n + 1)
  rw [← hf]
  exact higherOrderNonlinearity_succ_le_maximum_add_maximum r hr f

/-- The order-`n` Reed--Muller code has covering radius zero in dimension `n`. -/
theorem maximumHigherOrderNonlinearity_self (n : ℕ) :
    maximumHigherOrderNonlinearity n n = 0 := by
  obtain ⟨f, hf⟩ := exists_higherOrderNonlinearity_eq_maximum n n
  rw [← hf]
  apply Nat.eq_zero_of_le_zero
  calc
    higherOrderNonlinearity n f ≤ hammingDistance f f :=
      higherOrderNonlinearity_le_hammingDistance n f f
        (FABL.functionAlgebraicDegree_le_dimension f)
    _ = 0 := hammingDist_self f

/-- Iterating the Plotkin recurrence bounds `ρ(r,n)` by the sum of the
order-`r-1` covering radii in dimensions `r,…,n-1`. -/
theorem maximumHigherOrderNonlinearity_le_sum_Ico
    (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    maximumHigherOrderNonlinearity r n ≤
      ∑ j ∈ Finset.Ico r n, maximumHigherOrderNonlinearity (r - 1) j := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases heq : r = n + 1
      · subst r
        simp [maximumHigherOrderNonlinearity_self]
      · have hrn' : r ≤ n := by omega
        calc
          maximumHigherOrderNonlinearity r (n + 1) ≤
              maximumHigherOrderNonlinearity r n +
                maximumHigherOrderNonlinearity (r - 1) n :=
            maximumHigherOrderNonlinearity_succ_le r n hr
          _ ≤ (∑ j ∈ Finset.Ico r n,
                maximumHigherOrderNonlinearity (r - 1) j) +
                maximumHigherOrderNonlinearity (r - 1) n :=
            Nat.add_le_add_right (ih hrn') _
          _ = ∑ j ∈ Finset.Ico r (n + 1),
                maximumHigherOrderNonlinearity (r - 1) j := by
            rw [Finset.sum_Ico_succ_top hrn']

/-- A pointwise real-valued bound for the order-`r-1` covering radii can be
summed through the Plotkin recurrence to bound the order-`r` covering radius. -/
theorem maximumHigherOrderNonlinearity_cast_le_sum_Ico_of_le
    (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (bound : ℕ → ℝ)
    (hbound : ∀ j ∈ Finset.Ico r n,
      (maximumHigherOrderNonlinearity (r - 1) j : ℝ) ≤ bound j) :
    (maximumHigherOrderNonlinearity r n : ℝ) ≤
      ∑ j ∈ Finset.Ico r n, bound j := by
  calc
    (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (((∑ j ∈ Finset.Ico r n,
          maximumHigherOrderNonlinearity (r - 1) j) : ℕ) : ℝ) := by
      exact_mod_cast maximumHigherOrderNonlinearity_le_sum_Ico r n hr hrn
    _ = ∑ j ∈ Finset.Ico r n,
          (maximumHigherOrderNonlinearity (r - 1) j : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ j ∈ Finset.Ico r n, bound j := by
      exact Finset.sum_le_sum fun j hj ↦ hbound j hj

private theorem sqrtTwo_sub_one_ne_zero : Real.sqrt 2 - 1 ≠ 0 := by
  intro h
  have hsqrt : Real.sqrt 2 = 1 := sub_eq_zero.mp h
  have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsqrt] at hsquare
  norm_num at hsquare

/-- Carlet's finite higher-order induction step: a bound with leading
coefficient `A` at order `r-1` yields coefficient `A * (1 + √2)` at order
`r`, with the finite error terms summed over dimensions `r,…,n-1`. -/
theorem maximumHigherOrderNonlinearity_cast_le_carlet_step
    (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (A : ℝ) (error : ℕ → ℝ)
    (hlower : ∀ j ∈ Finset.Ico r n,
      (maximumHigherOrderNonlinearity (r - 1) j : ℝ) ≤
        (2 : ℝ) ^ j / 2 - A * (Real.sqrt 2) ^ j + error j) :
    (maximumHigherOrderNonlinearity r n : ℝ) ≤
      ((2 : ℝ) ^ n - (2 : ℝ) ^ r) / 2 -
        A * (1 + Real.sqrt 2) *
          ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) +
        ∑ j ∈ Finset.Ico r n, error j := by
  apply (maximumHigherOrderNonlinearity_cast_le_sum_Ico_of_le
    r n hr hrn
    (fun j ↦ (2 : ℝ) ^ j / 2 - A * (Real.sqrt 2) ^ j + error j)
    hlower).trans_eq
  have htwo :
      (∑ j ∈ Finset.Ico r n, (2 : ℝ) ^ j) =
        (2 : ℝ) ^ n - (2 : ℝ) ^ r := by
    rw [geom_sum_Ico (by norm_num : (2 : ℝ) ≠ 1) hrn]
    norm_num
  have hsqrt :
      (∑ j ∈ Finset.Ico r n, (Real.sqrt 2) ^ j) =
        ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) /
          (Real.sqrt 2 - 1) :=
    geom_sum_Ico (x := Real.sqrt 2)
      (sub_ne_zero.mp sqrtTwo_sub_one_ne_zero) hrn
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, htwo, hsqrt]
  have hquot :
      ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) /
          (Real.sqrt 2 - 1) =
        (1 + Real.sqrt 2) *
          ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) := by
    apply (div_eq_iff sqrtTwo_sub_one_ne_zero).2
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hfactor :
        (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = (1 : ℝ) := by
      nlinarith
    calc
      (Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r =
          1 * ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) := by ring
      _ = ((1 + Real.sqrt 2) * (Real.sqrt 2 - 1)) *
          ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) := by rw [hfactor]
      _ = (1 + Real.sqrt 2) *
          ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) *
            (Real.sqrt 2 - 1) := by ring
  rw [hquot]
  ring

/-- A polynomial error term propagates through one Plotkin step while the
square-root coefficient is multiplied by `1 + √2`. -/
theorem maximumHigherOrderNonlinearity_cast_le_carlet_polynomial_step
    (r n d : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlower : ∀ j ∈ Finset.Ico r n,
      (maximumHigherOrderNonlinearity (r - 1) j : ℝ) ≤
        (2 : ℝ) ^ j / 2 - A * (Real.sqrt 2) ^ j +
          C * (j + 1 : ℝ) ^ d) :
    (maximumHigherOrderNonlinearity r n : ℝ) ≤
      (2 : ℝ) ^ n / 2 -
        (A * (1 + Real.sqrt 2)) * (Real.sqrt 2) ^ n +
        (C + A * (1 + Real.sqrt 2) * (Real.sqrt 2) ^ r) *
          (n + 1 : ℝ) ^ (d + 1) := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsum :
      (∑ j ∈ Finset.Ico r n, C * (j + 1 : ℝ) ^ d) ≤
        C * (n + 1 : ℝ) ^ (d + 1) := by
    calc
      (∑ j ∈ Finset.Ico r n, C * (j + 1 : ℝ) ^ d) ≤
          ∑ _j ∈ Finset.Ico r n, C * (n + 1 : ℝ) ^ d := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j + 1 ≤ n + 1 := by
          have := (Finset.mem_Ico.mp hj).2
          omega
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hjn) d) hC
      _ = ((Finset.Ico r n).card : ℝ) *
          (C * (n + 1 : ℝ) ^ d) := by
        simp [nsmul_eq_mul]
      _ ≤ (n + 1 : ℝ) * (C * (n + 1 : ℝ) ^ d) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show (Finset.Ico r n).card ≤ n + 1 by
            rw [Nat.card_Ico]
            omega)
        · positivity
      _ = C * (n + 1 : ℝ) ^ (d + 1) := by
        rw [pow_succ]
        ring
  have hstep := maximumHigherOrderNonlinearity_cast_le_carlet_step
    r n hr hrn A (fun j ↦ C * (j + 1 : ℝ) ^ d) hlower
  have hpower : 1 ≤ (n + 1 : ℝ) ^ (d + 1) := by
    apply one_le_pow₀
    exact_mod_cast Nat.le_add_left 1 n
  have hcoefficient :
      0 ≤ A * (1 + Real.sqrt 2) * (Real.sqrt 2) ^ r := by
    positivity
  calc
    (maximumHigherOrderNonlinearity r n : ℝ) ≤
        ((2 : ℝ) ^ n - (2 : ℝ) ^ r) / 2 -
          A * (1 + Real.sqrt 2) *
            ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) +
          ∑ j ∈ Finset.Ico r n, C * (j + 1 : ℝ) ^ d := hstep
    _ ≤ ((2 : ℝ) ^ n - (2 : ℝ) ^ r) / 2 -
          A * (1 + Real.sqrt 2) *
            ((Real.sqrt 2) ^ n - (Real.sqrt 2) ^ r) +
          C * (n + 1 : ℝ) ^ (d + 1) := by linarith
    _ ≤ (2 : ℝ) ^ n / 2 -
          (A * (1 + Real.sqrt 2)) * (Real.sqrt 2) ^ n +
          (C + A * (1 + Real.sqrt 2) * (Real.sqrt 2) ^ r) *
            (n + 1 : ℝ) ^ (d + 1) := by
      have hscaled := mul_le_mul_of_nonneg_left hpower hcoefficient
      nlinarith [show 0 ≤ (2 : ℝ) ^ r by positivity]

/-- Iterating the Plotkin step propagates an order-two `O(1)` error to an
order-`r` polynomial error of degree `r - 2`. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_iterated_carlet
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbase : ∀ n : ℕ,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 - A * (Real.sqrt 2) ^ n + C)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          (A * (1 + Real.sqrt 2) ^ (r - 2)) * (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) := by
  refine Nat.le_induction ?_ ?_ r hr
  · refine ⟨C, hC, ?_⟩
    intro n _hn
    simpa using hbase n
  · intro k hk ih
    rcases ih with ⟨D, hD, hbound⟩
    let Ak : ℝ := A * (1 + Real.sqrt 2) ^ (k - 2)
    let Dnext : ℝ :=
      D + Ak * (1 + Real.sqrt 2) * (Real.sqrt 2) ^ (k + 1)
    have hAk : 0 ≤ Ak := by
      dsimp only [Ak]
      positivity
    have hDnext : 0 ≤ Dnext := by
      dsimp only [Dnext]
      positivity
    refine ⟨Dnext, hDnext, ?_⟩
    intro n hkn
    have hstep := maximumHigherOrderNonlinearity_cast_le_carlet_polynomial_step
      (k + 1) n (k - 2) (by omega) hkn Ak D hAk hD
      (fun j hj ↦ hbound j (by
        have hjlower := (Finset.mem_Ico.mp hj).1
        omega))
    have hexponent : k - 2 + 1 = k + 1 - 2 := by omega
    have hcoefficient :
        Ak * (1 + Real.sqrt 2) =
          A * (1 + Real.sqrt 2) ^ (k + 1 - 2) := by
      dsimp only [Ak]
      rw [show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]
      ring
    simpa only [hcoefficient, hexponent, Dnext] using hstep

/-- Every positive-order Reed--Muller covering radius is at most half the
ambient Boolean cube size. -/
theorem maximumHigherOrderNonlinearity_cast_le_half_two_pow
    (r n : ℕ) (hr : 1 ≤ r) :
    (maximumHigherOrderNonlinearity r n : ℝ) ≤ (2 : ℝ) ^ n / 2 := by
  obtain ⟨f, hf⟩ := exists_higherOrderNonlinearity_eq_maximum r n
  have hfinite := two_mul_higherOrderNonlinearity_le_two_pow r hr f
  have hfiniteReal :
      (2 : ℝ) * (higherOrderNonlinearity r f : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hfinite
  rw [← hf]
  linarith

/-- An eventual order-two `O(1)` bound can be enlarged on its finite prefix
to a nonnegative constant valid in every dimension. -/
theorem exists_global_orderTwo_bound_of_eventually
    (A C : ℝ) (hA : 0 ≤ A)
    (hbase : ∀ᶠ n in Filter.atTop,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 - A * (Real.sqrt 2) ^ n + C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 - A * (Real.sqrt 2) ^ n + C' := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbase
  let C' : ℝ := max 0 C + A * (Real.sqrt 2) ^ N
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]
    norm_num
  have hC' : 0 ≤ C' := by
    dsimp only [C']
    positivity
  refine ⟨C', hC', ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnBound := hN n hn
    have hCC' : C ≤ C' := by
      calc
        C ≤ max 0 C := le_max_right _ _
        _ ≤ max 0 C + A * (Real.sqrt 2) ^ N :=
          le_add_of_nonneg_right (mul_nonneg hA (by positivity))
        _ = C' := rfl
    linarith
  · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hpower : (Real.sqrt 2) ^ n ≤ (Real.sqrt 2) ^ N :=
      pow_le_pow_right₀ hsqrtOne hnN
    have hscaled := mul_le_mul_of_nonneg_left hpower hA
    have hhalf := maximumHigherOrderNonlinearity_cast_le_half_two_pow 2 n
      (by omega)
    have hprefix : A * (Real.sqrt 2) ^ n ≤ C' := by
      dsimp only [C']
      have hmax : 0 ≤ max 0 C := le_max_left _ _
      linarith
    linarith

/-- Carlet's full Plotkin propagation from an eventual order-two base: the
sharp coefficient is multiplied by `(1 + √2)^(r-2)` and the error is
`O(n^(r-2))`. -/
theorem exists_maximumHigherOrderNonlinearity_cast_le_of_eventual_orderTwo
    (A : ℝ) (hA : 0 ≤ A)
    (hbase : ∃ C : ℝ, ∀ᶠ n in Filter.atTop,
      (maximumHigherOrderNonlinearity 2 n : ℝ) ≤
        (2 : ℝ) ^ n / 2 - A * (Real.sqrt 2) ^ n + C)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, r ≤ n →
      (maximumHigherOrderNonlinearity r n : ℝ) ≤
        (2 : ℝ) ^ n / 2 -
          (A * (1 + Real.sqrt 2) ^ (r - 2)) * (Real.sqrt 2) ^ n +
          D * (n + 1 : ℝ) ^ (r - 2) := by
  rcases hbase with ⟨C, hbase⟩
  obtain ⟨C', hC', hglobal⟩ :=
    exists_global_orderTwo_bound_of_eventually A C hA hbase
  exact exists_maximumHigherOrderNonlinearity_cast_le_iterated_carlet
    A C' hA hC' hglobal r hr

private def toggleOn
    (g : BooleanFunction n) (S : Finset (FABL.F₂Cube n)) : BooleanFunction n :=
  fun x ↦ if x ∈ S then g x + 1 else g x

private theorem hammingDistance_toggleOn
    (g : BooleanFunction n) (S : Finset (FABL.F₂Cube n)) :
    hammingDistance (toggleOn g S) g = S.card := by
  classical
  unfold hammingDistance hammingDist toggleOn
  congr 1
  ext x
  by_cases hx : x ∈ S <;> simp [hx]

private def mismatchSet
    (f g : BooleanFunction n) : Finset (FABL.F₂Cube n) :=
  Finset.univ.filter fun x ↦ f x ≠ g x

private theorem toggleOn_mismatchSet (f g : BooleanFunction n) :
    toggleOn g (mismatchSet f g) = f := by
  funext x
  by_cases hfg : f x = g x
  · simp [toggleOn, mismatchSet, hfg]
  · have hsum : g x + 1 = f x := by
      by_cases hfx : f x = 0
      · have hgx0 : g x ≠ 0 := by
          intro hgx
          apply hfg
          rw [hfx, hgx]
        have hgx : g x = 1 := Fin.eq_one_of_ne_zero (g x) hgx0
        simp [hfx, hgx]
      · have hfone : f x = 1 := Fin.eq_one_of_ne_zero (f x) hfx
        have hgx : g x = 0 := by
          by_contra hgx
          exact hfg (hfone.trans (Fin.eq_one_of_ne_zero (g x) hgx).symm)
        simp [hfone, hgx]
    change (if x ∈ mismatchSet f g then g x + 1 else g x) = f x
    rw [if_pos]
    · exact hsum
    · simp [mismatchSet, hfg]

private theorem mismatchSet_card (f g : BooleanFunction n) :
    (mismatchSet f g).card = hammingDistance f g := by
  rfl

private theorem toggleOn_injective (g : BooleanFunction n) :
    Function.Injective (toggleOn g) := by
  intro S T hST
  ext x
  have hx := congrFun hST x
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;>
    simp only [toggleOn, hxS, hxT, if_pos] at hx ⊢ <;>
    simp_all

private def hammingSubsetFamily
    (α : Type*) [Fintype α] [DecidableEq α] (t : ℕ) : Finset (Finset α) :=
  (Finset.range (t + 1)).biUnion fun j ↦
    Finset.powersetCard j (Finset.univ : Finset α)

@[simp] private theorem mem_hammingSubsetFamily
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (t : ℕ) :
    S ∈ hammingSubsetFamily α t ↔ S.card ≤ t := by
  classical
  simp [hammingSubsetFamily]

/-- The cardinality of a binary Hamming ball of radius `t` in dimension `N`. -/
def hammingBallVolume (N t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), Nat.choose N j

private theorem card_hammingSubsetFamily
    (α : Type*) [Fintype α] [DecidableEq α] (t : ℕ) :
    (hammingSubsetFamily α t).card = hammingBallVolume (Fintype.card α) t := by
  classical
  have hdisjoint :
      ((Finset.range (t + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun j ↦ Finset.powersetCard j (Finset.univ : Finset α)) := by
    intro i hi j hj hij
    change Disjoint
      (Finset.powersetCard i (Finset.univ : Finset α))
      (Finset.powersetCard j (Finset.univ : Finset α))
    rw [Finset.disjoint_left]
    intro S hSi hSj
    exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans
      (Finset.mem_powersetCard.mp hSj).2)
  rw [hammingSubsetFamily, Finset.card_biUnion hdisjoint]
  simp [hammingBallVolume]

private def hammingBall
    (g : BooleanFunction n) (t : ℕ) : Finset (BooleanFunction n) :=
  Finset.univ.filter fun f ↦ hammingDistance f g ≤ t

private theorem hammingBall_eq_image (g : BooleanFunction n) (t : ℕ) :
    hammingBall g t =
      (hammingSubsetFamily (FABL.F₂Cube n) t).image (toggleOn g) := by
  classical
  ext f
  constructor
  · intro hf
    rw [Finset.mem_image]
    refine ⟨mismatchSet f g, ?_, ?_⟩
    · rw [mem_hammingSubsetFamily, mismatchSet_card]
      simpa [hammingBall] using hf
    · exact toggleOn_mismatchSet f g
  · intro hf
    rcases Finset.mem_image.mp hf with ⟨S, hS, rfl⟩
    simp [hammingBall, hammingDistance_toggleOn,
      (mem_hammingSubsetFamily S t).mp hS]

private theorem card_hammingBall (g : BooleanFunction n) (t : ℕ) :
    (hammingBall g t).card = hammingBallVolume (2 ^ n) t := by
  classical
  rw [hammingBall_eq_image,
    Finset.card_image_of_injective _ (toggleOn_injective g),
    card_hammingSubsetFamily]
  simp

/-- If the Reed--Muller Hamming balls of radius `t` have total cardinality
strictly below the Boolean-function space, some function has order-`r`
nonlinearity greater than `t`. -/
theorem exists_higherOrderNonlinearity_gt_of_counting
    (r n t : ℕ)
    (hcount :
      2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) *
          hammingBallVolume (2 ^ n) t < 2 ^ (2 ^ n)) :
    ∃ f : BooleanFunction n, t < higherOrderNonlinearity r f := by
  classical
  letI : Fintype (reedMuller r n) := Fintype.ofFinite (reedMuller r n)
  let covered : Finset (BooleanFunction n) :=
    (Finset.univ : Finset (reedMuller r n)).biUnion fun g ↦
      hammingBall g.1 t
  by_contra hnone
  push Not at hnone
  have hle (f : BooleanFunction n) : higherOrderNonlinearity r f ≤ t := by
    exact hnone f
  have hcovered : covered = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro f
    obtain ⟨g, hg, hdistance⟩ :=
      exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity r f
    change f ∈ (Finset.univ : Finset (reedMuller r n)).biUnion
      (fun g ↦ hammingBall g.1 t)
    rw [Finset.mem_biUnion]
    refine ⟨⟨g, hg⟩, Finset.mem_univ _, ?_⟩
    simp [hammingBall, hdistance, hle f]
  have hcoverCard :
      2 ^ (2 ^ n) ≤
        2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) *
          hammingBallVolume (2 ^ n) t := by
    calc
      2 ^ (2 ^ n) = covered.card := by
        rw [hcovered, Finset.card_univ, Fintype.card_fun]
        simp
      _ ≤ (Finset.univ : Finset (reedMuller r n)).card *
          hammingBallVolume (2 ^ n) t := by
        apply Finset.card_biUnion_le_card_mul
        intro g hg
        rw [card_hammingBall]
      _ = 2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) *
          hammingBallVolume (2 ^ n) t := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, reedMuller_card]
  exact (Nat.not_le_of_gt hcount) hcoverCard

/-- Power-of-two form of the exact finite sphere-covering criterion. -/
theorem exists_higherOrderNonlinearity_gt_of_hammingBallVolume_lt
    (r n t : ℕ)
    (hdimension :
      ∑ j ∈ Finset.range (r + 1), Nat.choose n j ≤ 2 ^ n)
    (hvolume :
      hammingBallVolume (2 ^ n) t <
        2 ^ (2 ^ n - ∑ j ∈ Finset.range (r + 1), Nat.choose n j)) :
    ∃ f : BooleanFunction n, t < higherOrderNonlinearity r f := by
  apply exists_higherOrderNonlinearity_gt_of_counting r n t
  have hpow : 0 <
      2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) := by
    positivity
  calc
    2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) *
        hammingBallVolume (2 ^ n) t <
      2 ^ (∑ j ∈ Finset.range (r + 1), Nat.choose n j) *
        2 ^ (2 ^ n - ∑ j ∈ Finset.range (r + 1), Nat.choose n j) :=
      Nat.mul_lt_mul_of_pos_left hvolume hpow
    _ = 2 ^ (2 ^ n) := by
      rw [← pow_add, Nat.add_sub_of_le hdimension]

local instance higherOrderSignMeasurableSpace : MeasurableSpace FABL.Sign := ⊤

local instance higherOrderSignMeasurableSingletonClass :
    MeasurableSingletonClass FABL.Sign where
  measurableSet_singleton _ := by simp

private def lowPositiveSignCube (N t : ℕ) : Finset ({−1,1}^[N]) :=
  Finset.univ.filter fun x ↦ FABL.positiveCoordinateCount x ≤ t

private theorem image_lowPositiveSignCube (N t : ℕ) :
    (lowPositiveSignCube N t).image (FABL.signCubeEquivFinset N) =
      hammingSubsetFamily (Fin N) t := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨x, hx, rfl⟩
    rw [mem_hammingSubsetFamily]
    simpa [lowPositiveSignCube] using hx
  · intro hS
    rw [Finset.mem_image]
    refine ⟨(FABL.signCubeEquivFinset N).symm S, ?_,
      (FABL.signCubeEquivFinset N).apply_symm_apply S⟩
    simp only [lowPositiveSignCube, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← FABL.signCubeEquivFinset_apply_card]
    simpa using (mem_hammingSubsetFamily S t).mp hS

private theorem card_lowPositiveSignCube (N t : ℕ) :
    (lowPositiveSignCube N t).card = hammingBallVolume N t := by
  calc
    (lowPositiveSignCube N t).card =
        ((lowPositiveSignCube N t).image (FABL.signCubeEquivFinset N)).card :=
      (Finset.card_image_of_injective _
        (FABL.signCubeEquivFinset N).injective).symm
    _ = (hammingSubsetFamily (Fin N) t).card := by
      rw [image_lowPositiveSignCube]
    _ = hammingBallVolume N t := by
      simpa using card_hammingSubsetFamily (Fin N) t

private theorem measure_uniformPMF_real_eq_ncard_div_card
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (A : Set Ω) :
    (FABL.uniformPMF Ω).toMeasure.real A =
      (A.ncard : ℝ) / Fintype.card Ω := by
  classical
  rw [Measure.real_def, PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.toReal_sum]
  · rw [Set.ncard_eq_toFinset_card' A]
    simp only [FABL.uniformPMF, Set.indicator_apply,
      PMF.uniformOfFintype_apply]
    calc
      (∑ x : Ω,
        (if x ∈ A then ((Fintype.card Ω : ℝ≥0∞)⁻¹) else 0).toReal) =
          ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ A),
            ((Fintype.card Ω : ℝ≥0∞)⁻¹).toReal := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ A <;> simp [hx]
      _ = ((Finset.univ.filter fun x : Ω ↦ x ∈ A).card : ℝ) *
          ((Fintype.card Ω : ℝ≥0∞)⁻¹).toReal := by
        simp [nsmul_eq_mul]
      _ = _ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
        simp [div_eq_mul_inv]
  · intro x _
    by_cases hx : x ∈ A <;> simp [hx, FABL.uniformPMF]

private theorem measure_lowPositiveSignCube (N t : ℕ) :
    (FABL.uniformPMF ({−1,1}^[N])).toMeasure.real
        {x | FABL.positiveCoordinateCount x ≤ t} =
      (hammingBallVolume N t : ℝ) / (2 : ℝ) ^ N := by
  classical
  rw [measure_uniformPMF_real_eq_ncard_div_card]
  have hncard :
      ({x : {−1,1}^[N] | FABL.positiveCoordinateCount x ≤ t} : Set _).ncard =
        (lowPositiveSignCube N t).card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [lowPositiveSignCube]
  rw [hncard, card_lowPositiveSignCube]
  congr 1
  norm_num [Fintype.card_pi, FABL.Sign]

private theorem expect_neg_signValue_eq_zero :
    Finset.expect Finset.univ (fun s : FABL.Sign ↦ -FABL.signValue s) = 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [FABL.Sign, FABL.signValue]

private theorem neg_signValue_mem_Icc (s : FABL.Sign) :
    -FABL.signValue s ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [FABL.signValue]

private theorem two_mul_sqrt_half (N D : ℕ) :
    2 * Real.sqrt ((N : ℝ) * D / 2) =
      Real.sqrt (2 * (N : ℝ) * D) := by
  rw [show (2 : ℝ) * N * D = 4 * ((N : ℝ) * D / 2) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

private theorem measure_lowPositiveSignCube_le_exp
    (N D t : ℕ) (hN : 0 < N)
    (ht : (t : ℝ) ≤ (N : ℝ) / 2 - Real.sqrt ((N : ℝ) * D / 2)) :
    (FABL.uniformPMF ({−1,1}^[N])).toMeasure.real
        {x | FABL.positiveCoordinateCount x ≤ t} ≤
      Real.exp (-(D : ℝ)) := by
  rw [FABL.uniformSample_toMeasure_eq_pi FABL.Sign N]
  let μ : Measure (Fin N → FABL.Sign) :=
    Measure.pi fun _ : Fin N ↦ (FABL.uniformPMF FABL.Sign).toMeasure
  let threshold : ℝ := Real.sqrt (2 * (N : ℝ) * D)
  have hcoordinate (i : Fin N) :
      HasSubgaussianMGF
        (fun samples : Fin N → FABL.Sign ↦ -FABL.signValue (samples i)) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := μ)
      (X := fun samples : Fin N → FABL.Sign ↦ -FABL.signValue (samples i))
      (measurable_of_finite fun samples : Fin N → FABL.Sign ↦
        -FABL.signValue (samples i)).aemeasurable
      (ae_of_all _ fun samples ↦ neg_signValue_mem_Icc (samples i))
    have hmean :
        ∫ samples : Fin N → FABL.Sign, -FABL.signValue (samples i) ∂μ = 0 := by
      rw [integral_comp_eval
        (μ := fun _ : Fin N ↦ (FABL.uniformPMF FABL.Sign).toMeasure)
        (i := i)
        (measurable_of_finite fun s : FABL.Sign ↦
          -FABL.signValue s).aestronglyMeasurable]
      rw [FABL.integral_uniformPMF_eq_expect, expect_neg_signValue_eq_zero]
    rw [hmean] at h
    norm_num at h ⊢
    exact h
  have hindep :
      iIndepFun
        (fun i (samples : Fin N → FABL.Sign) ↦ -FABL.signValue (samples i)) μ := by
    exact iIndepFun_pi fun _ ↦
      (measurable_of_finite fun s : FABL.Sign ↦ -FABL.signValue s).aemeasurable
  have htail :
      μ.real {samples |
          threshold ≤ ∑ i : Fin N, -FABL.signValue (samples i)} ≤
        Real.exp (-(D : ℝ)) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
      (c := fun _ : Fin N ↦ (1 : NNReal)) (s := Finset.univ)
      (fun i _ ↦ hcoordinate i)
      (ε := threshold)
      (Real.sqrt_nonneg _)
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hthresholdSq : threshold ^ 2 = 2 * (N : ℝ) * D := by
      exact Real.sq_sqrt (by positivity)
    have hexponent :
        -threshold ^ 2 / (2 * (N : ℝ)) = -(D : ℝ) := by
      rw [hthresholdSq]
      field_simp
    norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    rw [hexponent] at h
    simpa only [Finset.sum_neg_distrib] using h
  have hsubset :
      {x : Fin N → FABL.Sign | FABL.positiveCoordinateCount x ≤ t} ⊆
        {samples | threshold ≤ ∑ i : Fin N, -FABL.signValue (samples i)} := by
    intro x hx
    have hxR : (FABL.positiveCoordinateCount x : ℝ) ≤ t := by
      exact_mod_cast hx
    have hsum := FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub x
    change threshold ≤ ∑ i : Fin N, -FABL.signValue (x i)
    rw [Finset.sum_neg_distrib, hsum]
    dsimp only [threshold]
    rw [← two_mul_sqrt_half N D]
    nlinarith
  exact (measureReal_mono hsubset).trans htail

private theorem exp_neg_natCast_lt_two_pow_inv (D : ℕ) (hD : 0 < D) :
    Real.exp (-(D : ℝ)) < ((2 : ℝ) ^ D)⁻¹ := by
  have hbase : (Real.exp 1)⁻¹ < (2 : ℝ)⁻¹ :=
    (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).2
      Real.exp_one_gt_two
  have hpow : ((Real.exp 1)⁻¹) ^ D < ((2 : ℝ)⁻¹) ^ D :=
    pow_lt_pow_left₀ hbase (by positivity) (Nat.ne_of_gt hD)
  calc
    Real.exp (-(D : ℝ)) = Real.exp ((D : ℝ) * (-1)) := by
      congr 1
      ring
    _ = Real.exp (-1) ^ D := Real.exp_nat_mul (-1) D
    _ = ((Real.exp 1)⁻¹) ^ D := by rw [Real.exp_neg]
    _ < ((2 : ℝ)⁻¹) ^ D := hpow
    _ = ((2 : ℝ) ^ D)⁻¹ := by rw [inv_pow]

private theorem hammingBallVolume_lt_two_pow_sub
    (N D t : ℕ) (hN : 0 < N) (hD : 0 < D) (hDN : D ≤ N)
    (ht : (t : ℝ) ≤ (N : ℝ) / 2 - Real.sqrt ((N : ℝ) * D / 2)) :
    hammingBallVolume N t < 2 ^ (N - D) := by
  have hratio :
      (hammingBallVolume N t : ℝ) / (2 : ℝ) ^ N <
        ((2 : ℝ) ^ D)⁻¹ := by
    calc
      (hammingBallVolume N t : ℝ) / (2 : ℝ) ^ N =
          (FABL.uniformPMF ({−1,1}^[N])).toMeasure.real
            {x | FABL.positiveCoordinateCount x ≤ t} :=
        (measure_lowPositiveSignCube N t).symm
      _ ≤ Real.exp (-(D : ℝ)) :=
        measure_lowPositiveSignCube_le_exp N D t hN ht
      _ < ((2 : ℝ) ^ D)⁻¹ := exp_neg_natCast_lt_two_pow_inv D hD
  have hreal :
      (2 : ℝ) ^ D * hammingBallVolume N t < (2 : ℝ) ^ N := by
    have h := (div_lt_iff₀ (show 0 < (2 : ℝ) ^ N by positivity)).mp hratio
    have hmul := mul_lt_mul_of_pos_left h (show 0 < (2 : ℝ) ^ D by positivity)
    field_simp at hmul
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hnat : 2 ^ D * hammingBallVolume N t < 2 ^ N := by
    exact_mod_cast hreal
  have hpowN : 2 ^ N = 2 ^ D * 2 ^ (N - D) := by
    rw [← pow_add, Nat.add_sub_of_le hDN]
  rw [hpowN] at hnat
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ D)).mp hnat

/-- Finite-dimensional form of Carlet's probabilistic lower bound. -/
theorem exists_higherOrderNonlinearity_gt_lower_bound_of_dimension
    (r n : ℕ)
    (hdimension :
      2 * (∑ j ∈ Finset.range (r + 1), Nat.choose n j) ≤ 2 ^ n) :
    ∃ f : BooleanFunction n,
      (2 : ℝ) ^ n / 2 -
          Real.sqrt
            ((2 : ℝ) ^ n / 2 *
              (∑ j ∈ Finset.range (r + 1), Nat.choose n j : ℕ)) <
        (higherOrderNonlinearity r f : ℝ) := by
  let N : ℕ := 2 ^ n
  let D : ℕ := ∑ j ∈ Finset.range (r + 1), Nat.choose n j
  let threshold : ℝ :=
    (N : ℝ) / 2 - Real.sqrt ((N : ℝ) * D / 2)
  have hN : 0 < N := by simp [N]
  have hD : 0 < D := by
    simp only [D, Finset.sum_pos_iff]
    exact ⟨0, by simp, by simp⟩
  have hDN : D ≤ N := by
    dsimp only [D, N]
    omega
  have hthreshold : 0 ≤ threshold := by
    have hdimensionR : (2 : ℝ) * D ≤ N := by
      exact_mod_cast hdimension
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hsqrtSq : Real.sqrt ((N : ℝ) * D / 2) ^ 2 = (N : ℝ) * D / 2 :=
      Real.sq_sqrt (by positivity)
    have hsqrtNonneg := Real.sqrt_nonneg ((N : ℝ) * D / 2)
    dsimp only [threshold]
    have hproduct : 0 ≤ (N : ℝ) * ((N : ℝ) - 2 * D) :=
      mul_nonneg hNreal.le (sub_nonneg.mpr hdimensionR)
    nlinarith
  let t : ℕ := ⌊threshold⌋₊
  have ht : (t : ℝ) ≤ (N : ℝ) / 2 - Real.sqrt ((N : ℝ) * D / 2) := by
    exact Nat.floor_le hthreshold
  have hvolume : hammingBallVolume N t < 2 ^ (N - D) :=
    hammingBallVolume_lt_two_pow_sub N D t hN hD hDN ht
  obtain ⟨f, hf⟩ :=
    exists_higherOrderNonlinearity_gt_of_hammingBallVolume_lt
      r n t hDN (by simpa [N, D] using hvolume)
  refine ⟨f, ?_⟩
  have hthresholdLt : threshold < (higherOrderNonlinearity r f : ℝ) :=
    (Nat.floor_lt hthreshold).mp hf
  simpa [threshold, N, D, div_mul_eq_mul_div] using hthresholdLt

private theorem sum_choose_le_mul_pow (r n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (r + 1), Nat.choose n j) ≤ (r + 1) * n ^ r := by
  calc
    (∑ j ∈ Finset.range (r + 1), Nat.choose n j) ≤
        ∑ _j ∈ Finset.range (r + 1), n ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow n j).trans
        (Nat.pow_le_pow_right hn (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = (r + 1) * n ^ r := by simp [mul_comm]

/-- For fixed order `r`, the Reed--Muller dimension is eventually at most
half of the ambient Boolean cube dimension. -/
theorem eventually_twice_sum_choose_le_two_pow (r : ℕ) :
    ∀ᶠ n in Filter.atTop,
      2 * (∑ j ∈ Finset.range (r + 1), Nat.choose n j) ≤ 2 ^ n := by
  have hlittle :
      (fun n : ℕ ↦ (n : ℝ) ^ r) =o[Filter.atTop]
        (fun n : ℕ ↦ (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt r (by norm_num)
  have hconstant : (0 : ℝ) < (2 * (r + 1 : ℕ) : ℝ) := by positivity
  have hbound := hlittle.bound (inv_pos.mpr hconstant)
  filter_upwards [hbound, eventually_gt_atTop 0] with n hn hnpos
  have hn' : 0 < n := hnpos
  norm_num [Real.norm_eq_abs, abs_of_nonneg] at hn
  have hboundR :
      (2 : ℝ) * (r + 1 : ℕ) * (n : ℝ) ^ r ≤ (2 : ℝ) ^ n := by
    have hmul := mul_le_mul_of_nonneg_left hn hconstant.le
    field_simp at hmul
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hboundN : 2 * (r + 1) * n ^ r ≤ 2 ^ n := by
    exact_mod_cast hboundR
  calc
    2 * (∑ j ∈ Finset.range (r + 1), Nat.choose n j) ≤
        2 * ((r + 1) * n ^ r) :=
      Nat.mul_le_mul_left 2 (sum_choose_le_mul_pow r n hn')
    _ = 2 * (r + 1) * n ^ r := by ring
    _ ≤ 2 ^ n := hboundN

private theorem two_pow_nat_div_two_eq_rpow_sub_one (n : ℕ) :
    (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast]
  simpa using
    (Real.rpow_sub (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
      (n : ℝ) 1).symm

/-- Carlet's fixed-order asymptotic lower bound for higher-order nonlinearity. -/
theorem eventually_exists_higherOrderNonlinearity_gt_carlet_lower_bound (r : ℕ) :
    ∀ᶠ n in Filter.atTop,
      ∃ f : BooleanFunction n,
        (2 : ℝ) ^ ((n : ℝ) - 1) -
            Real.sqrt
              ((2 : ℝ) ^ ((n : ℝ) - 1) *
                (∑ j ∈ Finset.range (r + 1), Nat.choose n j : ℕ)) <
          (higherOrderNonlinearity r f : ℝ) := by
  filter_upwards [eventually_twice_sum_choose_le_two_pow r] with n hdimension
  simpa [two_pow_nat_div_two_eq_rpow_sub_one] using
    exists_higherOrderNonlinearity_gt_lower_bound_of_dimension r n hdimension

end CryptBoolean
