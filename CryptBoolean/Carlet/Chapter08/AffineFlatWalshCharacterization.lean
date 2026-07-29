/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Restrictions
public import CryptBoolean.Carlet.Chapter02.Subspaces
public import CryptBoolean.Carlet.Chapter04.AutocorrelationBounds
public import CryptBoolean.Carlet.Chapter04.PropagationCriteria

import FABL.Chapter05.DegreeOneWeight

/-!
# Affine-flat Walsh characterization of propagation criteria

Carlet Proposition 35, obtained by specializing raw Poisson summation to
coordinate subspaces.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance affineFlatWalshSubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

/-- The coordinate subspace consisting of the binary vectors whose supports
are contained in the support of `u`. -/
noncomputable def predecessorSubspace (u : FABL.F₂Cube n) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.perpendicularSubspace
    (FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u))

/-- Membership in the predecessor subspace is support inclusion. -/
@[simp] theorem mem_predecessorSubspace_iff
    (u w : FABL.F₂Cube n) :
    w ∈ predecessorSubspace u ↔ w ≼ u := by
  exact FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
    (FABL.f₂Support u) w

/-- The predecessor subspace has cardinality `2` to the Hamming weight of its
indexing vector. -/
theorem card_predecessorSubspace (u : FABL.F₂Cube n) :
    Nat.card (predecessorSubspace u) =
      2 ^ (FABL.f₂Support u).card := by
  unfold predecessorSubspace
  rw [FABL.card_perpendicularSubspace,
    FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace]

/-- The perpendicular of the predecessor subspace is the coordinate subspace
supported on the complementary coordinates. -/
theorem perpendicular_predecessorSubspace (u : FABL.F₂Cube n) :
    FABL.perpendicularSubspace (predecessorSubspace u) =
      FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u) := by
  unfold predecessorSubspace
  exact FABL.perpendicularSubspace_perpendicularSubspace _

/-- Membership in the perpendicular predecessor subspace is support inclusion
in the complementary coordinates. -/
theorem mem_perpendicular_predecessorSubspace_iff
    (u a : FABL.F₂Cube n) :
    a ∈ FABL.perpendicularSubspace (predecessorSubspace u) ↔
      FABL.f₂Support a ⊆ (FABL.f₂Support u)ᶜ := by
  rw [perpendicular_predecessorSubspace]
  constructor
  · intro ha i hi
    rw [Finset.mem_compl]
    intro hiu
    exact (FABL.mem_f₂Support a i).mp hi
      ((FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff
        (FABL.f₂Support u) a).mp ha i hiu)
  · intro ha
    rw [FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff]
    intro i hiu
    by_contra hai
    exact (Finset.mem_compl.mp (ha ((FABL.mem_f₂Support a i).mpr hai))) hiu

/-- The squared raw Walsh mass on the affine coordinate flat whose directions
precede `u`. -/
noncomputable def predecessorWalshSquareSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) : ℝ :=
  ∑ w ∈ (Finset.univ.filter fun w : FABL.F₂Cube n ↦ w ≼ u),
    (walshTransform f (w + v) : ℝ) ^ 2

private noncomputable def predecessorSubspaceEquiv
    (u : FABL.F₂Cube n) :
    {w : FABL.F₂Cube n // w ≼ u} ≃
      FABL.perpendicularSubspace
        (FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u)) :=
  Equiv.subtypeEquiv (Equiv.refl _) fun w ↦
    (FABL.mem_perpendicular_coordinateZeroSubspace_iff_f₂Support_subset
      (FABL.f₂Support u) w).symm

private theorem predecessorWalshSquareSum_eq_subspaceSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) :
    predecessorWalshSquareSum f u v =
      ∑ w : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u)),
        (walshTransform f (w.1 + v) : ℝ) ^ 2 := by
  classical
  unfold predecessorWalshSquareSum
  calc
    (∑ w ∈ (Finset.univ.filter fun w : FABL.F₂Cube n ↦ w ≼ u),
        (walshTransform f (w + v) : ℝ) ^ 2) =
        ∑ w : {w : FABL.F₂Cube n // w ≼ u},
          (walshTransform f (w.1 + v) : ℝ) ^ 2 := by
      exact Finset.sum_subtype
        (Finset.univ.filter fun w : FABL.F₂Cube n ↦ w ≼ u)
        (fun w ↦ by simp) (fun w ↦ (walshTransform f (w + v) : ℝ) ^ 2)
    _ = ∑ w : FABL.perpendicularSubspace
          (FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u)),
        (walshTransform f (w.1 + v) : ℝ) ^ 2 := by
      apply Fintype.sum_equiv (predecessorSubspaceEquiv u)
      intro w
      rfl

private theorem mem_coordinateZeroSubspace_iff_f₂Support_subset_compl
    (I : Finset (Fin n)) (x : FABL.F₂Cube n) :
    x ∈ FABL.F₂DecisionTree.coordinateZeroSubspace I ↔
      FABL.f₂Support x ⊆ Iᶜ := by
  rw [FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff]
  constructor
  · intro hx i hi
    apply Finset.mem_compl.mpr
    intro hiI
    exact (FABL.mem_f₂Support x i).mp hi (hx i hiI)
  · intro hx i hiI
    by_contra hxi
    have hiSupport : i ∈ FABL.f₂Support x :=
      (FABL.mem_f₂Support x i).mpr hxi
    exact (Finset.mem_compl.mp (hx hiSupport)) hiI

/-- Raw Poisson summation for the affine coordinate flat of predecessors of
`u`. -/
theorem predecessorWalshSquareSum_eq_autocorrelationSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) :
    predecessorWalshSquareSum f u v =
      (2 : ℝ) ^ (FABL.f₂Support u).card *
        ∑ x : FABL.F₂DecisionTree.coordinateZeroSubspace
            (FABL.f₂Support u),
          FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1 := by
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u)
  let E := FABL.perpendicularSubspace Z
  have hcardE : Nat.card E = 2 ^ (FABL.f₂Support u).card := by
    dsimp [E, Z]
    rw [FABL.card_perpendicularSubspace,
      FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace]
  have hperp : FABL.perpendicularSubspace E = Z := by
    dsimp [E]
    exact FABL.perpendicularSubspace_perpendicularSubspace Z
  have hpoisson := rawPoissonSummationFormula
    (autocorrelation f) E v 0
  simp_rw [rawFourierTransform_autocorrelation] at hpoisson
  rw [predecessorWalshSquareSum_eq_subspaceSum]
  rw [hcardE, hperp] at hpoisson
  simpa [E, Z, add_comm] using hpoisson

private theorem predecessorWalshSquareSum_eq_two_pow_iff
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    (∀ v, predecessorWalshSquareSum f u v =
      (2 : ℝ) ^ (n + (FABL.f₂Support u).card)) ↔
      ∀ a : FABL.F₂Cube n, a ≠ 0 →
        FABL.f₂Support a ⊆ (FABL.f₂Support u)ᶜ →
          autocorrelation f a = 0 := by
  classical
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support u)
  constructor
  · intro hsums a ha hasupport
    have haZ : a ∈ Z := by
      exact (mem_coordinateZeroSubspace_iff_f₂Support_subset_compl
        (FABL.f₂Support u) a).mpr hasupport
    have hsubspaceTransform (v : FABL.F₂Cube n) :
        (∑ x : Z, FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1) =
          (2 : ℝ) ^ n := by
      have hrelation := predecessorWalshSquareSum_eq_autocorrelationSum f u v
      rw [hsums v, pow_add] at hrelation
      apply mul_left_cancel₀
        (by positivity : (2 : ℝ) ^ (FABL.f₂Support u).card ≠ 0)
      calc
        (2 : ℝ) ^ (FABL.f₂Support u).card *
            (∑ x : Z,
              FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1) =
            (2 : ℝ) ^ n * (2 : ℝ) ^ (FABL.f₂Support u).card :=
          hrelation.symm
        _ = (2 : ℝ) ^ (FABL.f₂Support u).card * (2 : ℝ) ^ n := by
          ring
    let ψ : FABL.F₂Cube n → ℝ :=
      fun x ↦ if x ∈ Z then autocorrelation f x else 0
    have htransform (v : FABL.F₂Cube n) :
        rawFourierTransform ψ v = (2 : ℝ) ^ n := by
      rw [rawFourierTransform]
      calc
        (∑ x, ψ x * FABL.vectorWalshCharacter v x) =
            ∑ x ∈ (Finset.univ.filter fun x : FABL.F₂Cube n ↦ x ∈ Z),
              autocorrelation f x * FABL.vectorWalshCharacter v x := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hxZ : x ∈ Z <;> simp [ψ, hxZ]
        _ = ∑ x : Z,
              autocorrelation f x.1 * FABL.vectorWalshCharacter v x.1 := by
          exact Finset.sum_subtype
            (Finset.univ.filter fun x : FABL.F₂Cube n ↦ x ∈ Z)
            (fun x ↦ by simp)
            (fun x ↦ autocorrelation f x * FABL.vectorWalshCharacter v x)
        _ = ∑ x : Z,
              FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1 := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = (2 : ℝ) ^ n := hsubspaceTransform v
    have htransformFunction :
        rawFourierTransform ψ = fun _ ↦ (2 : ℝ) ^ n := by
      funext v
      exact htransform v
    have hconstantTransform :
        rawFourierTransform (fun _ : FABL.F₂Cube n ↦ (2 : ℝ) ^ n) a = 0 := by
      calc
        rawFourierTransform (fun _ : FABL.F₂Cube n ↦ (2 : ℝ) ^ n) a =
            (2 : ℝ) ^ n * rawFourierTransform (fun _ ↦ (1 : ℝ)) a := by
          unfold rawFourierTransform
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = 0 := by rw [rawFourierTransform_one, if_neg ha, mul_zero]
    have hinvolution := rawFourierTransform_involution ψ a
    rw [htransformFunction, hconstantTransform] at hinvolution
    have hψ : ψ a = autocorrelation f a := by simp [ψ, haZ]
    rw [hψ] at hinvolution
    exact (mul_eq_zero.mp hinvolution.symm).resolve_left (by positivity)
  · intro hautocorrelation v
    rw [predecessorWalshSquareSum_eq_autocorrelationSum]
    have hsum :
        (∑ x : Z, FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1) =
          (2 : ℝ) ^ n := by
      rw [Finset.sum_eq_single (0 : Z)]
      · simp [autocorrelation_zero]
      · intro x _hx hx0
        have hxne : x.1 ≠ 0 := by
          intro hxval
          exact hx0 (Subtype.ext hxval)
        have hxsupport :
            FABL.f₂Support x.1 ⊆ (FABL.f₂Support u)ᶜ := by
          exact (mem_coordinateZeroSubspace_iff_f₂Support_subset_compl
            (FABL.f₂Support u) x.1).mp x.2
        rw [hautocorrelation x.1 hxne hxsupport, mul_zero]
      · intro hzero
        exact (hzero (Finset.mem_univ _)).elim
    rw [show (∑ x : FABL.F₂DecisionTree.coordinateZeroSubspace
        (FABL.f₂Support u),
          FABL.vectorWalshCharacter v x.1 * autocorrelation f x.1) =
        (2 : ℝ) ^ n by simpa [Z] using hsum]
    rw [pow_add]
    ring

/-- Carlet Proposition 35: `PC(l)` is equivalent to a constant squared-Walsh
mass on every affine coordinate flat of dimension at least `n-l`. -/
theorem satisfiesPropagationCriterion_iff_predecessorWalshSquareSum
    (l : ℕ) (f : BooleanFunction n) :
    SatisfiesPropagationCriterion l f ↔
      ∀ u v : FABL.F₂Cube n,
        n - l ≤ (FABL.f₂Support u).card →
          predecessorWalshSquareSum f u v =
            (2 : ℝ) ^ (n + (FABL.f₂Support u).card) := by
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero]
  constructor
  · intro hpc u v hu
    apply (predecessorWalshSquareSum_eq_two_pow_iff f u).mpr
    intro a ha hasupport
    apply hpc a ha
    have hcard := Finset.card_le_card hasupport
    rw [Finset.card_compl, Fintype.card_fin] at hcard
    omega
  · intro hsums a ha hweight
    let u : FABL.F₂Cube n :=
      FABL.f₂CubeOfFinset (FABL.f₂Support a)ᶜ
    have husupport : FABL.f₂Support u = (FABL.f₂Support a)ᶜ := by
      exact (FABL.f₂CubeEquivFinset n).right_inv _
    have huweight : n - l ≤ (FABL.f₂Support u).card := by
      rw [husupport, Finset.card_compl, Fintype.card_fin]
      omega
    have hu := (predecessorWalshSquareSum_eq_two_pow_iff f u).mp
      (fun v ↦ hsums u v huweight)
    apply hu a ha
    rw [husupport]
    simp

end CryptBoolean
