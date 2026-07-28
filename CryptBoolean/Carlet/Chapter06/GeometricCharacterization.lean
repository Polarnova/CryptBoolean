/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderLowWeightFlats
public import CryptBoolean.Carlet.Chapter05.CoveringSequences
public import CryptBoolean.Carlet.Chapter06.Dual
public import CryptBoolean.Carlet.Chapter06.NNFCharacterization
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Geometric characterization of bent functions

Carlet Theorem 12 and Lemma 3: representations modulo `2^(n/2)` by
indicators of half-dimensional linear subspaces, and the perpendicular-space
formula for the dual of an exact generalized partial-spread representation.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

local instance geometricDualFinite
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V] :
    Finite (Module.Dual FABL.𝔽₂ V) :=
  Finite.of_injective
    (fun ell : Module.Dual FABL.𝔽₂ V ↦ (ell : V → FABL.𝔽₂))
    LinearMap.coe_injective

noncomputable local instance geometricDualFintype
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V] :
    Fintype (Module.Dual FABL.𝔽₂ V) :=
  Fintype.ofFinite _

/-- The integer indicator of a binary linear subspace. -/
noncomputable def linearSubspaceIndicatorInt
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (x : FABL.F₂Cube n) : ℤ := by
  classical
  exact if x ∈ E then 1 else 0

/-- An integer combination of all half-dimensional subspace indicators. -/
noncomputable def halfSubspaceCombination
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (x : FABL.F₂Cube n) : ℤ :=
  ∑ E ∈ binaryLinearSubspaces (n / 2) n,
    c E * linearSubspaceIndicatorInt E x

/-- The integer indicator of the origin. -/
def originIndicatorInt (x : FABL.F₂Cube n) : ℤ :=
  if x = 0 then 1 else 0

/-- The right-hand side of Carlet Relation (51). -/
noncomputable def geometricBentExpression
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (x : FABL.F₂Cube n) : ℤ :=
  halfSubspaceCombination c x -
    (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x

/-- The expression obtained by replacing every half-dimensional subspace by
its perpendicular subspace. -/
noncomputable def perpendicularGeometricBentExpression
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (x : FABL.F₂Cube n) : ℤ :=
  (∑ E ∈ binaryLinearSubspaces (n / 2) n,
      c E * linearSubspaceIndicatorInt (FABL.perpendicularSubspace E) x) -
    (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x

/-- Carlet Relation (16) in the integral normalization: the integer Fourier
transform of a subspace indicator is its cardinality on the perpendicular
subspace. -/
theorem integerWalshTransform_linearSubspaceIndicatorInt
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (u : FABL.F₂Cube n) :
    integerWalshTransform (linearSubspaceIndicatorInt E) u =
      (2 : ℤ) ^ Module.finrank FABL.𝔽₂ E *
        linearSubspaceIndicatorInt (FABL.perpendicularSubspace E) u := by
  classical
  apply Int.cast_injective (α := ℝ)
  have hleft :
      (integerWalshTransform (linearSubspaceIndicatorInt E) u : ℝ) =
        rawFourierTransform
          (FABL.setIndicator (E : Set (FABL.F₂Cube n))) u := by
    rw [integerWalshTransform, rawFourierTransform]
    push_cast
    apply Finset.sum_congr rfl
    intro x _hx
    rw [FABL.vectorWalshCharacter_apply, ← bitSignInt_cast]
    rw [show FABL.f₂DotProduct x u = FABL.f₂DotProduct u x by
      exact dotProduct_comm x u]
    by_cases hxE : x ∈ E <;>
      simp [linearSubspaceIndicatorInt, FABL.setIndicator, hxE]
  rw [hleft, rawFourierTransform_setIndicator_submodule,
    FABL.card_submodule_eq_two_pow_finrank]
  by_cases hu : u ∈ FABL.perpendicularSubspace E <;>
    simp [linearSubspaceIndicatorInt, hu]

/-- The integer Fourier transform of the origin indicator is identically one. -/
@[simp] theorem integerWalshTransform_originIndicatorInt
    (u : FABL.F₂Cube n) :
    integerWalshTransform originIndicatorInt u = 1 := by
  classical
  rw [integerWalshTransform]
  rw [Fintype.sum_eq_single 0]
  · simp [originIndicatorInt, FABL.f₂DotProduct, bitSignInt]
  · intro x hx
    simp [originIndicatorInt, hx]

/-- The integral Fourier transform of the zero-one embedding agrees with the
integral coefficient supplied by the numerical normal form. -/
theorem integerWalshTransform_bitValueInt_eq_booleanNNFFourierCoeffInt
    (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    integerWalshTransform (fun x ↦ bitValueInt (f x)) u =
      booleanNNFFourierCoeffInt f u := by
  apply Int.cast_injective (α := ℝ)
  rw [booleanNNFFourierCoeffInt_cast]
  rw [integerWalshTransform, rawFourierTransform]
  push_cast
  apply Finset.sum_congr rfl
  intro x _hx
  rw [FABL.vectorWalshCharacter_apply, ← bitSignInt_cast]
  rw [show FABL.f₂DotProduct x u = FABL.f₂DotProduct u x by
    exact dotProduct_comm x u]
  by_cases hfx : f x = 1 <;>
    simp [bitValueInt, FABL.booleanRealEmbedding, hfx]

/-- Fourier transformation sends a half-dimensional indicator combination to
the same coefficient combination on perpendicular subspaces, scaled by
`2^(n/2)`. -/
theorem integerWalshTransform_halfSubspaceCombination
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (u : FABL.F₂Cube n) :
    integerWalshTransform (halfSubspaceCombination c) u =
      (2 : ℤ) ^ (n / 2) *
        ∑ E ∈ binaryLinearSubspaces (n / 2) n,
          c E * linearSubspaceIndicatorInt
            (FABL.perpendicularSubspace E) u := by
  classical
  unfold integerWalshTransform halfSubspaceCombination
  calc
    (∑ x, (∑ E ∈ binaryLinearSubspaces (n / 2) n,
          c E * linearSubspaceIndicatorInt E x) *
        bitSignInt (FABL.f₂DotProduct x u)) =
        ∑ E ∈ binaryLinearSubspaces (n / 2) n,
          c E * ∑ x, linearSubspaceIndicatorInt E x *
            bitSignInt (FABL.f₂DotProduct x u) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _hE
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ E ∈ binaryLinearSubspaces (n / 2) n,
          c E * ((2 : ℤ) ^ (n / 2) *
            linearSubspaceIndicatorInt (FABL.perpendicularSubspace E) u) := by
      apply Finset.sum_congr rfl
      intro E hE
      change c E * integerWalshTransform
          (linearSubspaceIndicatorInt E) u = _
      rw [integerWalshTransform_linearSubspaceIndicatorInt,
        (mem_binaryLinearSubspaces E).mp hE]
    _ = (2 : ℤ) ^ (n / 2) *
        ∑ E ∈ binaryLinearSubspaces (n / 2) n,
          c E * linearSubspaceIndicatorInt
            (FABL.perpendicularSubspace E) u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _hE
      ring

/-- The integral transform of Relation (51). -/
theorem integerWalshTransform_geometricBentExpression
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (u : FABL.F₂Cube n) :
    integerWalshTransform (geometricBentExpression c) u =
      (2 : ℤ) ^ (n / 2) *
          ∑ E ∈ binaryLinearSubspaces (n / 2) n,
            c E * linearSubspaceIndicatorInt
              (FABL.perpendicularSubspace E) u -
        (2 : ℤ) ^ (n / 2 - 1) := by
  classical
  unfold geometricBentExpression
  rw [integerWalshTransform]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← integerWalshTransform,
    integerWalshTransform_halfSubspaceCombination]
  have horigin :
      (∑ x, ((2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) *
          bitSignInt (FABL.f₂DotProduct x u)) =
        (2 : ℤ) ^ (n / 2 - 1) := by
    calc
      (∑ x, ((2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) *
          bitSignInt (FABL.f₂DotProduct x u)) =
          (2 : ℤ) ^ (n / 2 - 1) *
            ∑ x, originIndicatorInt x *
              bitSignInt (FABL.f₂DotProduct x u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = (2 : ℤ) ^ (n / 2 - 1) *
          integerWalshTransform originIndicatorInt u := rfl
      _ = (2 : ℤ) ^ (n / 2 - 1) := by
        rw [integerWalshTransform_originIndicatorInt, mul_one]
  rw [horigin]

/-- A Boolean function satisfies Carlet Relation (51) when its integer
zero-one embedding is pointwise congruent to a geometric expression modulo
`2^(n/2)`. -/
def HasGeometricBentCongruence (f : BooleanFunction n) : Prop :=
  ∃ c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ,
    ∀ x : FABL.F₂Cube n,
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (bitValueInt (f x)) (geometricBentExpression c x)

/-- The sufficient direction of Carlet Theorem 12: every function satisfying
the geometric congruence is bent. -/
theorem isBent_of_hasGeometricBentCongruence
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : HasGeometricBentCongruence f) : IsBent f := by
  obtain ⟨c, hc⟩ := hf
  apply (isBent_iff_forall_booleanNNFFourierCoeffInt_modeq f hn hnTwo).2
  intro u
  have htransform :
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (integerWalshTransform (fun x ↦ bitValueInt (f x)) u)
        (integerWalshTransform (geometricBentExpression c) u) := by
    rw [Int.modEq_iff_dvd]
    unfold integerWalshTransform
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro x _hx
    have hx := (hc x).dvd.mul_right
      (bitSignInt (FABL.f₂DotProduct x u))
    convert hx using 1
    ring
  have hhalfPos : 1 ≤ n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hdouble : (2 : ℤ) ^ (n / 2) =
      2 * (2 : ℤ) ^ (n / 2 - 1) := by
    conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hexpression :
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (integerWalshTransform (geometricBentExpression c) u)
        ((2 : ℤ) ^ (n / 2 - 1)) := by
    rw [integerWalshTransform_geometricBentExpression,
      Int.modEq_iff_dvd]
    refine ⟨1 - ∑ E ∈ binaryLinearSubspaces (n / 2) n,
      c E * linearSubspaceIndicatorInt
        (FABL.perpendicularSubspace E) u, ?_⟩
    rw [hdouble]
    ring
  have hcoefficient := htransform.trans hexpression
  rwa [integerWalshTransform_bitValueInt_eq_booleanNNFFourierCoeffInt]
    at hcoefficient

/-- An exact generalized partial-spread representation is Relation (51)
without reduction modulo `2^(n/2)`. -/
def HasExactGPSRepresentation
    (f : BooleanFunction n)
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ) : Prop :=
  ∀ x : FABL.F₂Cube n,
    bitValueInt (f x) = geometricBentExpression c x

/-- Carlet Theorem 12, exact case: a generalized partial-spread
representation is bent, and its dual is obtained by replacing every subspace
with its perpendicular subspace. -/
theorem isBent_and_bitValueInt_bentDual_of_exactGPSRepresentation
    (f : BooleanFunction n)
    (c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ)
    (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : HasExactGPSRepresentation f c) :
    IsBent f ∧
      ∀ u : FABL.F₂Cube n,
        bitValueInt (bentDual f u) =
          perpendicularGeometricBentExpression c u := by
  have hcongruence : HasGeometricBentCongruence f := by
    refine ⟨c, fun x ↦ ?_⟩
    rw [hf x]
  have hbent := isBent_of_hasGeometricBentCongruence f hn hnTwo hcongruence
  refine ⟨hbent, ?_⟩
  intro u
  let S : ℤ :=
    ∑ E ∈ binaryLinearSubspaces (n / 2) n,
      c E * linearSubspaceIndicatorInt
        (FABL.perpendicularSubspace E) u
  have hsplit : n = n / 2 + n / 2 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hhalfPos : 1 ≤ n / 2 := by omega
  have hdouble : (2 : ℤ) ^ (n / 2) =
      2 * (2 : ℤ) ^ (n / 2 - 1) := by
    conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hpower : (2 : ℤ) ^ n =
      (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) := by
    calc
      (2 : ℤ) ^ n = (2 : ℤ) ^ (n / 2 + n / 2) :=
        congrArg (fun k : ℕ ↦ (2 : ℤ) ^ k) hsplit
      _ = (2 : ℤ) ^ (n / 2) * (2 : ℤ) ^ (n / 2) := by
        rw [pow_add]
  have htransform :
      integerWalshTransform (fun x ↦ bitValueInt (f x)) u =
        integerWalshTransform (geometricBentExpression c) u := by
    unfold integerWalshTransform
    apply Finset.sum_congr rfl
    intro x _hx
    exact congrArg
      (fun z : ℤ ↦ z * bitSignInt (FABL.f₂DotProduct x u)) (hf x)
  have hcoefficient : booleanNNFFourierCoeffInt f u =
      (2 : ℤ) ^ (n / 2) * S -
        (2 : ℤ) ^ (n / 2 - 1) := by
    rw [← integerWalshTransform_bitValueInt_eq_booleanNNFFourierCoeffInt,
      htransform, integerWalshTransform_geometricBentExpression]
  have hwalsh :=
    walshTransform_eq_indicator_sub_two_mul_booleanNNFFourierCoeffInt f u
  rw [hcoefficient] at hwalsh
  have hwalshExpression :
      walshTransform f u =
        (2 : ℤ) ^ (n / 2) *
          (1 - 2 * perpendicularGeometricBentExpression c u) := by
    rw [hwalsh]
    unfold perpendicularGeometricBentExpression originIndicatorInt
    change _ = (2 : ℤ) ^ (n / 2) *
      (1 - 2 * (S - (2 : ℤ) ^ (n / 2 - 1) *
        (if u = 0 then 1 else 0)))
    by_cases hu : u = 0
    · simp only [if_pos hu]
      rw [hpower, hdouble]
      ring
    · simp only [if_neg hu]
      rw [hdouble]
      ring
  have hdualWalsh :=
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hbent u
  rw [hwalshExpression] at hdualWalsh
  have hsign : bitSignInt (bentDual f u) =
      1 - 2 * perpendicularGeometricBentExpression c u := by
    exact mul_left_cancel₀ (by positivity : (2 : ℤ) ^ (n / 2) ≠ 0)
      hdualWalsh.symm
  rw [bitSignInt_eq_one_sub_two_mul_bitValueInt] at hsign
  omega

/-- The ambient image of the kernel of a linear functional on a subspace. -/
noncomputable def ambientFunctionalKernel
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ F) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  (LinearMap.ker ell).map F.subtype

theorem mem_ambientFunctionalKernel_iff
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ F)
    (x : FABL.F₂Cube n) (hx : x ∈ F) :
    x ∈ ambientFunctionalKernel F ell ↔ ell ⟨x, hx⟩ = 0 := by
  constructor
  · intro h
    rcases h with ⟨y, hy, hxy⟩
    have hyx : y = ⟨x, hx⟩ := by
      apply Subtype.ext
      exact hxy
    rw [← hyx]
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem finrank_ambientFunctionalKernel
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ F) (hell : ell ≠ 0) :
    Module.finrank FABL.𝔽₂ (ambientFunctionalKernel F ell) + 1 =
      Module.finrank FABL.𝔽₂ F := by
  rw [ambientFunctionalKernel, Submodule.finrank_map_subtype_eq]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hell

/-- The finite set of nonzero linear functionals on a subspace. -/
noncomputable def nonzeroDualFinset
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V] :
    Finset (Module.Dual FABL.𝔽₂ V) := by
  classical
  exact Finset.univ.filter fun ell ↦ ell ≠ 0

@[simp] theorem mem_nonzeroDualFinset
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V]
    (ell : Module.Dual FABL.𝔽₂ V) :
    ell ∈ nonzeroDualFinset V ↔ ell ≠ 0 := by
  classical
  simp [nonzeroDualFinset]

theorem card_nonzeroDualFinset
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V] :
    (nonzeroDualFinset V).card =
      2 ^ Module.finrank FABL.𝔽₂ V - 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hfinset : nonzeroDualFinset V =
      (Finset.univ : Finset (Module.Dual FABL.𝔽₂ V)).erase 0 := by
    ext ell
    simp [nonzeroDualFinset]
  rw [hfinset, Finset.card_erase_of_mem (Finset.mem_univ 0)]
  change Fintype.card (Module.Dual FABL.𝔽₂ V) - 1 = _
  rw [Module.card_eq_pow_finrank (K := FABL.𝔽₂)
      (V := Module.Dual FABL.𝔽₂ V),
    ZMod.card, Subspace.dual_finrank_eq]

private theorem dualEvaluation_ne_zero
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V]
    (y : V) (hy : y ≠ 0) :
    Module.Dual.eval FABL.𝔽₂ V y ≠ 0 := by
  intro hzero
  apply hy
  apply (Module.evalEquiv FABL.𝔽₂ V).injective
  simpa using hzero

private theorem card_nonzeroDual_vanishing
    (V : Type*) [Finite V] [AddCommGroup V] [Module FABL.𝔽₂ V]
    (y : V) (hy : y ≠ 0) :
    ((nonzeroDualFinset V).filter fun ell ↦ ell y = 0).card =
      2 ^ (Module.finrank FABL.𝔽₂ V - 1) - 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let ev : Module.Dual FABL.𝔽₂ V →ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
    Module.Dual.eval FABL.𝔽₂ V y
  have hev : ev ≠ 0 := dualEvaluation_ne_zero V y hy
  have hkerRank : Module.finrank FABL.𝔽₂ (LinearMap.ker ev) =
      Module.finrank FABL.𝔽₂ V - 1 := by
    have hrank := Module.Dual.finrank_ker_add_one_of_ne_zero hev
    rw [Subspace.dual_finrank_eq] at hrank
    omega
  have hfilter :
      (nonzeroDualFinset V).filter (fun ell ↦ ell y = 0) =
        ((Finset.univ : Finset (Module.Dual FABL.𝔽₂ V)).filter
          (fun ell ↦ ell y = 0)).erase 0 := by
    ext ell
    simp [nonzeroDualFinset]
  have hzero : (0 : Module.Dual FABL.𝔽₂ V) ∈
      (Finset.univ.filter fun ell ↦ ell y = 0) := by simp
  rw [hfilter, Finset.card_erase_of_mem hzero]
  rw [← Fintype.card_subtype (fun ell : Module.Dual FABL.𝔽₂ V ↦
      ell y = 0)]
  let e : { ell : Module.Dual FABL.𝔽₂ V // ell y = 0 } ≃
      LinearMap.ker ev := {
    toFun := fun ell ↦ ⟨ell.1, ell.2⟩
    invFun := fun ell ↦ ⟨ell.1, by
      change ev ell.1 = 0
      exact ell.2⟩
    left_inv := fun ell ↦ Subtype.ext rfl
    right_inv := fun ell ↦ Subtype.ext rfl }
  rw [Fintype.card_congr e,
    Module.card_eq_pow_finrank (K := FABL.𝔽₂) (V := LinearMap.ker ev),
    ZMod.card, hkerRank]

/-- Above half dimension, the indicator of a subspace is congruent modulo
`2^(n/2)` to the negative sum of the indicators of the kernels of all its
nonzero linear functionals. -/
theorem functionalKernelCombination_modeq
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hF : n / 2 < Module.finrank FABL.𝔽₂ F) :
    ∀ x : FABL.F₂Cube n,
      Int.ModEq ((2 : ℤ) ^ (n / 2))
        (linearSubspaceIndicatorInt F x)
        (-∑ ell ∈ nonzeroDualFinset F,
          linearSubspaceIndicatorInt (ambientFunctionalKernel F ell) x) := by
  classical
  intro x
  by_cases hxF : x ∈ F
  · by_cases hx0 : x = 0
    · subst x
      have hsum :
          (∑ ell ∈ nonzeroDualFinset F,
            linearSubspaceIndicatorInt (ambientFunctionalKernel F ell) 0) =
              ((nonzeroDualFinset F).card : ℤ) := by
        simp [linearSubspaceIndicatorInt]
      have hcard : ((nonzeroDualFinset F).card : ℤ) =
          (2 : ℤ) ^ Module.finrank FABL.𝔽₂ F - 1 := by
        have hle : 1 ≤ (2 : ℕ) ^ Module.finrank FABL.𝔽₂ F :=
          Nat.one_le_pow _ _ (by omega)
        rw [card_nonzeroDualFinset]
        norm_num [Nat.cast_sub hle]
      rw [linearSubspaceIndicatorInt, if_pos (Submodule.zero_mem F), hsum,
        hcard, Int.modEq_iff_dvd]
      have heq : -((2 : ℤ) ^ Module.finrank FABL.𝔽₂ F - 1) - 1 =
          -((2 : ℤ) ^ Module.finrank FABL.𝔽₂ F) := by ring
      rw [heq]
      exact (pow_dvd_pow (2 : ℤ) (Nat.le_of_lt hF)).neg_right
    · let y : F := ⟨x, hxF⟩
      have hy : y ≠ 0 := by
        intro hyzero
        apply hx0
        exact congrArg Subtype.val hyzero
      have hsum :
          (∑ ell ∈ nonzeroDualFinset F,
            linearSubspaceIndicatorInt (ambientFunctionalKernel F ell) x) =
              (((nonzeroDualFinset F).filter fun ell ↦ ell y = 0).card : ℤ) := by
        calc
          (∑ ell ∈ nonzeroDualFinset F,
              linearSubspaceIndicatorInt (ambientFunctionalKernel F ell) x) =
              ∑ ell ∈ nonzeroDualFinset F,
                if ell y = 0 then (1 : ℤ) else 0 := by
            apply Finset.sum_congr rfl
            intro ell _hell
            rw [linearSubspaceIndicatorInt,
              mem_ambientFunctionalKernel_iff F ell x hxF]
            simp [y]
          _ = (((nonzeroDualFinset F).filter fun ell ↦ ell y = 0).card : ℤ) := by
            rw [Finset.sum_boole]
      have hcard :
          (((nonzeroDualFinset F).filter fun ell ↦ ell y = 0).card : ℤ) =
            (2 : ℤ) ^ (Module.finrank FABL.𝔽₂ F - 1) - 1 := by
        have hle : 1 ≤ (2 : ℕ) ^ (Module.finrank FABL.𝔽₂ F - 1) :=
          Nat.one_le_pow _ _ (by omega)
        rw [card_nonzeroDual_vanishing F y hy]
        norm_num [Nat.cast_sub hle]
      rw [linearSubspaceIndicatorInt, if_pos hxF, hsum, hcard,
        Int.modEq_iff_dvd]
      have hrank : n / 2 ≤ Module.finrank FABL.𝔽₂ F - 1 := by omega
      have heq : -((2 : ℤ) ^ (Module.finrank FABL.𝔽₂ F - 1) - 1) - 1 =
          -((2 : ℤ) ^ (Module.finrank FABL.𝔽₂ F - 1)) := by ring
      rw [heq]
      exact (pow_dvd_pow (2 : ℤ) hrank).neg_right
  · have hkernel : ∀ ell : Module.Dual FABL.𝔽₂ F,
        x ∉ ambientFunctionalKernel F ell := by
      intro ell hx
      exact hxF (F.map_subtype_le (LinearMap.ker ell) hx)
    simp [linearSubspaceIndicatorInt, hxF, hkernel]

/-- An integer-valued function is representable modulo `2^(n/2)` by an
integer combination of half-dimensional subspace indicators. -/
def HasHalfSubspaceRepresentation
    (g : FABL.F₂Cube n → ℤ) : Prop :=
  ∃ c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ,
    ∀ x : FABL.F₂Cube n,
      Int.ModEq ((2 : ℤ) ^ (n / 2)) (g x) (halfSubspaceCombination c x)

private theorem hasHalfSubspaceRepresentation_of_pointwise_modeq
    {g h : FABL.F₂Cube n → ℤ}
    (hgh : ∀ x, Int.ModEq ((2 : ℤ) ^ (n / 2)) (g x) (h x))
    (hh : HasHalfSubspaceRepresentation h) :
    HasHalfSubspaceRepresentation g := by
  obtain ⟨c, hc⟩ := hh
  exact ⟨c, fun x ↦ (hgh x).trans (hc x)⟩

private theorem HasHalfSubspaceRepresentation.add
    {g h : FABL.F₂Cube n → ℤ}
    (hg : HasHalfSubspaceRepresentation g)
    (hh : HasHalfSubspaceRepresentation h) :
    HasHalfSubspaceRepresentation (fun x ↦ g x + h x) := by
  classical
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hh
  refine ⟨fun E ↦ c E + d E, fun x ↦ ?_⟩
  simpa [halfSubspaceCombination, add_mul, Finset.sum_add_distrib] using
    (hc x).add (hd x)

private theorem HasHalfSubspaceRepresentation.neg
    {g : FABL.F₂Cube n → ℤ}
    (hg : HasHalfSubspaceRepresentation g) :
    HasHalfSubspaceRepresentation (fun x ↦ -g x) := by
  classical
  obtain ⟨c, hc⟩ := hg
  refine ⟨fun E ↦ -c E, fun x ↦ ?_⟩
  simpa [halfSubspaceCombination] using (hc x).neg

private theorem HasHalfSubspaceRepresentation.intMul
    (a : ℤ) {g : FABL.F₂Cube n → ℤ}
    (hg : HasHalfSubspaceRepresentation g) :
    HasHalfSubspaceRepresentation (fun x ↦ a * g x) := by
  classical
  obtain ⟨c, hc⟩ := hg
  refine ⟨fun E ↦ a * c E, fun x ↦ ?_⟩
  have hx := (hc x).mul_left a
  rw [halfSubspaceCombination] at hx ⊢
  rw [Finset.mul_sum] at hx
  simpa [mul_assoc] using hx

private theorem HasHalfSubspaceRepresentation.sum
    {I : Type*}
    (s : Finset I) (g : I → FABL.F₂Cube n → ℤ)
    (hg : ∀ i ∈ s, HasHalfSubspaceRepresentation (g i)) :
    HasHalfSubspaceRepresentation (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ 0, fun x ↦ ?_⟩
      simp [halfSubspaceCombination]
  | @insert i s hi ih =>
      have hgi := hg i (Finset.mem_insert_self i s)
      have hgs : ∀ j ∈ s, HasHalfSubspaceRepresentation (g j) := by
        intro j hj
        exact hg j (Finset.mem_insert_of_mem hj)
      simpa [hi] using hgi.add (ih hgs)

/-- The indicator of a half-dimensional subspace is itself a half-subspace
combination. -/
theorem hasHalfSubspaceRepresentation_indicator_of_finrank_eq
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hF : Module.finrank FABL.𝔽₂ F = n / 2) :
    HasHalfSubspaceRepresentation (linearSubspaceIndicatorInt F) := by
  classical
  let c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ :=
    fun E ↦ if E = F then 1 else 0
  refine ⟨c, fun x ↦ ?_⟩
  have hmem : F ∈ binaryLinearSubspaces (n / 2) n :=
    (mem_binaryLinearSubspaces F).mpr hF
  have hcombination : halfSubspaceCombination c x =
      linearSubspaceIndicatorInt F x := by
    simp [halfSubspaceCombination, c, hmem]
  rw [hcombination]

private theorem hasHalfSubspaceRepresentation_indicator_of_half_le_finrank_aux
    (d : ℕ) :
    ∀ F : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      Module.finrank FABL.𝔽₂ F = d → n / 2 ≤ d →
        HasHalfSubspaceRepresentation (linearSubspaceIndicatorInt F) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro F hFd hhalf
      by_cases hd : d = n / 2
      · apply hasHalfSubspaceRepresentation_indicator_of_finrank_eq F
        omega
      · have hhalfLt : n / 2 < Module.finrank FABL.𝔽₂ F := by omega
        have hkernel : ∀ ell ∈ nonzeroDualFinset F,
            HasHalfSubspaceRepresentation
              (linearSubspaceIndicatorInt (ambientFunctionalKernel F ell)) := by
          intro ell hell
          have hrank := finrank_ambientFunctionalKernel F ell
            ((mem_nonzeroDualFinset F ell).mp hell)
          have hkernelRank :
              Module.finrank FABL.𝔽₂ (ambientFunctionalKernel F ell) = d - 1 := by
            rw [hFd] at hrank
            omega
          apply ih (d - 1) (by omega) (ambientFunctionalKernel F ell)
            hkernelRank
          omega
        have hsum := HasHalfSubspaceRepresentation.sum
          (nonzeroDualFinset F)
          (fun ell ↦ linearSubspaceIndicatorInt (ambientFunctionalKernel F ell))
          hkernel
        apply hasHalfSubspaceRepresentation_of_pointwise_modeq
          (functionalKernelCombination_modeq F hhalfLt)
        exact hsum.neg

/-- The high-dimensional branch of Carlet Lemma 3. -/
theorem hasHalfSubspaceRepresentation_indicator_of_half_le_finrank
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hF : n / 2 ≤ Module.finrank FABL.𝔽₂ F) :
    HasHalfSubspaceRepresentation (linearSubspaceIndicatorInt F) :=
  hasHalfSubspaceRepresentation_indicator_of_half_le_finrank_aux
    (Module.finrank FABL.𝔽₂ F) F rfl hF

private theorem exists_superSubmodule_finrank_add_two
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hF : Module.finrank FABL.𝔽₂ F + 2 ≤ n) :
    ∃ G : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      F ≤ G ∧
        Module.finrank FABL.𝔽₂ G =
          Module.finrank FABL.𝔽₂ F + 2 := by
  have hambient : Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hFlt : Module.finrank FABL.𝔽₂ F <
      Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) := by omega
  obtain ⟨a, ha⟩ := Submodule.exists_of_finrank_lt F hFlt
  have haF : a ∉ F := by simpa using ha 1 one_ne_zero
  let A := F ⊔ Submodule.span FABL.𝔽₂ {a}
  have hArank : Module.finrank FABL.𝔽₂ A =
      Module.finrank FABL.𝔽₂ F + 1 := by
    exact Submodule.finrank_sup_span_singleton haF
  have hAlt : Module.finrank FABL.𝔽₂ A <
      Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) := by omega
  obtain ⟨b, hb⟩ := Submodule.exists_of_finrank_lt A hAlt
  have hbA : b ∉ A := by simpa using hb 1 one_ne_zero
  let G := A ⊔ Submodule.span FABL.𝔽₂ {b}
  refine ⟨G, le_trans le_sup_left le_sup_left, ?_⟩
  rw [show Module.finrank FABL.𝔽₂ G =
      Module.finrank FABL.𝔽₂ A + 1 by
        exact Submodule.finrank_sup_span_singleton hbA,
    hArank]

/-- The preimage in the ambient cube of a functional kernel on the quotient
`G / F`. -/
local instance geometricRelativeQuotientFinite
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finite (G ⧸ F.comap G.subtype) :=
  Finite.of_surjective (Submodule.mkQ (F.comap G.subtype))
    (Submodule.mkQ_surjective (F.comap G.subtype))

noncomputable def rankTwoIntermediateSubspace
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ (G ⧸ F.comap G.subtype)) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  ambientFunctionalKernel G (ell.comp (Submodule.mkQ (F.comap G.subtype)))

theorem mem_rankTwoIntermediateSubspace_iff
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ (G ⧸ F.comap G.subtype))
    (x : FABL.F₂Cube n) (hxG : x ∈ G) :
    x ∈ rankTwoIntermediateSubspace F G ell ↔
      ell (Submodule.mkQ (F.comap G.subtype) ⟨x, hxG⟩) = 0 := by
  rw [rankTwoIntermediateSubspace,
    mem_ambientFunctionalKernel_iff G _ x hxG]
  rfl

theorem finrank_rankTwoIntermediateSubspace
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (ell : Module.Dual FABL.𝔽₂ (G ⧸ F.comap G.subtype))
    (hell : ell ≠ 0) :
    Module.finrank FABL.𝔽₂ (rankTwoIntermediateSubspace F G ell) + 1 =
      Module.finrank FABL.𝔽₂ G := by
  apply finrank_ambientFunctionalKernel
  intro hcomp
  apply hell
  apply LinearMap.ext
  intro q
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective (F.comap G.subtype) q
  have hg := LinearMap.congr_fun hcomp g
  simpa [rankTwoIntermediateSubspace] using hg

private theorem finrank_relativeQuotient_eq_two
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hFG : F ≤ G)
    (hG : Module.finrank FABL.𝔽₂ G =
      Module.finrank FABL.𝔽₂ F + 2) :
    Module.finrank FABL.𝔽₂ (G ⧸ F.comap G.subtype) = 2 := by
  let W : Submodule FABL.𝔽₂ G := F.comap G.subtype
  have hmap : W.map G.subtype = F := by
    rw [show W = F.comap G.subtype by rfl, Submodule.map_comap_subtype,
      inf_eq_right.mpr hFG]
  have hW : Module.finrank FABL.𝔽₂ W =
      Module.finrank FABL.𝔽₂ F := by
    rw [← Submodule.finrank_map_subtype_eq G W, hmap]
  have hquotient := W.finrank_quotient_add_finrank
  dsimp [W] at hW hquotient
  rw [hW, hG] at hquotient
  omega

/-- The rank-two subspace diamond: if `G/F` has dimension two, its three
nonzero dual kernels are the three intermediate subspaces, and their indicator
sum is `1_G + 2·1_F`. -/
theorem rankTwoSubspaceDiamond
    (F G : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hFG : F ≤ G)
    (hG : Module.finrank FABL.𝔽₂ G =
      Module.finrank FABL.𝔽₂ F + 2) :
    (∀ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
        Module.finrank FABL.𝔽₂ (rankTwoIntermediateSubspace F G ell) =
          Module.finrank FABL.𝔽₂ F + 1) ∧
      ∀ x : FABL.F₂Cube n,
        (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
          linearSubspaceIndicatorInt (rankTwoIntermediateSubspace F G ell) x) =
            linearSubspaceIndicatorInt G x +
              2 * linearSubspaceIndicatorInt F x := by
  classical
  have hquotient := finrank_relativeQuotient_eq_two F G hFG hG
  constructor
  · intro ell hell
    have hrank := finrank_rankTwoIntermediateSubspace F G ell
      ((mem_nonzeroDualFinset _ ell).mp hell)
    rw [hG] at hrank
    omega
  · intro x
    by_cases hxG : x ∈ G
    · let q : G ⧸ F.comap G.subtype :=
          Submodule.mkQ (F.comap G.subtype) ⟨x, hxG⟩
      have hqzero : q = 0 ↔ x ∈ F := by
        simp [q, Submodule.Quotient.mk_eq_zero]
      by_cases hxF : x ∈ F
      · have hq : q = 0 := hqzero.mpr hxF
        have hsum :
            (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
              linearSubspaceIndicatorInt (rankTwoIntermediateSubspace F G ell) x) =
                ((nonzeroDualFinset (G ⧸ F.comap G.subtype)).card : ℤ) := by
          calc
            (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
                linearSubspaceIndicatorInt
                  (rankTwoIntermediateSubspace F G ell) x) =
                ∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
                  (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro ell _hell
              have hmk :
                  Submodule.mkQ (F.comap G.subtype) ⟨x, hxG⟩ = 0 := hq
              rw [linearSubspaceIndicatorInt,
                mem_rankTwoIntermediateSubspace_iff F G ell x hxG]
              simp [hmk]
            _ = _ := by simp
        rw [hsum, card_nonzeroDualFinset, hquotient]
        norm_num [linearSubspaceIndicatorInt, hxG, hxF]
      · have hq : q ≠ 0 := fun h ↦ hxF (hqzero.mp h)
        have hsum :
            (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
              linearSubspaceIndicatorInt (rankTwoIntermediateSubspace F G ell) x) =
                (((nonzeroDualFinset (G ⧸ F.comap G.subtype)).filter
                  fun ell ↦ ell q = 0).card : ℤ) := by
          calc
            (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
                linearSubspaceIndicatorInt
                  (rankTwoIntermediateSubspace F G ell) x) =
                ∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
                  if ell q = 0 then (1 : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro ell _hell
              rw [linearSubspaceIndicatorInt,
                mem_rankTwoIntermediateSubspace_iff F G ell x hxG]
              simp [q]
            _ = _ := by rw [Finset.sum_boole]
        rw [hsum, card_nonzeroDual_vanishing _ q hq, hquotient]
        norm_num [linearSubspaceIndicatorInt, hxG, hxF]
    · have hxF : x ∉ F := fun hx ↦ hxG (hFG hx)
      have hkernel :
          ∀ ell : Module.Dual FABL.𝔽₂ (G ⧸ F.comap G.subtype),
            x ∉ rankTwoIntermediateSubspace F G ell := by
        intro ell hx
        exact hxG (G.map_subtype_le _ hx)
      simp [linearSubspaceIndicatorInt, hxG, hxF, hkernel]

private theorem hasHalfSubspaceRepresentation_scaledIndicator_aux
    (hn : Even n) (k : ℕ) :
    ∀ F : Submodule FABL.𝔽₂ (FABL.F₂Cube n),
      n / 2 - Module.finrank FABL.𝔽₂ F = k →
        Module.finrank FABL.𝔽₂ F ≤ n / 2 →
          HasHalfSubspaceRepresentation
            (fun x ↦ (2 : ℤ) ^
              (n / 2 - Module.finrank FABL.𝔽₂ F) *
                linearSubspaceIndicatorInt F x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro F hgap hFle
      by_cases hk : k = 0
      · have hFrank : Module.finrank FABL.𝔽₂ F = n / 2 := by omega
        simpa [hFrank] using
          hasHalfSubspaceRepresentation_indicator_of_finrank_eq F hFrank
      · have hFlt : Module.finrank FABL.𝔽₂ F < n / 2 := by omega
        have hroom : Module.finrank FABL.𝔽₂ F + 2 ≤ n := by
          rcases hn with ⟨r, hr⟩
          have hhalf : n / 2 = r := by omega
          omega
        obtain ⟨G, hFG, hGrank⟩ :=
          exists_superSubmodule_finrank_add_two F hroom
        have hdiamond := rankTwoSubspaceDiamond F G hFG hGrank
        let p : ℤ :=
          (2 : ℤ) ^ (n / 2 - Module.finrank FABL.𝔽₂ F - 1)
        have hinter : ∀ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
            HasHalfSubspaceRepresentation
              (fun x ↦ p * linearSubspaceIndicatorInt
                (rankTwoIntermediateSubspace F G ell) x) := by
          intro ell hell
          have hrank := hdiamond.1 ell hell
          have hle : Module.finrank FABL.𝔽₂
              (rankTwoIntermediateSubspace F G ell) ≤ n / 2 := by omega
          have hnewGap : n / 2 - Module.finrank FABL.𝔽₂
              (rankTwoIntermediateSubspace F G ell) = k - 1 := by omega
          have hrec := ih (k - 1) (by omega)
            (rankTwoIntermediateSubspace F G ell) hnewGap hle
          have hexponent :
              n / 2 - Module.finrank FABL.𝔽₂
                (rankTwoIntermediateSubspace F G ell) =
                n / 2 - Module.finrank FABL.𝔽₂ F - 1 := by omega
          simpa [p, hexponent] using hrec
        have hinterSum := HasHalfSubspaceRepresentation.sum
          (nonzeroDualFinset (G ⧸ F.comap G.subtype))
          (fun ell x ↦ p * linearSubspaceIndicatorInt
            (rankTwoIntermediateSubspace F G ell) x)
          hinter
        have hGrepresentation : HasHalfSubspaceRepresentation
            (fun x ↦ p * linearSubspaceIndicatorInt G x) := by
          by_cases hGle : Module.finrank FABL.𝔽₂ G ≤ n / 2
          · have hGgap : n / 2 - Module.finrank FABL.𝔽₂ G < k := by
              omega
            have hrec := ih (n / 2 - Module.finrank FABL.𝔽₂ G)
              hGgap G rfl hGle
            have hp : p = 2 * (2 : ℤ) ^
                (n / 2 - Module.finrank FABL.𝔽₂ G) := by
              have hexponent :
                  n / 2 - Module.finrank FABL.𝔽₂ F - 1 =
                    (n / 2 - Module.finrank FABL.𝔽₂ G) + 1 := by omega
              dsimp [p]
              rw [hexponent, pow_succ]
              ring
            simpa [hp, mul_assoc] using hrec.intMul 2
          · have hGhigh : n / 2 ≤ Module.finrank FABL.𝔽₂ G := by omega
            have hp : p = 1 := by
              have hexponent :
                  n / 2 - Module.finrank FABL.𝔽₂ F - 1 = 0 := by omega
              simp [p, hexponent]
            simpa [hp] using
              hasHalfSubspaceRepresentation_indicator_of_half_le_finrank G hGhigh
        have hright := hinterSum.add hGrepresentation.neg
        apply hasHalfSubspaceRepresentation_of_pointwise_modeq (h := fun x ↦
          (∑ ell ∈ nonzeroDualFinset (G ⧸ F.comap G.subtype),
            p * linearSubspaceIndicatorInt
              (rankTwoIntermediateSubspace F G ell) x) +
              -(p * linearSubspaceIndicatorInt G x))
        · intro x
          have hpower : (2 : ℤ) ^
              (n / 2 - Module.finrank FABL.𝔽₂ F) = 2 * p := by
            have hexponent : n / 2 - Module.finrank FABL.𝔽₂ F =
                (n / 2 - Module.finrank FABL.𝔽₂ F - 1) + 1 := by
              omega
            dsimp [p]
            conv_lhs => rw [hexponent]
            rw [pow_succ]
            ring
          rw [hpower, Int.modEq_iff_dvd]
          refine ⟨0, ?_⟩
          rw [← Finset.mul_sum, hdiamond.2 x]
          ring
        · exact hright

/-- The low-dimensional branch of Carlet Lemma 3, strengthened so that no
separate constant term is needed. -/
theorem hasHalfSubspaceRepresentation_scaledIndicator_of_finrank_le_half
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hn : Even n)
    (hF : Module.finrank FABL.𝔽₂ F ≤ n / 2) :
    HasHalfSubspaceRepresentation
      (fun x ↦ (2 : ℤ) ^
        (n / 2 - Module.finrank FABL.𝔽₂ F) *
          linearSubspaceIndicatorInt F x) :=
  hasHalfSubspaceRepresentation_scaledIndicator_aux hn
    (n / 2 - Module.finrank FABL.𝔽₂ F) F rfl hF

/-- Carlet Lemma 3 in its two source-facing branches. -/
theorem carletLemma3
    (F : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hn : Even n) :
    (Module.finrank FABL.𝔽₂ F < n / 2 →
      ∃ m : ℤ, ∃ c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ,
        ∀ x : FABL.F₂Cube n,
          Int.ModEq ((2 : ℤ) ^ (n / 2))
            ((2 : ℤ) ^ (n / 2 - Module.finrank FABL.𝔽₂ F) *
              linearSubspaceIndicatorInt F x)
            (m + halfSubspaceCombination c x)) ∧
    (n / 2 < Module.finrank FABL.𝔽₂ F →
      ∃ c : Submodule FABL.𝔽₂ (FABL.F₂Cube n) → ℤ,
        ∀ x : FABL.F₂Cube n,
          Int.ModEq ((2 : ℤ) ^ (n / 2))
            (linearSubspaceIndicatorInt F x)
            (halfSubspaceCombination c x)) := by
  constructor
  · intro hF
    obtain ⟨c, hc⟩ :=
      hasHalfSubspaceRepresentation_scaledIndicator_of_finrank_le_half F hn hF.le
    exact ⟨0, c, fun x ↦ by simpa using hc x⟩
  · intro hF
    exact hasHalfSubspaceRepresentation_indicator_of_half_le_finrank F hF.le

/-- The integer square-free numerical monomial indexed by a coordinate set. -/
def numericalMonomialInt
    (I : Finset (Fin n)) (x : FABL.F₂Cube n) : ℤ :=
  ∏ i ∈ I, bitValueInt (x i)

theorem numericalMonomialInt_cast
    (I : Finset (Fin n)) (x : FABL.F₂Cube n) :
    (numericalMonomialInt I x : ℝ) = FABL.numericalMonomial I x := by
  classical
  unfold numericalMonomialInt FABL.numericalMonomial
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hxi : x i = 1 <;> simp [bitValueInt, hxi]

private theorem coordinateZeroIndicatorInt_eq_prod
    (I : Finset (Fin n)) (x : FABL.F₂Cube n) :
    linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace I) x =
      ∏ i ∈ I, (1 - bitValueInt (x i)) := by
  classical
  by_cases hx : x ∈ FABL.F₂DecisionTree.coordinateZeroSubspace I
  · rw [linearSubspaceIndicatorInt, if_pos hx]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have hxi :=
      (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff I x).mp hx i hi
    simp [bitValueInt, hxi]
  · rw [linearSubspaceIndicatorInt, if_neg hx]
    have hnot := hx
    rw [FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff] at hnot
    push Not at hnot
    obtain ⟨i, hi, hxi⟩ := hnot
    have hxiOne : x i = 1 := Fin.eq_one_of_ne_zero _ hxi
    symm
    apply Finset.prod_eq_zero hi
    simp [bitValueInt, hxiOne]

/-- Inclusion-exclusion expresses a numerical monomial as an alternating sum
of indicators of coordinate zero subspaces. -/
theorem numericalMonomialInt_eq_sum_coordinateZeroIndicators
    (I : Finset (Fin n)) (x : FABL.F₂Cube n) :
    numericalMonomialInt I x =
      ∑ J ∈ I.powerset,
        (-1 : ℤ) ^ J.card *
          linearSubspaceIndicatorInt
            (FABL.F₂DecisionTree.coordinateZeroSubspace J) x := by
  classical
  have hexpand := Finset.prod_sub
    (fun _ : Fin n ↦ (1 : ℤ))
    (fun i ↦ 1 - bitValueInt (x i)) I
  simpa [numericalMonomialInt, coordinateZeroIndicatorInt_eq_prod] using hexpand

/-- The coordinate zero subspace indexed by `I` has dimension `n - |I|`. -/
theorem finrank_coordinateZeroSubspace
    (I : Finset (Fin n)) :
    Module.finrank FABL.𝔽₂
        (FABL.F₂DecisionTree.coordinateZeroSubspace I) = n - I.card := by
  have hcodimension :=
    FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace I
  rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace] at hcodimension
  have hfinrank : Module.finrank FABL.𝔽₂
      (FABL.F₂DecisionTree.coordinateZeroSubspace I) ≤ n := by
    simpa using
      (FABL.F₂DecisionTree.coordinateZeroSubspace I).finrank_le
  omega

@[simp] theorem linearSubspaceIndicatorInt_coordinateZeroSubspace_univ
    (x : FABL.F₂Cube n) :
    linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace Finset.univ) x =
      originIndicatorInt x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [linearSubspaceIndicatorInt, originIndicatorInt]
  · have hnot :
        x ∉ FABL.F₂DecisionTree.coordinateZeroSubspace
          (Finset.univ : Finset (Fin n)) := by
      intro hmem
      apply hx
      funext i
      exact (FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff _ x).mp
        hmem i (Finset.mem_univ i)
    simp [linearSubspaceIndicatorInt, originIndicatorInt, hx, hnot]

/-- The integral numerical normal form evaluates to the zero-one embedding of
a Boolean function. -/
theorem bitValueInt_eq_sum_booleanNumericalCoeffInt_mul_numericalMonomialInt
    (f : BooleanFunction n) (x : FABL.F₂Cube n) :
    bitValueInt (f x) =
      ∑ I : Finset (Fin n),
        FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x := by
  classical
  apply Int.cast_injective (α := ℝ)
  have hnormal := congrFun
    (FABL.numericalEval_numericalCoeff (FABL.booleanRealEmbedding f)) x
  rw [FABL.numericalEval] at hnormal
  calc
    (bitValueInt (f x) : ℝ) = FABL.booleanRealEmbedding f x := by
      by_cases hfx : f x = 1 <;> simp [bitValueInt, FABL.booleanRealEmbedding, hfx]
    _ = ∑ I : Finset (Fin n),
        FABL.numericalCoeff (FABL.booleanRealEmbedding f) I *
          FABL.numericalMonomial I x := hnormal.symm
    _ = (↑(∑ I : Finset (Fin n),
        FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro I _hI
      rw [FABL.numericalCoeff_booleanRealEmbedding_eq_intCast,
        numericalMonomialInt_cast]

private theorem hasHalfSubspaceRepresentation_intMul_coordinateZeroIndicator
    (I : Finset (Fin n)) (a : ℤ) (hn : Even n)
    (hdiv : Module.finrank FABL.𝔽₂
        (FABL.F₂DecisionTree.coordinateZeroSubspace I) < n / 2 →
      (2 : ℤ) ^ (n / 2 - Module.finrank FABL.𝔽₂
        (FABL.F₂DecisionTree.coordinateZeroSubspace I)) ∣ a) :
    HasHalfSubspaceRepresentation
      (fun x ↦ a * linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace I) x) := by
  let Z := FABL.F₂DecisionTree.coordinateZeroSubspace I
  by_cases hZ : Module.finrank FABL.𝔽₂ Z < n / 2
  · obtain ⟨q, hq⟩ := hdiv hZ
    have hscaled :=
      hasHalfSubspaceRepresentation_scaledIndicator_of_finrank_le_half Z hn hZ.le
    have hmultiple := hscaled.intMul q
    simpa [Z, hq, mul_assoc, mul_comm, mul_left_comm] using hmultiple
  · have hZhalf : n / 2 ≤ Module.finrank FABL.𝔽₂ Z := by omega
    exact (hasHalfSubspaceRepresentation_indicator_of_half_le_finrank Z hZhalf).intMul a

private theorem hasHalfSubspaceRepresentation_intMul_numericalMonomialInt
    (I : Finset (Fin n)) (a : ℤ) (hn : Even n)
    (hdiv : n / 2 < I.card →
      (2 : ℤ) ^ (I.card - n / 2) ∣ a) :
    HasHalfSubspaceRepresentation
      (fun x ↦ a * numericalMonomialInt I x) := by
  classical
  have hterms : ∀ J ∈ I.powerset,
      HasHalfSubspaceRepresentation (fun x ↦
        a * ((-1 : ℤ) ^ J.card * linearSubspaceIndicatorInt
          (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) := by
    intro J hJ
    have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
    have hbase := hasHalfSubspaceRepresentation_intMul_coordinateZeroIndicator
      J (a * (-1 : ℤ) ^ J.card) hn (by
        intro hZ
        have hJhalf : n / 2 < J.card := by
          rw [finrank_coordinateZeroSubspace] at hZ
          rcases hn with ⟨r, hr⟩
          have hhalf : n / 2 = r := by omega
          omega
        have hIhalf : n / 2 < I.card :=
          lt_of_lt_of_le hJhalf (Finset.card_le_card hJI)
        have hpowers : (2 : ℤ) ^ (J.card - n / 2) ∣
            (2 : ℤ) ^ (I.card - n / 2) :=
          pow_dvd_pow (2 : ℤ)
            (Nat.sub_le_sub_right (Finset.card_le_card hJI) (n / 2))
        have hcoefficient := (hpowers.trans (hdiv hIhalf)).mul_right
          ((-1 : ℤ) ^ J.card)
        rw [finrank_coordinateZeroSubspace]
        rcases hn with ⟨r, hr⟩
        have hhalf : n / 2 = r := by omega
        have hJle : J.card ≤ n := by simpa using Finset.card_le_univ J
        have hexponent : n / 2 - (n - J.card) = J.card - n / 2 := by omega
        rw [hexponent]
        exact hcoefficient)
    simpa [mul_assoc] using hbase
  have hsum := HasHalfSubspaceRepresentation.sum I.powerset
    (fun J x ↦ a * ((-1 : ℤ) ^ J.card *
      linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) hterms
  apply hasHalfSubspaceRepresentation_of_pointwise_modeq
    (h := fun x ↦ ∑ J ∈ I.powerset,
      a * ((-1 : ℤ) ^ J.card * linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace J) x))
  · intro x
    rw [numericalMonomialInt_eq_sum_coordinateZeroIndicators,
      Finset.mul_sum]
  · exact hsum

private theorem hasHalfSubspaceRepresentation_topMonomial_add_origin
    (hn : Even n) (hnTwo : 2 ≤ n) :
    HasHalfSubspaceRepresentation (fun x ↦
      (2 : ℤ) ^ (n / 2 - 1) *
          numericalMonomialInt (Finset.univ : Finset (Fin n)) x +
        (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) := by
  classical
  let t : ℤ := (2 : ℤ) ^ (n / 2 - 1)
  let N : Finset (Fin n) := Finset.univ
  let s : Finset (Finset (Fin n)) := N.powerset.erase N
  have hterms : ∀ J ∈ s,
      HasHalfSubspaceRepresentation (fun x ↦
        t * ((-1 : ℤ) ^ J.card * linearSubspaceIndicatorInt
          (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) := by
    intro J hJ
    have hJne : J ≠ N := Finset.ne_of_mem_erase hJ
    have hJsubset : J ⊆ N :=
      Finset.mem_powerset.mp (Finset.mem_of_mem_erase hJ)
    have hJcardLt : J.card < n := by
      have hcardLe : J.card ≤ n := by simpa [N] using Finset.card_le_univ J
      apply lt_of_le_of_ne hcardLe
      intro hcard
      apply hJne
      apply Finset.eq_univ_of_card
      simpa [N] using hcard
    have hbase := hasHalfSubspaceRepresentation_intMul_coordinateZeroIndicator
      J (t * (-1 : ℤ) ^ J.card) hn (by
        intro hZ
        have hexponent :
            n / 2 - Module.finrank FABL.𝔽₂
                (FABL.F₂DecisionTree.coordinateZeroSubspace J) =
              J.card - n / 2 := by
          rw [finrank_coordinateZeroSubspace]
          rcases hn with ⟨r, hr⟩
          have hhalf : n / 2 = r := by omega
          omega
        have hle : J.card - n / 2 ≤ n / 2 - 1 := by
          rcases hn with ⟨r, hr⟩
          have hhalf : n / 2 = r := by omega
          omega
        rw [hexponent]
        exact (pow_dvd_pow (2 : ℤ) hle).mul_right ((-1 : ℤ) ^ J.card))
    simpa [mul_assoc] using hbase
  have hsum := HasHalfSubspaceRepresentation.sum s
    (fun J x ↦ t * ((-1 : ℤ) ^ J.card *
      linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) hterms
  apply hasHalfSubspaceRepresentation_of_pointwise_modeq
    (h := fun x ↦ ∑ J ∈ s,
      t * ((-1 : ℤ) ^ J.card * linearSubspaceIndicatorInt
        (FABL.F₂DecisionTree.coordinateZeroSubspace J) x))
  · intro x
    have hNmem : N ∈ N.powerset := Finset.mem_powerset.mpr (Subset.rfl)
    have hdecomp := Finset.sum_erase_add N.powerset
      (fun J ↦ t * ((-1 : ℤ) ^ J.card *
        linearSubspaceIndicatorInt
          (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) hNmem
    have hNcard : N.card = n := by simp [N]
    have hsign : (-1 : ℤ) ^ N.card = 1 := by
      rw [hNcard, hn.neg_one_pow]
    have htopTerm :
        t * ((-1 : ℤ) ^ N.card *
          linearSubspaceIndicatorInt
            (FABL.F₂DecisionTree.coordinateZeroSubspace N) x) =
          t * originIndicatorInt x := by
      rw [hsign, one_mul]
      congr 1
      exact linearSubspaceIndicatorInt_coordinateZeroSubspace_univ x
    have hfull : t * numericalMonomialInt N x =
        (∑ J ∈ s, t * ((-1 : ℤ) ^ J.card *
          linearSubspaceIndicatorInt
            (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) +
          t * originIndicatorInt x := by
      rw [numericalMonomialInt_eq_sum_coordinateZeroIndicators,
        Finset.mul_sum]
      change (∑ J ∈ N.powerset, t * ((-1 : ℤ) ^ J.card *
          linearSubspaceIndicatorInt
            (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) = _
      calc
        _ = (∑ J ∈ N.powerset.erase N,
              t * ((-1 : ℤ) ^ J.card * linearSubspaceIndicatorInt
                (FABL.F₂DecisionTree.coordinateZeroSubspace J) x)) +
              t * ((-1 : ℤ) ^ N.card * linearSubspaceIndicatorInt
                (FABL.F₂DecisionTree.coordinateZeroSubspace N) x) :=
            hdecomp.symm
        _ = _ := by rw [htopTerm]
    have hdouble : (2 : ℤ) ^ (n / 2) = 2 * t := by
      dsimp [t]
      conv_lhs => rw [show n / 2 = (n / 2 - 1) + 1 by omega]
      rw [pow_succ]
      ring
    dsimp [t, N] at hfull ⊢
    rw [Int.modEq_iff_dvd]
    refine ⟨-originIndicatorInt x, ?_⟩
    rw [hfull, hdouble]
    ring
  · exact hsum

private theorem hasHalfSubspaceRepresentation_bitValueInt_add_origin_of_conditions
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : SatisfiesBentNNFCoefficientConditions f) :
    HasHalfSubspaceRepresentation (fun x ↦
      bitValueInt (f x) +
        (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) := by
  classical
  let N : Finset (Fin n) := Finset.univ
  let s : Finset (Finset (Fin n)) := Finset.univ.erase N
  have hterms : ∀ I ∈ s,
      HasHalfSubspaceRepresentation (fun x ↦
        FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) := by
    intro I hI
    have hIne : I ≠ N := Finset.ne_of_mem_erase hI
    have hIcardLt : I.card < n := by
      have hcardLe : I.card ≤ n := by simpa using Finset.card_le_univ I
      apply lt_of_le_of_ne hcardLe
      intro hcard
      apply hIne
      apply Finset.eq_univ_of_card
      simpa [N] using hcard
    apply hasHalfSubspaceRepresentation_intMul_numericalMonomialInt I
      (FABL.booleanNumericalCoeffInt f I) hn
    intro hIhalf
    exact hf.1 I hIhalf hIcardLt
  have hrest := HasHalfSubspaceRepresentation.sum s
    (fun I x ↦ FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x)
    hterms
  have htop := hasHalfSubspaceRepresentation_topMonomial_add_origin hn hnTwo
  have hright := hrest.add htop
  apply hasHalfSubspaceRepresentation_of_pointwise_modeq (h := fun x ↦
    (∑ I ∈ s,
      FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) +
      ((2 : ℤ) ^ (n / 2 - 1) * numericalMonomialInt N x +
        (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x))
  · intro x
    have hNmem : N ∈ (Finset.univ : Finset (Finset (Fin n))) :=
      Finset.mem_univ N
    have hdecomp := Finset.sum_erase_add
      (Finset.univ : Finset (Finset (Fin n)))
      (fun I ↦ FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x)
      hNmem
    have htopDvd := hf.2.dvd.mul_right (numericalMonomialInt N x)
    rw [Int.modEq_iff_dvd]
    have heq :
        (∑ I ∈ s,
            FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) +
              ((2 : ℤ) ^ (n / 2 - 1) * numericalMonomialInt N x +
                (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) -
            (bitValueInt (f x) +
              (2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x) =
          ((2 : ℤ) ^ (n / 2 - 1) -
            FABL.booleanNumericalCoeffInt f N) * numericalMonomialInt N x := by
      rw [bitValueInt_eq_sum_booleanNumericalCoeffInt_mul_numericalMonomialInt]
      change (∑ I ∈ Finset.univ.erase N,
          FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) + _ -
        ((∑ I : Finset (Fin n),
          FABL.booleanNumericalCoeffInt f I * numericalMonomialInt I x) + _) = _
      rw [← hdecomp]
      ring
    rw [heq]
    exact htopDvd
  · simpa [N] using hright

/-- The necessary direction of Carlet Theorem 12. -/
theorem hasGeometricBentCongruence_of_isBent
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n)
    (hf : IsBent f) :
    HasGeometricBentCongruence f := by
  have hconditions := (isBent_iff_nnfCoefficientConditions f hn hnTwo).mp hf
  obtain ⟨c, hc⟩ :=
    hasHalfSubspaceRepresentation_bitValueInt_add_origin_of_conditions
      f hn hnTwo hconditions
  refine ⟨c, fun x ↦ ?_⟩
  have hsub := (hc x).sub
    (Int.ModEq.refl ((2 : ℤ) ^ (n / 2 - 1) * originIndicatorInt x))
  simpa [geometricBentExpression] using hsub

/-- Carlet Theorem 12: in positive even dimension, bentness is equivalent to
the geometric congruence by half-dimensional subspace indicators. -/
theorem isBent_iff_hasGeometricBentCongruence
    (f : BooleanFunction n) (hn : Even n) (hnTwo : 2 ≤ n) :
    IsBent f ↔ HasGeometricBentCongruence f :=
  ⟨hasGeometricBentCongruence_of_isBent f hn hnTwo,
    isBent_of_hasGeometricBentCongruence f hn hnTwo⟩

end CryptBoolean
