/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightAffineSpan
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Rank-deficient seven-variable affine-map data

The rank-seven reduction for weight-sixteen words leaves affine maps from a
fixed seven-variable support pattern into the ambient Boolean cube.  This file
gives a dimension-free encoding of the rank-deficient maps.  A dependent
seven-tuple has a nonzero binary relation; choosing one nonzero coefficient
allows the corresponding direction to be recovered from the other six.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A nonzero binary relation among seven directions. -/
abbrev NonzeroSevenCoefficient :=
  {g : Fin 7 → FABL.𝔽₂ // g ≠ 0}

/-- A nonzero relation has a coordinate with nonzero coefficient. -/
theorem exists_nonzeroSevenCoefficient
    (g : NonzeroSevenCoefficient) : ∃ i, g.1 i ≠ 0 := by
  by_contra h
  push Not at h
  apply g.2
  funext i
  exact h i

/-- A canonical coordinate with nonzero coefficient in a nonzero relation. -/
noncomputable def nonzeroSevenCoefficientPivot
    (g : NonzeroSevenCoefficient) : Fin 7 :=
  Classical.choose (exists_nonzeroSevenCoefficient g)

theorem nonzeroSevenCoefficientPivot_ne_zero
    (g : NonzeroSevenCoefficient) :
    g.1 (nonzeroSevenCoefficientPivot g) ≠ 0 := by
  classical
  unfold nonzeroSevenCoefficientPivot
  exact Classical.choose_spec (exists_nonzeroSevenCoefficient g)

theorem nonzeroSevenCoefficientPivot_eq_one
    (g : NonzeroSevenCoefficient) :
    g.1 (nonzeroSevenCoefficientPivot g) = 1 :=
  Fin.eq_one_of_ne_zero _ (nonzeroSevenCoefficientPivot_ne_zero g)

/-- Data that reconstructs a dependent seven-tuple: a nonzero relation and
the six directions away from its canonical pivot. -/
abbrev SevenDirectionDependenceData (n : ℕ) :=
  NonzeroSevenCoefficient × (Fin 6 → FABL.F₂Cube n)

/-- Reconstruct the omitted direction as the binary linear combination of
the other six directions. -/
noncomputable def dependentSevenDirectionTupleOfData
    (d : SevenDirectionDependenceData n) :
    Fin 7 → FABL.F₂Cube n :=
  let i := nonzeroSevenCoefficientPivot d.1
  Fin.insertNth i
    (∑ k : Fin 6, d.1.1 (i.succAbove k) • d.2 k)
    d.2

theorem not_linearIndependent_dependentSevenDirectionTupleOfData
    (d : SevenDirectionDependenceData n) :
    ¬LinearIndependent FABL.𝔽₂
      (dependentSevenDirectionTupleOfData d) := by
  rw [Fintype.not_linearIndependent_iff]
  let i := nonzeroSevenCoefficientPivot d.1
  refine ⟨d.1.1, ?_, i, nonzeroSevenCoefficientPivot_ne_zero d.1⟩
  · rw [Fin.sum_univ_succAbove _ i,
      nonzeroSevenCoefficientPivot_eq_one d.1]
    simp only [i, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove,
      dependentSevenDirectionTupleOfData, one_smul]
    exact ZModModule.add_self _

/-- Every dependent seven-tuple is reconstructed by some dependence data. -/
theorem dependentSevenDirectionTupleOfData_surjective :
    Function.Surjective
      (fun d : SevenDirectionDependenceData n ↦
        (⟨dependentSevenDirectionTupleOfData d,
          not_linearIndependent_dependentSevenDirectionTupleOfData d⟩ :
          {v : Fin 7 → FABL.F₂Cube n //
            ¬LinearIndependent FABL.𝔽₂ v})) := by
  rintro ⟨v, hv⟩
  rw [Fintype.not_linearIndependent_iff] at hv
  obtain ⟨g, hg, j, hj⟩ := hv
  have hgNe : g ≠ 0 := by
    intro hzero
    rw [hzero, Pi.zero_apply] at hj
    exact hj rfl
  let c : NonzeroSevenCoefficient := ⟨g, hgNe⟩
  let i := nonzeroSevenCoefficientPivot c
  have hiOne : g i = 1 := by
    change c.1 i = 1
    exact nonzeroSevenCoefficientPivot_eq_one c
  rw [Fin.sum_univ_succAbove _ i, hiOne, one_smul] at hg
  have hpivot :
      (∑ k : Fin 6, g (i.succAbove k) • v (i.succAbove k)) = v i := by
    have hvi : v i =
        -(∑ k : Fin 6, g (i.succAbove k) • v (i.succAbove k)) :=
      add_eq_zero_iff_eq_neg.mp hg
    simpa only [ZModModule.neg_eq_self] using hvi.symm
  let d : SevenDirectionDependenceData n :=
    ⟨c, fun k ↦ v (i.succAbove k)⟩
  refine ⟨d, Subtype.ext ?_⟩
  funext j
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simpa only [d, i, c, dependentSevenDirectionTupleOfData,
      Fin.insertNth_apply_same] using hpivot
  · simp [d, i, dependentSevenDirectionTupleOfData]

/-- The finite family of dependent seven-tuples of ambient directions. -/
noncomputable def dependentSevenDirectionTuples (n : ℕ) :
    Finset (Fin 7 → FABL.F₂Cube n) := by
  classical
  exact Finset.univ.image dependentSevenDirectionTupleOfData

theorem mem_dependentSevenDirectionTuples_iff
    (v : Fin 7 → FABL.F₂Cube n) :
    v ∈ dependentSevenDirectionTuples n ↔
      ¬LinearIndependent FABL.𝔽₂ v := by
  classical
  constructor
  · rw [dependentSevenDirectionTuples, Finset.mem_image]
    rintro ⟨d, _hd, rfl⟩
    exact not_linearIndependent_dependentSevenDirectionTupleOfData d
  · intro hv
    obtain ⟨d, hd⟩ :=
      dependentSevenDirectionTupleOfData_surjective
        (n := n) ⟨v, hv⟩
    rw [dependentSevenDirectionTuples, Finset.mem_image]
    refine ⟨d, Finset.mem_univ d, ?_⟩
    exact congrArg Subtype.val hd

/-- There are at most `127 q^6` dependent seven-tuples in an ambient binary
space of cardinality `q`. -/
theorem card_dependentSevenDirectionTuples_le (n : ℕ) :
    (dependentSevenDirectionTuples n).card ≤
      127 * (2 ^ n) ^ 6 := by
  classical
  calc
    (dependentSevenDirectionTuples n).card ≤
        (Finset.univ : Finset (SevenDirectionDependenceData n)).card := by
      rw [dependentSevenDirectionTuples]
      exact Finset.card_image_le
    _ = Fintype.card (SevenDirectionDependenceData n) :=
      Finset.card_univ
    _ = 127 * (2 ^ n) ^ 6 := by
      simp [SevenDirectionDependenceData, NonzeroSevenCoefficient,
        Fintype.card_prod, ZMod.card]

/-- Translation together with seven direction vectors parameterizes an
affine map out of the seven-variable Boolean cube. -/
abbrev SevenVariableAffineMapData (n : ℕ) :=
  FABL.F₂Cube n × (Fin 7 → FABL.F₂Cube n)

/-- The affine point map encoded by a translation and seven directions. -/
def sevenVariableAffinePoint
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 7) :
    FABL.F₂Cube n :=
  d.1 + ∑ i : Fin 7, x i • d.2 i

/-- Seven-variable affine-map data are injective exactly when their seven
directions are linearly independent. -/
theorem sevenVariableAffinePoint_injective_iff
    (d : SevenVariableAffineMapData n) :
    Function.Injective (sevenVariableAffinePoint d) ↔
      LinearIndependent FABL.𝔽₂ d.2 := by
  constructor
  · intro hinjective
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hpoint : sevenVariableAffinePoint d g =
        sevenVariableAffinePoint d 0 := by
      simp only [sevenVariableAffinePoint, hg, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero]
    exact congrFun (hinjective hpoint) i
  · intro hindependent x y hxy
    have hsum : (∑ i : Fin 7, x i • d.2 i) =
        ∑ i : Fin 7, y i • d.2 i := by
      exact add_left_cancel hxy
    have hzero : ∑ i : Fin 7, (x i + y i) • d.2 i = 0 := by
      calc
        (∑ i : Fin 7, (x i + y i) • d.2 i) =
            (∑ i : Fin 7, x i • d.2 i) +
              ∑ i : Fin 7, y i • d.2 i := by
          simp only [add_smul, Finset.sum_add_distrib]
        _ = 0 := by rw [hsum, ZModModule.add_self]
    have hcoeff :=
      Fintype.linearIndependent_iff.mp hindependent
        (fun i ↦ x i + y i) hzero
    funext i
    have hi := hcoeff i
    exact (add_eq_zero_iff_eq_neg.mp hi).trans
      (ZMod.neg_eq_self_mod_two (y i))

/-- The affine-map data whose seven direction vectors are dependent. -/
noncomputable def rankDeficientSevenVariableAffineMapData (n : ℕ) :
    Finset (SevenVariableAffineMapData n) :=
  Finset.univ.product (dependentSevenDirectionTuples n)

theorem mem_rankDeficientSevenVariableAffineMapData_iff
    (d : SevenVariableAffineMapData n) :
    d ∈ rankDeficientSevenVariableAffineMapData n ↔
      ¬Function.Injective (sevenVariableAffinePoint d) := by
  simp [rankDeficientSevenVariableAffineMapData,
    mem_dependentSevenDirectionTuples_iff,
    sevenVariableAffinePoint_injective_iff]

/-- Rank-deficient seven-variable affine-map data have cardinality at most
`127 q^7` in an ambient binary space of cardinality `q`. -/
theorem card_rankDeficientSevenVariableAffineMapData_le (n : ℕ) :
    (rankDeficientSevenVariableAffineMapData n).card ≤
      127 * (2 ^ n) ^ 7 := by
  change
    ((Finset.univ : Finset (FABL.F₂Cube n)) ×ˢ
      dependentSevenDirectionTuples n).card ≤
        127 * (2 ^ n) ^ 7
  rw [Finset.card_product, Finset.card_univ, FABL.card_f₂Cube]
  have hbound := card_dependentSevenDirectionTuples_le n
  calc
    2 ^ n * (dependentSevenDirectionTuples n).card ≤
        2 ^ n * (127 * (2 ^ n) ^ 6) :=
      Nat.mul_le_mul_left _ hbound
    _ = 127 * (2 ^ n) ^ 7 := by ring

end CryptBoolean
