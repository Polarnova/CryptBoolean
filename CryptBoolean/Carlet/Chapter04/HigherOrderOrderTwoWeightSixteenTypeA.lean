/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen

/-!
# Type-a weight-sixteen words

The thirty ordered affine-hyperplane decompositions of an affine four-flat.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightSixteenTypeAFintypeDual
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fintype (Module.Dual FABL.𝔽₂ C.direction) :=
  Module.fintypeOfFintype
    (Module.finBasis FABL.𝔽₂ C.direction).dualBasis

noncomputable local instance weightSixteenTypeAFintypeNonzeroDual
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Fintype { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 } :=
  Fintype.ofFinite _

/-- A nonzero linear functional on the direction of an affine four-flat,
together with the value selecting its first affine hyperplane. -/
abbrev WeightSixteenTypeAParameter
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 } × FABL.𝔽₂

/-- The canonical finite parameter space for the ordered hyperplane
decompositions of an affine four-flat. -/
noncomputable def weightSixteenTypeAParameters
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (WeightSixteenTypeAParameter C) := by
  classical
  exact Finset.univ

private theorem card_nonzero_dual_of_finrank_four
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : Module.finrank FABL.𝔽₂ C.direction = 4) :
    Fintype.card
      { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 } = 15 := by
  classical
  let B : Module.Basis
      (Fin (Module.finrank FABL.𝔽₂ C.direction)) FABL.𝔽₂ C.direction :=
    Module.finBasis FABL.𝔽₂ C.direction
  have hcardDual :
      Fintype.card (Module.Dual FABL.𝔽₂ C.direction) = 16 := by
    calc
      Fintype.card (Module.Dual FABL.𝔽₂ C.direction) =
          Fintype.card
            (Fin (Module.finrank FABL.𝔽₂ C.direction) → FABL.𝔽₂) :=
        Fintype.card_congr B.dualBasis.equivFun.toEquiv
      _ = 16 := by
        rw [Fintype.card_fun, Fintype.card_fin, hC]
        norm_num
  rw [Fintype.card_subtype_compl (fun ℓ :
      Module.Dual FABL.𝔽₂ C.direction ↦ ℓ = 0),
    Fintype.card_subtype_eq, hcardDual]

/-- A four-flat has thirty functional/value parameters. -/
theorem card_weightSixteenTypeAParameters
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) :
    (weightSixteenTypeAParameters C).card = 30 := by
  classical
  have hCrank : Module.finrank FABL.𝔽₂ C.direction = 4 := by
    exact (by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hC :
          C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4).2
  rw [weightSixteenTypeAParameters, Finset.card_univ,
    Fintype.card_prod, card_nonzero_dual_of_finrank_four C hCrank]
  norm_num

/-- A chosen basepoint of an affine four-flat. -/
noncomputable def weightSixteenTypeABasepoint
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) : FABL.F₂Cube n := by
  have hCne : C ≠ ⊥ := by
    exact (by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hC :
          C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4).1
  exact Classical.choose ((AffineSubspace.nonempty_iff_ne_bot C).2 hCne)

private theorem weightSixteenTypeABasepoint_mem
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) :
    weightSixteenTypeABasepoint C hC ∈ C := by
  unfold weightSixteenTypeABasepoint
  exact Classical.choose_spec
    ((AffineSubspace.nonempty_iff_ne_bot C).2 (by
      exact (by
        simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
          true_and] using hC :
            C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4).1))

/-- A chosen direction vector on which a nonzero binary functional is one. -/
noncomputable def weightSixteenTypeANormal
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    C.direction :=
  Classical.choose ((LinearMap.surjective ℓ.property) (1 : FABL.𝔽₂))

@[simp] private theorem weightSixteenTypeANormal_apply
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    ℓ.1 (weightSixteenTypeANormal C ℓ) = 1 :=
  Classical.choose_spec
    ((LinearMap.surjective ℓ.property) (1 : FABL.𝔽₂))

/-- The ambient hyperplane direction given by the kernel of a functional on
the four-flat direction. -/
noncomputable def weightSixteenTypeADirection
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  (LinearMap.ker ℓ.1).map C.direction.subtype

/-- The affine hyperplane selected by a functional/value parameter. -/
noncomputable def weightSixteenTypeAHyperplane
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.binaryAffineSubspace (weightSixteenTypeADirection C p.1)
    (p.2 • (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
      weightSixteenTypeABasepoint C hC)

private theorem weightSixteenTypeADirection_le
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    weightSixteenTypeADirection C ℓ ≤ C.direction := by
  rintro x ⟨y, _hy, rfl⟩
  exact y.property

private theorem finrank_weightSixteenTypeADirection
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    Module.finrank FABL.𝔽₂ (weightSixteenTypeADirection C ℓ) = 3 := by
  have hCrank : Module.finrank FABL.𝔽₂ C.direction = 4 := by
    exact (by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using hC :
          C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4).2
  have hker := ℓ.1.finrank_ker_add_one_of_ne_zero ℓ.property
  rw [hCrank] at hker
  have hkerRank : Module.finrank FABL.𝔽₂ (LinearMap.ker ℓ.1) = 3 := by
    omega
  rw [weightSixteenTypeADirection, Submodule.finrank_map_subtype_eq]
  exact hkerRank

private theorem weightSixteenTypeAHyperplane_basepoint_mem
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    p.2 • (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC ∈ C := by
  have hdirection : p.2 •
      (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) ∈ C.direction :=
    C.direction.smul_mem p.2 (weightSixteenTypeANormal C p.1).property
  simpa only [vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction
    hdirection (weightSixteenTypeABasepoint_mem C hC)

private theorem weightSixteenTypeAHyperplane_le
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenTypeAHyperplane C hC p ≤ C := by
  intro x hx
  let a := p.2 •
      (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC
  have haC : a ∈ C := weightSixteenTypeAHyperplane_basepoint_mem C hC p
  have hxa : x -ᵥ a ∈ (weightSixteenTypeAHyperplane C hC p).direction :=
    AffineSubspace.vsub_mem_direction hx
      (AffineSubspace.self_mem_mk' _ _)
  have hxa' : x -ᵥ a ∈ C.direction := by
    rw [weightSixteenTypeAHyperplane,
      FABL.binaryAffineSubspace_direction] at hxa
    exact weightSixteenTypeADirection_le C p.1 hxa
  simpa only [vsub_vadd] using
    (AffineSubspace.vadd_mem_of_mem_direction hxa' haC)

private theorem weightSixteenTypeAHyperplane_mem_flats
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenTypeAHyperplane C hC p ∈ binaryAffineFlats 3 n := by
  apply binaryAffineSubspace_mem_binaryAffineFlats
  rw [mem_binaryLinearSubspaces]
  exact finrank_weightSixteenTypeADirection C hC p.1

/-- Exchanging zero and one selects the complementary hyperplane. -/
def weightSixteenTypeAComplementParameter
    {C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (p : WeightSixteenTypeAParameter C) :
    WeightSixteenTypeAParameter C :=
  (p.1, 1 + p.2)

/-- The ordered pair of complementary affine hyperplanes selected by a
type-`a` parameter. -/
noncomputable def weightSixteenTypeARepresentationPair
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  (weightSixteenTypeAHyperplane C hC p,
    weightSixteenTypeAHyperplane C hC
      (weightSixteenTypeAComplementParameter p))

@[simp] private theorem direction_weightSixteenTypeAHyperplane
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    (weightSixteenTypeAHyperplane C hC p).direction =
      weightSixteenTypeADirection C p.1 := by
  rw [weightSixteenTypeAHyperplane,
    FABL.binaryAffineSubspace_direction]

private theorem weightSixteenTypeAComplement_basepoint_add_basepoint
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    ((weightSixteenTypeAComplementParameter p).2 •
        (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC) +
      (p.2 • (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC) =
      (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) := by
  let v := (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n)
  let u := weightSixteenTypeABasepoint C hC
  have hcoefficient : (1 + p.2) + p.2 = 1 := by
    calc
      (1 + p.2) + p.2 = 1 + (p.2 + p.2) := by abel
      _ = 1 := by rw [ZModModule.add_self, add_zero]
  change ((1 + p.2) • v + u) + (p.2 • v + u) = v
  calc
    ((1 + p.2) • v + u) + (p.2 • v + u) =
        ((1 + p.2) • v + p.2 • v) + (u + u) := by abel
    _ = ((1 + p.2) + p.2) • v + (u + u) := by
      rw [← add_smul]
    _ = v := by rw [hcoefficient, one_smul, ZModModule.add_self, add_zero]

private theorem weightSixteenTypeANormal_not_mem_direction
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (ℓ : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 }) :
    (weightSixteenTypeANormal C ℓ : FABL.F₂Cube n) ∉
      weightSixteenTypeADirection C ℓ := by
  intro hnormal
  obtain ⟨y, hy, hyval⟩ := hnormal
  have hyEq : y = weightSixteenTypeANormal C ℓ := by
    apply Subtype.ext
    exact hyval
  have hyZero : ℓ.1 y = 0 := by
    change ℓ.1 y = 0 at hy
    exact hy
  rw [hyEq, weightSixteenTypeANormal_apply] at hyZero
  exact one_ne_zero hyZero

private theorem weightSixteenTypeAHyperplanes_ne
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenTypeAHyperplane C hC p ≠
      weightSixteenTypeAHyperplane C hC
        (weightSixteenTypeAComplementParameter p) := by
  intro heq
  let a := p.2 •
      (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC
  let b := (weightSixteenTypeAComplementParameter p).2 •
      (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) +
        weightSixteenTypeABasepoint C hC
  have ha : a ∈ weightSixteenTypeAHyperplane C hC p :=
    AffineSubspace.self_mem_mk' _ _
  have hbComplement : b ∈ weightSixteenTypeAHyperplane C hC
      (weightSixteenTypeAComplementParameter p) :=
    AffineSubspace.self_mem_mk' _ _
  have hb : b ∈ weightSixteenTypeAHyperplane C hC p := by
    rw [heq]
    exact hbComplement
  have hdiff := AffineSubspace.vsub_mem_direction hb ha
  have hdiff' : (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) ∈
      weightSixteenTypeADirection C p.1 := by
    rw [direction_weightSixteenTypeAHyperplane] at hdiff
    have hba : b -ᵥ a =
        (weightSixteenTypeANormal C p.1 : FABL.F₂Cube n) := by
      change b - a = _
      have hnega : -a = a := by
        funext i
        exact ZMod.neg_eq_self_mod_two (a i)
      rw [sub_eq_add_neg, hnega]
      exact weightSixteenTypeAComplement_basepoint_add_basepoint C hC p
    rwa [hba] at hdiff
  exact weightSixteenTypeANormal_not_mem_direction C p.1 hdiff'

private theorem weightSixteenTypeAHyperplanes_inf_eq_bot
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenTypeAHyperplane C hC p ⊓
        weightSixteenTypeAHyperplane C hC
          (weightSixteenTypeAComplementParameter p) = ⊥ := by
  by_contra hmeet
  obtain ⟨x, hx⟩ := (AffineSubspace.nonempty_iff_ne_bot _).2 hmeet
  have hxFirst : x ∈ weightSixteenTypeAHyperplane C hC p := hx.1
  have hxSecond : x ∈ weightSixteenTypeAHyperplane C hC
      (weightSixteenTypeAComplementParameter p) := hx.2
  apply weightSixteenTypeAHyperplanes_ne C hC p
  apply (AffineSubspace.eq_iff_direction_eq_of_mem hxFirst hxSecond).2
  simp only [direction_weightSixteenTypeAHyperplane,
    weightSixteenTypeAComplementParameter]

/-- Every type-`a` parameter gives an ordered disjoint pair of affine
three-flats. -/
theorem weightSixteenTypeARepresentationPair_mem
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenTypeARepresentationPair C hC p ∈
      disjointBinaryAffineThreeFlatPairs n := by
  have hproduct : weightSixteenTypeARepresentationPair C hC p ∈
      binaryAffineThreeFlatPairs n := by
    change weightSixteenTypeARepresentationPair C hC p ∈
      (binaryAffineFlats 3 n).product (binaryAffineFlats 3 n)
    apply Finset.mem_product.mpr
    exact ⟨weightSixteenTypeAHyperplane_mem_flats C hC p,
      weightSixteenTypeAHyperplane_mem_flats C hC
        (weightSixteenTypeAComplementParameter p)⟩
  simp only [disjointBinaryAffineThreeFlatPairs, Finset.mem_filter]
  exact ⟨hproduct, weightSixteenTypeAHyperplanes_inf_eq_bot C hC p⟩

private theorem weightSixteenTypeAHyperplanePoints_disjoint
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    Disjoint
      (binaryAffineFlatPoints (weightSixteenTypeAHyperplane C hC p))
      (binaryAffineFlatPoints (weightSixteenTypeAHyperplane C hC
        (weightSixteenTypeAComplementParameter p))) := by
  rw [Finset.disjoint_left]
  intro x hxFirst hxSecond
  have hxMeet : x ∈
      weightSixteenTypeAHyperplane C hC p ⊓
        weightSixteenTypeAHyperplane C hC
          (weightSixteenTypeAComplementParameter p) :=
    ⟨(mem_binaryAffineFlatPoints _ _).mp hxFirst,
      (mem_binaryAffineFlatPoints _ _).mp hxSecond⟩
  rw [weightSixteenTypeAHyperplanes_inf_eq_bot C hC p] at hxMeet
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hxMeet
  exact hxMeet

private theorem weightSixteenTypeAHyperplanePoints_union
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    binaryAffineFlatPoints C =
      binaryAffineFlatPoints (weightSixteenTypeAHyperplane C hC p) ∪
        binaryAffineFlatPoints (weightSixteenTypeAHyperplane C hC
          (weightSixteenTypeAComplementParameter p)) := by
  have hCdata : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  have hfirstFlat := weightSixteenTypeAHyperplane_mem_flats C hC p
  have hsecondFlat := weightSixteenTypeAHyperplane_mem_flats C hC
    (weightSixteenTypeAComplementParameter p)
  have hfirstData : weightSixteenTypeAHyperplane C hC p ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂
        (weightSixteenTypeAHyperplane C hC p).direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hfirstFlat
  have hsecondData : weightSixteenTypeAHyperplane C hC
        (weightSixteenTypeAComplementParameter p) ≠ ⊥ ∧
      Module.finrank FABL.𝔽₂
        (weightSixteenTypeAHyperplane C hC
          (weightSixteenTypeAComplementParameter p)).direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hsecondFlat
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_union.mp hx with hxFirst | hxSecond
    · exact (mem_binaryAffineFlatPoints C x).mpr
        (weightSixteenTypeAHyperplane_le C hC p
          ((mem_binaryAffineFlatPoints _ x).mp hxFirst))
    · exact (mem_binaryAffineFlatPoints C x).mpr
        (weightSixteenTypeAHyperplane_le C hC
          (weightSixteenTypeAComplementParameter p)
          ((mem_binaryAffineFlatPoints _ x).mp hxSecond))
  · rw [Finset.card_union_of_disjoint
        (weightSixteenTypeAHyperplanePoints_disjoint C hC p),
      card_binaryAffineFlatPoints _ hfirstData.1, hfirstData.2,
      card_binaryAffineFlatPoints _ hsecondData.1, hsecondData.2,
      card_binaryAffineFlatPoints C hCdata.1, hCdata.2]
    norm_num

/-- The two hyperplanes selected by a type-`a` parameter sum to the
indicator of the original affine four-flat. -/
theorem weightSixteenTypeARepresentationWord_eq_indicator
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (p : WeightSixteenTypeAParameter C) :
    weightSixteenRepresentationWord
        (weightSixteenTypeARepresentationPair C hC p).1
        (weightSixteenTypeARepresentationPair C hC p).2 =
      binaryAffineFlatIndicator C := by
  have hpoints : binaryAffineFlatPoints C =
      binaryAffineFlatPoints
          (weightSixteenTypeARepresentationPair C hC p).1 ∪
        binaryAffineFlatPoints
          (weightSixteenTypeARepresentationPair C hC p).2 := by
    simpa only [weightSixteenTypeARepresentationPair] using
      weightSixteenTypeAHyperplanePoints_union C hC p
  have hdisjoint : Disjoint
      (binaryAffineFlatPoints
        (weightSixteenTypeARepresentationPair C hC p).1)
      (binaryAffineFlatPoints
        (weightSixteenTypeARepresentationPair C hC p).2) := by
    simpa only [weightSixteenTypeARepresentationPair] using
      weightSixteenTypeAHyperplanePoints_disjoint C hC p
  symm
  exact binaryAffineFlatIndicator_eq_add_of_points_eq_union
    (weightSixteenTypeARepresentationPair C hC p).1
    (weightSixteenTypeARepresentationPair C hC p).2 C
    hpoints hdisjoint

private theorem binaryDual_eq_of_ker_eq
    {H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)}
    (f g : Module.Dual FABL.𝔽₂ H)
    (hker : LinearMap.ker f = LinearMap.ker g) : f = g := by
  ext x
  by_cases hfx : f x = 0
  · have hxKerF : x ∈ LinearMap.ker f := hfx
    have hxKerG : x ∈ LinearMap.ker g := by rwa [← hker]
    have hgx : g x = 0 := hxKerG
    exact hfx.trans hgx.symm
  · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    have hgx : g x ≠ 0 := by
      intro hgx
      have hxKerG : x ∈ LinearMap.ker g := hgx
      have hxKerF : x ∈ LinearMap.ker f := by rwa [hker]
      exact hfx hxKerF
    have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
    exact hfxOne.trans hgxOne.symm

private theorem weightSixteenTypeAHyperplane_injective
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) :
    Function.Injective (weightSixteenTypeAHyperplane C hC) := by
  rintro ⟨ℓ, b⟩ ⟨m, c⟩ hflat
  have hdirections := congrArg AffineSubspace.direction hflat
  simp only [direction_weightSixteenTypeAHyperplane] at hdirections
  have hkers : LinearMap.ker ℓ.1 = LinearMap.ker m.1 := by
    apply Submodule.map_injective_of_injective C.direction.subtype_injective
    exact hdirections
  have hfunctionals : ℓ = m := by
    apply Subtype.ext
    exact binaryDual_eq_of_ker_eq ℓ.1 m.1 hkers
  subst m
  let v := weightSixteenTypeANormal C ℓ
  let u := weightSixteenTypeABasepoint C hC
  let a : FABL.F₂Cube n := b • (v : FABL.F₂Cube n) + u
  let d : FABL.F₂Cube n := c • (v : FABL.F₂Cube n) + u
  have ha : a ∈ weightSixteenTypeAHyperplane C hC (ℓ, b) :=
    AffineSubspace.self_mem_mk' _ _
  have ha' : a ∈ weightSixteenTypeAHyperplane C hC (ℓ, c) := by
    rw [← hflat]
    exact ha
  have hd : d ∈ weightSixteenTypeAHyperplane C hC (ℓ, c) :=
    AffineSubspace.self_mem_mk' _ _
  have hadiff := AffineSubspace.vsub_mem_direction ha' hd
  rw [direction_weightSixteenTypeAHyperplane] at hadiff
  have hadiffEq : a -ᵥ d =
      ((b + c) • v : C.direction) := by
    change a - d = (b + c) • (v : FABL.F₂Cube n)
    have hnegd : -d = d := by
      funext i
      exact ZMod.neg_eq_self_mod_two (d i)
    rw [sub_eq_add_neg, hnegd]
    change (b • (v : FABL.F₂Cube n) + u) +
        (c • (v : FABL.F₂Cube n) + u) =
      (b + c) • (v : FABL.F₂Cube n)
    calc
      (b • (v : FABL.F₂Cube n) + u) +
          (c • (v : FABL.F₂Cube n) + u) =
        (b • (v : FABL.F₂Cube n) +
          c • (v : FABL.F₂Cube n)) + (u + u) := by abel
      _ = (b + c) • (v : FABL.F₂Cube n) := by
        rw [← add_smul, ZModModule.add_self, add_zero]
  rw [hadiffEq] at hadiff
  obtain ⟨y, hy, hyval⟩ := hadiff
  have hyEq : y = (b + c) • v := by
    apply Subtype.ext
    exact hyval
  have hyZero : ℓ.1 y = 0 := by
    change ℓ.1 y = 0 at hy
    exact hy
  have hbc : b + c = 0 := by
    rw [hyEq, map_smul, weightSixteenTypeANormal_apply, smul_eq_mul,
      mul_one] at hyZero
    exact hyZero
  have hbcEq : b = c :=
    (add_eq_zero_iff_eq_neg.mp hbc).trans (ZMod.neg_eq_self_mod_two c)
  subst c
  rfl

/-- The affine three-flats contained in a fixed affine four-flat. -/
noncomputable def affineThreeFlatsInFourFlat
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact (binaryAffineFlats 3 n).filter fun A ↦ A ≤ C

private theorem exists_typeAParameter_eq_hyperplane
    (C A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n)
    (hA : A ∈ affineThreeFlatsInFourFlat C) :
    ∃ p : WeightSixteenTypeAParameter C,
      weightSixteenTypeAHyperplane C hC p = A := by
  have hCdata : C ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ C.direction = 4 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hC
  have hAdata : A ∈ binaryAffineFlats 3 n ∧ A ≤ C := by
    simpa only [affineThreeFlatsInFourFlat, Finset.mem_filter] using hA
  have hAflat : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = 3 := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hAdata.1
  have hdirLe : A.direction ≤ C.direction :=
    AffineSubspace.direction_le hAdata.2
  let K : Submodule FABL.𝔽₂ C.direction :=
    A.direction.comap C.direction.subtype
  have hKmap : K.map C.direction.subtype = A.direction := by
    dsimp only [K]
    rw [Submodule.map_comap_subtype, inf_of_le_right hdirLe]
  have hKrank : Module.finrank FABL.𝔽₂ K = 3 := by
    have hmapRank := Submodule.finrank_map_subtype_eq C.direction K
    rw [hKmap, hAflat.2] at hmapRank
    exact hmapRank.symm
  have hKlt : K < ⊤ :=
    Submodule.lt_of_le_of_finrank_lt_finrank le_top (by
      rw [hKrank, finrank_top, hCdata.2]
      omega)
  obtain ⟨ℓ, hℓne, hKker⟩ := K.exists_le_ker_of_lt_top hKlt
  have hkerRank : Module.finrank FABL.𝔽₂ (LinearMap.ker ℓ) = 3 := by
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := ℓ) hℓne
    rw [hCdata.2] at hker
    omega
  have hKkerEq : K = LinearMap.ker ℓ :=
    Submodule.eq_of_le_of_finrank_eq hKker (hKrank.trans hkerRank.symm)
  let ℓ' : { ℓ : Module.Dual FABL.𝔽₂ C.direction // ℓ ≠ 0 } := ⟨ℓ, hℓne⟩
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hAflat.1
  let u := weightSixteenTypeABasepoint C hC
  have haC : a ∈ C := hAdata.2 ha
  have hau : a + u ∈ C.direction := by
    have hvsub := AffineSubspace.vsub_mem_direction haC
      (weightSixteenTypeABasepoint_mem C hC)
    change a - u ∈ C.direction at hvsub
    have hnegu : -u = u := by
      funext i
      exact ZMod.neg_eq_self_mod_two (u i)
    rwa [sub_eq_add_neg, hnegu] at hvsub
  let d : C.direction := ⟨a + u, hau⟩
  let b : FABL.𝔽₂ := ℓ d
  let p : WeightSixteenTypeAParameter C := (ℓ', b)
  let v := weightSixteenTypeANormal C ℓ'
  let y : C.direction := b • v + d
  have hℓv : ℓ v = 1 := by
    simpa only [v, ℓ'] using weightSixteenTypeANormal_apply C ℓ'
  have hyKer : y ∈ LinearMap.ker ℓ := by
    change ℓ y = 0
    rw [show ℓ y = b • ℓ v + ℓ d by
      simp only [y, map_add, map_smul]]
    rw [hℓv]
    change b * 1 + ℓ d = 0
    rw [mul_one]
    change ℓ d + ℓ d = 0
    exact ZModModule.add_self _
  have hyK : y ∈ K := by
    rw [hKkerEq]
    exact hyKer
  have hyDirection : (y : FABL.F₂Cube n) ∈ A.direction := by
    rw [← hKmap]
    exact ⟨y, hyK, rfl⟩
  have hbaseA : b • (v : FABL.F₂Cube n) + u ∈ A := by
    have hva := AffineSubspace.vadd_mem_of_mem_direction hyDirection ha
    change (y : FABL.F₂Cube n) + a ∈ A at hva
    have hyadd : (y : FABL.F₂Cube n) + a =
        b • (v : FABL.F₂Cube n) + u := by
      change (b • (v : FABL.F₂Cube n) + (a + u)) + a =
        b • (v : FABL.F₂Cube n) + u
      calc
        (b • (v : FABL.F₂Cube n) + (a + u)) + a =
            b • (v : FABL.F₂Cube n) + (a + a) + u := by abel
        _ = b • (v : FABL.F₂Cube n) + u := by
          rw [ZModModule.add_self, add_zero]
    rwa [hyadd] at hva
  refine ⟨p, ?_⟩
  apply (AffineSubspace.eq_iff_direction_eq_of_mem
    (AffineSubspace.self_mem_mk' _ _) hbaseA).2
  rw [AffineSubspace.direction_mk']
  change weightSixteenTypeADirection C p.1 = A.direction
  dsimp only [p]
  rw [weightSixteenTypeADirection, ← hKkerEq, hKmap]

/-- An affine four-flat contains exactly thirty affine three-flats. -/
theorem card_affineThreeFlatsInFourFlat
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) :
    (affineThreeFlatsInFourFlat C).card = 30 := by
  classical
  rw [← card_weightSixteenTypeAParameters C hC]
  symm
  apply Finset.card_bij
      (fun p _hp ↦ weightSixteenTypeAHyperplane C hC p)
  · intro p _hp
    simp only [affineThreeFlatsInFourFlat, Finset.mem_filter]
    exact ⟨weightSixteenTypeAHyperplane_mem_flats C hC p,
      weightSixteenTypeAHyperplane_le C hC p⟩
  · intro p _hp q _hq heq
    exact weightSixteenTypeAHyperplane_injective C hC heq
  · intro A hA
    obtain ⟨p, hp⟩ := exists_typeAParameter_eq_hyperplane C A hC hA
    exact ⟨p, Finset.mem_univ p, hp⟩

private theorem weightSixteenDisjointPairData
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ disjointBinaryAffineThreeFlatPairs n) :
    p.1 ∈ binaryAffineFlats 3 n ∧
      p.2 ∈ binaryAffineFlats 3 n ∧ p.1 ⊓ p.2 = ⊥ := by
  have hp' : p ∈ binaryAffineThreeFlatPairs n ∧ p.1 ⊓ p.2 = ⊥ := by
    simpa only [disjointBinaryAffineThreeFlatPairs,
      Finset.mem_filter] using hp
  have hproduct : p ∈
      (binaryAffineFlats 3 n).product (binaryAffineFlats 3 n) := hp'.1
  exact ⟨(Finset.mem_product.mp hproduct).1,
    (Finset.mem_product.mp hproduct).2, hp'.2⟩

private theorem weightSixteenDisjointPair_pointSets
    {p : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) ×
      AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)}
    (hp : p ∈ disjointBinaryAffineThreeFlatPairs n) :
    Disjoint (binaryAffineFlatPoints p.1) (binaryAffineFlatPoints p.2) := by
  rw [Finset.disjoint_left]
  intro x hxFirst hxSecond
  have hxMeet : x ∈ p.1 ⊓ p.2 :=
    ⟨(mem_binaryAffineFlatPoints p.1 x |>.mp hxFirst),
      (mem_binaryAffineFlatPoints p.2 x).mp hxSecond⟩
  rw [(weightSixteenDisjointPairData hp).2.2] at hxMeet
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hxMeet
  exact hxMeet

/-- A type-`a` affine-four-flat indicator has exactly thirty ordered
disjoint-three-flat representations. -/
theorem card_weightSixteenRepresentationFiber_typeAIndicator
    (C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hC : C ∈ binaryAffineFlats 4 n) :
    (weightSixteenRepresentationFiber
      (binaryAffineFlatIndicator C)).card = 30 := by
  classical
  rw [← card_affineThreeFlatsInFourFlat C hC]
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' : p ∈ disjointBinaryAffineThreeFlatPairs n ∧
        weightSixteenRepresentationWord p.1 p.2 =
          binaryAffineFlatIndicator C := by
      simpa only [weightSixteenRepresentationFiber,
        Finset.mem_filter] using hp
    have hpdata := weightSixteenDisjointPairData hp'.1
    have hpoints := binaryAffineFlatPoints_eq_union_of_indicator_eq_add
      p.1 p.2 C (weightSixteenDisjointPair_pointSets hp'.1) (by
        simpa only [weightSixteenRepresentationWord] using hp'.2.symm)
    have hfirstLe : p.1 ≤ C := by
      intro x hx
      apply (mem_binaryAffineFlatPoints C x).mp
      rw [hpoints]
      exact Finset.mem_union_left _
        ((mem_binaryAffineFlatPoints p.1 x).mpr hx)
    simp only [affineThreeFlatsInFourFlat, Finset.mem_filter]
    exact ⟨hpdata.1, hfirstLe⟩
  · intro p hp q hq hfirst
    have hp' : p ∈ disjointBinaryAffineThreeFlatPairs n ∧
        weightSixteenRepresentationWord p.1 p.2 =
          binaryAffineFlatIndicator C := by
      simpa only [weightSixteenRepresentationFiber,
        Finset.mem_filter] using hp
    have hq' : q ∈ disjointBinaryAffineThreeFlatPairs n ∧
        weightSixteenRepresentationWord q.1 q.2 =
          binaryAffineFlatIndicator C := by
      simpa only [weightSixteenRepresentationFiber,
        Finset.mem_filter] using hq
    have hsums : binaryAffineFlatIndicator p.1 +
        binaryAffineFlatIndicator p.2 =
          binaryAffineFlatIndicator q.1 + binaryAffineFlatIndicator q.2 := by
      exact hp'.2.trans hq'.2.symm
    rw [hfirst] at hsums
    have hsecondIndicator : binaryAffineFlatIndicator p.2 =
        binaryAffineFlatIndicator q.2 := add_left_cancel hsums
    have hpSecondData : p.2 ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ p.2.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using (weightSixteenDisjointPairData hp'.1).2.1
    have hqSecondData : q.2 ≠ ⊥ ∧
        Module.finrank FABL.𝔽₂ q.2.direction = 3 := by
      simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
        true_and] using (weightSixteenDisjointPairData hq'.1).2.1
    have hsecond : p.2 = q.2 :=
      binaryAffineFlatIndicator_injective_on_nonempty
        hpSecondData.1 hqSecondData.1 hsecondIndicator
    exact Prod.ext hfirst hsecond
  · intro A hA
    obtain ⟨p, hp⟩ := exists_typeAParameter_eq_hyperplane C A hC hA
    let pair := weightSixteenTypeARepresentationPair C hC p
    have hpairFiber : pair ∈ weightSixteenRepresentationFiber
        (binaryAffineFlatIndicator C) := by
      simp only [weightSixteenRepresentationFiber, Finset.mem_filter]
      exact ⟨weightSixteenTypeARepresentationPair_mem C hC p,
        weightSixteenTypeARepresentationWord_eq_indicator C hC p⟩
    refine ⟨pair, hpairFiber, ?_⟩
    simpa only [pair, weightSixteenTypeARepresentationPair] using hp

/-- Every word in the canonical type-`a` family has representation fiber
cardinality thirty. -/
theorem card_weightSixteenRepresentationFiber_of_mem_typeAWords
    (h : BooleanFunction n) (hh : h ∈ orderTwoWeightSixteenTypeAWords n) :
    (weightSixteenRepresentationFiber h).card = 30 := by
  classical
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hh
  exact card_weightSixteenRepresentationFiber_typeAIndicator C hC

end CryptBoolean
