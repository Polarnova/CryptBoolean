/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMuller
public import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Carlet Proposition 12: minimum-weight Reed--Muller words

The equality cases in the Reed--Muller minimum-weight bound are precisely the indicators of
affine flats of the corresponding dimension.
-/

open Finset
open Module
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n r : ℕ}

/-- The `𝔽₂`-valued indicator of the affine flat `H + a`. -/
noncomputable def affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    BooleanFunction n := by
  classical
  exact fun x ↦ if x ∈ FABL.binaryAffineSubspace H a then 1 else 0

@[simp] theorem affineFlatIndicator_apply_eq_one_iff
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a x : FABL.F₂Cube n) :
    affineFlatIndicator H a x = 1 ↔ x ∈ FABL.binaryAffineSubspace H a := by
  classical
  simp [affineFlatIndicator]

@[simp] theorem mem_support_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a x : FABL.F₂Cube n) :
    x ∈ support (affineFlatIndicator H a) ↔
      x ∈ FABL.binaryAffineSubspace H a := by
  rw [mem_support, affineFlatIndicator_apply_eq_one_iff]

/-- A nonempty set closed under ternary sums is an affine set over `𝔽₂`. -/
def IsBinaryAffineSet (S : Set (FABL.F₂Cube n)) : Prop :=
  S.Nonempty ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ ⦃z⦄, z ∈ S → x + y + z ∈ S

private theorem isBinaryAffineSet_iff_exists_binaryAffineSubspace
    (S : Set (FABL.F₂Cube n)) :
    IsBinaryAffineSet S ↔
      ∃ (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n),
        S = FABL.binaryAffineSubspace H a := by
  constructor
  · rintro hS
    obtain ⟨a, ha⟩ := hS.1
    let H : Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
      { carrier := {x | x + a ∈ S}
        zero_mem' := by simpa using ha
        add_mem' := by
          intro x y hx hy
          have hmem := hS.2 hx hy ha
          have heq : (x + a) + (y + a) + a = x + y + a := by
            calc
              (x + a) + (y + a) + a = x + y + (a + a) + a := by abel
              _ = x + y + a := by rw [ZModModule.add_self, add_zero]
          change x + y + a ∈ S
          simpa only [heq] using hmem
        smul_mem' := by
          intro c x hx
          by_cases hc : c = 0
          · subst c
            simpa using ha
          · have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
            subst c
            simpa using hx }
    refine ⟨H, a, Set.ext fun x ↦ ?_⟩
    have hcancel : (x + a) + a = x := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    constructor
    · intro hx
      apply (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).2
      change (x + a) + a ∈ S
      simpa only [hcancel] using hx
    · intro hx
      have hx' := (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).1 hx
      change (x + a) + a ∈ S at hx'
      simpa only [hcancel] using hx'
  · rintro ⟨H, a, rfl⟩
    constructor
    · exact FABL.binaryAffineSubspace_nonempty H a
    · intro x hx y hy z hz
      have hx' := (FABL.mem_binaryAffineSubspace_iff_add_mem H a x).1 hx
      have hy' := (FABL.mem_binaryAffineSubspace_iff_add_mem H a y).1 hy
      have hz' := (FABL.mem_binaryAffineSubspace_iff_add_mem H a z).1 hz
      apply (FABL.mem_binaryAffineSubspace_iff_add_mem H a (x + y + z)).2
      have hsum := H.add_mem (H.add_mem hx' hy') hz'
      have heq : (x + a) + (y + a) + (z + a) = (x + y + z) + a := by
        calc
          (x + a) + (y + a) + (z + a) =
              (x + y + z) + ((a + a) + a) := by abel
          _ = (x + y + z) + a := by rw [ZModModule.add_self, zero_add]
      simpa only [heq] using hsum

private def liftedPartition
    (A₀ A₁ : Set (FABL.F₂Cube n)) : Set (FABL.F₂Cube (n + 1)) :=
  {x | (x 0 = 0 ∧ Fin.tail x ∈ A₀) ∨ (x 0 = 1 ∧ Fin.tail x ∈ A₁)}

private theorem finCons_add (a b : FABL.𝔽₂) (x y : FABL.F₂Cube n) :
    (Fin.cons a x : FABL.F₂Cube (n + 1)) +
      (Fin.cons b y : FABL.F₂Cube (n + 1)) =
        (Fin.cons (a + b) (x + y) : FABL.F₂Cube (n + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

private theorem finCons_add_add
    (a b c : FABL.𝔽₂) (x y z : FABL.F₂Cube n) :
    (Fin.cons a x : FABL.F₂Cube (n + 1)) +
        (Fin.cons b y : FABL.F₂Cube (n + 1)) +
        (Fin.cons c z : FABL.F₂Cube (n + 1)) =
      (Fin.cons (a + b + c) (x + y + z) : FABL.F₂Cube (n + 1)) := by
  rw [finCons_add, finCons_add]

private theorem ternary_sum_mem_right_of_two_mem_left
    {A B U : Set (FABL.F₂Cube n)}
    (hA : IsBinaryAffineSet A) (hU : IsBinaryAffineSet U)
    (hUnion : U = A ∪ B) (hdisjoint : Disjoint A B)
    {x y z : FABL.F₂Cube n} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ B) :
    x + y + z ∈ B := by
  have hxyzU : x + y + z ∈ U := by
    apply hU.2
    · simpa [hUnion] using Or.inl hx
    · simpa [hUnion] using Or.inl hy
    · simpa [hUnion] using Or.inr hz
  rw [hUnion] at hxyzU
  rcases hxyzU with hleft | hright
  · have hzA : z ∈ A := by
      have hmem := hA.2 hx hy hleft
      have heq : x + y + (x + y + z) = z := by
        calc
          x + y + (x + y + z) = (x + x) + (y + y) + z := by abel
          _ = z := by simp only [ZModModule.add_self, zero_add]
      simpa [heq] using hmem
    exact (Set.disjoint_left.1 hdisjoint hzA hz).elim
  · exact hright

private theorem isBinaryAffineSet_liftedPartition
    {A₀ A₁ U : Set (FABL.F₂Cube n)}
    (hA₀ : IsBinaryAffineSet A₀) (hA₁ : IsBinaryAffineSet A₁)
    (hU : IsBinaryAffineSet U) (hUnion : U = A₀ ∪ A₁)
    (hdisjoint : Disjoint A₀ A₁) :
    IsBinaryAffineSet (liftedPartition A₀ A₁) := by
  constructor
  · obtain ⟨x, hx⟩ := hA₀.1
    exact ⟨Fin.cons 0 x, by simp [liftedPartition, hx]⟩
  · intro x hx y hy z hz
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
    · left
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      simpa [liftedPartition] using hA₀.2 hx.2 hy.2 hz.2
    · right
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₀ hU hUnion hdisjoint
        hx.2 hy.2 hz.2
      simpa [liftedPartition] using hmem
    · right
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₀ hU hUnion hdisjoint
        hx.2 hz.2 hy.2
      simpa [liftedPartition, add_assoc, add_left_comm, add_comm] using hmem
    · left
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₁ hU
        (by simpa [Set.union_comm] using hUnion) hdisjoint.symm hy.2 hz.2 hx.2
      simpa [liftedPartition, add_assoc, add_left_comm, add_comm] using hmem
    · right
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₀ hU hUnion hdisjoint
        hy.2 hz.2 hx.2
      simpa [liftedPartition, add_assoc, add_left_comm, add_comm] using hmem
    · left
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₁ hU
        (by simpa [Set.union_comm] using hUnion) hdisjoint.symm hx.2 hz.2 hy.2
      simpa [liftedPartition, add_assoc, add_left_comm, add_comm] using hmem
    · left
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      have hmem := ternary_sum_mem_right_of_two_mem_left hA₁ hU
        (by simpa [Set.union_comm] using hUnion) hdisjoint.symm hx.2 hy.2 hz.2
      simpa [liftedPartition, add_assoc, add_left_comm, add_comm] using hmem
    · right
      rw [← Fin.cons_self_tail x, hx.1, ← Fin.cons_self_tail y, hy.1,
        ← Fin.cons_self_tail z, hz.1, finCons_add_add]
      simpa [liftedPartition] using hA₁.2 hx.2 hy.2 hz.2

private theorem isBinaryAffineSet_liftedLeft
    {A : Set (FABL.F₂Cube n)} (hA : IsBinaryAffineSet A) :
    IsBinaryAffineSet (liftedPartition A ∅) := by
  constructor
  · obtain ⟨x, hx⟩ := hA.1
    exact ⟨Fin.cons 0 x, by simp [liftedPartition, hx]⟩
  · intro x hx y hy z hz
    have hx' : x 0 = 0 ∧ Fin.tail x ∈ A := hx.elim id (fun h ↦ (h.2.elim))
    have hy' : y 0 = 0 ∧ Fin.tail y ∈ A := hy.elim id (fun h ↦ (h.2.elim))
    have hz' : z 0 = 0 ∧ Fin.tail z ∈ A := hz.elim id (fun h ↦ (h.2.elim))
    left
    rw [← Fin.cons_self_tail x, hx'.1, ← Fin.cons_self_tail y, hy'.1,
      ← Fin.cons_self_tail z, hz'.1, finCons_add_add]
    simpa [liftedPartition] using hA.2 hx'.2 hy'.2 hz'.2

private theorem isBinaryAffineSet_liftedRight
    {A : Set (FABL.F₂Cube n)} (hA : IsBinaryAffineSet A) :
    IsBinaryAffineSet (liftedPartition ∅ A) := by
  constructor
  · obtain ⟨x, hx⟩ := hA.1
    exact ⟨Fin.cons 1 x, by simp [liftedPartition, hx]⟩
  · intro x hx y hy z hz
    have hx' : x 0 = 1 ∧ Fin.tail x ∈ A := hx.elim (fun h ↦ h.2.elim) id
    have hy' : y 0 = 1 ∧ Fin.tail y ∈ A := hy.elim (fun h ↦ h.2.elim) id
    have hz' : z 0 = 1 ∧ Fin.tail z ∈ A := hz.elim (fun h ↦ h.2.elim) id
    right
    rw [← Fin.cons_self_tail x, hx'.1, ← Fin.cons_self_tail y, hy'.1,
      ← Fin.cons_self_tail z, hz'.1, finCons_add_add]
    simpa [liftedPartition] using hA.2 hx'.2 hy'.2 hz'.2

private theorem isBinaryAffineSet_liftedSame
    {A : Set (FABL.F₂Cube n)} (hA : IsBinaryAffineSet A) :
    IsBinaryAffineSet (liftedPartition A A) := by
  constructor
  · obtain ⟨x, hx⟩ := hA.1
    exact ⟨Fin.cons 0 x, by simp [liftedPartition, hx]⟩
  · intro x hx y hy z hz
    have hxt : Fin.tail x ∈ A := hx.elim And.right And.right
    have hyt : Fin.tail y ∈ A := hy.elim And.right And.right
    have hzt : Fin.tail z ∈ A := hz.elim And.right And.right
    have htail := hA.2 hxt hyt hzt
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y,
      ← Fin.cons_self_tail z, finCons_add_add]
    by_cases hb : x 0 + y 0 + z 0 = 0
    · left
      simpa [liftedPartition, hb] using htail
    · right
      have hb_one : x 0 + y 0 + z 0 = 1 := Fin.eq_one_of_ne_zero _ hb
      simpa [liftedPartition, hb_one] using htail

/-- Restriction of a Boolean function to a fixed value of its first
coordinate. -/
def firstCoordinateSlice
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂) : BooleanFunction n :=
  fun x ↦ f (Fin.cons b x)

private theorem support_eq_liftedPartition (f : BooleanFunction (n + 1)) :
    (support f : Set (FABL.F₂Cube (n + 1))) =
      liftedPartition
        (support (firstCoordinateSlice f 0) : Set (FABL.F₂Cube n))
        (support (firstCoordinateSlice f 1) : Set (FABL.F₂Cube n)) := by
  ext x
  simp only [Finset.mem_coe, mem_support, liftedPartition, Set.mem_setOf_eq]
  by_cases hx : x 0 = 0
  · rw [← Fin.cons_self_tail x, hx]
    simp [firstCoordinateSlice]
  · have hx_one : x 0 = 1 := Fin.eq_one_of_ne_zero _ hx
    rw [← Fin.cons_self_tail x, hx_one]
    simp [firstCoordinateSlice]

/-- Inclusion-exclusion for the Hamming weight of a sum of Boolean
functions. -/
theorem hammingWeight_add_add_two_mul_card_inter
    (f g : BooleanFunction n) :
    hammingWeight (f + g) + 2 * (support f ∩ support g).card =
      hammingWeight f + hammingWeight g := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support,
    hammingWeight_eq_card_support]
  have hinter :
      support f ∩ support g =
        Finset.univ.filter fun x : FABL.F₂Cube n ↦ f x = 1 ∧ g x = 1 := by
    ext x
    simp [mem_support]
  rw [hinter]
  simp only [support, FABL.f₂OneSupport, Pi.add_apply]
  simp only [Finset.card_filter]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · norm_num [hfx, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfx, hgx_one]
  · have hfx_one : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    by_cases hgx : g x = 0
    · norm_num [hfx_one, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfx_one, hgx_one]

private theorem disjoint_support_of_hammingWeight_add_eq_sum
    (f g : BooleanFunction n)
    (hweight : hammingWeight (f + g) = hammingWeight f + hammingWeight g) :
    Disjoint (support f) (support g) := by
  have hidentity := hammingWeight_add_add_two_mul_card_inter f g
  rw [hweight] at hidentity
  have hcard : (support f ∩ support g).card = 0 := by omega
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.card_eq_zero.mp hcard]

private theorem support_add_eq_union_of_disjoint
    (f g : BooleanFunction n) (hdisjoint : Disjoint (support f) (support g)) :
    support (f + g) = support f ∪ support g := by
  ext x
  have hnotBoth : ¬(f x = 1 ∧ g x = 1) := by
    intro h
    exact Finset.disjoint_left.1 hdisjoint (mem_support f x |>.2 h.1)
      (mem_support g x |>.2 h.2)
  rw [mem_support]
  simp only [Pi.add_apply, Finset.mem_union, mem_support]
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · simp [hfx, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      simp [hfx, hgx_one]
  · have hfx_one : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    by_cases hgx : g x = 0
    · simp [hfx_one, hgx]
    · have hgx_one : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      exact (hnotBoth ⟨hfx_one, hgx_one⟩).elim

private theorem f₂CubeOfFinset_tailFrequency (T : Finset (Fin n)) :
    FABL.f₂CubeOfFinset (FABL.tailFrequency T) =
      Fin.cons 0 (FABL.f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]

private theorem f₂CubeOfFinset_insert_zero_tailFrequency
    (T : Finset (Fin n)) :
    FABL.f₂CubeOfFinset (insert 0 (FABL.tailFrequency T)) =
      Fin.cons 1 (FABL.f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [FABL.f₂CubeOfFinset]
  · simp [FABL.f₂CubeOfFinset, FABL.tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_zero
    (f : BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    FABL.anfCoeff (firstCoordinateSlice f 0) S =
      FABL.anfCoeff f (FABL.tailFrequency S) := by
  classical
  simp only [FABL.anfCoeff, firstCoordinateSlice]
  apply Finset.sum_bij (fun T _ ↦ FABL.tailFrequency T)
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    exact Finset.map_subset_map.mpr hT
  · intro T₁ hT₁ T₂ hT₂ heq
    exact Finset.map_injective (Fin.succEmb n) heq
  · intro U hU
    rw [Finset.mem_powerset] at hU
    obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
    exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
  · intro T hT
    rw [f₂CubeOfFinset_tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_one
    (f : BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    FABL.anfCoeff (firstCoordinateSlice f 1) S =
      FABL.anfCoeff f (FABL.tailFrequency S) +
        FABL.anfCoeff f (insert 0 (FABL.tailFrequency S)) := by
  classical
  have hsplit := Finset.sum_powerset_insert (FABL.zero_notMem_tailFrequency S)
    (fun U ↦ f (FABL.f₂CubeOfFinset U))
  have htail :
      (∑ U ∈ (FABL.tailFrequency S).powerset,
          f (FABL.f₂CubeOfFinset U)) =
        FABL.anfCoeff (firstCoordinateSlice f 0) S := by
    rw [anfCoeff_firstCoordinateSlice_zero]
    rfl
  have hone :
      (∑ U ∈ (FABL.tailFrequency S).powerset,
          f (FABL.f₂CubeOfFinset (insert 0 U))) =
        FABL.anfCoeff (firstCoordinateSlice f 1) S := by
    simp only [FABL.anfCoeff, firstCoordinateSlice]
    symm
    apply Finset.sum_bij (fun T _ ↦ FABL.tailFrequency T)
    · intro T hT
      rw [Finset.mem_powerset] at hT ⊢
      exact Finset.map_subset_map.mpr hT
    · intro T₁ hT₁ T₂ hT₂ heq
      exact Finset.map_injective (Fin.succEmb n) heq
    · intro U hU
      rw [Finset.mem_powerset] at hU
      obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
      exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
    · intro T hT
      rw [f₂CubeOfFinset_insert_zero_tailFrequency]
  have hcoeff :
      FABL.anfCoeff f (insert 0 (FABL.tailFrequency S)) =
        FABL.anfCoeff (firstCoordinateSlice f 0) S +
          FABL.anfCoeff (firstCoordinateSlice f 1) S := by
    simpa only [FABL.anfCoeff, htail, hone] using hsplit
  rw [← anfCoeff_firstCoordinateSlice_zero]
  rw [hcoeff, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Hamming weight splits as the sum of the two first-coordinate slice
weights. -/
theorem hammingWeight_firstCoordinateSlices
    (f : BooleanFunction (n + 1)) :
    hammingWeight f =
      hammingWeight (firstCoordinateSlice f 0) +
        hammingWeight (firstCoordinateSlice f 1) := by
  classical
  simp only [FABL.hammingNorm_eq_card_f₂OneSupport, FABL.f₂OneSupport,
    Finset.card_filter]
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (n + 1) ↦ FABL.𝔽₂)).symm
    (fun x ↦ if f x = 1 then 1 else 0)
    (fun bx ↦ if f (Fin.cons bx.1 bx.2) = 1 then 1 else 0)
    (fun x ↦ by rw [← Fin.cons_self_tail x]; rfl)]
  rw [Fintype.sum_prod_type]
  have htwo : (Finset.univ : Finset FABL.𝔽₂) = {0, 1} := rfl
  rw [htwo]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton]
  rfl

/-- Restricting one coordinate does not increase algebraic degree. -/
theorem firstCoordinateSlice_degree_le
    (f : BooleanFunction (n + 1)) (b : FABL.𝔽₂)
    (hdeg : FABL.functionAlgebraicDegree f ≤ r) :
    FABL.functionAlgebraicDegree (firstCoordinateSlice f b) ≤ r := by
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hS
  by_cases hb : b = 0
  · subst b
    rw [anfCoeff_firstCoordinateSlice_zero] at hS
    have hcard := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
      (FABL.tailFrequency S) hS
    simpa [FABL.card_tailFrequency] using hcard
  · have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
    subst b
    rw [anfCoeff_firstCoordinateSlice_one] at hS
    have hne :
        FABL.anfCoeff f (FABL.tailFrequency S) ≠ 0 ∨
          FABL.anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hS (by rw [h.1, h.2, add_zero])
    cases hne with
    | inl htail =>
        have hcard := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
          (FABL.tailFrequency S) htail
        simpa [FABL.card_tailFrequency] using hcard
    | inr hinsert =>
        have hcard := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
          (insert 0 (FABL.tailFrequency S)) hinsert
        rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
          FABL.card_tailFrequency] at hcard
        omega

/-- The sum of the two first-coordinate slices lowers the degree bound by
one. -/
theorem firstCoordinateDifference_degree_le_pred
    (f : BooleanFunction (n + 1))
    (hdeg : FABL.functionAlgebraicDegree f ≤ r) :
    FABL.functionAlgebraicDegree
      (firstCoordinateSlice f 0 + firstCoordinateSlice f 1) ≤ r - 1 := by
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hS
  rw [FABL.anfCoeff_add] at hS
  change FABL.anfCoeff (firstCoordinateSlice f 0) S +
    FABL.anfCoeff (firstCoordinateSlice f 1) S ≠ 0 at hS
  rw [anfCoeff_firstCoordinateSlice_zero,
    anfCoeff_firstCoordinateSlice_one] at hS
  simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at hS
  have hcard := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
    (insert 0 (FABL.tailFrequency S)) hS
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hcard
  omega

private theorem function_eq_zero_of_both_firstCoordinateSlices_zero
    (f : BooleanFunction (n + 1))
    (hzero : firstCoordinateSlice f 0 = 0)
    (hone : firstCoordinateSlice f 1 = 0) :
    f = 0 := by
  funext x
  rw [← Fin.cons_self_tail x]
  by_cases hx : x 0 = 0
  · rw [hx]
    exact congrFun hzero (Fin.tail x)
  · have hxone : x 0 = 1 := Fin.eq_one_of_ne_zero _ hx
    rw [hxone]
    exact congrFun hone (Fin.tail x)

private theorem exists_anfCoeff_ne_zero_of_ne_zero
    (f : BooleanFunction n) (hf : f ≠ 0) :
    ∃ S, FABL.anfCoeff f S ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  calc
    f = FABL.anfEval (FABL.anfCoeff f) := (FABL.anfEval_anfCoeff f).symm
    _ = 0 := by
      funext x
      simp [FABL.anfEval, h]

private theorem degree_index_pos_of_exactly_one_nonzero_slice
    (f : BooleanFunction (n + 1))
    (hzero : firstCoordinateSlice f 0 = 0)
    (hone : firstCoordinateSlice f 1 ≠ 0)
    (hdeg : FABL.functionAlgebraicDegree f ≤ r) :
    0 < r := by
  obtain ⟨T, hT⟩ := exists_anfCoeff_ne_zero_of_ne_zero
    (firstCoordinateSlice f 1) hone
  have hzeroCoeff : FABL.anfCoeff (firstCoordinateSlice f 0) T = 0 := by
    rw [hzero]
    simp
  have hinsert : FABL.anfCoeff f (insert 0 (FABL.tailFrequency T)) ≠ 0 := by
    rw [anfCoeff_firstCoordinateSlice_one, ← anfCoeff_firstCoordinateSlice_zero,
      hzeroCoeff, zero_add] at hT
    exact hT
  have hbound := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
    (insert 0 (FABL.tailFrequency T)) hinsert
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency T),
    FABL.card_tailFrequency] at hbound
  omega

private theorem degree_index_pos_of_zero_slice_nonzero
    (f : BooleanFunction (n + 1))
    (hone : firstCoordinateSlice f 1 = 0)
    (hzero : firstCoordinateSlice f 0 ≠ 0)
    (hdeg : FABL.functionAlgebraicDegree f ≤ r) :
    0 < r := by
  obtain ⟨S, hS⟩ := exists_anfCoeff_ne_zero_of_ne_zero
    (firstCoordinateSlice f 0) hzero
  have honeCoeff : FABL.anfCoeff (firstCoordinateSlice f 1) S = 0 := by
    rw [hone]
    simp
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hinsert : FABL.anfCoeff f (insert 0 (FABL.tailFrequency S)) ≠ 0 := by
    intro hinsert
    have hrel := anfCoeff_firstCoordinateSlice_one f S
    rw [honeCoeff, hinsert, add_zero] at hrel
    exact hS hrel.symm
  have hbound := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
    (insert 0 (FABL.tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hbound
  omega

private theorem degree_index_pos_of_firstCoordinateDifference_nonzero
    (f : BooleanFunction (n + 1))
    (hdiff : firstCoordinateSlice f 0 + firstCoordinateSlice f 1 ≠ 0)
    (hdeg : FABL.functionAlgebraicDegree f ≤ r) :
    0 < r := by
  obtain ⟨S, hS⟩ := exists_anfCoeff_ne_zero_of_ne_zero
    (firstCoordinateSlice f 0 + firstCoordinateSlice f 1) hdiff
  rw [FABL.anfCoeff_add] at hS
  change FABL.anfCoeff (firstCoordinateSlice f 0) S +
    FABL.anfCoeff (firstCoordinateSlice f 1) S ≠ 0 at hS
  rw [anfCoeff_firstCoordinateSlice_zero,
    anfCoeff_firstCoordinateSlice_one] at hS
  simp only [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at hS
  have hbound := (FABL.algebraicDegree_le_iff (FABL.anfCoeff f) r).mp hdeg
    (insert 0 (FABL.tailFrequency S)) hS
  rw [Finset.card_insert_of_notMem (FABL.zero_notMem_tailFrequency S),
    FABL.card_tailFrequency] at hbound
  omega

private theorem hammingWeight_add_le
    (f g : BooleanFunction n) :
    hammingWeight (f + g) ≤ hammingWeight f + hammingWeight g := by
  have htriangle := hammingDist_triangle_left f g 0
  rw [hammingDist_zero_left] at htriangle
  change hammingDistance f g ≤ hammingWeight f + hammingWeight g at htriangle
  rw [hammingDistance_eq_hammingWeight_add] at htriangle
  exact htriangle

private theorem minimumWeight_support_isBinaryAffineSet
    (f : BooleanFunction n) (hrn : r ≤ n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ r)
    (hweight : hammingWeight f = 2 ^ (n - r)) (hf : f ≠ 0) :
    IsBinaryAffineSet (support f : Set (FABL.F₂Cube n)) := by
  induction n generalizing r with
  | zero =>
      have hsupp : (support f : Set (FABL.F₂Cube 0)) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        rw [Finset.mem_coe, mem_support]
        have hx : f x ≠ 0 := by
          intro hx
          apply hf
          funext y
          simp [Subsingleton.elim y x, hx]
        exact Fin.eq_one_of_ne_zero _ hx
      rw [hsupp]
      constructor
      · exact Set.univ_nonempty
      · simp
  | succ n ih =>
      let f₀ : BooleanFunction n := firstCoordinateSlice f 0
      let f₁ : BooleanFunction n := firstCoordinateSlice f 1
      have hsplit : hammingWeight f = hammingWeight f₀ + hammingWeight f₁ := by
        simpa [f₀, f₁] using hammingWeight_firstCoordinateSlices f
      by_cases hf₀ : f₀ = 0
      · have hf₁ : f₁ ≠ 0 := by
          intro hf₁
          apply hf
          exact function_eq_zero_of_both_firstCoordinateSlices_zero f
            (by simpa [f₀] using hf₀) (by simpa [f₁] using hf₁)
        have hrpos : 0 < r := degree_index_pos_of_exactly_one_nonzero_slice f
          (by simpa [f₀] using hf₀) (by simpa [f₁] using hf₁) hdegree
        have hdegree₁ : FABL.functionAlgebraicDegree f₁ ≤ r - 1 := by
          have hdiff := firstCoordinateDifference_degree_le_pred f hdegree
          simpa [f₀, f₁, hf₀] using hdiff
        have hrpred : r - 1 ≤ n := by omega
        have hexp : (n + 1) - r = n - (r - 1) := by omega
        have hweight₁ : hammingWeight f₁ = 2 ^ (n - (r - 1)) := by
          rw [hsplit, hf₀] at hweight
          simpa [hexp] using hweight
        have hA₁ := ih f₁ hrpred hdegree₁ hweight₁ hf₁
        rw [support_eq_liftedPartition f]
        have hsupp₀ : support f₀ = ∅ := by
          ext x
          simp [hf₀, support, FABL.f₂OneSupport]
        simpa [f₀, f₁, hsupp₀] using isBinaryAffineSet_liftedRight hA₁
      · by_cases hf₁ : f₁ = 0
        · have hrpos : 0 < r := degree_index_pos_of_zero_slice_nonzero f
            (by simpa [f₁] using hf₁) (by simpa [f₀] using hf₀) hdegree
          have hdegree₀ : FABL.functionAlgebraicDegree f₀ ≤ r - 1 := by
            have hdiff := firstCoordinateDifference_degree_le_pred f hdegree
            simpa [f₀, f₁, hf₁] using hdiff
          have hrpred : r - 1 ≤ n := by omega
          have hexp : (n + 1) - r = n - (r - 1) := by omega
          have hweight₀ : hammingWeight f₀ = 2 ^ (n - (r - 1)) := by
            rw [hsplit, hf₁] at hweight
            simpa [hexp] using hweight
          have hA₀ := ih f₀ hrpred hdegree₀ hweight₀ hf₀
          rw [support_eq_liftedPartition f]
          have hsupp₁ : support f₁ = ∅ := by
            ext x
            simp [hf₁, support, FABL.f₂OneSupport]
          simpa [f₀, f₁, hsupp₁] using isBinaryAffineSet_liftedLeft hA₀
        · have hrn' : r ≤ n := by
            by_contra h
            have hre : r = n + 1 := by omega
            have hpositive₀ : 0 < hammingWeight f₀ := hammingNorm_pos_iff.mpr hf₀
            have hpositive₁ : 0 < hammingWeight f₁ := hammingNorm_pos_iff.mpr hf₁
            rw [hsplit, hre] at hweight
            norm_num at hweight
            omega
          have hdegree₀ : FABL.functionAlgebraicDegree f₀ ≤ r := by
            simpa [f₀] using firstCoordinateSlice_degree_le f 0 hdegree
          have hdegree₁ : FABL.functionAlgebraicDegree f₁ ≤ r := by
            simpa [f₁] using firstCoordinateSlice_degree_le f 1 hdegree
          have hlower₀ := two_pow_sub_le_hammingWeight_of_degree_le f₀ hdegree₀ hf₀
          have hlower₁ := two_pow_sub_le_hammingWeight_of_degree_le f₁ hdegree₁ hf₁
          have hexp : 2 ^ ((n + 1) - r) = 2 ^ (n - r) + 2 ^ (n - r) := by
            rw [show (n + 1) - r = (n - r) + 1 by omega, pow_succ]
            omega
          have hsum : hammingWeight f₀ + hammingWeight f₁ =
              2 ^ (n - r) + 2 ^ (n - r) := by
            rw [← hsplit, hweight, hexp]
          have hweight₀ : hammingWeight f₀ = 2 ^ (n - r) := by omega
          have hweight₁ : hammingWeight f₁ = 2 ^ (n - r) := by omega
          have hA₀ := ih f₀ hrn' hdegree₀ hweight₀ hf₀
          have hA₁ := ih f₁ hrn' hdegree₁ hweight₁ hf₁
          let g : BooleanFunction n := f₀ + f₁
          have hdegreeg : FABL.functionAlgebraicDegree g ≤ r - 1 := by
            simpa [g, f₀, f₁] using firstCoordinateDifference_degree_le_pred f hdegree
          by_cases hg : g = 0
          · have heq : f₀ = f₁ := by
              funext x
              have hx := congrFun hg x
              change f₀ x + f₁ x = 0 at hx
              exact (add_eq_zero_iff_eq_neg.mp hx).trans
                (ZMod.neg_eq_self_mod_two (f₁ x))
            rw [support_eq_liftedPartition f]
            simpa [f₀, f₁, heq] using isBinaryAffineSet_liftedSame hA₀
          · have hrpos : 0 < r := by
              apply degree_index_pos_of_firstCoordinateDifference_nonzero f
              · simpa [g, f₀, f₁] using hg
              · exact hdegree
            have hrpred : r - 1 ≤ n := by omega
            have hlowerg := two_pow_sub_le_hammingWeight_of_degree_le g hdegreeg hg
            have hupperg : hammingWeight g ≤ hammingWeight f₀ + hammingWeight f₁ :=
              hammingWeight_add_le f₀ f₁
            have hexpg : 2 ^ (n - (r - 1)) =
                2 ^ (n - r) + 2 ^ (n - r) := by
              rw [show n - (r - 1) = (n - r) + 1 by omega, pow_succ]
              omega
            have hweightg : hammingWeight g = 2 ^ (n - (r - 1)) := by
              rw [hweight₀, hweight₁, ← hexpg] at hupperg
              omega
            have hAg := ih g hrpred hdegreeg hweightg hg
            have hweightgSum :
                hammingWeight g = hammingWeight f₀ + hammingWeight f₁ := by
              rw [hweightg, hexpg, hweight₀, hweight₁]
            have hdisjointFin :=
              disjoint_support_of_hammingWeight_add_eq_sum f₀ f₁
                (by simpa [g] using hweightgSum)
            have hdisjointSet :
                Disjoint (support f₀ : Set (FABL.F₂Cube n))
                  (support f₁ : Set (FABL.F₂Cube n)) := by
              rw [Set.disjoint_left]
              intro x hx₀ hx₁
              exact Finset.disjoint_left.1 hdisjointFin hx₀ hx₁
            have hUnion :
                (support g : Set (FABL.F₂Cube n)) =
                  (support f₀ : Set (FABL.F₂Cube n)) ∪
                    (support f₁ : Set (FABL.F₂Cube n)) := by
              have hfin := support_add_eq_union_of_disjoint f₀ f₁ hdisjointFin
              simpa [g] using congrArg (fun s : Finset (FABL.F₂Cube n) ↦
                (s : Set (FABL.F₂Cube n))) hfin
            rw [support_eq_liftedPartition f]
            exact isBinaryAffineSet_liftedPartition hA₀ hA₁ hAg hUnion hdisjointSet

private noncomputable def submoduleEquivAffineFlatSubtype
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    H ≃ {x : FABL.F₂Cube n // x ∈ FABL.binaryAffineSubspace H a} where
  toFun x := ⟨x.1 + a, by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
    simpa only [add_assoc, ZModModule.add_self, add_zero] using x.2⟩
  invFun x := ⟨x.1 + a, (FABL.mem_binaryAffineSubspace_iff_add_mem H a x.1).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp only [add_assoc, ZModModule.add_self, add_zero]
  right_inv x := by
    apply Subtype.ext
    simp only [add_assoc, ZModModule.add_self, add_zero]

/-- The Hamming weight of an affine-flat indicator is the cardinality of its direction. -/
theorem hammingWeight_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    hammingWeight (affineFlatIndicator H a) =
      2 ^ Module.finrank FABL.𝔽₂ H := by
  classical
  rw [hammingWeight_eq_card_support]
  have hsupp :
      support (affineFlatIndicator H a) =
        Finset.univ.filter fun x : FABL.F₂Cube n ↦
          x ∈ FABL.binaryAffineSubspace H a := by
    ext x
    simp
  rw [hsupp]
  calc
    (Finset.univ.filter fun x : FABL.F₂Cube n ↦
        x ∈ FABL.binaryAffineSubspace H a).card =
        Fintype.card {x : FABL.F₂Cube n // x ∈ FABL.binaryAffineSubspace H a} := by
      symm
      exact Fintype.card_subtype _
    _ = Fintype.card H := Fintype.card_congr (submoduleEquivAffineFlatSubtype H a).symm
    _ = Nat.card H := Nat.card_eq_fintype_card.symm
    _ = 2 ^ Module.finrank FABL.𝔽₂ H := FABL.card_submodule_eq_two_pow_finrank H

private noncomputable def affineFlatBasisProduct
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    BooleanFunction n := by
  let P := FABL.perpendicularSubspace H
  let B : Basis (Fin (Module.finrank FABL.𝔽₂ P)) FABL.𝔽₂ P :=
    Module.finBasis FABL.𝔽₂ P
  exact ∏ i, FABL.affineFunction
    (1 + FABL.f₂DotProduct (B i).1 a) (B i).1

private theorem affineFlatBasisProduct_apply_eq_one_iff
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a x : FABL.F₂Cube n) :
    affineFlatBasisProduct H a x = 1 ↔
      x ∈ FABL.binaryAffineSubspace H a := by
  classical
  simp only [affineFlatBasisProduct, Finset.prod_apply]
  let P := FABL.perpendicularSubspace H
  let B : Basis (Fin (Module.finrank FABL.𝔽₂ P)) FABL.𝔽₂ P :=
    Module.finBasis FABL.𝔽₂ P
  change (∏ i, FABL.affineFunction
    (1 + FABL.f₂DotProduct (B i).1 a) (B i).1 x) = 1 ↔ _
  constructor
  · intro hproduct
    rw [Finset.prod_eq_one_iff] at hproduct
    have hbasis (i : Fin (Module.finrank FABL.𝔽₂ P)) :
        FABL.f₂DotProduct (B i).1 x = FABL.f₂DotProduct (B i).1 a := by
      have hi := hproduct i (Finset.mem_univ i)
      change 1 + FABL.f₂DotProduct (B i).1 a +
        FABL.f₂DotProduct (B i).1 x = 1 at hi
      have hzero : FABL.f₂DotProduct (B i).1 a +
          FABL.f₂DotProduct (B i).1 x = 0 := by
        apply add_left_cancel (a := (1 : FABL.𝔽₂))
        simpa [add_assoc] using hi
      have hzero' : FABL.f₂DotProduct (B i).1 x +
          FABL.f₂DotProduct (B i).1 a = 0 := by
        simpa [add_comm] using hzero
      exact (add_eq_zero_iff_eq_neg.mp hzero').trans
        (ZMod.neg_eq_self_mod_two (FABL.f₂DotProduct (B i).1 a))
    let L : P →ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
      ((dotProductEquiv FABL.𝔽₂ (Fin n)) (x + a)).comp P.subtype
    have hL : L = 0 := by
      apply B.ext
      intro i
      change (x + a) ⬝ᵥ (B i).1 = 0
      rw [dotProduct_comm, dotProduct_add]
      change FABL.f₂DotProduct (B i).1 x +
        FABL.f₂DotProduct (B i).1 a = 0
      rw [hbasis]
      exact ZModModule.add_self _
    rw [FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity]
    intro γ hγ
    have hzero := DFunLike.congr_fun hL ⟨γ, hγ⟩
    change (x + a) ⬝ᵥ γ = 0 at hzero
    rw [dotProduct_comm, dotProduct_add] at hzero
    change FABL.f₂DotProduct γ x + FABL.f₂DotProduct γ a = 0 at hzero
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans
      (ZMod.neg_eq_self_mod_two (FABL.f₂DotProduct γ a))
  · intro hx
    rw [Finset.prod_eq_one_iff]
    intro i hi
    have hparity :=
      (FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity H a x).1 hx
        (B i).1 (B i).2
    change 1 + FABL.f₂DotProduct (B i).1 a +
      FABL.f₂DotProduct (B i).1 x = 1
    rw [hparity, add_assoc, ZModModule.add_self, add_zero]

private theorem affineFlatBasisProduct_eq_indicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    affineFlatBasisProduct H a = affineFlatIndicator H a := by
  funext x
  have hone : affineFlatBasisProduct H a x = 1 ↔ affineFlatIndicator H a x = 1 :=
    (affineFlatBasisProduct_apply_eq_one_iff H a x).trans
      (affineFlatIndicator_apply_eq_one_iff H a x).symm
  by_cases hproduct : affineFlatBasisProduct H a x = 0
  · have hindicator : affineFlatIndicator H a x = 0 := by
      by_contra h
      have hOne := Fin.eq_one_of_ne_zero _ h
      exact zero_ne_one (hproduct.symm.trans (hone.mpr hOne))
    exact hproduct.trans hindicator.symm
  · have hOne := Fin.eq_one_of_ne_zero _ hproduct
    exact hOne.trans (hone.mp hOne).symm

private theorem functionAlgebraicDegree_affineFlatIndicator_le_codimension
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    FABL.functionAlgebraicDegree (affineFlatIndicator H a) ≤
      FABL.f₂Codimension H := by
  classical
  rw [← affineFlatBasisProduct_eq_indicator H a]
  let P := FABL.perpendicularSubspace H
  let B : Basis (Fin (Module.finrank FABL.𝔽₂ P)) FABL.𝔽₂ P :=
    Module.finBasis FABL.𝔽₂ P
  change FABL.functionAlgebraicDegree
    (∏ i, FABL.affineFunction
      (1 + FABL.f₂DotProduct (B i).1 a) (B i).1) ≤ FABL.f₂Codimension H
  calc
    FABL.functionAlgebraicDegree
        (∏ i, FABL.affineFunction
          (1 + FABL.f₂DotProduct (B i).1 a) (B i).1) ≤
        ∑ i : Fin (Module.finrank FABL.𝔽₂ P),
          FABL.functionAlgebraicDegree
            (FABL.affineFunction
              (1 + FABL.f₂DotProduct (B i).1 a) (B i).1) := by
      simpa using FABL.functionAlgebraicDegree_finset_prod_le
        (Finset.univ : Finset (Fin (Module.finrank FABL.𝔽₂ P)))
        (fun i ↦ FABL.affineFunction
          (1 + FABL.f₂DotProduct (B i).1 a) (B i).1)
    _ ≤ ∑ _i : Fin (Module.finrank FABL.𝔽₂ P), 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact FABL.functionAlgebraicDegree_affineFunction_le_one _ _
    _ = FABL.f₂Codimension H := by simp [FABL.f₂Codimension, P]

/-- An affine flat of codimension `k` has indicator of algebraic degree exactly `k`. -/
theorem functionAlgebraicDegree_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n) :
    FABL.functionAlgebraicDegree (affineFlatIndicator H a) =
      FABL.f₂Codimension H := by
  apply Nat.le_antisymm (functionAlgebraicDegree_affineFlatIndicator_le_codimension H a)
  by_contra hnot
  have hlt : FABL.functionAlgebraicDegree (affineFlatIndicator H a) <
      FABL.f₂Codimension H := by
    omega
  have hcodim : FABL.f₂Codimension H =
      n - Module.finrank FABL.𝔽₂ H := by
    exact FABL.finrank_perpendicularSubspace H
  have hcodimle : FABL.f₂Codimension H ≤ n := by omega
  have hcodimpos : 0 < FABL.f₂Codimension H := by
    by_contra hzero
    have : FABL.f₂Codimension H = 0 := by omega
    omega
  have hdegreePred :
      FABL.functionAlgebraicDegree (affineFlatIndicator H a) ≤
        FABL.f₂Codimension H - 1 := by
    omega
  have hnonzero : affineFlatIndicator H a ≠ 0 := by
    intro hzero
    have ha := congrFun hzero a
    have hmem : a ∈ FABL.binaryAffineSubspace H a := by
      rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
      rw [ZModModule.add_self]
      exact H.zero_mem
    simp [affineFlatIndicator, hmem] at ha
  have hlower := two_pow_sub_le_hammingWeight_of_degree_le
    (affineFlatIndicator H a) hdegreePred hnonzero
  rw [hammingWeight_affineFlatIndicator] at hlower
  have hexp : n - (FABL.f₂Codimension H - 1) =
      Module.finrank FABL.𝔽₂ H + 1 := by
    omega
  rw [hexp, pow_succ] at hlower
  have hpositive : 0 < 2 ^ Module.finrank FABL.𝔽₂ H := Nat.two_pow_pos _
  omega

/-- Reverse direction of Carlet Proposition 12: every affine flat of dimension `n - r` has
degree `r` and minimum Reed--Muller weight. -/
theorem degree_eq_and_hammingWeight_eq_affineFlatIndicator
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hrn : r ≤ n) (hfinrank : Module.finrank FABL.𝔽₂ H = n - r) :
    FABL.functionAlgebraicDegree (affineFlatIndicator H a) = r ∧
      hammingWeight (affineFlatIndicator H a) = 2 ^ (n - r) := by
  have hcodim : FABL.f₂Codimension H = r := by
    rw [FABL.f₂Codimension, FABL.finrank_perpendicularSubspace, hfinrank]
    omega
  constructor
  · rw [functionAlgebraicDegree_affineFlatIndicator, hcodim]
  · rw [hammingWeight_affineFlatIndicator, hfinrank]

/-- A binary Boolean function is the affine-flat indicator exactly when its support is that flat. -/
theorem eq_affineFlatIndicator_iff_support_eq
    (f : BooleanFunction n) (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    f = affineFlatIndicator H a ↔
      (support f : Set (FABL.F₂Cube n)) = FABL.binaryAffineSubspace H a := by
  constructor
  · rintro rfl
    ext x
    simp
  · intro hsupp
    funext x
    by_cases hx : f x = 0
    · have hnotmem : x ∉ FABL.binaryAffineSubspace H a := by
        intro hmem
        have hxSupp : x ∈ (support f : Set (FABL.F₂Cube n)) := by
          rw [hsupp]
          exact hmem
        have hxOne := (mem_support f x).1 hxSupp
        exact zero_ne_one (hx.symm.trans hxOne)
      simp [affineFlatIndicator, hx, hnotmem]
    · have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hx
      have hmem : x ∈ FABL.binaryAffineSubspace H a := by
        have hxSupp : x ∈ (support f : Set (FABL.F₂Cube n)) := by
          rw [Finset.mem_coe, mem_support]
          exact hxOne
        rw [hsupp] at hxSupp
        exact hxSupp
      simp [affineFlatIndicator, hxOne, hmem]

/-- Forward direction of Carlet Proposition 12: every minimum-weight word is an affine-flat
indicator of dimension `n - r`. -/
theorem exists_affineFlatIndicator_of_degree_eq_and_hammingWeight_eq
    (f : BooleanFunction n) (hrn : r ≤ n)
    (hdegree : FABL.functionAlgebraicDegree f = r)
    (hweight : hammingWeight f = 2 ^ (n - r)) :
    ∃ (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n),
      Module.finrank FABL.𝔽₂ H = n - r ∧ f = affineFlatIndicator H a := by
  have hf : f ≠ 0 := by
    intro hf
    subst f
    simp at hweight
    exact (pow_ne_zero (n - r) (by norm_num : (2 : ℕ) ≠ 0)) hweight.symm
  have hAffine := minimumWeight_support_isBinaryAffineSet f hrn hdegree.le hweight hf
  obtain ⟨H, a, hsupp⟩ :=
    (@isBinaryAffineSet_iff_exists_binaryAffineSubspace n
      (support f : Set (FABL.F₂Cube n))).1 hAffine
  have hfindicator : f = affineFlatIndicator H a :=
    (eq_affineFlatIndicator_iff_support_eq f H a).2 hsupp
  have hpow : 2 ^ Module.finrank FABL.𝔽₂ H = 2 ^ (n - r) := by
    calc
      2 ^ Module.finrank FABL.𝔽₂ H = hammingWeight (affineFlatIndicator H a) :=
        (hammingWeight_affineFlatIndicator H a).symm
      _ = hammingWeight f := by rw [hfindicator]
      _ = 2 ^ (n - r) := hweight
  have hfinrank : Module.finrank FABL.𝔽₂ H = n - r :=
    Nat.pow_right_injective (by norm_num) hpow
  exact ⟨H, a, hfinrank, hfindicator⟩

/-- Carlet Proposition 12: for `0 ≤ r ≤ n`, the Boolean functions of degree `r` and
weight `2^(n-r)` are exactly the indicators of affine flats of dimension `n-r`. -/
theorem degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator
    (f : BooleanFunction n) (hrn : r ≤ n) :
    (FABL.functionAlgebraicDegree f = r ∧ hammingWeight f = 2 ^ (n - r)) ↔
      ∃ (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n),
        Module.finrank FABL.𝔽₂ H = n - r ∧ f = affineFlatIndicator H a := by
  constructor
  · rintro ⟨hdegree, hweight⟩
    exact exists_affineFlatIndicator_of_degree_eq_and_hammingWeight_eq
      f hrn hdegree hweight
  · rintro ⟨H, a, hfinrank, rfl⟩
    exact degree_eq_and_hammingWeight_eq_affineFlatIndicator H a hrn hfinrank

/-- Carlet Proposition 12 in support form: the minimum-weight words of degree `r` are exactly
the Boolean functions whose support is an affine flat of dimension `n-r`. -/
theorem degree_eq_and_hammingWeight_eq_iff_support_is_affineFlat
    (f : BooleanFunction n) (hrn : r ≤ n) :
    (FABL.functionAlgebraicDegree f = r ∧ hammingWeight f = 2 ^ (n - r)) ↔
      ∃ (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n),
        Module.finrank FABL.𝔽₂ H = n - r ∧
          (support f : Set (FABL.F₂Cube n)) = FABL.binaryAffineSubspace H a := by
  rw [degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator f hrn]
  constructor
  · rintro ⟨H, a, hfinrank, hfunction⟩
    exact ⟨H, a, hfinrank,
      (eq_affineFlatIndicator_iff_support_eq f H a).1 hfunction⟩
  · rintro ⟨H, a, hfinrank, hsupp⟩
    exact ⟨H, a, hfinrank,
      (eq_affineFlatIndicator_iff_support_eq f H a).2 hsupp⟩

end CryptBoolean
