/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwo
public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight

/-!
# Affine-flat characters for low-weight Reed--Muller words

Canonical affine-flat enumerators and the support-character identities shared by
the weight-eight, weight-twelve, weight-fourteen, and weight-sixteen analyses.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance lowWeightFlatsAffineSubspaceFintype : Fintype
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance lowWeightFlatsAffineSubspaceDecidableEq : DecidableEq
    (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Classical.decEq _

noncomputable local instance lowWeightFlatsSubmoduleFintype : Fintype
    (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

/-- The canonical finite family of `k`-dimensional affine flats in the
binary cube. -/
noncomputable def binaryAffineFlats (k n : ℕ) :
    Finset (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact Finset.univ.filter fun A ↦
    A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = k

/-- The canonical finite family of `k`-dimensional linear subspaces in the
binary cube. -/
noncomputable def binaryLinearSubspaces (k n : ℕ) :
    Finset (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
  classical
  exact Finset.univ.filter fun H ↦ Module.finrank FABL.𝔽₂ H = k

@[simp] theorem mem_binaryLinearSubspaces
    {k : ℕ}
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    H ∈ binaryLinearSubspaces k n ↔ Module.finrank FABL.𝔽₂ H = k := by
  classical
  simp [binaryLinearSubspaces]

theorem binaryAffineSubspace_mem_binaryAffineFlats
    {k : ℕ}
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (u : FABL.F₂Cube n) (hH : H ∈ binaryLinearSubspaces k n) :
    FABL.binaryAffineSubspace H u ∈ binaryAffineFlats k n := by
  simp only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hbot
    have hu : u ∈ (⊥ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
      rw [← hbot]
      exact AffineSubspace.self_mem_mk' _ _
    rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hu
    exact hu
  · rw [FABL.binaryAffineSubspace_direction]
    exact (mem_binaryLinearSubspaces H).mp hH

/-- The Boolean indicator of a Mathlib affine subspace. -/
noncomputable def binaryAffineFlatIndicator
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    BooleanFunction n := by
  classical
  exact fun x ↦ if x ∈ A then 1 else 0

/-- The finite point set of an affine flat. -/
noncomputable def binaryAffineFlatPoints
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    Finset (FABL.F₂Cube n) := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ A

@[simp] theorem mem_binaryAffineFlatPoints
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (x : FABL.F₂Cube n) :
    x ∈ binaryAffineFlatPoints A ↔ x ∈ A := by
  classical
  simp [binaryAffineFlatPoints]

@[simp] theorem binaryAffineFlatIndicator_apply_eq_one_iff
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (x : FABL.F₂Cube n) :
    binaryAffineFlatIndicator A x = 1 ↔ x ∈ A := by
  classical
  simp [binaryAffineFlatIndicator]

theorem binaryAffineFlatIndicator_eq_affineFlatIndicator
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) (ha : a ∈ A) :
    binaryAffineFlatIndicator A = affineFlatIndicator A.direction a := by
  classical
  have hflat : FABL.binaryAffineSubspace A.direction a = A := by
    exact AffineSubspace.mk'_eq ha
  funext x
  simp only [binaryAffineFlatIndicator, affineFlatIndicator]
  rw [hflat]

/-- The indicator of a binary `k`-flat belongs to the Reed--Muller code of
complementary order. -/
theorem binaryAffineFlatIndicator_mem_reedMuller
    {k : ℕ}
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ∈ binaryAffineFlats k n) :
    binaryAffineFlatIndicator A ∈ reedMuller (n - k) n := by
  have hAdata : A ≠ ⊥ ∧ Module.finrank FABL.𝔽₂ A.direction = k := by
    simpa only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and] using hA
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hAdata.1
  have hdegree : FABL.functionAlgebraicDegree
      (binaryAffineFlatIndicator A) = n - k := by
    rw [binaryAffineFlatIndicator_eq_affineFlatIndicator A a ha,
      functionAlgebraicDegree_affineFlatIndicator, FABL.f₂Codimension,
      FABL.finrank_perpendicularSubspace, hAdata.2]
  simpa only [mem_reedMuller_iff] using hdegree.le

/-- A nonempty `k`-flat has exactly `2^k` points. -/
theorem hammingWeight_binaryAffineFlatIndicator
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ≠ ⊥) :
    hammingWeight (binaryAffineFlatIndicator A) =
      2 ^ Module.finrank FABL.𝔽₂ A.direction := by
  obtain ⟨a, ha⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hA
  rw [binaryAffineFlatIndicator_eq_affineFlatIndicator A a ha,
    hammingWeight_affineFlatIndicator]

theorem card_binaryAffineFlatPoints
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hA : A ≠ ⊥) :
    (binaryAffineFlatPoints A).card =
      2 ^ Module.finrank FABL.𝔽₂ A.direction := by
  rw [← hammingWeight_binaryAffineFlatIndicator A hA,
    hammingWeight_eq_card_support]
  congr 1
  ext x
  simp [binaryAffineFlatPoints, binaryAffineFlatIndicator]

theorem support_binaryAffineFlatIndicator
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    support (binaryAffineFlatIndicator A) = binaryAffineFlatPoints A := by
  ext x
  simp [support, FABL.f₂OneSupport, binaryAffineFlatIndicator,
    binaryAffineFlatPoints]

/-- Binary addition removes twice the common support from the sum of the
two Hamming weights. -/
theorem hammingWeight_add_add_two_mul_card_support_inter
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
  intro x _hx
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · norm_num [hfx, hgx]
    · have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfx, hgxOne]
  · have hfxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hfx
    by_cases hgx : g x = 0
    · norm_num [hfxOne, hgx]
    · have hgxOne : g x = 1 := Fin.eq_one_of_ne_zero _ hgx
      norm_num [hfxOne, hgxOne]

/-- Indicators distinguish nonempty affine subspaces. -/
theorem binaryAffineFlatIndicator_injective_on_nonempty :
    Set.InjOn
      (binaryAffineFlatIndicator (n := n))
      {A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) | A ≠ ⊥} := by
  intro A hA B hB hindicator
  ext x
  have hx := congrFun hindicator x
  simpa only [binaryAffineFlatIndicator_apply_eq_one_iff] using
    (show binaryAffineFlatIndicator A x = 1 ↔
        binaryAffineFlatIndicator B x = 1 by rw [hx])

/-- The character attached to an affine flat and a Boolean function. -/
noncomputable def binaryAffineFlatCharacter
    (f : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) : ℝ :=
  FABL.binarySign
    (booleanFunctionPairing n f (binaryAffineFlatIndicator A))

/-- The character of the affine coset `u + H`. -/
noncomputable def binaryAffineCosetCharacter
    (f : BooleanFunction n) (u : FABL.F₂Cube n)
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : ℝ :=
  binaryAffineFlatCharacter f (FABL.binaryAffineSubspace H u)

/-- The canonical character sum over the `k`-dimensional affine flats. -/
noncomputable def binaryAffineFlatCharacterSum
    (k : ℕ) (f : BooleanFunction n) : ℝ :=
  ∑ A ∈ binaryAffineFlats k n, binaryAffineFlatCharacter f A

/-- The indicator of a disjoint union is the binary sum of its indicators. -/
theorem binaryAffineFlatIndicator_eq_add_of_points_eq_union
    (A B C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hpoints : binaryAffineFlatPoints C =
      binaryAffineFlatPoints A ∪ binaryAffineFlatPoints B)
    (hdisjoint : Disjoint (binaryAffineFlatPoints A)
      (binaryAffineFlatPoints B)) :
    binaryAffineFlatIndicator C =
      binaryAffineFlatIndicator A + binaryAffineFlatIndicator B := by
  funext x
  have hmem : x ∈ C ↔ x ∈ A ∨ x ∈ B := by
    have hx := Finset.ext_iff.mp hpoints x
    simpa only [mem_binaryAffineFlatPoints, Finset.mem_union] using hx
  have hnotBoth : ¬ (x ∈ A ∧ x ∈ B) := by
    intro hboth
    exact (Finset.disjoint_left.mp hdisjoint)
      (by simpa only [mem_binaryAffineFlatPoints] using hboth.1)
      (by simpa only [mem_binaryAffineFlatPoints] using hboth.2)
  simp only [binaryAffineFlatIndicator, Pi.add_apply]
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
  · exact (hnotBoth ⟨hxA, hxB⟩).elim
  · simp [hxA, hxB, hmem]
  · simp [hxA, hxB, hmem]
  · simp [hxA, hxB, hmem]

/-- For disjoint affine flats, an indicator decomposition recovers the
corresponding disjoint union of point sets. -/
theorem binaryAffineFlatPoints_eq_union_of_indicator_eq_add
    (A B C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hdisjoint : Disjoint (binaryAffineFlatPoints A)
      (binaryAffineFlatPoints B))
    (hindicator : binaryAffineFlatIndicator C =
      binaryAffineFlatIndicator A + binaryAffineFlatIndicator B) :
    binaryAffineFlatPoints C =
      binaryAffineFlatPoints A ∪ binaryAffineFlatPoints B := by
  classical
  ext x
  simp only [mem_binaryAffineFlatPoints, Finset.mem_union]
  have happ := congrFun hindicator x
  have hnotBoth : ¬(x ∈ A ∧ x ∈ B) := by
    intro hboth
    exact (Finset.disjoint_left.mp hdisjoint)
      (by simpa only [mem_binaryAffineFlatPoints] using hboth.1)
      (by simpa only [mem_binaryAffineFlatPoints] using hboth.2)
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
  · exact (hnotBoth ⟨hxA, hxB⟩).elim
  · have hC : x ∈ C := by
      apply (binaryAffineFlatIndicator_apply_eq_one_iff C x).mp
      rw [hindicator, Pi.add_apply]
      simp [binaryAffineFlatIndicator, hxA, hxB]
    simp [hC, hxA, hxB]
  · have hC : x ∈ C := by
      apply (binaryAffineFlatIndicator_apply_eq_one_iff C x).mp
      rw [hindicator, Pi.add_apply]
      simp [binaryAffineFlatIndicator, hxA, hxB]
    simp [hC, hxA, hxB]
  · have hC : x ∉ C := by
      intro hxC
      have hCOne :=
        (binaryAffineFlatIndicator_apply_eq_one_iff C x).2 hxC
      rw [hindicator, Pi.add_apply] at hCOne
      simp [binaryAffineFlatIndicator, hxA, hxB] at hCOne
    simp [hC, hxA, hxB]

/-- A linear subspace contained in the union of two linear subspaces is
contained in one of them. -/
theorem submodule_le_left_or_right_of_subset_union
    (A B C : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hsubset : ∀ x ∈ A, x ∈ B ∨ x ∈ C) :
    A ≤ B ∨ A ≤ C := by
  by_contra hneither
  have hnotAB : ¬ A ≤ B := fun hAB ↦ hneither (Or.inl hAB)
  have hnotAC : ¬ A ≤ C := fun hAC ↦ hneither (Or.inr hAC)
  obtain ⟨x, hxA, hxB⟩ := SetLike.not_le_iff_exists.mp hnotAB
  obtain ⟨y, hyA, hyC⟩ := SetLike.not_le_iff_exists.mp hnotAC
  have hxC : x ∈ C := (hsubset x hxA).resolve_left hxB
  have hyB : y ∈ B := (hsubset y hyA).resolve_right hyC
  have hxyA : x + y ∈ A := A.add_mem hxA hyA
  rcases hsubset (x + y) hxyA with hxyB | hxyC
  · apply hxB
    have hsub := B.sub_mem hxyB hyB
    simpa only [add_sub_cancel_right] using hsub
  · apply hyC
    have hsub := C.sub_mem hxyC hxC
    simpa only [add_sub_cancel_left] using hsub

/-- Equal unions of two distinct equidimensional linear subspaces determine
the same unordered pair. -/
theorem unordered_submodule_pair_eq_of_union_eq
    (A B C D : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hrankAC : Module.finrank FABL.𝔽₂ A = Module.finrank FABL.𝔽₂ C)
    (hrankAD : Module.finrank FABL.𝔽₂ A = Module.finrank FABL.𝔽₂ D)
    (hrankBC : Module.finrank FABL.𝔽₂ B = Module.finrank FABL.𝔽₂ C)
    (hrankBD : Module.finrank FABL.𝔽₂ B = Module.finrank FABL.𝔽₂ D)
    (hneAB : A ≠ B)
    (hunion : ∀ x, x ∈ A ∨ x ∈ B ↔ x ∈ C ∨ x ∈ D) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  have hAle : A ≤ C ∨ A ≤ D :=
    submodule_le_left_or_right_of_subset_union A C D
      (fun x hx ↦ (hunion x).mp (Or.inl hx))
  rcases hAle with hAC | hAD
  · left
    have hACeq : A = C :=
      Submodule.eq_of_le_of_finrank_eq hAC hrankAC
    have hBle : B ≤ C ∨ B ≤ D :=
      submodule_le_left_or_right_of_subset_union B C D
        (fun x hx ↦ (hunion x).mp (Or.inr hx))
    have hBD : B ≤ D := hBle.resolve_left (fun hBC ↦ by
      apply hneAB
      exact hACeq.trans
        (Submodule.eq_of_le_of_finrank_eq hBC hrankBC).symm)
    exact ⟨hACeq, Submodule.eq_of_le_of_finrank_eq hBD hrankBD⟩
  · right
    have hADeq : A = D :=
      Submodule.eq_of_le_of_finrank_eq hAD hrankAD
    have hBle : B ≤ C ∨ B ≤ D :=
      submodule_le_left_or_right_of_subset_union B C D
        (fun x hx ↦ (hunion x).mp (Or.inr hx))
    have hBC : B ≤ C := hBle.resolve_right (fun hBD ↦ by
      apply hneAB
      exact hADeq.trans
        (Submodule.eq_of_le_of_finrank_eq hBD hrankBD).symm)
    exact ⟨hADeq, Submodule.eq_of_le_of_finrank_eq hBC hrankBC⟩

/-- Characters turn a binary disjoint-support sum into multiplication. -/
theorem binaryAffineFlatCharacter_eq_mul_of_indicator_eq_add
    (f : BooleanFunction n)
    (A B C : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n))
    (hindicator : binaryAffineFlatIndicator C =
      binaryAffineFlatIndicator A + binaryAffineFlatIndicator B) :
    binaryAffineFlatCharacter f C =
      binaryAffineFlatCharacter f A * binaryAffineFlatCharacter f B := by
  rw [binaryAffineFlatCharacter, hindicator, map_add, AddChar.map_add_eq_mul]
  rfl

/-- Every affine-flat character has square one. -/
@[simp] theorem sq_binaryAffineFlatCharacter
    (f : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineFlatCharacter f A ^ 2 = 1 := by
  unfold binaryAffineFlatCharacter
  by_cases hzero : booleanFunctionPairing n f
      (binaryAffineFlatIndicator A) = 0
  · rw [hzero]
    norm_num
  · have hone : booleanFunctionPairing n f
        (binaryAffineFlatIndicator A) = 1 := Fin.eq_one_of_ne_zero _ hzero
    rw [hone]
    rw [FABL.binarySign_one]
    norm_num

theorem binaryAffineFlatCharacter_eq_one_or_neg_one
    (f : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineFlatCharacter f A = 1 ∨
      binaryAffineFlatCharacter f A = -1 := by
  unfold binaryAffineFlatCharacter
  by_cases hzero : booleanFunctionPairing n f
      (binaryAffineFlatIndicator A) = 0
  · left
    rw [hzero]
    exact AddChar.map_zero_eq_one FABL.binarySign
  · right
    have hone : booleanFunctionPairing n f
        (binaryAffineFlatIndicator A) = 1 := Fin.eq_one_of_ne_zero _ hzero
    rw [hone, FABL.binarySign_one]

theorem neg_one_le_binaryAffineFlatCharacter
    (f : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    -1 ≤ binaryAffineFlatCharacter f A := by
  rcases binaryAffineFlatCharacter_eq_one_or_neg_one f A with h | h
  · rw [h]
    norm_num
  · rw [h]

theorem binaryAffineFlatCharacter_le_one
    (f : BooleanFunction n)
    (A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineFlatCharacter f A ≤ 1 := by
  rcases binaryAffineFlatCharacter_eq_one_or_neg_one f A with h | h
  · rw [h]
  · rw [h]
    norm_num

theorem binaryAffineCosetCharacter_mul_le_one
    (f : BooleanFunction n) (u : FABL.F₂Cube n)
    (H K : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    binaryAffineCosetCharacter f u H *
      binaryAffineCosetCharacter f u K ≤ 1 := by
  rcases binaryAffineFlatCharacter_eq_one_or_neg_one f
      (FABL.binaryAffineSubspace H u) with hH | hH <;>
    rcases binaryAffineFlatCharacter_eq_one_or_neg_one f
      (FABL.binaryAffineSubspace K u) with hK | hK <;>
    simp only [binaryAffineCosetCharacter, hH, hK] <;> norm_num

end CryptBoolean
