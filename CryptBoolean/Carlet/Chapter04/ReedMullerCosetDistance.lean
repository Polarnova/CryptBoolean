/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity

/-!
# Distances of unions of first-order Reed--Muller cosets

The corrected finite-family form of Carlet's distance identity, with the
necessary hypothesis that distinct representatives define distinct cosets.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The minimum Hamming distance between distinct functions in a finite code,
with value zero for a code having fewer than two words. -/
noncomputable def minimumHammingDistance
    (C : Finset (BooleanFunction n)) : ℕ :=
  if hC : C.offDiag.Nonempty then
    C.offDiag.inf' hC fun p ↦ hammingDistance p.1 p.2
  else 0

/-- The union of the first-order Reed--Muller cosets represented by `F`. -/
noncomputable def firstOrderCosetUnion
    (F : Finset (BooleanFunction n)) : Finset (BooleanFunction n) :=
  by
    classical
    exact Finset.univ.filter fun c ↦ ∃ f ∈ F, c + f ∈ reedMuller 1 n

/-- The first-order Reed--Muller coset represented by `f`, as a finite code. -/
noncomputable def firstOrderReedMullerCoset
    (f : BooleanFunction n) : Finset (BooleanFunction n) :=
  by
    classical
    exact Finset.univ.filter fun c ↦ c + f ∈ reedMuller 1 n

/-- Distinct members of `F` represent distinct first-order Reed--Muller cosets. -/
def HasDistinctFirstOrderCosets
    (F : Finset (BooleanFunction n)) : Prop :=
  ∀ ⦃f⦄, f ∈ F → ∀ ⦃g⦄, g ∈ F → f ≠ g →
    f + g ∉ reedMuller 1 n

/-- The minimum nonlinearity of a sum of two distinct representatives, with
value zero for a family having fewer than two representatives. -/
noncomputable def minimumPairNonlinearity
    (F : Finset (BooleanFunction n)) : ℕ :=
  if hF : F.offDiag.Nonempty then
    F.offDiag.inf' hF fun p ↦ nonlinearity (p.1 + p.2)
  else 0

@[simp] theorem mem_firstOrderCosetUnion_iff
    {F : Finset (BooleanFunction n)} {c : BooleanFunction n} :
    c ∈ firstOrderCosetUnion F ↔
      ∃ f ∈ F, c + f ∈ reedMuller 1 n := by
  classical
  simp [firstOrderCosetUnion]

@[simp] theorem mem_firstOrderReedMullerCoset_iff
    {f c : BooleanFunction n} :
    c ∈ firstOrderReedMullerCoset f ↔ c + f ∈ reedMuller 1 n := by
  classical
  simp [firstOrderReedMullerCoset]

/-- A two-representative union is the union of the corresponding two cosets. -/
theorem firstOrderCosetUnion_pair
    (f g : BooleanFunction n) :
    firstOrderCosetUnion {f, g} =
      firstOrderReedMullerCoset f ∪ firstOrderReedMullerCoset g := by
  classical
  ext c
  simp

theorem minimumHammingDistance_le
    {C : Finset (BooleanFunction n)} (hC : C.offDiag.Nonempty)
    {f g : BooleanFunction n} (hf : f ∈ C) (hg : g ∈ C) (hfg : f ≠ g) :
    minimumHammingDistance C ≤ hammingDistance f g := by
  classical
  rw [minimumHammingDistance, dif_pos hC]
  have hp : (f, g) ∈ C.offDiag := by simp [hf, hg, hfg]
  exact Finset.inf'_le _ hp

theorem le_minimumHammingDistance
    {C : Finset (BooleanFunction n)} (hC : C.offDiag.Nonempty) {d : ℕ}
    (h : ∀ ⦃f⦄, f ∈ C → ∀ ⦃g⦄, g ∈ C → f ≠ g →
      d ≤ hammingDistance f g) :
    d ≤ minimumHammingDistance C := by
  classical
  rw [minimumHammingDistance, dif_pos hC]
  apply Finset.le_inf'
  intro p hp
  exact h (Finset.mem_offDiag.mp hp).1
    (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2

theorem minimumPairNonlinearity_le
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty)
    {f g : BooleanFunction n} (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g) :
    minimumPairNonlinearity F ≤ nonlinearity (f + g) := by
  classical
  rw [minimumPairNonlinearity, dif_pos hF]
  have hp : (f, g) ∈ F.offDiag := by simp [hf, hg, hfg]
  exact Finset.inf'_le _ hp

theorem le_minimumPairNonlinearity
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty) {d : ℕ}
    (h : ∀ ⦃f⦄, f ∈ F → ∀ ⦃g⦄, g ∈ F → f ≠ g →
      d ≤ nonlinearity (f + g)) :
    d ≤ minimumPairNonlinearity F := by
  classical
  rw [minimumPairNonlinearity, dif_pos hF]
  apply Finset.le_inf'
  intro p hp
  exact h (Finset.mem_offDiag.mp hp).1
    (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2

/-- Adding the same Boolean function to both endpoints preserves Hamming distance. -/
theorem hammingDistance_add_right
    (f g h : BooleanFunction n) :
    hammingDistance (f + h) (g + h) = hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add,
    hammingDistance_eq_hammingWeight_add]
  congr 1
  funext x
  simp only [Pi.add_apply]
  calc
    (f x + h x) + (g x + h x) =
        (f x + g x) + (h x + h x) := by ac_rfl
    _ = f x + g x := by rw [CharTwo.add_self_eq_zero, add_zero]

/-- Distances between two coset words are distances from the sum of their
representatives to a first-order Reed--Muller word. -/
theorem hammingDistance_eq_cosetDifference
    (c d f g : BooleanFunction n) :
    hammingDistance c d =
      hammingDistance (f + g) ((c + f) + (d + g)) := by
  rw [hammingDistance_eq_hammingWeight_add,
    hammingDistance_eq_hammingWeight_add]
  congr 1
  funext x
  simp only [Pi.add_apply]
  symm
  calc
    (f x + g x) + ((c x + f x) + (d x + g x)) =
        (c x + d x) + (f x + f x) + (g x + g x) := by ac_rfl
    _ = c x + d x := by
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
      simp

/-- The representative-sum nonlinearity lower-bounds every distance between
the corresponding first-order Reed--Muller cosets. -/
theorem nonlinearity_le_hammingDistance_of_mem_cosets
    {c d f g : BooleanFunction n}
    (hc : c + f ∈ reedMuller 1 n) (hd : d + g ∈ reedMuller 1 n) :
    nonlinearity (f + g) ≤ hammingDistance c d := by
  rw [nonlinearity_eq_higherOrderNonlinearity_one]
  calc
    higherOrderNonlinearity 1 (f + g) ≤
        hammingDistance (f + g) ((c + f) + (d + g)) :=
      higherOrderNonlinearity_le_hammingDistance 1 (f + g)
        ((c + f) + (d + g)) ((reedMuller 1 n).add_mem hc hd)
    _ = hammingDistance c d :=
      (hammingDistance_eq_cosetDifference c d f g).symm

/-- Ordinary nonlinearity never exceeds half the cube size in positive dimension. -/
theorem nonlinearity_le_two_pow_sub_one
    (hn : 0 < n) (f : BooleanFunction n) :
    nonlinearity f ≤ 2 ^ (n - 1) := by
  have h := two_mul_higherOrderNonlinearity_le_two_pow 1 (by omega) f
  rw [← nonlinearity_eq_higherOrderNonlinearity_one] at h
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at h
  omega

/-- A nontrivial finite representative family has a pair attaining its minimum
pair nonlinearity. -/
theorem exists_pair_nonlinearity_eq_minimumPairNonlinearity
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty) :
    ∃ f ∈ F, ∃ g ∈ F, f ≠ g ∧
      nonlinearity (f + g) = minimumPairNonlinearity F := by
  classical
  obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' hF
    (fun p : BooleanFunction n × BooleanFunction n ↦
      nonlinearity (p.1 + p.2))
  have hmem := Finset.mem_offDiag.mp hp
  refine ⟨p.1, hmem.1, p.2, hmem.2.1, hmem.2.2, ?_⟩
  rw [minimumPairNonlinearity, dif_pos hF]
  exact hmin.symm

/-- A nontrivial family of representatives yields at least two words in its
union of first-order Reed--Muller cosets. -/
theorem firstOrderCosetUnion_offDiag_nonempty
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty) :
    (firstOrderCosetUnion F).offDiag.Nonempty := by
  classical
  obtain ⟨p, hp⟩ := hF
  have hmem := Finset.mem_offDiag.mp hp
  refine ⟨(p.1, p.2), Finset.mem_offDiag.mpr ⟨?_, ?_, hmem.2.2⟩⟩
  · rw [mem_firstOrderCosetUnion_iff]
    have hzero : p.1 + p.1 = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero _
    exact ⟨p.1, hmem.1, by rw [hzero]; exact (reedMuller 1 n).zero_mem⟩
  · rw [mem_firstOrderCosetUnion_iff]
    have hzero : p.2 + p.2 = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero _
    exact ⟨p.2, hmem.2.1, by rw [hzero]; exact (reedMuller 1 n).zero_mem⟩

/-- Distinct first-order Reed--Muller cosets cannot occur in dimension zero. -/
theorem dimension_pos_of_hasDistinctFirstOrderCosets
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty)
    (hcosets : HasDistinctFirstOrderCosets F) :
    0 < n := by
  by_contra hn
  have hnzero : n = 0 := by omega
  obtain ⟨p, hp⟩ := hF
  have hmem := Finset.mem_offDiag.mp hp
  apply hcosets hmem.1 hmem.2.1 hmem.2.2
  rw [mem_reedMuller_iff]
  exact (FABL.functionAlgebraicDegree_le_dimension (p.1 + p.2)).trans
    (by omega)

/-- Distinct words in the same first-order Reed--Muller coset have distance at
least half the cube size. -/
theorem two_pow_sub_one_le_hammingDistance_of_mem_same_coset
    {c d f : BooleanFunction n}
    (hc : c + f ∈ reedMuller 1 n) (hd : d + f ∈ reedMuller 1 n)
    (hcd : c ≠ d) :
    2 ^ (n - 1) ≤ hammingDistance c d := by
  have haddne : c + f ≠ d + f := fun h ↦ hcd (add_right_cancel h)
  have hbound := reedMuller_one_distance_lower_bound hc hd haddne
  rwa [hammingDistance_add_right] at hbound

/-- The minimum pair nonlinearity of distinct coset representatives is at
most half the cube size. -/
theorem minimumPairNonlinearity_le_two_pow_sub_one
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty) (hn : 0 < n) :
    minimumPairNonlinearity F ≤ 2 ^ (n - 1) := by
  obtain ⟨f, hf, g, hg, hfg, _hmin⟩ :=
    exists_pair_nonlinearity_eq_minimumPairNonlinearity hF
  exact (minimumPairNonlinearity_le hF hf hg hfg).trans
    (nonlinearity_le_two_pow_sub_one hn (f + g))

/-- The corrected finite-family form of Carlet's Reed--Muller coset identity:
the cosets represented by distinct members of `F` must themselves be distinct. -/
theorem minimumHammingDistance_firstOrderCosetUnion
    {F : Finset (BooleanFunction n)} (hF : F.offDiag.Nonempty)
    (hcosets : HasDistinctFirstOrderCosets F) :
    minimumHammingDistance (firstOrderCosetUnion F) =
      minimumPairNonlinearity F := by
  classical
  have hC := firstOrderCosetUnion_offDiag_nonempty hF
  have hn := dimension_pos_of_hasDistinctFirstOrderCosets hF hcosets
  apply le_antisymm
  · obtain ⟨f, hf, g, hg, hfg, hpair⟩ :=
      exists_pair_nonlinearity_eq_minimumPairNonlinearity hF
    obtain ⟨ℓ, hℓ, hdist⟩ :=
      exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity 1 (f + g)
    have hzeroF : f + f = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero _
    have hzeroG : g + g = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero _
    have hfC : f ∈ firstOrderCosetUnion F := by
      rw [mem_firstOrderCosetUnion_iff]
      exact ⟨f, hf, by rw [hzeroF]; exact (reedMuller 1 n).zero_mem⟩
    have hgℓC : g + ℓ ∈ firstOrderCosetUnion F := by
      rw [mem_firstOrderCosetUnion_iff]
      refine ⟨g, hg, ?_⟩
      have hcancel : (g + ℓ) + g = ℓ := by
        funext x
        calc
          (g x + ℓ x) + g x = g x + (g x + ℓ x) := by ac_rfl
          _ = ℓ x := CharTwo.add_cancel_left _ _
      rwa [hcancel]
    have hfgℓ : f ≠ g + ℓ := by
      intro heq
      apply hcosets hf hg hfg
      have hsum : f + g = ℓ := by
        calc
          f + g = (g + ℓ) + g := congrArg (fun h ↦ h + g) heq
          _ = ℓ := by
            funext x
            calc
              (g x + ℓ x) + g x = g x + (g x + ℓ x) := by ac_rfl
              _ = ℓ x := CharTwo.add_cancel_left _ _
      rwa [hsum]
    calc
      minimumHammingDistance (firstOrderCosetUnion F) ≤
          hammingDistance f (g + ℓ) :=
        minimumHammingDistance_le hC hfC hgℓC hfgℓ
      _ = hammingDistance (f + g) ℓ := by
        have htranslate := hammingDistance_add_right (f + g) ℓ g
        have hcancel : (f + g) + g = f := by
          funext x
          exact CharTwo.add_cancel_right _ _
        have hcomm : ℓ + g = g + ℓ := add_comm ℓ g
        rwa [hcancel, hcomm] at htranslate
      _ = higherOrderNonlinearity 1 (f + g) := hdist
      _ = nonlinearity (f + g) :=
        (nonlinearity_eq_higherOrderNonlinearity_one (f + g)).symm
      _ = minimumPairNonlinearity F := hpair
  · apply le_minimumHammingDistance hC
    intro c hc d hd hcd
    rw [mem_firstOrderCosetUnion_iff] at hc hd
    obtain ⟨f, hf, hcf⟩ := hc
    obtain ⟨g, hg, hdg⟩ := hd
    by_cases hfg : f = g
    · subst g
      exact (minimumPairNonlinearity_le_two_pow_sub_one hF hn).trans
        (two_pow_sub_one_le_hammingDistance_of_mem_same_coset hcf hdg hcd)
    · exact (minimumPairNonlinearity_le hF hf hg hfg).trans
        (nonlinearity_le_hammingDistance_of_mem_cosets hcf hdg)

/-- The pair `{0,f}` represents distinct first-order Reed--Muller cosets
exactly when `f` is not affine. -/
theorem hasDistinctFirstOrderCosets_pair_zero
    {f : BooleanFunction n} (hf : f ∉ reedMuller 1 n) :
    HasDistinctFirstOrderCosets ({0, f} : Finset (BooleanFunction n)) := by
  classical
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · simpa using hf
  · simpa [add_comm] using hf
  · exact (hab rfl).elim

/-- For a non-affine `f`, the only representative-pair nonlinearity of
`{0,f}` is the nonlinearity of `f`. -/
theorem minimumPairNonlinearity_pair_zero
    {f : BooleanFunction n} (hf : f ∉ reedMuller 1 n) :
    minimumPairNonlinearity ({0, f} : Finset (BooleanFunction n)) =
      nonlinearity f := by
  classical
  have hfzero : f ≠ 0 := by
    intro hzero
    apply hf
    rw [hzero]
    exact (reedMuller 1 n).zero_mem
  have hF : ({0, f} : Finset (BooleanFunction n)).offDiag.Nonempty := by
    refine ⟨(0, f), Finset.mem_offDiag.mpr ⟨by simp, by simp, ?_⟩⟩
    exact hfzero.symm
  apply le_antisymm
  · simpa using minimumPairNonlinearity_le hF
      (f := (0 : BooleanFunction n)) (g := f) (by simp) (by simp) hfzero.symm
  · apply le_minimumPairNonlinearity hF
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · simp
    · simp
    · exact (hab rfl).elim

/-- Corrected two-coset identity: if `f` is non-affine, its nonlinearity is
the minimum distance of `R(1,n) ∪ (f + R(1,n))`. -/
theorem minimumHammingDistance_two_firstOrderReedMullerCosets
    {f : BooleanFunction n} (hf : f ∉ reedMuller 1 n) :
    minimumHammingDistance
        (firstOrderReedMullerCoset 0 ∪ firstOrderReedMullerCoset f) =
      nonlinearity f := by
  classical
  have hfzero : f ≠ 0 := by
    intro hzero
    apply hf
    rw [hzero]
    exact (reedMuller 1 n).zero_mem
  have hF : ({0, f} : Finset (BooleanFunction n)).offDiag.Nonempty := by
    refine ⟨(0, f), Finset.mem_offDiag.mpr ⟨by simp, by simp, ?_⟩⟩
    exact hfzero.symm
  rw [← firstOrderCosetUnion_pair]
  exact (minimumHammingDistance_firstOrderCosetUnion hF
    (hasDistinctFirstOrderCosets_pair_zero hf)).trans
      (minimumPairNonlinearity_pair_zero hf)

end CryptBoolean
