/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.ReedMullerCosetDistance
public import CryptBoolean.Carlet.Chapter06.Bentness

/-!
# Carlet Chapter 6 Kerdock-code parameters

The code parameters obtained from a finite family of quadratic representatives
whose pairwise sums are bent. The finite-field construction of such a family
is a separate existence problem.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The source conditions on a finite family of Kerdock coset representatives:
zero is represented, every nonzero representative is quadratic, distinct
representatives have bent sum, and the family has `2^(n-1)` members. -/
def IsKerdockRepresentativeFamily
    (F : Finset (BooleanFunction n)) : Prop :=
  (0 : BooleanFunction n) ∈ F ∧
    (∀ f ∈ F, f ≠ 0 → FABL.functionAlgebraicDegree f = 2) ∧
    (∀ ⦃f⦄, f ∈ F → ∀ ⦃g⦄, g ∈ F → f ≠ g → IsBent (f + g)) ∧
    F.card = 2 ^ (n - 1)

/-- The union of first-order Reed--Muller cosets determined by a finite
Kerdock representative family. -/
noncomputable def kerdockCodeOfRepresentatives
    (F : Finset (BooleanFunction n)) : Finset (BooleanFunction n) :=
  firstOrderCosetUnion F

/-- Every representative in a Kerdock family has algebraic degree at most
two, including the zero representative. -/
theorem functionAlgebraicDegree_le_two_of_mem_kerdockRepresentatives
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F)
    {f : BooleanFunction n} (hf : f ∈ F) :
    FABL.functionAlgebraicDegree f ≤ 2 := by
  by_cases hfZero : f = 0
  · subst f
    simp
  · exact (hF.2.1 f hf hfZero).le

/-- The Kerdock coset union contains the first-order Reed--Muller code. -/
theorem reedMuller_one_subset_kerdockCodeOfRepresentatives
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F) :
    ∀ ⦃c : BooleanFunction n⦄, c ∈ reedMuller 1 n →
      c ∈ kerdockCodeOfRepresentatives F := by
  intro c hc
  rw [kerdockCodeOfRepresentatives, mem_firstOrderCosetUnion_iff]
  refine ⟨0, hF.1, ?_⟩
  simpa using hc

/-- The Kerdock coset union is contained in the second-order Reed--Muller
code. -/
theorem kerdockCodeOfRepresentatives_subset_reedMuller_two
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F) :
    ∀ ⦃c : BooleanFunction n⦄,
      c ∈ kerdockCodeOfRepresentatives F → c ∈ reedMuller 2 n := by
  intro c hc
  rw [kerdockCodeOfRepresentatives, mem_firstOrderCosetUnion_iff] at hc
  obtain ⟨f, hf, hcf⟩ := hc
  have hcfTwo : c + f ∈ reedMuller 2 n :=
    reedMuller_mono (n := n) (by omega) hcf
  have hfTwo : f ∈ reedMuller 2 n :=
    functionAlgebraicDegree_le_two_of_mem_kerdockRepresentatives hF hf
  have hsum := (reedMuller 2 n).add_mem hcfTwo hfTwo
  have hcancel : (c + f) + f = c := by
    funext x
    exact CharTwo.add_cancel_right _ _
  rwa [hcancel] at hsum

/-- Distinct representatives in a Kerdock family have the exact bent
nonlinearity value. -/
theorem nonlinearity_add_eq_kerdockDistance_of_mem
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F) (hn : 2 ≤ n)
    {f g : BooleanFunction n} (hf : f ∈ F) (hg : g ∈ F)
    (hfg : f ≠ g) :
    nonlinearity (f + g) =
      2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  exact nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent
    (f + g) (hF.2.2.1 hf hg hfg) hn

/-- In dimension at least two, bent pairwise sums force distinct Kerdock
representatives to determine distinct first-order Reed--Muller cosets. -/
theorem hasDistinctFirstOrderCosets_of_isKerdockRepresentativeFamily
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F)
    (hnEven : Even n) (hn : 2 ≤ n) :
    HasDistinctFirstOrderCosets F := by
  intro f hf g hg hfg hmem
  obtain ⟨b, a, haffine⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (f + g) hmem
  have hzero : nonlinearity (f + g) = 0 := by
    rw [haffine, nonlinearity_affineFunction]
  have hexact :=
    nonlinearity_add_eq_kerdockDistance_of_mem hF hn hf hg hfg
  have hexponents : n / 2 - 1 < n - 1 := by
    rcases hnEven with ⟨k, rfl⟩
    omega
  have hpowers : 2 ^ (n / 2 - 1) < 2 ^ (n - 1) :=
    Nat.pow_lt_pow_right (by omega) hexponents
  rw [hzero] at hexact
  omega

/-- A Kerdock representative family in dimension at least two contains two
distinct representatives. -/
theorem kerdockRepresentativeFamily_offDiag_nonempty
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F) (hn : 2 ≤ n) :
    F.offDiag.Nonempty := by
  have htwo : 2 ≤ F.card := by
    rw [hF.2.2.2]
    have hexponent : 1 ≤ n - 1 := by omega
    simpa using
      (Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hexponent)
  obtain ⟨f, hf, g, hg, hfg⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  exact ⟨(f, g), Finset.mem_offDiag.mpr ⟨hf, hg, hfg⟩⟩

/-- A Kerdock coset union has `2^(2n)` codewords in dimension at least two. -/
theorem card_kerdockCodeOfRepresentatives
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F)
    (hnEven : Even n) (hn : 2 ≤ n) :
    (kerdockCodeOfRepresentatives F).card = 2 ^ (2 * n) := by
  rw [kerdockCodeOfRepresentatives,
    card_firstOrderCosetUnion
      (hasDistinctFirstOrderCosets_of_isKerdockRepresentativeFamily
        hF hnEven hn),
    hF.2.2.2, reedMuller_card]
  have hsum :
      (∑ j ∈ Finset.range (1 + 1), Nat.choose n j) = n + 1 := by
    norm_num [Finset.sum_range_succ, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.add_comm]
  rw [hsum, ← pow_add]
  congr 1
  omega

/-- The minimum pair nonlinearity of a Kerdock representative family is the
bent nonlinearity value. -/
theorem minimumPairNonlinearity_eq_kerdockDistance
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F) (hn : 2 ≤ n) :
    minimumPairNonlinearity F =
      2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  have hnonempty := kerdockRepresentativeFamily_offDiag_nonempty hF hn
  obtain ⟨p, hp⟩ := hnonempty
  have hnonempty' : F.offDiag.Nonempty := ⟨p, hp⟩
  have hpMem := Finset.mem_offDiag.mp hp
  apply le_antisymm
  · calc
      minimumPairNonlinearity F ≤ nonlinearity (p.1 + p.2) :=
        minimumPairNonlinearity_le hnonempty' hpMem.1 hpMem.2.1 hpMem.2.2
      _ = 2 ^ (n - 1) - 2 ^ (n / 2 - 1) :=
        nonlinearity_add_eq_kerdockDistance_of_mem
          hF hn hpMem.1 hpMem.2.1 hpMem.2.2
  · apply le_minimumPairNonlinearity hnonempty'
    intro f hf g hg hfg
    rw [nonlinearity_add_eq_kerdockDistance_of_mem hF hn hf hg hfg]

/-- The minimum distance of a Kerdock coset union is
`2^(n-1) - 2^(n/2-1)`. -/
theorem minimumHammingDistance_kerdockCodeOfRepresentatives
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F)
    (hnEven : Even n) (hn : 2 ≤ n) :
    minimumHammingDistance (kerdockCodeOfRepresentatives F) =
      2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  rw [kerdockCodeOfRepresentatives,
    minimumHammingDistance_firstOrderCosetUnion
      (kerdockRepresentativeFamily_offDiag_nonempty hF hn)
      (hasDistinctFirstOrderCosets_of_isKerdockRepresentativeFamily
        hF hnEven hn),
    minimumPairNonlinearity_eq_kerdockDistance hF hn]

/-- The Kerdock parameters determined by a finite quadratic representative
family in positive even dimension. -/
theorem kerdockCodeOfRepresentatives_parameters
    {F : Finset (BooleanFunction n)}
    (hF : IsKerdockRepresentativeFamily F)
    (hnEven : Even n) (hn : 2 ≤ n) :
    F.offDiag.Nonempty ∧
      HasDistinctFirstOrderCosets F ∧
      (∀ ⦃c : BooleanFunction n⦄, c ∈ reedMuller 1 n →
        c ∈ kerdockCodeOfRepresentatives F) ∧
      (∀ ⦃c : BooleanFunction n⦄,
        c ∈ kerdockCodeOfRepresentatives F → c ∈ reedMuller 2 n) ∧
      (kerdockCodeOfRepresentatives F).card = 2 ^ (2 * n) ∧
      minimumHammingDistance (kerdockCodeOfRepresentatives F) =
        2 ^ (n - 1) - 2 ^ (n / 2 - 1) := by
  exact ⟨kerdockRepresentativeFamily_offDiag_nonempty hF hn,
    hasDistinctFirstOrderCosets_of_isKerdockRepresentativeFamily
      hF hnEven hn,
    reedMuller_one_subset_kerdockCodeOfRepresentatives hF,
    kerdockCodeOfRepresentatives_subset_reedMuller_two hF,
    card_kerdockCodeOfRepresentatives hF hnEven hn,
    minimumHammingDistance_kerdockCodeOfRepresentatives hF hnEven hn⟩

end CryptBoolean
