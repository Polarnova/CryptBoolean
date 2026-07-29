/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMuller
public import CryptBoolean.Carlet.Chapter05.Affine
public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree

/-!
# The naive count of resilient functions

The highest-order classification and the Siegenthaler degree-count bound from
Carlet Chapter 7.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A highest-order resilient Boolean function is full parity or its
complement. -/
theorem exists_eq_affineFunction_fullFrequency_of_isResilient_natPred
    (f : BooleanFunction n) (hn : 0 < n)
    (hf : IsResilient (n - 1) f) :
    ∃ b : FABL.𝔽₂,
      f = FABL.affineFunction b
        (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin n))) := by
  obtain ⟨b, a, hfa⟩ :=
    exists_affineFunction_of_isResilient_natPred f hn hf
  have hwalshNonzero : walshTransform f a ≠ 0 := by
    rw [hfa, walshTransform_affineFunction, if_pos rfl]
    fin_cases b <;> simp [bitSignInt]
  have hwalshZero :=
    theorem_3_resilient_iff_walshTransform_eq_zero
      (n - 1) f hn (by omega) |>.mp hf
  have hweight : n ≤ (FABL.f₂Support a).card := by
    by_contra hnot
    have hle : (FABL.f₂Support a).card ≤ n - 1 := by omega
    exact hwalshNonzero (hwalshZero a hle)
  have hsupport : FABL.f₂Support a = Finset.univ := by
    have hcardLe : (FABL.f₂Support a).card ≤ n := by
      calc
        (FABL.f₂Support a).card ≤
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hcardEq : (FABL.f₂Support a).card = n :=
      le_antisymm hcardLe hweight
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin] using hcardEq
  refine ⟨b, hfa.trans ?_⟩
  congr 1
  apply (FABL.f₂CubeEquivFinset n).injective
  simpa [FABL.f₂CubeEquivFinset_apply, hsupport] using
    ((FABL.f₂CubeEquivFinset n).right_inv
      (Finset.univ : Finset (Fin n))).symm

private theorem natCard_highestOrderResilient_le_two
    (hn : 0 < n) :
    Nat.card {f : BooleanFunction n // IsResilient (n - 1) f} ≤ 2 := by
  let valueAtZero :
      {f : BooleanFunction n // IsResilient (n - 1) f} → FABL.𝔽₂ :=
    fun f ↦ f.1 0
  have hinjective : Function.Injective valueAtZero := by
    intro f g hvalue
    obtain ⟨b, hb⟩ :=
      exists_eq_affineFunction_fullFrequency_of_isResilient_natPred
        f.1 hn f.2
    obtain ⟨c, hc⟩ :=
      exists_eq_affineFunction_fullFrequency_of_isResilient_natPred
        g.1 hn g.2
    have hbc : b = c := by
      change f.1 0 = g.1 0 at hvalue
      rw [hb, hc] at hvalue
      simpa [FABL.affineFunction, FABL.f₂DotProduct] using hvalue
    apply Subtype.ext
    rw [hb, hc, hbc]
  have hcard :=
    Nat.card_le_card_of_injective valueAtZero hinjective
  simpa [Nat.card_eq_fintype_card] using hcard

/-- Carlet's naive upper bound on the number of `m`-resilient
`n`-variable Boolean functions. -/
theorem natCard_isResilient_le_naiveBound
    (m n : ℕ) (hm : m < n) :
    Nat.card {f : BooleanFunction n // IsResilient m f} ≤
      2 ^ (∑ i ∈ Finset.range (n - m - 1 + 1), Nat.choose n i) := by
  by_cases hbelow : m < n - 1
  · let toReedMuller :
        {f : BooleanFunction n // IsResilient m f} →
          reedMuller (n - m - 1) n :=
      fun f ↦
        ⟨f.1,
          functionAlgebraicDegree_le_sub_sub_one_of_isResilient
            f.1 m f.2 hbelow⟩
    have hinjective : Function.Injective toReedMuller := by
      intro f g hfg
      apply Subtype.ext
      exact congrArg
        (fun z : reedMuller (n - m - 1) n ↦ z.1) hfg
    calc
      Nat.card {f : BooleanFunction n // IsResilient m f} ≤
          Nat.card (reedMuller (n - m - 1) n) :=
        Nat.card_le_card_of_injective toReedMuller hinjective
      _ = 2 ^ (∑ i ∈ Finset.range (n - m - 1 + 1),
            Nat.choose n i) :=
        reedMuller_card
  · have hmPred : m = n - 1 := by omega
    subst m
    have hn : 0 < n := by omega
    calc
      Nat.card {f : BooleanFunction n // IsResilient (n - 1) f} ≤ 2 :=
        natCard_highestOrderResilient_le_two hn
      _ = 2 ^ (∑ i ∈ Finset.range (n - (n - 1) - 1 + 1),
            Nat.choose n i) := by
        have hnSub : n - (n - 1) = 1 := by omega
        rw [hnSub]
        simp

end CryptBoolean
