/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.CoveringConsequences

/-!
# Carlet Chapter 5 derivative spaces and partial covering sequences

Finite binary subspaces consisting of derivatives yield partial covering sequences.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance
    (D : Submodule FABL.𝔽₂ (BooleanFunction n)) : Fintype D :=
  Fintype.ofFinite D

/-- A nonzero binary subspace of Boolean functions whose elements are derivatives of `f`. -/
def IsDerivativeSpace (f : BooleanFunction n)
    (D : Submodule FABL.𝔽₂ (BooleanFunction n)) : Prop :=
  D ≠ ⊥ ∧ ∀ g : D, ∃ a : FABL.F₂Cube n,
    FABL.booleanDerivative f a = (g : BooleanFunction n)

/-- At a fixed point, the integer sum over a binary function subspace is either zero or
half the cardinality of the subspace. -/
theorem sum_bitValueInt_submodule_eq_zero_or_half
    (D : Submodule FABL.𝔽₂ (BooleanFunction n)) (x : FABL.F₂Cube n) :
    (∑ g : D, bitValueInt (g.1 x)) = 0 ∨
      (∑ g : D, bitValueInt (g.1 x)) = ((Nat.card D / 2 : ℕ) : ℤ) := by
  classical
  by_cases heval : ∀ g : D, g.1 x = 0
  · left
    simp [bitValueInt, heval]
  · right
    push Not at heval
    obtain ⟨h, hh⟩ := heval
    have hhOne : h.1 x = 1 := Fin.eq_one_of_ne_zero _ hh
    let valueSum : ℤ := ∑ g : D, bitValueInt (g.1 x)
    have htranslate :
        (∑ g : D, bitValueInt ((g + h).1 x)) = valueSum := by
      dsimp [valueSum]
      exact Equiv.sum_comp (Equiv.addRight h) (fun g : D ↦ bitValueInt (g.1 x))
    have hpair (g : D) :
        bitValueInt (g.1 x) + bitValueInt ((g + h).1 x) = 1 := by
      change bitValueInt (g.1 x) + bitValueInt (g.1 x + h.1 x) = 1
      rw [hhOne]
      by_cases hg : g.1 x = 0
      · simp [bitValueInt, hg]
      · have hgOne : g.1 x = 1 := Fin.eq_one_of_ne_zero _ hg
        simp [bitValueInt, hgOne]
    have hdouble : 2 * valueSum = (Nat.card D : ℤ) := by
      calc
        2 * valueSum = valueSum + valueSum := by ring
        _ = (∑ g : D, bitValueInt (g.1 x)) +
            ∑ g : D, bitValueInt ((g + h).1 x) := by rw [htranslate]
        _ = ∑ g : D,
            (bitValueInt (g.1 x) + bitValueInt ((g + h).1 x)) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ _g : D, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro g _hg
          exact hpair g
        _ = (Nat.card D : ℤ) := by
          rw [Nat.card_eq_fintype_card]
          simp
    dsimp [valueSum] at hdouble ⊢
    omega

/-- A chosen direction representing a prescribed derivative in a derivative space. -/
noncomputable def derivativeDirectionRepresentative
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) (g : D) : FABL.F₂Cube n :=
  Classical.choose (hD.2 g)

@[simp] theorem booleanDerivative_derivativeDirectionRepresentative
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) (g : D) :
    FABL.booleanDerivative f (derivativeDirectionRepresentative f D hD g) =
      (g : BooleanFunction n) :=
  Classical.choose_spec (hD.2 g)

/-- Distinct derivatives receive distinct representative directions. -/
theorem derivativeDirectionRepresentative_injective
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) :
    Function.Injective (derivativeDirectionRepresentative f D hD) := by
  intro g h hrepresentative
  apply Subtype.ext
  rw [← booleanDerivative_derivativeDirectionRepresentative f D hD g,
    ← booleanDerivative_derivativeDirectionRepresentative f D hD h,
    hrepresentative]

/-- One chosen direction for every derivative in `D`. -/
noncomputable def derivativeRepresentativeDirections
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) : Finset (FABL.F₂Cube n) :=
  Finset.univ.image (derivativeDirectionRepresentative f D hD)

/-- The representative direction set has exactly one element for every member of `D`. -/
theorem card_derivativeRepresentativeDirections
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) :
    (derivativeRepresentativeDirections f D hD).card = Nat.card D := by
  rw [derivativeRepresentativeDirections,
    Finset.card_image_of_injective _
      (derivativeDirectionRepresentative_injective f D hD),
    Finset.card_univ, Nat.card_eq_fintype_card]

/-- The derivative map restricts to a bijection from the chosen directions onto `D`. -/
theorem bijOn_booleanDerivative_derivativeRepresentativeDirections
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) :
    Set.BijOn (FABL.booleanDerivative f)
      (derivativeRepresentativeDirections f D hD : Set (FABL.F₂Cube n))
      (D : Set (BooleanFunction n)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [derivativeRepresentativeDirections] at ha
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp ha
    rw [booleanDerivative_derivativeDirectionRepresentative]
    exact g.2
  · intro a ha b hb heq
    rw [derivativeRepresentativeDirections] at ha hb
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hb
    have hgh : g = h := by
      apply Subtype.ext
      simpa only [booleanDerivative_derivativeDirectionRepresentative] using heq
    exact congrArg (derivativeDirectionRepresentative f D hD) hgh
  · intro g hg
    let gD : D := ⟨g, hg⟩
    refine ⟨derivativeDirectionRepresentative f D hD gD, ?_, ?_⟩
    · rw [derivativeRepresentativeDirections]
      exact Finset.mem_image.mpr ⟨gD, Finset.mem_univ _, rfl⟩
    · exact booleanDerivative_derivativeDirectionRepresentative f D hD gD

/-- Summing over the chosen directions is the same as summing over the derivative space. -/
theorem sum_derivativeRepresentativeDirections
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) (x : FABL.F₂Cube n) :
    ∑ a ∈ derivativeRepresentativeDirections f D hD,
        bitValueInt (FABL.booleanDerivative f a x) =
      ∑ g : D, bitValueInt (g.1 x) := by
  classical
  rw [derivativeRepresentativeDirections]
  rw [Finset.sum_image]
  · simp
  · intro g _hg h _hh heq
    exact derivativeDirectionRepresentative_injective f D hD heq

/-- The chosen representative directions give Carlet's nontrivial partial covering sequence
with levels zero and half the derivative-space cardinality. -/
theorem isPartialCoveringSequence_derivativeRepresentativeDirections
    (f : BooleanFunction n) (D : Submodule FABL.𝔽₂ (BooleanFunction n))
    (hD : IsDerivativeSpace f D) :
    IsPartialCoveringSequence f
      (directionFamilyIndicator (derivativeRepresentativeDirections f D hD)) 0
      ((Nat.card D / 2 : ℕ) : ℤ) ∧
      ((Nat.card D / 2 : ℕ) : ℤ) ≠ 0 := by
  constructor
  · intro x
    rw [weightedDerivativeSum]
    have hsum :
        (∑ a, directionFamilyIndicator
            (derivativeRepresentativeDirections f D hD) a *
              bitValueInt (FABL.booleanDerivative f a x)) =
          ∑ a ∈ derivativeRepresentativeDirections f D hD,
            bitValueInt (FABL.booleanDerivative f a x) := by
      simp [directionFamilyIndicator]
    rw [hsum, sum_derivativeRepresentativeDirections f D hD x]
    exact sum_bitValueInt_submodule_eq_zero_or_half D x
  · haveI : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr hD.1
    have hcard : 1 < Nat.card D := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact_mod_cast (Nat.div_pos hcard (by norm_num : 0 < 2)).ne'

end CryptBoolean
