/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.AffineFlatWalshCharacterization
public import CryptBoolean.Carlet.Chapter08.OrderCharacterization

/-!
# Restriction-Walsh characterization of propagation criteria of order

Carlet Proposition 37, obtained by applying raw Poisson summation in the
direction and restriction-frequency variables.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance restrictionWalshSubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

/-- The raw Walsh transform of the restriction of `f` to the coordinate
subspace indexed by `v`. -/
noncomputable def coordinateRestrictedWalshTransform
    (f : BooleanFunction n) (v w : FABL.F₂Cube n) : ℝ :=
  ∑ x : predecessorSubspace v,
    realSignView f x.1 * FABL.vectorWalshCharacter w x.1

/-- The product sum in Carlet Proposition 37. -/
noncomputable def predecessorWalshRestrictionProductSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) : ℝ :=
  ∑ w : predecessorSubspace u,
    (walshTransform f w.1 : ℝ) *
      coordinateRestrictedWalshTransform f v w.1

/-- The rectangular sum of the derivative Walsh transform over the two
complementary coordinate subspaces. -/
noncomputable def derivativeWalshRectangleSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) : ℝ :=
  ∑ a : FABL.perpendicularSubspace (predecessorSubspace u),
    ∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
      (walshTransform (FABL.booleanDerivative f a.1) b.1 : ℝ)

private theorem card_perpendicular_predecessorSubspace
    (v : FABL.F₂Cube n) :
    Nat.card (FABL.perpendicularSubspace (predecessorSubspace v)) =
      2 ^ (n - (FABL.f₂Support v).card) := by
  rw [FABL.card_submodule_eq_two_pow_finrank,
    FABL.finrank_perpendicularSubspace]
  rw [show Module.finrank FABL.𝔽₂ (predecessorSubspace v) =
      (FABL.f₂Support v).card by
    unfold predecessorSubspace
    change FABL.f₂Codimension
      (FABL.F₂DecisionTree.coordinateZeroSubspace (FABL.f₂Support v)) = _
    rw [FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace]]

private theorem sum_walshTransform_perpendicularPredecessor_eq
    (f : BooleanFunction n) (v w : FABL.F₂Cube n) :
    (∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
        (walshTransform f (w + b.1) : ℝ)) =
      (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
        coordinateRestrictedWalshTransform f v w := by
  have hraw (a : FABL.F₂Cube n) :
      rawFourierTransform (realSignView f) a =
        (walshTransform f a : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  have hpoisson := rawPoissonSummationFormula
    (realSignView f)
    (FABL.perpendicularSubspace (predecessorSubspace v)) w 0
  rw [FABL.perpendicularSubspace_perpendicularSubspace,
    card_perpendicular_predecessorSubspace] at hpoisson
  simp_rw [hraw] at hpoisson
  simpa [coordinateRestrictedWalshTransform, add_comm, mul_comm] using hpoisson

private theorem rawFourierTransform_derivativeWalsh_eq
    (f : BooleanFunction n) (b w : FABL.F₂Cube n) :
    rawFourierTransform
        (fun a ↦ (walshTransform (FABL.booleanDerivative f a) b : ℝ)) w =
      (walshTransform f (b + w) : ℝ) *
        (walshTransform f w : ℝ) := by
  have hconvolution :
      (fun a ↦ (walshTransform (FABL.booleanDerivative f a) b : ℝ)) =
        rawConvolution
          (fun x ↦ FABL.vectorWalshCharacter b x * realSignView f x)
          (realSignView f) := by
    funext a
    rw [walshTransform_cast_eq_sum_realSignView_mul_character,
      rawConvolution]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [realSignView_booleanDerivative]
    ring_nf
  rw [hconvolution, rawFourierTransform_rawConvolution]
  have hmodulation := rawFourierTransform_modulate_translate
    (realSignView f) b 0 w
  have hfirst :
      rawFourierTransform
          (fun x ↦ FABL.vectorWalshCharacter b x * realSignView f x) w =
        (walshTransform f (b + w) : ℝ) := by
    rw [show (fun x ↦ FABL.vectorWalshCharacter b x * realSignView f x) =
        (fun x ↦ FABL.vectorWalshCharacter b x * realSignView f (x + 0)) by
      funext x
      simp]
    rw [hmodulation]
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
    simp
  have hsecond :
      rawFourierTransform (realSignView f) w =
        (walshTransform f w : ℝ) := by
    rw [rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff,
      walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  rw [hfirst, hsecond]

/-- Double Poisson summation identifies the restriction-Walsh product sum
with the rectangular derivative-Walsh sum. -/
theorem predecessorWalshRestrictionProductSum_eq_derivativeWalshRectangleSum
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) :
    (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
        predecessorWalshRestrictionProductSum f u v =
      (2 : ℝ) ^ (FABL.f₂Support u).card *
        derivativeWalshRectangleSum f u v := by
  have hdirection
      (b : FABL.perpendicularSubspace (predecessorSubspace v)) :
      (∑ w : predecessorSubspace u,
          (walshTransform f w.1 : ℝ) *
            (walshTransform f (w.1 + b.1) : ℝ)) =
        (2 : ℝ) ^ (FABL.f₂Support u).card *
          ∑ a : FABL.perpendicularSubspace (predecessorSubspace u),
            (walshTransform (FABL.booleanDerivative f a.1) b.1 : ℝ) := by
    have hpoisson := rawPoissonSummationFormula
      (fun a ↦ (walshTransform (FABL.booleanDerivative f a) b.1 : ℝ))
      (predecessorSubspace u) 0 0
    rw [card_predecessorSubspace] at hpoisson
    simp_rw [rawFourierTransform_derivativeWalsh_eq] at hpoisson
    simpa [add_comm, mul_comm] using hpoisson
  unfold predecessorWalshRestrictionProductSum derivativeWalshRectangleSum
  calc
    (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
        ∑ w : predecessorSubspace u,
          (walshTransform f w.1 : ℝ) *
            coordinateRestrictedWalshTransform f v w.1 =
        ∑ w : predecessorSubspace u,
          (walshTransform f w.1 : ℝ) *
            ∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
              (walshTransform f (w.1 + b.1) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _hw
      rw [sum_walshTransform_perpendicularPredecessor_eq]
      ring
    _ = ∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
          ∑ w : predecessorSubspace u,
            (walshTransform f w.1 : ℝ) *
              (walshTransform f (w.1 + b.1) : ℝ) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
          ((2 : ℝ) ^ (FABL.f₂Support u).card *
            ∑ a : FABL.perpendicularSubspace (predecessorSubspace u),
              (walshTransform (FABL.booleanDerivative f a.1) b.1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact hdirection b
    _ = (2 : ℝ) ^ (FABL.f₂Support u).card *
          ∑ a : FABL.perpendicularSubspace (predecessorSubspace u),
            ∑ b : FABL.perpendicularSubspace (predecessorSubspace v),
              (walshTransform (FABL.booleanDerivative f a.1) b.1 : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]

private theorem eq_zero_of_predecessorRectangleSum_eq_constant
    (g : FABL.F₂Cube n → FABL.F₂Cube n → ℝ)
    (P : FABL.F₂Cube n → FABL.F₂Cube n → Prop)
    (c : ℝ) (l k : ℕ)
    (hPmono : ∀ x y a b : FABL.F₂Cube n,
      FABL.f₂Support x ⊆ FABL.f₂Support a →
      FABL.f₂Support y ⊆ FABL.f₂Support b →
      P a b → P x y)
    (hbase : g 0 0 = c)
    (hrectangle : ∀ a b : FABL.F₂Cube n,
      (FABL.f₂Support a).card ≤ l →
      (FABL.f₂Support b).card ≤ k →
      P a b →
        (∑ x : predecessorSubspace a,
          ∑ y : predecessorSubspace b, g x.1 y.1) = c)
    (a b : FABL.F₂Cube n)
    (haweight : (FABL.f₂Support a).card ≤ l)
    (hbweight : (FABL.f₂Support b).card ≤ k)
    (hab : (a, b) ≠ (0, 0))
    (hP : P a b) :
    g a b = 0 := by
  induction m : (FABL.f₂Support a).card +
      (FABL.f₂Support b).card using Nat.strong_induction_on generalizing a b with
  | h m ih =>
      let pa : predecessorSubspace a :=
        ⟨a, (mem_predecessorSubspace_iff a a).mpr Finset.Subset.rfl⟩
      let pb : predecessorSubspace b :=
        ⟨b, (mem_predecessorSubspace_iff b b).mpr Finset.Subset.rfl⟩
      let za : predecessorSubspace a := ⟨0, by simp⟩
      let zb : predecessorSubspace b := ⟨0, by simp⟩
      let target : predecessorSubspace a × predecessorSubspace b := (pa, pb)
      let base : predecessorSubspace a × predecessorSubspace b := (za, zb)
      let rectangle : Finset
          (predecessorSubspace a × predecessorSubspace b) :=
        Finset.univ ×ˢ Finset.univ
      have htarget : target ∈ rectangle := by simp [target, rectangle]
      have hbaseMem : base ∈ rectangle := by simp [base, rectangle]
      have htargetBase : target ≠ base := by
        intro h
        apply hab
        apply Prod.ext
        · exact Subtype.ext_iff.mp
            (congrArg Prod.fst h) |>.trans (by rfl)
        · exact Subtype.ext_iff.mp
            (congrArg Prod.snd h) |>.trans (by rfl)
      have hbaseErase : base ∈ rectangle.erase target := by
        exact Finset.mem_erase.mpr ⟨htargetBase.symm, hbaseMem⟩
      have hrest :
          ∀ p ∈ (rectangle.erase target).erase base,
            g p.1.1 p.2.1 = 0 := by
        intro p hp
        have hpBase : p ≠ base := (Finset.mem_erase.mp hp).1
        have hpTarget : p ≠ target :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
        have hpx : FABL.f₂Support p.1.1 ⊆ FABL.f₂Support a :=
          (mem_predecessorSubspace_iff a p.1.1).mp p.1.2
        have hpy : FABL.f₂Support p.2.1 ⊆ FABL.f₂Support b :=
          (mem_predecessorSubspace_iff b p.2.1).mp p.2.2
        have hxcard := Finset.card_le_card hpx
        have hycard := Finset.card_le_card hpy
        have hmeasure :
            (FABL.f₂Support p.1.1).card +
                (FABL.f₂Support p.2.1).card <
              (FABL.f₂Support a).card +
                (FABL.f₂Support b).card := by
          apply lt_of_le_of_ne
          · omega
          · intro heq
            have hxcardEq :
                (FABL.f₂Support p.1.1).card =
                  (FABL.f₂Support a).card := by omega
            have hycardEq :
                (FABL.f₂Support p.2.1).card =
                  (FABL.f₂Support b).card := by omega
            have hxSupport : FABL.f₂Support p.1.1 = FABL.f₂Support a :=
              Finset.eq_of_subset_of_card_le hpx hxcardEq.ge
            have hySupport : FABL.f₂Support p.2.1 = FABL.f₂Support b :=
              Finset.eq_of_subset_of_card_le hpy hycardEq.ge
            apply hpTarget
            apply Prod.ext
            · apply Subtype.ext
              exact (FABL.f₂CubeEquivFinset n).injective hxSupport
            · apply Subtype.ext
              exact (FABL.f₂CubeEquivFinset n).injective hySupport
        rw [m] at hmeasure
        have hpP : P p.1.1 p.2.1 :=
          hPmono p.1.1 p.2.1 a b hpx hpy hP
        apply ih _ hmeasure p.1.1 p.2.1
        · exact hxcard.trans haweight
        · exact hycard.trans hbweight
        · intro hpzero
          apply hpBase
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg Prod.fst hpzero
          · apply Subtype.ext
            exact congrArg Prod.snd hpzero
        · exact hpP
        · rfl
      have hsumRest :
          (∑ p ∈ (rectangle.erase target).erase base,
            g p.1.1 p.2.1) = 0 :=
        Finset.sum_eq_zero hrest
      have hsumRectangle :
          (∑ p ∈ rectangle, g p.1.1 p.2.1) = c + g a b := by
        rw [← Finset.sum_erase_add _ _ htarget,
          ← Finset.sum_erase_add _ _ hbaseErase, hsumRest, zero_add]
        rw [show g base.1.1 base.2.1 = c by simpa [base, za, zb] using hbase]
      have hsumProduct :
          (∑ p ∈ rectangle, g p.1.1 p.2.1) =
            ∑ x : predecessorSubspace a,
              ∑ y : predecessorSubspace b, g x.1 y.1 := by
        simpa [rectangle] using
          (Finset.sum_product
            (Finset.univ : Finset (predecessorSubspace a))
            (Finset.univ : Finset (predecessorSubspace b))
            (fun p ↦ g p.1.1 p.2.1))
      rw [hsumProduct, hrectangle a b haweight hbweight hP] at hsumRectangle
      linarith

private theorem walshTransform_zeroDerivative_zero_cast
    (f : BooleanFunction n) :
    (walshTransform (FABL.booleanDerivative f 0) 0 : ℝ) =
      (2 : ℝ) ^ n := by
  rw [walshTransform_cast_eq_sum_realSignView_mul_character]
  simp_rw [realSignView_booleanDerivative]
  simp only [add_zero, FABL.vectorWalshCharacter_zero,
    AddChar.one_apply, mul_one]
  calc
    (∑ x, realSignView f x * realSignView f x) =
        ∑ _x : FABL.F₂Cube n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : f x = 0
      · simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, hx]
      · have hxOne : f x = 1 := Fin.eq_one_of_ne_zero _ hx
        simp [realSignView, FABL.realSignEncodedFunction,
          FABL.signEncodedFunction, hxOne]
    _ = (2 : ℝ) ^ n := by simp

private theorem derivativeWalshRectangleSum_eq_two_pow_of_zero
    (f : BooleanFunction n) (u v : FABL.F₂Cube n)
    (hzero : ∀
      (a : FABL.perpendicularSubspace (predecessorSubspace u))
      (b : FABL.perpendicularSubspace (predecessorSubspace v)),
      (a.1, b.1) ≠ (0, 0) →
        walshTransform (FABL.booleanDerivative f a.1) b.1 = 0) :
    derivativeWalshRectangleSum f u v = (2 : ℝ) ^ n := by
  unfold derivativeWalshRectangleSum
  rw [Finset.sum_eq_single
    (0 : FABL.perpendicularSubspace (predecessorSubspace u))]
  · rw [Finset.sum_eq_single
      (0 : FABL.perpendicularSubspace (predecessorSubspace v))]
    · exact walshTransform_zeroDerivative_zero_cast f
    · intro b _hb hbzero
      exact_mod_cast hzero 0 b (by
        intro hpair
        apply hbzero
        apply Subtype.ext
        exact congrArg Prod.snd hpair)
    · intro hzeroMem
      exact (hzeroMem (Finset.mem_univ _)).elim
  · intro a _ha hazero
    apply Finset.sum_eq_zero
    intro b _hb
    exact_mod_cast hzero a b (by
      intro hpair
      apply hazero
      apply Subtype.ext
      exact congrArg Prod.fst hpair)
  · intro hzeroMem
    exact (hzeroMem (Finset.mem_univ _)).elim

private theorem derivativeWalshRectangleSum_eq_two_pow_iff
    (l k : ℕ) (f : BooleanFunction n) :
    (∀ a b : FABL.F₂Cube n,
      (FABL.f₂Support a).card ≤ l →
      (FABL.f₂Support b).card ≤ k →
      (a, b) ≠ (0, 0) →
        walshTransform (FABL.booleanDerivative f a) b = 0) ↔
      ∀ u v : FABL.F₂Cube n,
        n - l ≤ (FABL.f₂Support u).card →
        n - k ≤ (FABL.f₂Support v).card →
          derivativeWalshRectangleSum f u v = (2 : ℝ) ^ n := by
  constructor
  · intro hzero u v huweight hvweight
    have haweight
        (a : FABL.perpendicularSubspace (predecessorSubspace u)) :
        (FABL.f₂Support a.1).card ≤ l := by
      have hsubset :=
        (mem_perpendicular_predecessorSubspace_iff u a.1).mp a.2
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_compl, Fintype.card_fin] at hcard
      omega
    have hbweight
        (b : FABL.perpendicularSubspace (predecessorSubspace v)) :
        (FABL.f₂Support b.1).card ≤ k := by
      have hsubset :=
        (mem_perpendicular_predecessorSubspace_iff v b.1).mp b.2
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_compl, Fintype.card_fin] at hcard
      omega
    apply derivativeWalshRectangleSum_eq_two_pow_of_zero f u v
    intro a b hab
    exact hzero a.1 b.1 (haweight a) (hbweight b) hab
  · intro hrectangles a b haweight hbweight hab
    let g : FABL.F₂Cube n → FABL.F₂Cube n → ℝ :=
      fun x y ↦ (walshTransform (FABL.booleanDerivative f x) y : ℝ)
    have hbase : g 0 0 = (2 : ℝ) ^ n :=
      walshTransform_zeroDerivative_zero_cast f
    have hrectangle : ∀ x y : FABL.F₂Cube n,
        (FABL.f₂Support x).card ≤ l →
        (FABL.f₂Support y).card ≤ k →
          (∑ a' : predecessorSubspace x,
            ∑ b' : predecessorSubspace y, g a'.1 b'.1) =
              (2 : ℝ) ^ n := by
      intro x y hxweight hyweight
      let u : FABL.F₂Cube n :=
        FABL.f₂CubeOfFinset (FABL.f₂Support x)ᶜ
      let v : FABL.F₂Cube n :=
        FABL.f₂CubeOfFinset (FABL.f₂Support y)ᶜ
      have husupport : FABL.f₂Support u = (FABL.f₂Support x)ᶜ :=
        (FABL.f₂CubeEquivFinset n).right_inv _
      have hvsupport : FABL.f₂Support v = (FABL.f₂Support y)ᶜ :=
        (FABL.f₂CubeEquivFinset n).right_inv _
      have huweight : n - l ≤ (FABL.f₂Support u).card := by
        rw [husupport, Finset.card_compl, Fintype.card_fin]
        omega
      have hvweight : n - k ≤ (FABL.f₂Support v).card := by
        rw [hvsupport, Finset.card_compl, Fintype.card_fin]
        omega
      have hspaceU :
          FABL.perpendicularSubspace (predecessorSubspace u) =
            predecessorSubspace x := by
        ext z
        rw [mem_perpendicular_predecessorSubspace_iff,
          mem_predecessorSubspace_iff, husupport]
        simp only [compl_compl]
        change (z ≼ x) ↔ (z ≼ x)
        rfl
      have hspaceV :
          FABL.perpendicularSubspace (predecessorSubspace v) =
            predecessorSubspace y := by
        ext z
        rw [mem_perpendicular_predecessorSubspace_iff,
          mem_predecessorSubspace_iff, hvsupport]
        simp only [compl_compl]
        change (z ≼ y) ↔ (z ≼ y)
        rfl
      have hrectangleUV := hrectangles u v huweight hvweight
      unfold derivativeWalshRectangleSum at hrectangleUV
      rw [hspaceU, hspaceV] at hrectangleUV
      exact hrectangleUV
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero]
    exact eq_zero_of_predecessorRectangleSum_eq_constant
      g (fun _ _ ↦ True) ((2 : ℝ) ^ n) l k
      (by intros; trivial) hbase (by
        intro x y hx hy _htrue
        exact hrectangle x y hx hy)
      a b haweight hbweight hab trivial

private theorem predecessorWalshRestrictionProductSum_eq_two_pow_iff
    (f : BooleanFunction n) (u v : FABL.F₂Cube n) :
    predecessorWalshRestrictionProductSum f u v =
        (2 : ℝ) ^ ((FABL.f₂Support u).card +
          (FABL.f₂Support v).card) ↔
      derivativeWalshRectangleSum f u v = (2 : ℝ) ^ n := by
  have hidentity :=
    predecessorWalshRestrictionProductSum_eq_derivativeWalshRectangleSum
      f u v
  have huCard : (FABL.f₂Support u).card ≤ n := by
    simpa using Finset.card_le_univ (FABL.f₂Support u)
  have hvCard : (FABL.f₂Support v).card ≤ n := by
    simpa using Finset.card_le_univ (FABL.f₂Support v)
  have hscaleU : (2 : ℝ) ^ (FABL.f₂Support u).card ≠ 0 := by
    positivity
  have hscaleV : (2 : ℝ) ^ (n - (FABL.f₂Support v).card) ≠ 0 := by
    positivity
  constructor
  · intro hproduct
    apply mul_left_cancel₀ hscaleU
    calc
      (2 : ℝ) ^ (FABL.f₂Support u).card *
          derivativeWalshRectangleSum f u v =
          (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
            predecessorWalshRestrictionProductSum f u v := hidentity.symm
      _ = (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
          (2 : ℝ) ^ ((FABL.f₂Support u).card +
            (FABL.f₂Support v).card) := by rw [hproduct]
      _ = (2 : ℝ) ^ (FABL.f₂Support u).card * (2 : ℝ) ^ n := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  · intro hrectangle
    apply mul_left_cancel₀ hscaleV
    calc
      (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
          predecessorWalshRestrictionProductSum f u v =
          (2 : ℝ) ^ (FABL.f₂Support u).card *
            derivativeWalshRectangleSum f u v := hidentity
      _ = (2 : ℝ) ^ (FABL.f₂Support u).card * (2 : ℝ) ^ n := by
        rw [hrectangle]
      _ = (2 : ℝ) ^ (n - (FABL.f₂Support v).card) *
          (2 : ℝ) ^ ((FABL.f₂Support u).card +
            (FABL.f₂Support v).card) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega

/-- Carlet Proposition 37, extended form: `EPC(l)` of order `k` is
equivalent to the restriction-Walsh product identity on all qualifying
coordinate subspaces. -/
theorem satisfiesExtendedPropagationCriterion_iff_predecessorWalshRestrictionProductSum
    (l k : ℕ) (f : BooleanFunction n) (hparameters : l + k ≤ n) :
    SatisfiesExtendedPropagationCriterion l k f ↔
      ∀ u v : FABL.F₂Cube n,
        n - l ≤ (FABL.f₂Support u).card →
        n - k ≤ (FABL.f₂Support v).card →
          predecessorWalshRestrictionProductSum f u v =
            (2 : ℝ) ^ ((FABL.f₂Support u).card +
              (FABL.f₂Support v).card) := by
  constructor
  · intro hepc u v hu hv
    apply (predecessorWalshRestrictionProductSum_eq_two_pow_iff f u v).mpr
    apply (derivativeWalshRectangleSum_eq_two_pow_iff l k f).mp
      ((satisfiesExtendedPropagationCriterion_iff_walshTransform_booleanDerivative_eq_zero
        l k f hparameters).mp hepc)
    · exact hu
    · exact hv
  · intro hsums
    apply
      (satisfiesExtendedPropagationCriterion_iff_walshTransform_booleanDerivative_eq_zero
        l k f hparameters).mpr
    apply (derivativeWalshRectangleSum_eq_two_pow_iff l k f).mpr
    intro u v hu hv
    exact (predecessorWalshRestrictionProductSum_eq_two_pow_iff f u v).mp
      (hsums u v hu hv)

private theorem derivativeWalshRectangleSum_disjoint_eq_two_pow_iff
    (l k : ℕ) (f : BooleanFunction n) :
    (∀ a b : FABL.F₂Cube n,
      (FABL.f₂Support a).card ≤ l →
      (FABL.f₂Support b).card ≤ k →
      (a, b) ≠ (0, 0) →
      Disjoint (FABL.f₂Support a) (FABL.f₂Support b) →
        walshTransform (FABL.booleanDerivative f a) b = 0) ↔
      ∀ u v : FABL.F₂Cube n,
        n - l ≤ (FABL.f₂Support u).card →
        n - k ≤ (FABL.f₂Support v).card →
        Disjoint (FABL.f₂Support u)ᶜ (FABL.f₂Support v)ᶜ →
          derivativeWalshRectangleSum f u v = (2 : ℝ) ^ n := by
  constructor
  · intro hzero u v huweight hvweight huv
    apply derivativeWalshRectangleSum_eq_two_pow_of_zero f u v
    intro a b hab
    have hasubset :=
      (mem_perpendicular_predecessorSubspace_iff u a.1).mp a.2
    have hbsubset :=
      (mem_perpendicular_predecessorSubspace_iff v b.1).mp b.2
    have hacard := Finset.card_le_card hasubset
    have hbcard := Finset.card_le_card hbsubset
    rw [Finset.card_compl, Fintype.card_fin] at hacard hbcard
    apply hzero a.1 b.1 (by omega) (by omega) hab
    exact huv.mono hasubset hbsubset
  · intro hrectangles a b haweight hbweight hab habdisjoint
    let g : FABL.F₂Cube n → FABL.F₂Cube n → ℝ :=
      fun x y ↦ (walshTransform (FABL.booleanDerivative f x) y : ℝ)
    have hbase : g 0 0 = (2 : ℝ) ^ n :=
      walshTransform_zeroDerivative_zero_cast f
    have hrectangle : ∀ x y : FABL.F₂Cube n,
        (FABL.f₂Support x).card ≤ l →
        (FABL.f₂Support y).card ≤ k →
        Disjoint (FABL.f₂Support x) (FABL.f₂Support y) →
          (∑ a' : predecessorSubspace x,
            ∑ b' : predecessorSubspace y, g a'.1 b'.1) =
              (2 : ℝ) ^ n := by
      intro x y hxweight hyweight hxydisjoint
      let u : FABL.F₂Cube n :=
        FABL.f₂CubeOfFinset (FABL.f₂Support x)ᶜ
      let v : FABL.F₂Cube n :=
        FABL.f₂CubeOfFinset (FABL.f₂Support y)ᶜ
      have husupport : FABL.f₂Support u = (FABL.f₂Support x)ᶜ :=
        (FABL.f₂CubeEquivFinset n).right_inv _
      have hvsupport : FABL.f₂Support v = (FABL.f₂Support y)ᶜ :=
        (FABL.f₂CubeEquivFinset n).right_inv _
      have huweight : n - l ≤ (FABL.f₂Support u).card := by
        rw [husupport, Finset.card_compl, Fintype.card_fin]
        omega
      have hvweight : n - k ≤ (FABL.f₂Support v).card := by
        rw [hvsupport, Finset.card_compl, Fintype.card_fin]
        omega
      have huv :
          Disjoint (FABL.f₂Support u)ᶜ (FABL.f₂Support v)ᶜ := by
        simpa only [husupport, hvsupport, compl_compl] using hxydisjoint
      have hspaceU :
          FABL.perpendicularSubspace (predecessorSubspace u) =
            predecessorSubspace x := by
        ext z
        rw [mem_perpendicular_predecessorSubspace_iff,
          mem_predecessorSubspace_iff, husupport]
        simp only [compl_compl]
        change (z ≼ x) ↔ (z ≼ x)
        rfl
      have hspaceV :
          FABL.perpendicularSubspace (predecessorSubspace v) =
            predecessorSubspace y := by
        ext z
        rw [mem_perpendicular_predecessorSubspace_iff,
          mem_predecessorSubspace_iff, hvsupport]
        simp only [compl_compl]
        change (z ≼ y) ↔ (z ≼ y)
        rfl
      have hrectangleUV := hrectangles u v huweight hvweight huv
      unfold derivativeWalshRectangleSum at hrectangleUV
      rw [hspaceU, hspaceV] at hrectangleUV
      exact hrectangleUV
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero]
    exact eq_zero_of_predecessorRectangleSum_eq_constant
      g (fun x y ↦ Disjoint (FABL.f₂Support x) (FABL.f₂Support y))
      ((2 : ℝ) ^ n) l k
      (by
        intro x y a b hxa hyb hab'
        exact hab'.mono hxa hyb)
      hbase hrectangle a b haweight hbweight hab habdisjoint

/-- Carlet Proposition 37, coordinate-restriction form: `PC(l)` of order `k`
is equivalent to the restriction-Walsh product identity when the complements
of the two indexing supports are disjoint. -/
theorem satisfiesPropagationCriterionOfOrder_iff_predecessorWalshRestrictionProductSum
    (l k : ℕ) (f : BooleanFunction n) (hparameters : l + k ≤ n) :
    SatisfiesPropagationCriterionOfOrder l k f ↔
      ∀ u v : FABL.F₂Cube n,
        n - l ≤ (FABL.f₂Support u).card →
        n - k ≤ (FABL.f₂Support v).card →
        Disjoint (FABL.f₂Support u)ᶜ (FABL.f₂Support v)ᶜ →
          predecessorWalshRestrictionProductSum f u v =
            (2 : ℝ) ^ ((FABL.f₂Support u).card +
              (FABL.f₂Support v).card) := by
  constructor
  · intro hpc u v hu hv huv
    apply (predecessorWalshRestrictionProductSum_eq_two_pow_iff f u v).mpr
    apply (derivativeWalshRectangleSum_disjoint_eq_two_pow_iff l k f).mp
      ((satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
        l k f hparameters).mp hpc)
    · exact hu
    · exact hv
    · exact huv
  · intro hsums
    apply
      (satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero
        l k f hparameters).mpr
    apply (derivativeWalshRectangleSum_disjoint_eq_two_pow_iff l k f).mpr
    intro u v hu hv huv
    exact (predecessorWalshRestrictionProductSum_eq_two_pow_iff f u v).mp
      (hsums u v hu hv huv)

end CryptBoolean
