/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Resiliency
public import CryptBoolean.Carlet.Chapter04.LinearStructures
public import CryptBoolean.Carlet.Chapter06.DirectSum

/-!
# Direct sums of resilient Boolean functions

Carlet Section 7.5.2: resiliency, Walsh spectra, and nonlinearity of direct sums.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s t m : ℕ}

/-- The integer sign of a binary value has absolute value one. -/
theorem natAbs_bitSignInt (b : FABL.𝔽₂) :
    (bitSignInt b).natAbs = 1 := by
  rw [bitSignInt_eq_if_one]
  split <;> simp

/-- Hamming weight is additive under the canonical concatenation of binary cubes. -/
theorem card_f₂Support_append
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    (FABL.f₂Support (Fin.append a b)).card =
      (FABL.f₂Support a).card + (FABL.f₂Support b).card := by
  simp only [FABL.f₂Support, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp

/-- Every raw Walsh magnitude is bounded by the maximum Walsh magnitude. -/
theorem walshTransform_natAbs_le_maxWalshMagnitude
    (f : BooleanFunction r) (a : FABL.F₂Cube r) :
    (walshTransform f a).natAbs ≤ maxWalshMagnitude f := by
  unfold maxWalshMagnitude
  exact Finset.le_sup'
    (fun u : FABL.F₂Cube r ↦ (walshTransform f u).natAbs)
    (Finset.mem_univ a)

private theorem exists_walshTransform_natAbs_eq_maxWalshMagnitude
    (f : BooleanFunction r) :
    ∃ a : FABL.F₂Cube r,
      (walshTransform f a).natAbs = maxWalshMagnitude f := by
  unfold maxWalshMagnitude
  obtain ⟨a, _ha, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (FABL.F₂Cube r)))
    Finset.univ_nonempty
    (fun u ↦ (walshTransform f u).natAbs)
  exact ⟨a, hmax.symm⟩

/-- The maximum raw Walsh magnitude of a direct sum is the product of the
maximum magnitudes of its summands. -/
theorem maxWalshMagnitude_booleanDirectSum
    (f : BooleanFunction r) (g : BooleanFunction s) :
    maxWalshMagnitude (booleanDirectSum f g) =
      maxWalshMagnitude f * maxWalshMagnitude g := by
  apply le_antisymm
  · unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro u _hu
    let p := (Fin.appendEquiv r s).symm u
    have hu : Fin.append p.1 p.2 = u :=
      (Fin.appendEquiv r s).apply_symm_apply u
    rw [← hu, walshTransform_directSum, Int.natAbs_mul]
    exact Nat.mul_le_mul
      (walshTransform_natAbs_le_maxWalshMagnitude f p.1)
      (walshTransform_natAbs_le_maxWalshMagnitude g p.2)
  · obtain ⟨a, ha⟩ := exists_walshTransform_natAbs_eq_maxWalshMagnitude f
    obtain ⟨b, hb⟩ := exists_walshTransform_natAbs_eq_maxWalshMagnitude g
    calc
      maxWalshMagnitude f * maxWalshMagnitude g =
          (walshTransform f a).natAbs * (walshTransform g b).natAbs := by
            rw [ha, hb]
      _ = (walshTransform (booleanDirectSum f g)
          (Fin.append a b)).natAbs := by
            rw [walshTransform_directSum, Int.natAbs_mul]
      _ ≤ maxWalshMagnitude (booleanDirectSum f g) :=
        walshTransform_natAbs_le_maxWalshMagnitude _ _

/-- The direct sum of a `t`-resilient function and an `m`-resilient function
is `(t + m + 1)`-resilient. -/
theorem isResilient_booleanDirectSum
    {f : BooleanFunction r} {g : BooleanFunction s}
    (ht : t < r) (hm : m < s)
    (hf : IsResilient t f) (hg : IsResilient m g) :
    IsResilient (t + m + 1) (booleanDirectSum f g) := by
  have hr : 0 < r := (Nat.zero_le t).trans_lt ht
  have hs : 0 < s := (Nat.zero_le m).trans_lt hm
  have hrs : 0 < r + s := Nat.add_pos_left hr s
  have horder : t + m + 1 < r + s := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (t + m + 1) (booleanDirectSum f g) hrs horder]
  intro u huweight
  let p := (Fin.appendEquiv r s).symm u
  have hu : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  have hpweight :
      (FABL.f₂Support p.1).card + (FABL.f₂Support p.2).card ≤
        t + m + 1 := by
    rw [← card_f₂Support_append]
    simpa only [hu] using huweight
  rw [← hu, walshTransform_directSum]
  by_cases hleft : (FABL.f₂Support p.1).card ≤ t
  · rw [(theorem_3_resilient_iff_walshTransform_eq_zero
      t f hr ht).mp hf p.1 hleft, zero_mul]
  · have hright : (FABL.f₂Support p.2).card ≤ m := by omega
    rw [(theorem_3_resilient_iff_walshTransform_eq_zero
      m g hs hm).mp hg p.2 hright, mul_zero]

/-- Division-free nonlinearity identity for a Boolean direct sum. -/
theorem two_mul_nonlinearity_booleanDirectSum_add_product
    (f : BooleanFunction r) (g : BooleanFunction s) :
    2 * nonlinearity (booleanDirectSum f g) +
        (2 ^ r - 2 * nonlinearity f) *
          (2 ^ s - 2 * nonlinearity g) =
      2 ^ (r + s) := by
  have hf := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hg := two_mul_nonlinearity_add_maxWalshMagnitude g
  have hsum :=
    two_mul_nonlinearity_add_maxWalshMagnitude (booleanDirectSum f g)
  rw [maxWalshMagnitude_booleanDirectSum] at hsum
  have hfMagnitude :
      2 ^ r - 2 * nonlinearity f = maxWalshMagnitude f := by omega
  have hgMagnitude :
      2 ^ s - 2 * nonlinearity g = maxWalshMagnitude g := by omega
  rw [hfMagnitude, hgMagnitude]
  exact hsum

/-- Carlet's first direct-sum nonlinearity formula, in a total real-valued
form that retains the factor one half. -/
theorem nonlinearity_booleanDirectSum_cast_eq_half_product
    (f : BooleanFunction r) (g : BooleanFunction s) :
    (nonlinearity (booleanDirectSum f g) : ℝ) =
      (2 : ℝ) ^ (r + s) / 2 -
        (((2 : ℝ) ^ r - 2 * (nonlinearity f : ℝ)) *
          ((2 : ℝ) ^ s - 2 * (nonlinearity g : ℝ))) / 2 := by
  rw [nonlinearity_cast_eq_relation_35,
    maxWalshMagnitude_booleanDirectSum]
  have hf := congrArg (fun x : ℕ ↦ (x : ℝ))
    (two_mul_nonlinearity_add_maxWalshMagnitude f)
  have hg := congrArg (fun x : ℕ ↦ (x : ℝ))
    (two_mul_nonlinearity_add_maxWalshMagnitude g)
  push_cast at hf hg ⊢
  rw [pow_add]
  nlinarith

/-- Carlet's first displayed direct-sum formula in its positive-dimensional
source form. -/
theorem nonlinearity_booleanDirectSum_cast_eq_source
    (f : BooleanFunction r) (g : BooleanFunction s)
    (hsum : 0 < r + s) :
    (nonlinearity (booleanDirectSum f g) : ℝ) =
      (2 : ℝ) ^ (r + s - 1) -
        (((2 : ℝ) ^ r - 2 * (nonlinearity f : ℝ)) *
          ((2 : ℝ) ^ s - 2 * (nonlinearity g : ℝ))) / 2 := by
  rw [nonlinearity_booleanDirectSum_cast_eq_half_product]
  have hsucc : r + s = (r + s - 1) + 1 := by omega
  have hpow : (2 : ℝ) ^ (r + s) / 2 = (2 : ℝ) ^ (r + s - 1) := by
    calc
      (2 : ℝ) ^ (r + s) / 2 =
          (2 : ℝ) ^ ((r + s - 1) + 1) / 2 :=
        congrArg (fun q : ℕ ↦ (2 : ℝ) ^ q / 2) hsucc
      _ = (2 : ℝ) ^ (r + s - 1) := by
        rw [pow_succ]
        ring
  rw [hpow]

/-- Carlet's second direct-sum nonlinearity formula over the natural numbers. -/
theorem nonlinearity_booleanDirectSum
    (f : BooleanFunction r) (g : BooleanFunction s) :
    nonlinearity (booleanDirectSum f g) =
      2 ^ r * nonlinearity g + 2 ^ s * nonlinearity f -
        2 * nonlinearity f * nonlinearity g := by
  have hf := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hbound :
      2 * nonlinearity f * nonlinearity g ≤
        2 ^ r * nonlinearity g + 2 ^ s * nonlinearity f := by
    calc
      2 * nonlinearity f * nonlinearity g ≤
          2 ^ r * nonlinearity g := by
            apply Nat.mul_le_mul_right
            omega
      _ ≤ 2 ^ r * nonlinearity g + 2 ^ s * nonlinearity f :=
        Nat.le_add_right _ _
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_sub hbound]
  push_cast
  rw [nonlinearity_booleanDirectSum_cast_eq_half_product, pow_add]
  ring

/-- Binary derivatives split over the two blocks of a Boolean direct sum. -/
theorem booleanDerivative_booleanDirectSum_append
    (f : BooleanFunction r) (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    FABL.booleanDerivative (booleanDirectSum f g) (Fin.append a b) =
      booleanDirectSum (FABL.booleanDerivative f a)
        (FABL.booleanDerivative g b) := by
  funext z
  let p := (Fin.appendEquiv r s).symm z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz]
  simp [FABL.booleanDerivative, booleanDirectSum]
  abel

/-- A concatenated direction is a linear structure of a direct sum exactly
when both block directions are linear structures of their summands. -/
theorem isLinearStructure_booleanDirectSum_append
    (f : BooleanFunction r) (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    IsLinearStructure (booleanDirectSum f g) (Fin.append a b) ↔
      IsLinearStructure f a ∧ IsLinearStructure g b := by
  rw [IsLinearStructure, IsLinearStructure, IsLinearStructure,
    booleanDerivative_booleanDirectSum_append]
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨⟨ε + FABL.booleanDerivative g b (fun _ ↦ 0), ?_⟩,
      ⟨ε + FABL.booleanDerivative f a (fun _ ↦ 0), ?_⟩⟩
    · intro x
      have hx : FABL.booleanDerivative f a x +
          FABL.booleanDerivative g b (fun _ ↦ 0) = ε := by
        simpa [booleanDirectSum] using hε (Fin.append x (fun _ ↦ 0))
      calc
        FABL.booleanDerivative f a x =
            FABL.booleanDerivative f a x +
              (FABL.booleanDerivative g b (fun _ ↦ 0) +
                FABL.booleanDerivative g b (fun _ ↦ 0)) := by
          rw [ZModModule.add_self, add_zero]
        _ = (FABL.booleanDerivative f a x +
              FABL.booleanDerivative g b (fun _ ↦ 0)) +
                FABL.booleanDerivative g b (fun _ ↦ 0) := by abel
        _ = ε + FABL.booleanDerivative g b (fun _ ↦ 0) := by rw [hx]
    · intro y
      have hy : FABL.booleanDerivative f a (fun _ ↦ 0) +
          FABL.booleanDerivative g b y = ε := by
        simpa [booleanDirectSum] using hε (Fin.append (fun _ ↦ 0) y)
      calc
        FABL.booleanDerivative g b y =
            (FABL.booleanDerivative f a (fun _ ↦ 0) +
              FABL.booleanDerivative f a (fun _ ↦ 0)) +
                FABL.booleanDerivative g b y := by
          rw [ZModModule.add_self, zero_add]
        _ = FABL.booleanDerivative f a (fun _ ↦ 0) +
              (FABL.booleanDerivative f a (fun _ ↦ 0) +
                FABL.booleanDerivative g b y) := by abel
        _ = ε + FABL.booleanDerivative f a (fun _ ↦ 0) := by
          rw [hy]
          abel
  · rintro ⟨⟨ε, hε⟩, ⟨δ, hδ⟩⟩
    refine ⟨ε + δ, ?_⟩
    intro z
    let p := (Fin.appendEquiv r s).symm z
    have hz : Fin.append p.1 p.2 = z :=
      (Fin.appendEquiv r s).apply_symm_apply z
    rw [← hz]
    simp [booleanDirectSum, hε, hδ]

/-- A direct sum has no nonzero linear structure exactly when neither summand
has a nonzero linear structure. -/
theorem noNonzeroLinearStructure_booleanDirectSum
    (f : BooleanFunction r) (g : BooleanFunction s) :
    (∀ e : FABL.F₂Cube (r + s), e ≠ 0 →
      ¬ IsLinearStructure (booleanDirectSum f g) e) ↔
      (∀ a : FABL.F₂Cube r, a ≠ 0 → ¬ IsLinearStructure f a) ∧
      (∀ b : FABL.F₂Cube s, b ≠ 0 → ¬ IsLinearStructure g b) := by
  constructor
  · intro h
    constructor
    · intro a ha hstructure
      have happend : Fin.append a (0 : FABL.F₂Cube s) ≠ 0 := by
        intro happend
        apply ha
        funext i
        have hi := congrFun happend (Fin.castAdd s i)
        simpa using hi
      exact h (Fin.append a 0) happend
        ((isLinearStructure_booleanDirectSum_append f g a 0).2
          ⟨hstructure, isLinearStructure_zero g⟩)
    · intro b hb hstructure
      have happend : Fin.append (0 : FABL.F₂Cube r) b ≠ 0 := by
        intro happend
        apply hb
        funext i
        have hi := congrFun happend (Fin.natAdd r i)
        simpa using hi
      exact h (Fin.append 0 b) happend
        ((isLinearStructure_booleanDirectSum_append f g 0 b).2
          ⟨isLinearStructure_zero f, hstructure⟩)
  · rintro ⟨hf, hg⟩ e he hstructure
    let p := (Fin.appendEquiv r s).symm e
    have hp : Fin.append p.1 p.2 = e :=
      (Fin.appendEquiv r s).apply_symm_apply e
    have hpstructure : IsLinearStructure f p.1 ∧ IsLinearStructure g p.2 :=
      (isLinearStructure_booleanDirectSum_append f g p.1 p.2).1
        (hp.symm ▸ hstructure)
    by_cases hleft : p.1 = 0
    · have hright : p.2 ≠ 0 := by
        intro hright
        apply he
        rw [← hp, hleft, hright]
        funext i
        exact Fin.addCases (fun j ↦ by simp) (fun j ↦ by simp) i
      exact hg p.2 hright hpstructure.2
    · exact hf p.1 hleft hpstructure.1

end CryptBoolean
