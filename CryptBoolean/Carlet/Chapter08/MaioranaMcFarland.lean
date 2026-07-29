/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarland

/-!
# Maiorana--McFarland propagation criteria

Carlet Section 8.1.2: the derivative identity, the fiber-distance condition,
and the resulting propagation construction.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- The additive derivative of a binary-cube-valued map. -/
def binaryMapDerivative
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (b : FABL.F₂Cube s) :
    FABL.F₂Cube s → FABL.F₂Cube r :=
  fun y ↦ φ y + φ (y + b)

/-- The additive derivative of a binary map in the zero direction vanishes. -/
@[simp] theorem binaryMapDerivative_zero
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) :
    binaryMapDerivative φ 0 = 0 := by
  funext y
  simp [binaryMapDerivative, ZModModule.add_self]

/-- The fibers of `φ` have minimum Hamming distance greater than `l`.
Empty and singleton fibers satisfy the condition vacuously. -/
def MaioranaMcFarlandFibersHaveMinimumDistanceGreaterThan
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (l : ℕ) : Prop :=
  ∀ ⦃y z : FABL.F₂Cube s⦄, y ≠ z → φ y = φ z →
    l < (FABL.f₂Support (y + z)).card

/-- The derivative of a general Maiorana--McFarland function is again a
general Maiorana--McFarland function. -/
theorem booleanDerivative_booleanMaioranaMcFarlandGeneral_append
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    FABL.booleanDerivative (booleanMaioranaMcFarlandGeneral φ g)
        (Fin.append a b) =
      booleanMaioranaMcFarlandGeneral (binaryMapDerivative φ b)
        (fun y ↦
          FABL.f₂DotProduct a (φ (y + b)) +
            FABL.booleanDerivative g b y) := by
  funext z
  let p := (Fin.appendEquiv r s).symm z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv r s).apply_symm_apply z
  rw [← hz]
  have hadd :
      Fin.append p.1 p.2 + Fin.append a b =
        Fin.append (p.1 + a) (p.2 + b) := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  rw [FABL.booleanDerivative, hadd,
    booleanMaioranaMcFarlandGeneral_append,
    booleanMaioranaMcFarlandGeneral_append,
    booleanMaioranaMcFarlandGeneral_append]
  simp only [binaryMapDerivative, FABL.booleanDerivative,
    FABL.f₂DotProduct, add_dotProduct, dotProduct_add]
  abel

/-- Carlet's displayed pointwise derivative identity. -/
theorem booleanDerivative_booleanMaioranaMcFarlandGeneral_append_apply
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a x : FABL.F₂Cube r) (b y : FABL.F₂Cube s) :
    FABL.booleanDerivative (booleanMaioranaMcFarlandGeneral φ g)
        (Fin.append a b) (Fin.append x y) =
      FABL.f₂DotProduct x (binaryMapDerivative φ b y) +
        FABL.f₂DotProduct a (φ (y + b)) +
          FABL.booleanDerivative g b y := by
  rw [booleanDerivative_booleanMaioranaMcFarlandGeneral_append,
    booleanMaioranaMcFarlandGeneral_append]
  abel

/-- Nonvanishing map derivatives in all nonzero directions of weight at most
`l` are equivalent to every fiber having minimum distance greater than `l`. -/
theorem binaryMapDerivative_ne_zero_iff_fibersHaveMinimumDistanceGreaterThan
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) (l : ℕ) :
    (∀ b : FABL.F₂Cube s, b ≠ 0 →
      (FABL.f₂Support b).card ≤ l →
        ∀ y, binaryMapDerivative φ b y ≠ 0) ↔
      MaioranaMcFarlandFibersHaveMinimumDistanceGreaterThan φ l := by
  constructor
  · intro hderivative y z hyz hfiber
    by_contra hdistance
    have hle : (FABL.f₂Support (y + z)).card ≤ l :=
      Nat.le_of_not_gt hdistance
    have hdirection : y + z ≠ 0 := by
      intro hzero
      apply hyz
      exact (add_eq_zero_iff_eq_neg.mp hzero).trans
        (ZModModule.neg_eq_self z)
    apply hderivative (y + z) hdirection hle y
    have hyz' : y + (y + z) = z := by
      rw [← add_assoc, ZModModule.add_self, zero_add]
    simp only [binaryMapDerivative, hyz', hfiber, ZModModule.add_self]
  · intro hfibers b hb hweight y hzero
    have hyneq : y ≠ y + b := by
      intro hy
      apply hb
      apply add_left_cancel (a := y)
      simpa using hy.symm
    have hsame : φ y = φ (y + b) :=
      (add_eq_zero_iff_eq_neg.mp hzero).trans
        (ZModModule.neg_eq_self (φ (y + b)))
    have hdistance := hfibers hyneq hsame
    have hyb : y + (y + b) = b := by
      rw [← add_assoc, ZModModule.add_self, zero_add]
    rw [hyb] at hdistance
    exact (Nat.not_lt_of_ge hweight) hdistance

private theorem isBalanced_booleanMaioranaMcFarlandGeneral_zeroMap
    (h : BooleanFunction s) (hh : IsBalanced h) :
    IsBalanced
      (booleanMaioranaMcFarlandGeneral
        (0 : FABL.F₂Cube s → FABL.F₂Cube r) h) := by
  apply (isBalanced_iff_walshTransform_zero_eq_zero _).mpr
  have hzero :
      (0 : FABL.F₂Cube (r + s)) =
        Fin.append (0 : FABL.F₂Cube r) (0 : FABL.F₂Cube s) := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  rw [hzero, walshTransform_booleanMaioranaMcFarlandGeneral]
  have hhzero := (isBalanced_iff_walshTransform_zero_eq_zero h).mp hh
  rw [walshTransform] at hhzero
  simpa [maioranaMcFarlandFiberCharacterSum, walshTerm,
    FABL.f₂DotProduct] using congrArg (fun z : ℤ ↦ (2 ^ r : ℤ) * z) hhzero

/-- Carlet's Maiorana--McFarland sufficient condition for `PC(l)`. -/
theorem satisfiesPropagationCriterion_booleanMaioranaMcFarlandGeneral
    (l : ℕ)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hderivative :
      ∀ b : FABL.F₂Cube s, b ≠ 0 →
        (FABL.f₂Support b).card ≤ l →
          ∀ y, binaryMapDerivative φ b y ≠ 0)
    (hbalanced :
      ∀ a : FABL.F₂Cube r, a ≠ 0 →
        (FABL.f₂Support a).card ≤ l →
          IsBalanced (fun y ↦ FABL.f₂DotProduct a (φ y))) :
    SatisfiesPropagationCriterion l
      (booleanMaioranaMcFarlandGeneral φ g) := by
  intro d hd
  let p := (Fin.appendEquiv r s).symm d
  have hp : Fin.append p.1 p.2 = d :=
    (Fin.appendEquiv r s).apply_symm_apply d
  have hweight :
      (FABL.f₂Support p.1).card +
          (FABL.f₂Support p.2).card ≤ l := by
    rw [← card_f₂Support_append, hp]
    exact hd.2
  rw [← hp, booleanDerivative_booleanMaioranaMcFarlandGeneral_append]
  by_cases hb : p.2 = 0
  · have ha : p.1 ≠ 0 := by
      intro ha
      apply hd.1
      rw [← hp, ha, hb]
      funext i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
    have habalanced := hbalanced p.1 ha (by omega)
    simpa [binaryMapDerivative, hb, FABL.booleanDerivative,
      ZModModule.add_self] using
      isBalanced_booleanMaioranaMcFarlandGeneral_zeroMap
        (r := r) (h := fun y ↦ FABL.f₂DotProduct p.1 (φ y)) habalanced
  · apply isBalanced_booleanMaioranaMcFarlandGeneral
    intro y
    exact hderivative p.2 hb (by omega) y

/-- The fiber-distance form of Carlet's Maiorana--McFarland propagation
construction. -/
theorem satisfiesPropagationCriterion_booleanMaioranaMcFarlandGeneral_of_fibers
    (l : ℕ)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hfibers :
      MaioranaMcFarlandFibersHaveMinimumDistanceGreaterThan φ l)
    (hbalanced :
      ∀ a : FABL.F₂Cube r, a ≠ 0 →
        (FABL.f₂Support a).card ≤ l →
          IsBalanced (fun y ↦ FABL.f₂DotProduct a (φ y))) :
    SatisfiesPropagationCriterion l
      (booleanMaioranaMcFarlandGeneral φ g) :=
  satisfiesPropagationCriterion_booleanMaioranaMcFarlandGeneral
    l φ g
      ((binaryMapDerivative_ne_zero_iff_fibersHaveMinimumDistanceGreaterThan
        φ l).mpr hfibers)
      hbalanced

end CryptBoolean
