/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandGeneral
public import CryptBoolean.Carlet.Chapter07.DirectSum

/-!
# Resilient Maiorana--McFarland functions

Carlet Chapter 7, Relations (59)--(60), and their basic resiliency consequences.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- Carlet Relation (59): the general Boolean-valued
Maiorana--McFarland function on two coordinate blocks. -/
def booleanMaioranaMcFarlandGeneral
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    BooleanFunction (r + s) :=
  fun z ↦
    let blocks := (Fin.appendEquiv r s).symm z
    FABL.f₂DotProduct blocks.1 (φ blocks.2) + g blocks.2

/-- Evaluation of a general Maiorana--McFarland function on its two
coordinate blocks. -/
@[simp] theorem booleanMaioranaMcFarlandGeneral_append
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (x : FABL.F₂Cube r) (y : FABL.F₂Cube s) :
    booleanMaioranaMcFarlandGeneral φ g (Fin.append x y) =
      FABL.f₂DotProduct x (φ y) + g y := by
  simp [booleanMaioranaMcFarlandGeneral]

/-- Carlet Relation (60): the raw Walsh spectrum of the general
Maiorana--McFarland function is its fiber character sum scaled by `2 ^ r`. -/
theorem walshTransform_booleanMaioranaMcFarlandGeneral
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    walshTransform (booleanMaioranaMcFarlandGeneral φ g) (Fin.append a b) =
      (2 ^ r : ℤ) * maioranaMcFarlandFiberCharacterSum φ g a b :=
  walshTransform_maioranaMcFarlandGeneral
    (booleanMaioranaMcFarlandGeneral φ g) φ g
    (booleanMaioranaMcFarlandGeneral_append φ g) a b

private theorem card_f₂Support_left_le_append
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    (FABL.f₂Support a).card ≤
      (FABL.f₂Support (Fin.append a b)).card := by
  apply Finset.card_le_card_of_injOn (Fin.castAdd s)
  · intro i hi
    exact (FABL.mem_f₂Support _ _).2 (by
      rw [Fin.append_left]
      exact (FABL.mem_f₂Support _ _).1 hi)
  · exact (Fin.castAdd_injective r s).injOn

private theorem f₂Support_nonempty_of_ne_zero
    (a : FABL.F₂Cube r) (ha : a ≠ 0) :
    (FABL.f₂Support a).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hsupport
  apply ha
  apply (FABL.f₂CubeEquivFinset r).injective
  change FABL.f₂Support a = FABL.f₂Support (0 : FABL.F₂Cube r)
  rw [hsupport]
  ext i
  simp [FABL.f₂Support]

/-- If every value of the frequency map has weight greater than `k`, the
general Maiorana--McFarland function is `k`-resilient. -/
theorem isResilient_booleanMaioranaMcFarlandGeneral
    (k : ℕ)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hφ : ∀ y, k < (FABL.f₂Support (φ y)).card) :
    IsResilient k (booleanMaioranaMcFarlandGeneral φ g) := by
  have hk_r : k < r := by
    apply (hφ 0).trans_le
    calc
      (FABL.f₂Support (φ 0)).card ≤
          (Finset.univ : Finset (Fin r)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = r := by simp
  have hn : 0 < r + s := by omega
  have hk : k < r + s := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    k (booleanMaioranaMcFarlandGeneral φ g) hn hk]
  intro u hu
  let blocks := (Fin.appendEquiv r s).symm u
  have hblocks : Fin.append blocks.1 blocks.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  rw [← hblocks,
    walshTransform_booleanMaioranaMcFarlandGeneral]
  have hnoFiber : ∀ y, φ y ≠ blocks.1 := by
    intro y hy
    have hleft :
        (FABL.f₂Support blocks.1).card ≤
          (FABL.f₂Support
            (Fin.append blocks.1 blocks.2)).card :=
      card_f₂Support_left_le_append _ _
    have hu' :
        (FABL.f₂Support
          (Fin.append blocks.1 blocks.2)).card ≤ k := by
      rw [hblocks]
      exact hu
    have hweight := hφ y
    rw [hy] at hweight
    exact (not_lt_of_ge (hleft.trans hu')) hweight
  simp [maioranaMcFarlandFiberCharacterSum, hnoFiber]

/-- Excluding zero from the image of the frequency map makes the general
Maiorana--McFarland function balanced. -/
theorem isBalanced_booleanMaioranaMcFarlandGeneral
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hφ : ∀ y, φ y ≠ 0) :
    IsBalanced (booleanMaioranaMcFarlandGeneral φ g) := by
  have hresilient :
      IsResilient 0 (booleanMaioranaMcFarlandGeneral φ g) := by
    apply isResilient_booleanMaioranaMcFarlandGeneral 0 φ g
    intro y
    exact Finset.card_pos.mpr (f₂Support_nonempty_of_ne_zero (φ y) (hφ y))
  exact hresilient.2

private theorem eq_zero_of_f₂Support_card_eq_zero
    (a : FABL.F₂Cube s) (ha : (FABL.f₂Support a).card = 0) :
    a = 0 := by
  have hsupport : FABL.f₂Support a = ∅ := Finset.card_eq_zero.mp ha
  apply (FABL.f₂CubeEquivFinset s).injective
  change FABL.f₂Support a = FABL.f₂Support (0 : FABL.F₂Cube s)
  rw [hsupport]
  ext i
  simp [FABL.f₂Support]

/-- If every frequency-map value has weight greater than `k` and the offset
has zero signed sum on every fiber, the construction is `(k + 1)`-resilient. -/
theorem isResilient_succ_booleanMaioranaMcFarlandGeneral
    (k : ℕ)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hs : 0 < s)
    (hφ : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hbalancedFiber :
      ∀ a, maioranaMcFarlandFiberCharacterSum φ g a 0 = 0) :
    IsResilient (k + 1) (booleanMaioranaMcFarlandGeneral φ g) := by
  have hk_r : k < r := by
    apply (hφ 0).trans_le
    calc
      (FABL.f₂Support (φ 0)).card ≤
          (Finset.univ : Finset (Fin r)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = r := by simp
  have hn : 0 < r + s := by omega
  have hk : k + 1 < r + s := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (k + 1) (booleanMaioranaMcFarlandGeneral φ g) hn hk]
  intro u hu
  let blocks := (Fin.appendEquiv r s).symm u
  have hblocks : Fin.append blocks.1 blocks.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  rw [← hblocks,
    walshTransform_booleanMaioranaMcFarlandGeneral]
  by_cases hleft : (FABL.f₂Support blocks.1).card ≤ k
  · have hnoFiber : ∀ y, φ y ≠ blocks.1 := by
      intro y hy
      have hweight := hφ y
      rw [hy] at hweight
      exact (not_lt_of_ge hleft) hweight
    simp [maioranaMcFarlandFiberCharacterSum, hnoFiber]
  · have htotal :
        (FABL.f₂Support blocks.1).card +
            (FABL.f₂Support blocks.2).card ≤ k + 1 := by
      rw [← card_f₂Support_append, hblocks]
      exact hu
    have hright :
        (FABL.f₂Support blocks.2).card = 0 := by
      omega
    have hb : blocks.2 = 0 :=
      eq_zero_of_f₂Support_card_eq_zero blocks.2 hright
    rw [hb, hbalancedFiber blocks.1, mul_zero]

/-- The cardinality of one fiber of a general Maiorana--McFarland frequency
map. -/
def maioranaMcFarlandFiberCardinality
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (a : FABL.F₂Cube r) : ℕ :=
  ((Finset.univ : Finset (FABL.F₂Cube s)).filter fun y ↦ φ y = a).card

/-- The largest fiber cardinality of a general Maiorana--McFarland frequency
map. -/
noncomputable def maxMaioranaMcFarlandFiberCardinality
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) : ℕ :=
  (Finset.univ : Finset (FABL.F₂Cube r)).sup'
    Finset.univ_nonempty (maioranaMcFarlandFiberCardinality φ)

/-- Every fiber cardinality is bounded by the largest fiber cardinality. -/
theorem maioranaMcFarlandFiberCardinality_le_max
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (a : FABL.F₂Cube r) :
    maioranaMcFarlandFiberCardinality φ a ≤
      maxMaioranaMcFarlandFiberCardinality φ := by
  unfold maxMaioranaMcFarlandFiberCardinality
  exact Finset.le_sup'
    (maioranaMcFarlandFiberCardinality φ) (Finset.mem_univ a)

/-- A fiber character sum is bounded by the cardinality of its fiber. -/
theorem maioranaMcFarlandFiberCharacterSum_natAbs_le_cardinality
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs ≤
      maioranaMcFarlandFiberCardinality φ a := by
  classical
  rw [maioranaMcFarlandFiberCharacterSum,
    maioranaMcFarlandFiberCardinality]
  calc
    (∑ y with φ y = a,
        bitSignInt (g y + FABL.f₂DotProduct b y)).natAbs ≤
        ∑ y with φ y = a,
          (bitSignInt (g y + FABL.f₂DotProduct b y)).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ _y with φ _y = a, 1 := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [natAbs_bitSignInt]
    _ = ((Finset.univ : Finset (FABL.F₂Cube s)).filter
          fun y ↦ φ y = a).card := by simp

/-- The largest raw Walsh magnitude of a general Maiorana--McFarland
function is bounded by `2 ^ r` times its largest fiber. -/
theorem maxWalshMagnitude_booleanMaioranaMcFarlandGeneral_le
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    maxWalshMagnitude (booleanMaioranaMcFarlandGeneral φ g) ≤
      2 ^ r * maxMaioranaMcFarlandFiberCardinality φ := by
  unfold maxWalshMagnitude
  apply Finset.sup'_le
  intro u _hu
  let blocks := (Fin.appendEquiv r s).symm u
  have hblocks : Fin.append blocks.1 blocks.2 = u :=
    (Fin.appendEquiv r s).apply_symm_apply u
  rw [← hblocks, walshTransform_booleanMaioranaMcFarlandGeneral,
    Int.natAbs_mul]
  norm_num
  exact
    (maioranaMcFarlandFiberCharacterSum_natAbs_le_cardinality
      φ g blocks.1 blocks.2).trans
        (maioranaMcFarlandFiberCardinality_le_max φ blocks.1)

/-- Division-free form of Carlet Relation (61). -/
theorem relation_61_booleanMaioranaMcFarlandGeneral
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    2 ^ (r + s) ≤
      2 * nonlinearity (booleanMaioranaMcFarlandGeneral φ g) +
        2 ^ r * maxMaioranaMcFarlandFiberCardinality φ := by
  rw [← two_mul_nonlinearity_add_maxWalshMagnitude
    (booleanMaioranaMcFarlandGeneral φ g)]
  exact Nat.add_le_add_left
    (maxWalshMagnitude_booleanMaioranaMcFarlandGeneral_le φ g) _

/-- Carlet Relation (61): the nonlinearity lower bound determined by the
largest fiber of the frequency map. -/
theorem nonlinearity_booleanMaioranaMcFarlandGeneral_lower_bound
    (hr : 0 < r)
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) :
    2 ^ (r + s - 1) -
        2 ^ (r - 1) * maxMaioranaMcFarlandFiberCardinality φ ≤
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) := by
  have hbound := relation_61_booleanMaioranaMcFarlandGeneral φ g
  have hrs : 0 < r + s := by omega
  have htotal :
      2 ^ (r + s) = 2 * 2 ^ (r + s - 1) := by
    conv_lhs => rw [show r + s = (r + s - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have hleft : 2 ^ r = 2 * 2 ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
    omega
  rw [htotal, hleft] at hbound
  have hmul :
      (2 * 2 ^ (r - 1)) * maxMaioranaMcFarlandFiberCardinality φ =
        2 * (2 ^ (r - 1) * maxMaioranaMcFarlandFiberCardinality φ) := by
    simp [mul_assoc]
  rw [hmul] at hbound
  have hhalf :
      2 ^ (r + s - 1) ≤
        nonlinearity (booleanMaioranaMcFarlandGeneral φ g) +
          2 ^ (r - 1) * maxMaioranaMcFarlandFiberCardinality φ := by
    omega
  exact Nat.sub_le_iff_le_add.mpr (by
    simpa [add_comm] using hhalf)

end CryptBoolean
