/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandCounting
public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarland
public import CryptBoolean.Carlet.Chapter07.MaximumCorrelation

/-!
# Counting resilient Maiorana--McFarland construction data

Carlet Section 7.6: exact counts for the parameter pairs in Relation (59),
together with the corrected range of the stated balanced-data upper bound.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s m : ℕ}

/-- The frequency-map and Boolean-offset data in the general
Maiorana--McFarland construction. -/
abbrev GeneralMaioranaMcFarlandParameters (r s : ℕ) :=
  (FABL.F₂Cube s → FABL.F₂Cube r) × BooleanFunction s

/-- A pointwise constraint on the frequency map is equivalent to choosing
one constrained frequency independently at every input, together with an
unconstrained Boolean offset. -/
def pointwiseConstrainedGeneralMaioranaMcFarlandParametersEquiv
    (P : FABL.F₂Cube r → Prop) :
    {p : GeneralMaioranaMcFarlandParameters r s //
        ∀ y, P (p.1 y)} ≃
      (FABL.F₂Cube s → {a : FABL.F₂Cube r // P a}) ×
        BooleanFunction s :=
  Equiv.prodSubtypeFstEquivSubtypeProd.trans
    (Equiv.prodCongr Equiv.subtypePiEquivPi (Equiv.refl _))

/-- The cardinality of pointwise-constrained Relation (59) construction data
is the corresponding one-fiber count, including the free offset bit, raised
to the number of inputs. -/
theorem card_pointwiseConstrainedGeneralMaioranaMcFarlandParameters
    (P : FABL.F₂Cube r → Prop) [DecidablePred P] :
    Fintype.card
        {p : GeneralMaioranaMcFarlandParameters r s //
          ∀ y, P (p.1 y)} =
      (2 * Fintype.card {a : FABL.F₂Cube r // P a}) ^ (2 ^ s) := by
  classical
  rw [Fintype.card_congr
      (pointwiseConstrainedGeneralMaioranaMcFarlandParametersEquiv P),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fun]
  norm_num [BooleanFunction, card_f₂Cube, ← mul_pow, mul_comm]

/-- The punctured `r`-dimensional binary cube has `2^r - 1` elements. -/
theorem card_nonzero_f₂Cube (r : ℕ) :
    Fintype.card {a : FABL.F₂Cube r // a ≠ 0} = 2 ^ r - 1 := by
  classical
  rw [Fintype.card_subtype_compl
    (fun a : FABL.F₂Cube r ↦ a = 0)]
  simp

/-- The number of binary frequencies of weight greater than `m` is the upper
binomial tail. -/
theorem card_f₂Cube_weight_gt_eq_sum_choose (r m : ℕ) :
    Fintype.card
        {a : FABL.F₂Cube r // m < (FABL.f₂Support a).card} =
      ∑ i ∈ Finset.Icc (m + 1) r, r.choose i := by
  classical
  rw [Fintype.card_subtype]
  simpa using
    (card_highWeightFrequenciesSupportedIn_eq_sum_choose
      (Finset.univ : Finset (Fin r)) m)

/-- The exact number of Relation (59) construction pairs whose frequency map
is nonzero at every input. -/
theorem card_nonzeroGeneralMaioranaMcFarlandParameters (r s : ℕ) :
    Fintype.card
        {p : GeneralMaioranaMcFarlandParameters r s //
          ∀ y, p.1 y ≠ 0} =
      (2 ^ (r + 1) - 2) ^ (2 ^ s) := by
  rw [card_pointwiseConstrainedGeneralMaioranaMcFarlandParameters
      (r := r) (s := s) (P := fun a ↦ a ≠ 0),
    card_nonzero_f₂Cube]
  congr 1
  rw [pow_succ]
  omega

/-- The exact number of Relation (59) construction pairs whose frequency-map
values all have weight greater than `m`. -/
theorem card_highWeightGeneralMaioranaMcFarlandParameters
    (r s m : ℕ) :
    Fintype.card
        {p : GeneralMaioranaMcFarlandParameters r s //
          ∀ y, m < (FABL.f₂Support (p.1 y)).card} =
      (2 * (∑ i ∈ Finset.Icc (m + 1) r, r.choose i)) ^ (2 ^ s) := by
  rw [card_pointwiseConstrainedGeneralMaioranaMcFarlandParameters
      (r := r) (s := s)
      (P := fun a ↦ m < (FABL.f₂Support a).card),
    card_f₂Cube_weight_gt_eq_sum_choose]

/-- For every `k ≥ 2`, the elementary exponential estimate
`k + 2 ≤ 2^k` holds. -/
private theorem add_two_le_two_pow (k : ℕ) (hk : 2 ≤ k) :
    k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      omega

/-- The one-fiber balanced-data count satisfies Carlet's claimed exponential
bound when `r = 1` or `r ≥ 3`. -/
private theorem nonzeroGeneralMaioranaMcFarlandFiberCount_le
    (r : ℕ) (hr : r = 1 ∨ 3 ≤ r) :
    2 ^ (r + 1) - 2 ≤ 2 ^ (2 ^ (r - 1)) := by
  rcases hr with rfl | hr
  · norm_num
  · have hexponent : r + 1 ≤ 2 ^ (r - 1) := by
      have h := add_two_le_two_pow (r - 1) (by omega)
      omega
    exact (Nat.sub_le _ _).trans
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hexponent)

/-- Corrected form of Carlet's upper bound: for `r = 1` or `r ≥ 3`, the
number of everywhere-nonzero Relation (59) construction pairs is at most
`2^(2^(r+s-1))`. -/
theorem card_nonzeroGeneralMaioranaMcFarlandParameters_le
    (r s : ℕ) (hr : r = 1 ∨ 3 ≤ r) :
    Fintype.card
        {p : GeneralMaioranaMcFarlandParameters r s //
          ∀ y, p.1 y ≠ 0} ≤
      2 ^ (2 ^ (r + s - 1)) := by
  rw [card_nonzeroGeneralMaioranaMcFarlandParameters]
  calc
    (2 ^ (r + 1) - 2) ^ (2 ^ s) ≤
        (2 ^ (2 ^ (r - 1))) ^ (2 ^ s) :=
      Nat.pow_le_pow_left
        (nonzeroGeneralMaioranaMcFarlandFiberCount_le r hr) _
    _ = 2 ^ (2 ^ (r + s - 1)) := by
      rw [← pow_mul]
      congr 2
      rw [show r + s - 1 = (r - 1) + s by omega, pow_add]

/-- Source correction: at `r = 2`, Carlet's stated upper bound is reversed
strictly for every `s`; the smallest instance is already `6 > 4`. -/
theorem card_nonzeroGeneralMaioranaMcFarlandParameters_sourceBound_lt_at_two
    (s : ℕ) :
    2 ^ (2 ^ (2 + s - 1)) <
      Fintype.card
        {p : GeneralMaioranaMcFarlandParameters 2 s //
          ∀ y, p.1 y ≠ 0} := by
  rw [card_nonzeroGeneralMaioranaMcFarlandParameters]
  have hleft : 2 ^ (2 ^ (2 + s - 1)) = 4 ^ (2 ^ s) := by
    rw [show 2 + s - 1 = s + 1 by omega, pow_succ]
    rw [mul_comm, pow_mul]
    norm_num
  rw [hleft]
  norm_num
  exact Nat.pow_lt_pow_left (by omega) (by positivity)

end CryptBoolean
