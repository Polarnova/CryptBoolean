/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.TraceMonomialDegree
public import CryptBoolean.Carlet.Chapter04.FastAlgebraic
public import Mathlib.Data.Int.CardIntervalMod

/-!
# Algebraic immunity of trace power functions

The Nawaz--Gong--Gupta multiplier and its cyclic binary run bound from
Carlet Chapter 9.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable section

/-- A Boolean trace-power function in fixed finite-field coordinates. -/
def tracePowerFunction {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n) (d : ℕ) : BooleanFunction n :=
  fun x ↦ absoluteTrace n (a * (θ x) ^ d)

private theorem absoluteTrace_mul_absoluteTrace
    {n : ℕ} (hn : 0 < n) (A B : BinaryGaloisField n) :
    absoluteTrace n A * absoluteTrace n B =
      ∑ s ∈ Finset.range n, absoluteTrace n (B * A ^ (2 ^ s)) := by
  calc
    absoluteTrace n A * absoluteTrace n B =
        absoluteTrace n ((absoluteTrace n A) • B) := by
      exact ((absoluteTrace n).map_smul (absoluteTrace n A) B).symm
    _ = absoluteTrace n
        (algebraMap FABL.𝔽₂ (BinaryGaloisField n) (absoluteTrace n A) * B) := by
      rw [Algebra.smul_def]
    _ = absoluteTrace n ((∑ s ∈ Finset.range n, A ^ (2 ^ s)) * B) := by
      rw [algebraMap_absoluteTrace_eq_sum_frobenius (Nat.ne_of_gt hn)]
    _ = absoluteTrace n (∑ s ∈ Finset.range n, B * A ^ (2 ^ s)) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = ∑ s ∈ Finset.range n, absoluteTrace n (B * A ^ (2 ^ s)) := by
      exact map_sum (absoluteTrace n) _ _

/-- The number of cyclic one-runs in the canonical `n`-bit representative of
an exponent modulo `2^n-1`. -/
def cyclicOneRunCount (n d : ℕ) : ℕ :=
  let k := d % (2 ^ n - 1)
  ∑ i : Fin n, if k.testBit i && !(k.testBit (finRotate n i)) then 1 else 0

private theorem cyclicOneRunCount_of_lt {n d : ℕ}
    (hd : d < 2 ^ n - 1) :
    cyclicOneRunCount n d =
      ∑ i : Fin n, if d.testBit i && !(d.testBit (finRotate n i)) then 1 else 0 := by
  rw [cyclicOneRunCount, Nat.mod_eq_of_lt hd]

private theorem cyclicOneRunCount_rotateBinaryExponent
    {n d : ℕ} (hn : 0 < n) (hd : d < 2 ^ n - 1) :
    cyclicOneRunCount n (rotateBinaryExponent n d) = cyclicOneRunCount n d := by
  rw [cyclicOneRunCount_of_lt
    (by
      calc
        rotateBinaryExponent n d =
            rotateBinaryExponent n (binaryCyclicExponent n d 0) := by
              simp [binaryCyclicExponent, Nat.mod_eq_of_lt hd]
        _ = binaryCyclicExponent n d 1 :=
          (binaryCyclicExponent_succ_eq_rotate n d 0 hn).symm
        _ < 2 ^ n - 1 := binaryCyclicExponent_lt n d hn 1),
    cyclicOneRunCount_of_lt hd]
  have hrewrite :
      (∑ i : Fin n,
        if (rotateBinaryExponent n d).testBit i &&
            !((rotateBinaryExponent n d).testBit (finRotate n i)) then 1 else 0) =
        ∑ i : Fin n,
          if d.testBit ((finRotate n).symm i) && !(d.testBit i) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [testBit_rotateBinaryExponent, testBit_rotateBinaryExponent,
      Equiv.symm_apply_apply]
  rw [hrewrite]
  have hsum := Equiv.sum_comp (finRotate n).symm
    (fun i : Fin n ↦ if d.testBit i && !(d.testBit (finRotate n i)) then 1 else 0)
  simpa only [Equiv.apply_symm_apply] using hsum

/-- Cyclic Frobenius rotation preserves the number of cyclic one-runs. -/
theorem cyclicOneRunCount_binaryCyclicExponent
    {n d s : ℕ} (hn : 0 < n) (hd : d < 2 ^ n - 1) :
    cyclicOneRunCount n (binaryCyclicExponent n d s) = cyclicOneRunCount n d := by
  induction s with
  | zero => simp [binaryCyclicExponent, Nat.mod_eq_of_lt hd]
  | succ s ih =>
      rw [binaryCyclicExponent_succ_eq_rotate n d s hn,
        cyclicOneRunCount_rotateBinaryExponent hn
          (binaryCyclicExponent_lt n d hn s), ih]

/-- Every nonzero canonical exponent has a nonempty cyclic one-run. -/
theorem cyclicOneRunCount_pos {n d : ℕ} (hn : 0 < n)
    (hd0 : 0 < d) (hd : d < 2 ^ n - 1) :
    0 < cyclicOneRunCount n d := by
  letI : NeZero n := ⟨hn.ne'⟩
  by_contra hnot
  have hzero : cyclicOneRunCount n d = 0 := Nat.eq_zero_of_not_pos hnot
  rw [cyclicOneRunCount_of_lt hd] at hzero
  have hterm (i : Fin n) :
      (if d.testBit i && !(d.testBit (finRotate n i)) then 1 else 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hzero i
      (Finset.mem_univ i)
  have hstep (i : Fin n) (hi : d.testBit i = true) :
      d.testBit (finRotate n i) = true := by
    by_contra hnext
    have hnextFalse : d.testBit (finRotate n i) = false :=
      Bool.eq_false_of_not_eq_true hnext
    have ht := hterm i
    rw [hi, hnextFalse] at ht
    contradiction
  have hexists : ∃ i : Fin n, d.testBit i = true := by
    by_contra hnone
    push Not at hnone
    have hall (i : ℕ) : d.testBit i = false := by
      by_cases hi : i < n
      · exact Bool.eq_false_iff.mpr (hnone ⟨i, hi⟩)
      · exact Nat.testBit_eq_false_of_lt
          ((hd.trans (Nat.sub_lt (Nat.two_pow_pos n) (by omega))).trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))
    exact (Nat.ne_of_gt hd0) (Nat.zero_of_testBit_eq_false hall)
  obtain ⟨i₀, hi₀⟩ := hexists
  have horbit (k : ℕ) :
      d.testBit ((finRotate n)^[k] i₀) = true := by
    induction k with
    | zero => simpa using hi₀
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hstep _ ih
  have hallFin (j : Fin n) : d.testBit j = true := by
    let k : Fin n := j - i₀
    have heq : ((finRotate n)^[k.1]) i₀ = j := by
      rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
      dsimp [k]
      calc
        i₀ + (j - i₀) = (j - i₀) + i₀ := add_comm _ _
        _ = j := sub_add_cancel j i₀
    rw [← heq]
    exact horbit k.1
  have hdeq : d = 2 ^ n - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · rw [hallFin ⟨i, hi⟩]
      rw [Nat.testBit_two_pow_sub_succ
        (x := 0) (Nat.two_pow_pos n) i]
      simp [hi]
    · have hdpow : d < 2 ^ n :=
        hd.trans (Nat.sub_lt (Nat.two_pow_pos n) (by omega))
      rw [Nat.testBit_eq_false_of_lt
        (hdpow.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))]
      exact (Nat.testBit_eq_false_of_lt
        ((Nat.sub_lt (Nat.two_pow_pos n) (by omega)).trans_le
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))).symm
  exact (Nat.ne_of_lt hd) hdeq

/-- The nonzero bit positions of the Nawaz--Gong--Gupta multiplier. If
`k = n mod ⌊√n⌋` vanishes these are `0,⌊√n⌋,…`; otherwise they are
`0,k,k+⌊√n⌋,…`, exactly as in the cited construction. -/
def traceRunMultiplierPositions (n : ℕ) : List ℕ :=
  let l := Nat.sqrt n
  let q := n / l
  let k := n % l
  if k = 0 then
    (List.range q).map fun i ↦ i * l
  else
    0 :: (List.range q).map fun i ↦ k + i * l

/-- The Nawaz--Gong--Gupta multiplier exponent. -/
def traceRunMultiplierExponent (n : ℕ) : ℕ :=
  ((traceRunMultiplierPositions n).map fun i ↦ 2 ^ i).sum

private theorem traceRunMultiplierPositions_sortedLT {n : ℕ} (hn : 0 < n) :
    (traceRunMultiplierPositions n).SortedLT := by
  have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have htail :
      ((List.range (n / Nat.sqrt n)).map fun i ↦ i * Nat.sqrt n).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    exact (List.sortedLT_iff_pairwise.mp (List.sortedLT_range _)).imp
      (fun hij ↦ Nat.mul_lt_mul_of_pos_right hij hl)
  have hshift :
      ((List.range (n / Nat.sqrt n)).map
          fun i ↦ n % Nat.sqrt n + i * Nat.sqrt n).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    exact (List.sortedLT_iff_pairwise.mp (List.sortedLT_range _)).imp
      (fun hij ↦ Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hl) _)
  rw [traceRunMultiplierPositions]
  split_ifs with hk
  · exact htail
  · rw [List.sortedLT_iff_pairwise, List.pairwise_cons]
    refine ⟨?_, List.sortedLT_iff_pairwise.mp hshift⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact Nat.add_pos_left (Nat.pos_of_ne_zero hk) _

theorem bitIndices_traceRunMultiplierExponent {n : ℕ} (hn : 0 < n) :
    (traceRunMultiplierExponent n).bitIndices = traceRunMultiplierPositions n := by
  exact Nat.bitIndices_sum_map_two_pow (traceRunMultiplierPositions_sortedLT hn)

private theorem traceRunMultiplierPositions_lt {n i : ℕ} (hn : 0 < n)
    (hi : i ∈ traceRunMultiplierPositions n) : i < n := by
  have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  rw [traceRunMultiplierPositions] at hi
  split_ifs at hi with hk
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hjq : j < n / Nat.sqrt n := List.mem_range.mp hj
    have hmul : (j + 1) * Nat.sqrt n ≤ (n / Nat.sqrt n) * Nat.sqrt n :=
      Nat.mul_le_mul_right _ hjq
    have hdiv := Nat.div_mul_le_self n (Nat.sqrt n)
    exact (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self j) hl).trans_le
      (hmul.trans hdiv)
  · rcases List.mem_cons.mp hi with rfl | hi
    · exact hn
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hjq : j < n / Nat.sqrt n := List.mem_range.mp hj
      have hmul : j * Nat.sqrt n < (n / Nat.sqrt n) * Nat.sqrt n :=
        Nat.mul_lt_mul_of_pos_right hjq hl
      have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
      calc
        n % Nat.sqrt n + j * Nat.sqrt n <
            n % Nat.sqrt n + (n / Nat.sqrt n) * Nat.sqrt n :=
          Nat.add_lt_add_left hmul _
        _ = n := by omega

@[simp] theorem testBit_traceRunMultiplierExponent {n i : ℕ} (hn : 0 < n) :
    (traceRunMultiplierExponent n).testBit i ↔
      i ∈ traceRunMultiplierPositions n := by
  rw [← Nat.mem_bitIndices, bitIndices_traceRunMultiplierExponent hn]

theorem traceRunMultiplierExponent_lt_two_pow {n : ℕ} (hn : 0 < n) :
    traceRunMultiplierExponent n < 2 ^ n := by
  let e := Nat.ofBits fun i : Fin n ↦ decide ((i : ℕ) ∈ traceRunMultiplierPositions n)
  have heq : traceRunMultiplierExponent n = e := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      have hleft : (traceRunMultiplierExponent n).testBit i =
          decide (i ∈ traceRunMultiplierPositions n) := by
        rw [Bool.eq_iff_iff, decide_eq_true_eq]
        simpa [j] using testBit_traceRunMultiplierExponent (n := n) (i := i) hn
      rw [hleft]
      simpa [e] using
        (Nat.testBit_ofBits_lt
          (fun j : Fin n ↦ decide ((j : ℕ) ∈ traceRunMultiplierPositions n)) i hi).symm
    · have hleft : (traceRunMultiplierExponent n).testBit i = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        exact hi (traceRunMultiplierPositions_lt hn
          ((testBit_traceRunMultiplierExponent hn).mp htrue))
      have hright : e.testBit i = false :=
        Nat.testBit_eq_false_of_lt
          ((Nat.ofBits_lt_two_pow _).trans_le
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))
      rw [hleft, hright]
  rw [heq]
  exact Nat.ofBits_lt_two_pow _

/-- The multiplier has precisely `⌈n/⌊√n⌋⌉` nonzero binary digits. -/
theorem binaryWeight_traceRunMultiplierExponent {n : ℕ} (hn : 0 < n) :
    binaryWeight (traceRunMultiplierExponent n) = n ⌈/⌉ Nat.sqrt n := by
  have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  rw [binaryWeight, bitIndices_traceRunMultiplierExponent hn,
    traceRunMultiplierPositions]
  split_ifs with hk
  · simp only [List.length_map, List.length_range]
    apply le_antisymm
    · exact (floorDiv_le_ceilDiv (α := ℕ) (β := ℕ)
        (a := Nat.sqrt n) (b := n))
    · apply (ceilDiv_le_iff_le_mul hl).mpr
      have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
      have hcomm : Nat.sqrt n * (n / Nat.sqrt n) =
          (n / Nat.sqrt n) * Nat.sqrt n := Nat.mul_comm _ _
      omega
  · simp only [List.length_cons, List.length_map, List.length_range]
    apply le_antisymm
    · apply Nat.succ_le_of_lt
      by_contra hnot
      have hceil : n ⌈/⌉ Nat.sqrt n ≤ n / Nat.sqrt n := Nat.le_of_not_gt hnot
      have hnle : n ≤ Nat.sqrt n * (n / Nat.sqrt n) :=
        (ceilDiv_le_iff_le_mul hl).mp hceil
      have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
      have hkpos : 0 < n % Nat.sqrt n := Nat.pos_of_ne_zero hk
      have hcomm : Nat.sqrt n * (n / Nat.sqrt n) =
          (n / Nat.sqrt n) * Nat.sqrt n := Nat.mul_comm _ _
      omega
    · have hmodlt := Nat.mod_lt n hl
      apply (ceilDiv_le_iff_le_mul hl).mpr
      have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
      calc
        n = (n / Nat.sqrt n) * Nat.sqrt n + n % Nat.sqrt n := hdecomp.symm
        _ ≤ (n / Nat.sqrt n) * Nat.sqrt n + Nat.sqrt n :=
          Nat.add_le_add_left (Nat.le_of_lt hmodlt) _
        _ = Nat.sqrt n * (n / Nat.sqrt n + 1) := by ring

private def binaryCarryBit (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

private def binarySumBit (a b c : Bool) : Bool :=
  (a.xor b).xor c

private theorem binary_full_adder_identity (a b c : Bool) :
    a.toNat + b.toNat + c.toNat =
      (binarySumBit a b c).toNat + 2 * (binaryCarryBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

private def binaryCarryIn (x y : ℕ) (c : Bool) : ℕ → Bool
  | 0 => c
  | i + 1 => binaryCarryBit (x.testBit i) (y.testBit i) (binaryCarryIn x y c i)

@[simp] private theorem binaryCarryIn_zero (x y : ℕ) (c : Bool) :
    binaryCarryIn x y c 0 = c := rfl

@[simp] private theorem binaryCarryIn_succ (x y : ℕ) (c : Bool) (i : ℕ) :
    binaryCarryIn x y c (i + 1) =
      binaryCarryBit (x.testBit i) (y.testBit i) (binaryCarryIn x y c i) := rfl

private def binaryAdditionBit (x y : ℕ) (c : Bool) (i : ℕ) : Bool :=
  binarySumBit (x.testBit i) (y.testBit i) (binaryCarryIn x y c i)

private theorem binary_addition_bit_identity (x y : ℕ) (c : Bool) (i : ℕ) :
    (x.testBit i).toNat + (y.testBit i).toNat + (binaryCarryIn x y c i).toNat =
      (binaryAdditionBit x y c i).toNat +
        2 * (binaryCarryIn x y c (i + 1)).toNat := by
  exact binary_full_adder_identity _ _ _

private theorem sum_binaryCarryIn_succ_add_initial
    (x y n : ℕ) (c : Bool) :
    (∑ i ∈ Finset.range n, (binaryCarryIn x y c (i + 1)).toNat) + c.toNat =
      (∑ i ∈ Finset.range n, (binaryCarryIn x y c i).toNat) +
        (binaryCarryIn x y c n).toNat := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

private theorem binary_addition_weight_identity_of_cyclic_carry
    (x y n : ℕ) (c : Bool)
    (hcyclic : binaryCarryIn x y c n = c) :
    (∑ i ∈ Finset.range n, (binaryAdditionBit x y c i).toNat) +
        ∑ i ∈ Finset.range n, (binaryCarryIn x y c (i + 1)).toNat =
      (∑ i ∈ Finset.range n, (x.testBit i).toNat) +
        ∑ i ∈ Finset.range n, (y.testBit i).toNat := by
  have hlocal :
      (∑ i ∈ Finset.range n, ((x.testBit i).toNat + (y.testBit i).toNat +
        (binaryCarryIn x y c i).toNat)) =
        ∑ i ∈ Finset.range n, ((binaryAdditionBit x y c i).toNat +
          2 * (binaryCarryIn x y c (i + 1)).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact binary_addition_bit_identity x y c i
  simp only [Finset.sum_add_distrib] at hlocal
  rw [← Finset.mul_sum] at hlocal
  have hshift := sum_binaryCarryIn_succ_add_initial x y n c
  rw [hcyclic] at hshift
  omega

private def binaryAdditionNat (n x y : ℕ) (c : Bool) : ℕ :=
  Nat.ofBits fun i : Fin n ↦ binaryAdditionBit x y c i

private theorem binaryAdditionNat_lt_two_pow (n x y : ℕ) (c : Bool) :
    binaryAdditionNat n x y c < 2 ^ n := by
  exact Nat.ofBits_lt_two_pow _

private theorem sum_testBit_mul_two_pow_eq {n x : ℕ} (hx : x < 2 ^ n) :
    (∑ i ∈ Finset.range n, (x.testBit i).toNat * 2 ^ i) = x := by
  calc
    _ = ∑ i : Fin n, (x.testBit i).toNat * 2 ^ (i : ℕ) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun i ↦ (x.testBit i).toNat * 2 ^ i) n).symm
    _ = Nat.ofBits (fun i : Fin n ↦ x.testBit i) := (ofBits_eq_sum _).symm
    _ = x := by rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hx]

private theorem binaryAdditionNat_eq_sum (n x y : ℕ) (c : Bool) :
    binaryAdditionNat n x y c =
      ∑ i ∈ Finset.range n, (binaryAdditionBit x y c i).toNat * 2 ^ i := by
  rw [binaryAdditionNat, ofBits_eq_sum]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ (binaryAdditionBit x y c i).toNat * 2 ^ i) n

private theorem sum_binaryCarryIn_succ_mul_two_pow_add_initial
    (x y n : ℕ) (c : Bool) :
    (∑ i ∈ Finset.range n,
        (binaryCarryIn x y c (i + 1)).toNat * 2 ^ (i + 1)) + c.toNat =
      (∑ i ∈ Finset.range n, (binaryCarryIn x y c i).toNat * 2 ^ i) +
        (binaryCarryIn x y c n).toNat * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

private theorem binaryAdditionNat_add_finalCarry_mul_two_pow
    {n x y : ℕ} (c : Bool) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    binaryAdditionNat n x y c + (binaryCarryIn x y c n).toNat * 2 ^ n =
      x + y + c.toNat := by
  have hlocal :
      (∑ i ∈ Finset.range n,
        (((x.testBit i).toNat + (y.testBit i).toNat +
          (binaryCarryIn x y c i).toNat) * 2 ^ i)) =
        ∑ i ∈ Finset.range n,
          (((binaryAdditionBit x y c i).toNat +
            2 * (binaryCarryIn x y c (i + 1)).toNat) * 2 ^ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [binary_addition_bit_identity]
  simp only [add_mul, Finset.sum_add_distrib] at hlocal
  have hshift := sum_binaryCarryIn_succ_mul_two_pow_add_initial x y n c
  rw [sum_testBit_mul_two_pow_eq hx, sum_testBit_mul_two_pow_eq hy] at hlocal
  rw [binaryAdditionNat_eq_sum]
  have hpow :
      (∑ i ∈ Finset.range n,
        2 * (binaryCarryIn x y c (i + 1)).toNat * 2 ^ i) =
      ∑ i ∈ Finset.range n,
        (binaryCarryIn x y c (i + 1)).toNat * 2 ^ (i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
    ring
  rw [hpow] at hlocal
  omega

private def cyclicAdditionInitialCarry (n x y : ℕ) : Bool :=
  decide (2 ^ n ≤ x + y)

/-- The positive representative of `x+y` modulo `2^n-1`, for bounded
positive summands. -/
def positiveCyclicSum (n x y : ℕ) : ℕ :=
  if 2 ^ n ≤ x + y then x + y - (2 ^ n - 1) else x + y

private theorem positiveCyclicSum_pos {n x y : ℕ} (hxy : 0 < x + y) :
    0 < positiveCyclicSum n x y := by
  rw [positiveCyclicSum]
  split_ifs with h
  · have hpow := Nat.two_pow_pos n
    omega
  · exact hxy

/-- Positive cyclic reduction of an exponent preserves finite-field powers,
including at zero. -/
theorem pow_positiveCyclicSum {n x y : ℕ} (hn : 0 < n)
    (hxy : 0 < x + y) (z : BinaryGaloisField n) :
    z ^ positiveCyclicSum n x y = z ^ (x + y) := by
  by_cases hz : z = 0
  · subst z
    rw [zero_pow (Nat.ne_of_gt (positiveCyclicSum_pos hxy)),
      zero_pow (Nat.ne_of_gt hxy)]
  · letI := Fintype.ofFinite (BinaryGaloisField n)
    have hcard : Fintype.card (BinaryGaloisField n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 n (Nat.ne_of_gt hn)
    have horder : z ^ (2 ^ n - 1) = 1 := by
      rw [← hcard]
      exact FiniteField.pow_card_sub_one_eq_one z hz
    rw [positiveCyclicSum]
    split_ifs with hoverflow
    · have hmodle : 2 ^ n - 1 ≤ x + y := by omega
      conv_rhs => rw [show x + y = x + y - (2 ^ n - 1) + (2 ^ n - 1) by
        omega]
      rw [pow_add, horder, mul_one]
    · rfl

private theorem binaryCarryIn_cyclicAdditionInitialCarry
    {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    binaryCarryIn x y (cyclicAdditionInitialCarry n x y) n =
      cyclicAdditionInitialCarry n x y := by
  by_cases hsum : 2 ^ n ≤ x + y
  · simp only [cyclicAdditionInitialCarry, hsum, decide_true]
    by_contra hcarry
    have hcarryFalse : binaryCarryIn x y true n = false := by
      cases h : binaryCarryIn x y true n
      · rfl
      · exact (hcarry h).elim
    have hadd := binaryAdditionNat_add_finalCarry_mul_two_pow true hx hy
    rw [hcarryFalse] at hadd
    simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, add_zero] at hadd
    have hlt := binaryAdditionNat_lt_two_pow n x y true
    omega
  · simp only [cyclicAdditionInitialCarry, hsum, decide_false]
    by_contra hcarry
    have hcarryTrue : binaryCarryIn x y false n = true := by
      cases h : binaryCarryIn x y false n
      · exact (hcarry h).elim
      · rfl
    have hadd := binaryAdditionNat_add_finalCarry_mul_two_pow false hx hy
    rw [hcarryTrue] at hadd
    simp only [Bool.toNat_false, Bool.toNat_true, one_mul, add_zero] at hadd
    omega

private theorem binaryAdditionNat_cyclic_eq_positiveCyclicSum
    {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    binaryAdditionNat n x y (cyclicAdditionInitialCarry n x y) =
      positiveCyclicSum n x y := by
  have hadd := binaryAdditionNat_add_finalCarry_mul_two_pow
    (cyclicAdditionInitialCarry n x y) hx hy
  rw [binaryCarryIn_cyclicAdditionInitialCarry hx hy] at hadd
  by_cases hsum : 2 ^ n ≤ x + y
  · simp only [cyclicAdditionInitialCarry, hsum, decide_true,
      Bool.toNat_true, one_mul] at hadd
    rw [positiveCyclicSum, if_pos hsum]
    simp only [cyclicAdditionInitialCarry, hsum, decide_true]
    have hpow := Nat.two_pow_pos n
    omega
  · simp only [cyclicAdditionInitialCarry, hsum, decide_false,
      Bool.toNat_false, zero_mul, add_zero] at hadd
    rw [positiveCyclicSum, if_neg hsum]
    simp only [cyclicAdditionInitialCarry, hsum, decide_false]
    exact hadd

private theorem positiveCyclicSum_lt_two_pow
    {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    positiveCyclicSum n x y < 2 ^ n := by
  rw [← binaryAdditionNat_cyclic_eq_positiveCyclicSum hx hy]
  exact binaryAdditionNat_lt_two_pow _ _ _ _

private theorem exists_traceRunMultiplierPosition_le
    {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    ∃ p ∈ traceRunMultiplierPositions n,
      p ≤ i ∧ i - p < Nat.sqrt n := by
  have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  rw [traceRunMultiplierPositions]
  by_cases hk : n % Nat.sqrt n = 0
  · simp only [hk, if_pos]
    let j := i / Nat.sqrt n
    refine ⟨j * Nat.sqrt n, ?_, Nat.div_mul_le_self _ _, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨j, List.mem_range.mpr ?_, rfl⟩
      rw [Nat.div_lt_iff_lt_mul hl]
      have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
      omega
    · have hmod := Nat.mod_lt i hl
      rw [Nat.mod_eq_sub_mul_div] at hmod
      simpa [j, Nat.mul_comm] using hmod
  · simp only [hk]
    by_cases hik : i < n % Nat.sqrt n
    · refine ⟨0, List.mem_cons_self, Nat.zero_le _, ?_⟩
      exact hik.trans (Nat.mod_lt n hl)
    · let j := (i - n % Nat.sqrt n) / Nat.sqrt n
      let p := n % Nat.sqrt n + j * Nat.sqrt n
      have hk_le_i : n % Nat.sqrt n ≤ i := Nat.le_of_not_gt hik
      have hmul := Nat.div_mul_le_self (i - n % Nat.sqrt n) (Nat.sqrt n)
      have hp_le : p ≤ i := by
        dsimp [p, j]
        omega
      refine ⟨p, ?_, hp_le, ?_⟩
      · apply List.mem_cons_of_mem
        apply List.mem_map.mpr
        refine ⟨j, List.mem_range.mpr ?_, rfl⟩
        rw [Nat.div_lt_iff_lt_mul hl]
        have hdecomp := Nat.div_add_mod' n (Nat.sqrt n)
        omega
      · have hmod := Nat.mod_lt (i - n % Nat.sqrt n) hl
        rw [Nat.mod_eq_sub_mul_div] at hmod
        have hsub : i - p =
            (i - n % Nat.sqrt n) -
              Nat.sqrt n * ((i - n % Nat.sqrt n) / Nat.sqrt n) := by
          dsimp [p, j]
          rw [← Nat.sub_sub, Nat.mul_comm]
        rw [hsub]
        exact hmod

private theorem binaryCarryIn_true_of_marker_of_all_true
    {x y p i : ℕ} {c : Bool} (hpi : p ≤ i)
    (hy : y.testBit p = true)
    (hx : ∀ j, p ≤ j → j ≤ i → x.testBit j = true) :
    binaryCarryIn x y c (i + 1) = true := by
  induction i, hpi using Nat.le_induction with
  | base =>
      rw [binaryCarryIn_succ, hx p le_rfl le_rfl, hy]
      simp [binaryCarryBit]
  | succ i hpi ih =>
      have ih' : binaryCarryIn x y c (i + 1) = true :=
        ih fun j hpj hji ↦ hx j hpj (hji.trans (Nat.le_succ i))
      rw [binaryCarryIn_succ,
        hx (i + 1) (hpi.trans (Nat.le_succ i)) (Nat.le_refl _), ih']
      simp [binaryCarryBit]

private theorem exists_false_true_between
    (b : ℕ → Bool) {p i : ℕ} (hpi : p < i)
    (hp : b p = false) (hi : b i = true) :
    ∃ j, p ≤ j ∧ j < i ∧ b j = false ∧ b (j + 1) = true := by
  induction i using Nat.strong_induction_on generalizing p with
  | h i ih =>
      by_cases hstep : p + 1 = i
      · subst i
        exact ⟨p, le_rfl, Nat.lt_succ_self p, hp, hi⟩
      · have hi0 : 0 < i := Nat.zero_lt_of_lt hpi
        let q := i - 1
        have hqi : q < i := by dsimp [q]; omega
        have hpq : p < q := by dsimp [q]; omega
        by_cases hq : b q = true
        · obtain ⟨j, hpj, hjq, hj0, hj1⟩ := ih q hqi hpq hp hq
          exact ⟨j, hpj, hjq.trans hqi, hj0, hj1⟩
        · have hsucc : q + 1 = i := by dsimp [q]; omega
          exact ⟨q, Nat.le_of_lt hpq, hqi, Bool.eq_false_of_not_eq_true hq,
            hsucc.symm ▸ hi⟩

private theorem exists_rise_near_uncarried_one
    {n x i : ℕ} {c : Bool} (hn : 0 < n) (hi : i < n)
    (hxi : x.testBit i = true)
    (hcarry : binaryCarryIn x (traceRunMultiplierExponent n) c (i + 1) = false) :
    ∃ j, j < i ∧ i - j < Nat.sqrt n ∧
      x.testBit j = false ∧ x.testBit (j + 1) = true := by
  obtain ⟨p, hpMarker, hpi, hdistance⟩ :=
    exists_traceRunMultiplierPosition_le hn hi
  have hy : (traceRunMultiplierExponent n).testBit p = true :=
    (testBit_traceRunMultiplierExponent hn).mpr hpMarker
  have hnotAll : ¬ ∀ j, p ≤ j → j ≤ i → x.testBit j = true := by
    intro hall
    have hpropagates :=
      binaryCarryIn_true_of_marker_of_all_true (c := c) hpi hy hall
    rw [hcarry] at hpropagates
    contradiction
  push Not at hnotAll
  obtain ⟨q, hpq, hqi, hq⟩ := hnotAll
  have hqfalse : x.testBit q = false := Bool.eq_false_of_not_eq_true hq
  have hq_lt_i : q < i := hqi.lt_of_ne fun heq ↦ by
    subst q
    rw [hxi] at hqfalse
    contradiction
  obtain ⟨j, hqj, hji, hj0, hj1⟩ :=
    exists_false_true_between (fun t ↦ x.testBit t) hq_lt_i hqfalse hxi
  refine ⟨j, hji, ?_, hj0, hj1⟩
  have hpj : p ≤ j := hpq.trans hqj
  omega

private def cyclicRiseCount (n x : ℕ) : ℕ :=
  ∑ i : Fin n, if !(x.testBit i) && x.testBit (finRotate n i) then 1 else 0

private theorem cyclicRiseCount_eq_cyclicFallCount (n x : ℕ) :
    cyclicRiseCount n x =
      ∑ i : Fin n, if x.testBit i && !(x.testBit (finRotate n i)) then 1 else 0 := by
  have hbit (a b : Bool) :
      (if !a && b then 1 else 0) + a.toNat =
        (if a && !b then 1 else 0) + b.toNat := by
    cases a <;> cases b <;> decide
  have hlocal :
      (∑ i : Fin n,
        ((if !(x.testBit i) && x.testBit (finRotate n i) then 1 else 0) +
          (x.testBit i).toNat)) =
      ∑ i : Fin n,
        ((if x.testBit i && !(x.testBit (finRotate n i)) then 1 else 0) +
          (x.testBit (finRotate n i)).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hbit _ _
  simp only [Finset.sum_add_distrib] at hlocal
  have hreindex := Equiv.sum_comp (finRotate n)
    (fun i : Fin n ↦ (x.testBit i).toNat)
  rw [cyclicRiseCount]
  omega

private def internalRisePositions (n x : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun j ↦
    x.testBit j = false ∧ x.testBit (j + 1) = true

private theorem card_internalRisePositions_le_cyclicRiseCount
    {n x : ℕ} (hx : x < 2 ^ n) :
    (internalRisePositions n x).card ≤ cyclicRiseCount n x := by
  let cyclicRises : Finset (Fin n) :=
    Finset.univ.filter fun i ↦
      x.testBit i = false ∧ x.testBit (finRotate n i) = true
  have hcard : (internalRisePositions n x).card ≤ cyclicRises.card := by
    have hmap (j : ℕ) (hj : j ∈ internalRisePositions n x) :
        (⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩ : Fin n) ∈ cyclicRises := by
      rcases Finset.mem_filter.mp hj with ⟨hjn, hj0, hj1⟩
      have hsucc : j + 1 < n := by
        by_contra hnot
        have hfalse : x.testBit (j + 1) = false :=
          Nat.testBit_eq_false_of_lt
            (hx.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hnot)))
        rw [hfalse] at hj1
        contradiction
      change ⟨j, _⟩ ∈ Finset.univ.filter (fun i : Fin n ↦
        x.testBit i = false ∧ x.testBit (finRotate n i) = true)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hj0, ?_⟩
      cases n with
      | zero => omega
      | succ m =>
          have hjm : j < m := by omega
          rw [finRotate_of_lt hjm]
          exact hj1
    let f : {j // j ∈ internalRisePositions n x} → {i // i ∈ cyclicRises} :=
      fun j ↦ ⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp j.2).1⟩,
        hmap j j.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext_iff.mp (congrArg Subtype.val hab)
    simpa [f] using Fintype.card_le_of_injective f hf
  calc
    _ ≤ cyclicRises.card := hcard
    _ = cyclicRiseCount n x := by
      rw [cyclicRiseCount]
      dsimp [cyclicRises]
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      cases h0 : x.testBit i <;> cases h1 : x.testBit (finRotate n i) <;>
        rfl

private def uncarriedOnePositions (n x y : ℕ) (c : Bool) : Finset ℕ :=
  (Finset.range n).filter fun i ↦
    x.testBit i = true ∧ binaryCarryIn x y c (i + 1) = false

private theorem card_uncarriedOnePositions_le
    {n x : ℕ} {c : Bool} (hn : 0 < n) :
    (uncarriedOnePositions n x (traceRunMultiplierExponent n) c).card ≤
      (internalRisePositions n x).card * (Nat.sqrt n - 1) := by
  let arc (j : ℕ) : Finset ℕ := Finset.Ioc j (j + (Nat.sqrt n - 1))
  have hsubset :
      uncarriedOnePositions n x (traceRunMultiplierExponent n) c ⊆
        (internalRisePositions n x).biUnion arc := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hin, hxi, hcarry⟩
    obtain ⟨j, hji, hdistance, hj0, hj1⟩ :=
      exists_rise_near_uncarried_one hn (Finset.mem_range.mp hin) hxi hcarry
    rw [Finset.mem_biUnion]
    refine ⟨j, ?_, ?_⟩
    · rw [internalRisePositions, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (hji.trans (Finset.mem_range.mp hin)), hj0, hj1⟩
    · change i ∈ Finset.Ioc j (j + (Nat.sqrt n - 1))
      rw [Finset.mem_Ioc]
      have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
      omega
  calc
    _ ≤ ((internalRisePositions n x).biUnion arc).card :=
      Finset.card_le_card hsubset
    _ ≤ (internalRisePositions n x).card * (Nat.sqrt n - 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      change (Finset.Ioc j (j + (Nat.sqrt n - 1))).card ≤ Nat.sqrt n - 1
      rw [Nat.card_Ioc]
      omega

private theorem binaryWeight_eq_sum_testBit_of_lt
    {n x : ℕ} (hx : x < 2 ^ n) :
    binaryWeight x = ∑ i ∈ Finset.range n, (x.testBit i).toNat := by
  have hxBits : Nat.ofBits (fun i : Fin n ↦ x.testBit i) = x := by
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hx]
  calc
    binaryWeight x = binaryWeight (Nat.ofBits (fun i : Fin n ↦ x.testBit i)) :=
      congrArg binaryWeight hxBits.symm
    _ = ∑ i : Fin n, (x.testBit i).toNat := binaryWeight_ofBits _
    _ = _ := Fin.sum_univ_eq_sum_range (fun i ↦ (x.testBit i).toNat) n

private theorem binaryWeight_le_carries_add_uncarried
    {n x y : ℕ} {c : Bool} (hx : x < 2 ^ n) :
    binaryWeight x ≤
      (∑ i ∈ Finset.range n, (binaryCarryIn x y c (i + 1)).toNat) +
        (uncarriedOnePositions n x y c).card := by
  rw [binaryWeight_eq_sum_testBit_of_lt hx, uncarriedOnePositions,
    Finset.card_filter]
  have hpoint : ∀ i ∈ Finset.range n,
      (x.testBit i).toNat ≤ (binaryCarryIn x y c (i + 1)).toNat +
        if x.testBit i = true ∧ binaryCarryIn x y c (i + 1) = false then 1 else 0 := by
    intro i hi
    cases hxbit : x.testBit i <;>
      cases hc : binaryCarryIn x y c (i + 1) <;> simp
  exact (Finset.sum_le_sum hpoint).trans_eq Finset.sum_add_distrib

private theorem binaryWeight_le_carries_add_runs
    {n x : ℕ} {c : Bool} (hn : 0 < n)
    (hx : x < 2 ^ n - 1) :
    binaryWeight x ≤
      (∑ i ∈ Finset.range n,
        (binaryCarryIn x (traceRunMultiplierExponent n) c (i + 1)).toNat) +
        cyclicOneRunCount n x * (Nat.sqrt n - 1) := by
  have hxpow : x < 2 ^ n := hx.trans
    (Nat.sub_lt (Nat.two_pow_pos n) (by omega))
  have hbase := binaryWeight_le_carries_add_uncarried
    (y := traceRunMultiplierExponent n) (c := c) hxpow
  have hbad := card_uncarriedOnePositions_le (x := x) (c := c) hn
  have hrise := card_internalRisePositions_le_cyclicRiseCount hxpow
  have hcount : cyclicRiseCount n x = cyclicOneRunCount n x := by
    rw [cyclicRiseCount_eq_cyclicFallCount,
      cyclicOneRunCount_of_lt hx]
  rw [hcount] at hrise
  have hmul : (internalRisePositions n x).card * (Nat.sqrt n - 1) ≤
      cyclicOneRunCount n x * (Nat.sqrt n - 1) :=
    Nat.mul_le_mul_right _ hrise
  exact hbase.trans (Nat.add_le_add_left (hbad.trans hmul) _)

private theorem binaryWeight_binaryAdditionNat (n x y : ℕ) (c : Bool) :
    binaryWeight (binaryAdditionNat n x y c) =
      ∑ i ∈ Finset.range n, (binaryAdditionBit x y c i).toNat := by
  rw [binaryAdditionNat, binaryWeight_ofBits]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ (binaryAdditionBit x y c i).toNat) n

/-- Adding the Nawaz--Gong--Gupta multiplier to a canonical nonzero exponent
costs at most one block-minus-one per cyclic one-run, in addition to the
multiplier's own binary weight. -/
theorem binaryWeight_positiveCyclicSum_traceRunMultiplier_le
    {n x : ℕ} (hn : 0 < n) (hx : x < 2 ^ n - 1) :
    binaryWeight
        (positiveCyclicSum n x (traceRunMultiplierExponent n)) ≤
      cyclicOneRunCount n x * (Nat.sqrt n - 1) + n ⌈/⌉ Nat.sqrt n := by
  let y := traceRunMultiplierExponent n
  let c := cyclicAdditionInitialCarry n x y
  have hxpow : x < 2 ^ n := hx.trans
    (Nat.sub_lt (Nat.two_pow_pos n) (by omega))
  have hypow : y < 2 ^ n := traceRunMultiplierExponent_lt_two_pow hn
  have hcyclic : binaryCarryIn x y c n = c :=
    binaryCarryIn_cyclicAdditionInitialCarry hxpow hypow
  have hweight := binary_addition_weight_identity_of_cyclic_carry x y n c hcyclic
  have hxWeight := binaryWeight_eq_sum_testBit_of_lt hxpow
  have hyWeight := binaryWeight_eq_sum_testBit_of_lt hypow
  have hzWeight := binaryWeight_binaryAdditionNat n x y c
  have hzValue := binaryAdditionNat_cyclic_eq_positiveCyclicSum hxpow hypow
  have hinput := binaryWeight_le_carries_add_runs (c := c) hn hx
  have hyExact := binaryWeight_traceRunMultiplierExponent hn
  dsimp [y] at hyWeight hyExact hinput hweight hzWeight hzValue ⊢
  rw [← hxWeight, ← hyWeight] at hweight
  rw [← hzValue, hzWeight]
  rw [hyExact] at hweight
  omega

/-- Nawaz--Gong--Gupta's cyclic carry estimate for every Frobenius rotation of
a nonzero canonical exponent. -/
theorem binaryWeight_traceRunMultiplier_add_binaryCyclicExponent_le
    {n d s : ℕ} (hn : 0 < n) (hd0 : 0 < d) (hd : d < 2 ^ n - 1) :
    binaryWeight
        (positiveCyclicSum n (binaryCyclicExponent n d s)
          (traceRunMultiplierExponent n)) ≤
      cyclicOneRunCount n d * Nat.sqrt n + n ⌈/⌉ Nat.sqrt n - 1 := by
  have hstrong := binaryWeight_positiveCyclicSum_traceRunMultiplier_le hn
    (binaryCyclicExponent_lt n d hn s)
  rw [cyclicOneRunCount_binaryCyclicExponent hn hd] at hstrong
  have hu : 0 < cyclicOneRunCount n d := cyclicOneRunCount_pos hn hd0 hd
  have hl : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hsplit :
      cyclicOneRunCount n d * Nat.sqrt n =
        cyclicOneRunCount n d * (Nat.sqrt n - 1) + cyclicOneRunCount n d := by
    calc
      _ = cyclicOneRunCount n d * ((Nat.sqrt n - 1) + 1) := by
        rw [Nat.sub_add_cancel hl]
      _ = _ := by ring
  omega

private theorem functionAlgebraicDegree_tracePowerFunction_mul_traceRunMultiplier_le
    {n d : ℕ} (hn : 0 < n) (hd0 : 0 < d) (hd : d < 2 ^ n - 1)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a gamma : BinaryGaloisField n) :
    FABL.functionAlgebraicDegree
        (tracePowerFunction θ a d *
          tracePowerFunction θ gamma (traceRunMultiplierExponent n)) ≤
      cyclicOneRunCount n d * Nat.sqrt n + n ⌈/⌉ Nat.sqrt n - 1 := by
  let r := traceRunMultiplierExponent n
  let target := cyclicOneRunCount n d * Nat.sqrt n + n ⌈/⌉ Nat.sqrt n - 1
  have hrpow : r < 2 ^ n := traceRunMultiplierExponent_lt_two_pow hn
  have hexpand :
      tracePowerFunction θ a d * tracePowerFunction θ gamma r =
        ∑ s ∈ Finset.range n, fun x : FABL.F₂Cube n ↦
          absoluteTrace n
            (gamma * a ^ (2 ^ s) *
              (θ x) ^ positiveCyclicSum n (binaryCyclicExponent n d s) r) := by
    funext x
    rw [Finset.sum_apply]
    change absoluteTrace n (a * (θ x) ^ d) *
        absoluteTrace n (gamma * (θ x) ^ r) = _
    rw [absoluteTrace_mul_absoluteTrace hn]
    apply Finset.sum_congr rfl
    intro s hs
    apply congrArg (absoluteTrace n)
    have hrotPos : 0 < binaryCyclicExponent n d s :=
      binaryCyclicExponent_pos hn hd0 hd s
    have hrotate := pow_binaryCyclicExponent hn hd0 hd (θ x) s
    have hpositive := pow_positiveCyclicSum hn
      (Nat.add_pos_left hrotPos r) (θ x)
    calc
      gamma * (θ x) ^ r * (a * (θ x) ^ d) ^ (2 ^ s) =
          gamma * a ^ (2 ^ s) *
            ((θ x) ^ r * (θ x) ^ (d * 2 ^ s)) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ = gamma * a ^ (2 ^ s) *
          ((θ x) ^ r * (θ x) ^ binaryCyclicExponent n d s) := by
        rw [hrotate]
      _ = gamma * a ^ (2 ^ s) *
          (θ x) ^ (binaryCyclicExponent n d s + r) := by
        rw [add_comm, pow_add]
      _ = gamma * a ^ (2 ^ s) *
          (θ x) ^ positiveCyclicSum n (binaryCyclicExponent n d s) r := by
        rw [hpositive]
  rw [hexpand]
  apply FABL.functionAlgebraicDegree_finset_sum_le (Finset.range n) _ target
  intro s hs
  have hrotPow : binaryCyclicExponent n d s < 2 ^ n :=
    (binaryCyclicExponent_lt n d hn s).trans
      (Nat.sub_lt (Nat.two_pow_pos n) (by omega))
  have hkpow := positiveCyclicSum_lt_two_pow hrotPow hrpow
  exact (functionAlgebraicDegree_traceMonomial_le_binaryWeight hn
    (by omega) θ (gamma * a ^ (2 ^ s))).trans
      (binaryWeight_traceRunMultiplier_add_binaryCyclicExponent_le hn hd0 hd)

private theorem algebraicImmunity_eq_zero_of_eq_zero_or_eq_one
    {n : ℕ} (f : BooleanFunction n) (hf : f = 0 ∨ f = 1) :
    algebraicImmunity f = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hwitness : IsAlgebraicImmunityWitness f 1 := by
    rcases hf with hf | hf
    · left
      refine ⟨one_ne_zero, ?_⟩
      simp [hf]
    · right
      refine ⟨one_ne_zero, ?_⟩
      rw [hf]
      funext x
      change ((1 : FABL.𝔽₂) + 1) * 1 = 0
      decide
  simpa using algebraicImmunity_le_functionAlgebraicDegree f 1 hwitness

/-- Carlet's trace-power run bound: if the cyclic run count is below
`√n/2`, then the algebraic immunity is bounded by the
Nawaz--Gong--Gupta multiplier estimate. -/
theorem algebraicImmunity_tracePowerFunction_le_runBound
    {n d : ℕ} (hn : 0 < n) (hd : d < 2 ^ n - 1)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n)
    (_hrun : (cyclicOneRunCount n d : ℝ) < Real.sqrt n / 2) :
    algebraicImmunity (tracePowerFunction θ a d) ≤
      cyclicOneRunCount n d * Nat.sqrt n + n ⌈/⌉ Nat.sqrt n - 1 := by
  by_cases hd0 : d = 0
  · subst d
    have hconstant : tracePowerFunction θ a 0 =
        fun _ ↦ absoluteTrace n a := by
      funext x
      simp [tracePowerFunction]
    have hconstant01 : tracePowerFunction θ a 0 = 0 ∨
        tracePowerFunction θ a 0 = 1 := by
      by_cases haTrace : absoluteTrace n a = 0
      · left
        rw [hconstant]
        funext x
        exact haTrace
      · right
        have haTraceOne : absoluteTrace n a = 1 :=
          Fin.eq_one_of_ne_zero _ haTrace
        rw [hconstant]
        funext x
        exact haTraceOne
    rw [algebraicImmunity_eq_zero_of_eq_zero_or_eq_one _ hconstant01]
    exact Nat.zero_le _
  · let f := tracePowerFunction θ a d
    by_cases hf : f = 0
    · rw [algebraicImmunity_eq_zero_of_eq_zero_or_eq_one f (Or.inl hf)]
      exact Nat.zero_le _
    · have hexists : ∃ x₀ : FABL.F₂Cube n, f x₀ ≠ 0 := by
        by_contra hnone
        apply hf
        funext x
        by_cases hx : f x = 0
        · exact hx
        · exact (hnone ⟨x, hx⟩).elim
      obtain ⟨x₀, hx₀⟩ := hexists
      have hfx₀ : f x₀ = 1 := Fin.eq_one_of_ne_zero _ hx₀
      have htheta : θ x₀ ≠ 0 := by
        intro hzero
        have hvalue : f x₀ = 0 := by
          simp [f, tracePowerFunction, hzero, zero_pow hd0]
        rw [hvalue] at hfx₀
        contradiction
      let r := traceRunMultiplierExponent n
      let y₀ : BinaryGaloisField n := (θ x₀) ^ r
      have hy₀ : y₀ ≠ 0 := pow_ne_zero _ htheta
      obtain ⟨traceOne, htraceOne⟩ := exists_absoluteTrace_eq_one n
      let gamma : BinaryGaloisField n := traceOne * y₀⁻¹
      let g := tracePowerFunction θ gamma r
      have hgx₀ : g x₀ = 1 := by
        change absoluteTrace n (gamma * (θ x₀) ^ r) = 1
        rw [show (θ x₀) ^ r = y₀ by rfl]
        dsimp [gamma]
        rw [mul_assoc, inv_mul_cancel₀ hy₀, mul_one, htraceOne]
      have hproduct : f * g ≠ 0 := by
        intro hzero
        have hvalue := congrFun hzero x₀
        change f x₀ * g x₀ = 0 at hvalue
        rw [hfx₀, hgx₀, one_mul] at hvalue
        exact one_ne_zero hvalue
      have hdegree :=
        functionAlgebraicDegree_tracePowerFunction_mul_traceRunMultiplier_le
          hn (Nat.pos_of_ne_zero hd0) hd θ a gamma
      dsimp [f, g, r] at hproduct hdegree ⊢
      exact (algebraicImmunity_le_degree_of_mul_eq_of_ne_zero
        (tracePowerFunction θ a d)
        (tracePowerFunction θ gamma (traceRunMultiplierExponent n))
        _ rfl hproduct).trans hdegree

end

end CryptBoolean
