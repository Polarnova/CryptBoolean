/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FiniteFieldAlgebraicDegree

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Algebraic degree of finite-field trace monomials

The binary exponents in a Frobenius orbit are cyclic rotations, so every nonzero term in
the canonical univariate representation of a trace monomial has the same binary weight.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable section

private def truncatedBinarySupport (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ k.testBit i

private def truncatedBinaryWeight (n k : ℕ) : ℕ :=
  (truncatedBinarySupport n k).card

private theorem truncatedBinaryWeight_eq_sum_testBit (n k : ℕ) :
    truncatedBinaryWeight n k = ∑ i : Fin n, (k.testBit i).toNat := by
  classical
  rw [truncatedBinaryWeight, truncatedBinarySupport, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases k.testBit i <;> rfl

private theorem binaryWeight_eq_truncatedBinaryWeight
    (n k : ℕ) (hk : k < 2 ^ n) :
    binaryWeight k = truncatedBinaryWeight n k := by
  classical
  rw [binaryWeight, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  apply Finset.card_bij
    (fun i hi ↦ ⟨i, by
      by_contra hni
      have hfalse : k.testBit i = false := Nat.testBit_eq_false_of_lt
        (hk.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hni)))
      have htrue : k.testBit i := Nat.mem_bitIndices.mp (by simpa using hi)
      simp [hfalse] at htrue⟩)
  · intro i hi
    simp only [truncatedBinarySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.mem_bitIndices.mp (by simpa using hi)
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro i hi
    refine ⟨(i : ℕ), ?_, ?_⟩
    · simpa [truncatedBinarySupport] using
        (Nat.mem_bitIndices.mpr
          (show k.testBit (i : ℕ) from (by simpa [truncatedBinarySupport] using hi)))
    · apply Fin.ext
      rfl

private theorem ofBits_eq_sum {n : ℕ} (f : Fin n → Bool) :
    Nat.ofBits f = ∑ i : Fin n, (f i).toNat * 2 ^ (i : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.ofBits_succ, Fin.sum_univ_succ, ih]
      simp only [Function.comp_apply, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [Finset.mul_sum]
      simp_rw [pow_succ']
      have hsum :
          (∑ i : Fin n, 2 * ((f i.succ).toNat * 2 ^ (i : ℕ))) =
            ∑ i : Fin n, (f i.succ).toNat * (2 * 2 ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum, Nat.add_comm]

private def rotateBinaryExponent (n k : ℕ) : ℕ :=
  Nat.ofBits fun i : Fin n ↦ k.testBit ((finRotate n).symm i)

private theorem rotateBinaryExponent_weight (n k : ℕ) :
    truncatedBinaryWeight n (rotateBinaryExponent n k) = truncatedBinaryWeight n k := by
  rw [truncatedBinaryWeight_eq_sum_testBit, truncatedBinaryWeight_eq_sum_testBit]
  simp only [rotateBinaryExponent, Nat.testBit_ofBits_lt _ _ (Fin.isLt _)]
  simpa using
    (Equiv.sum_comp (finRotate n).symm (fun i : Fin n ↦ (k.testBit i).toNat))

private theorem two_pow_mod_two_pow_sub_one (n : ℕ) (_hn : 0 < n) :
    2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
  rw [Nat.ModEq]
  have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
  conv_lhs => rw [show 2 ^ n = (2 ^ n - 1) + 1 by omega]
  simp

private theorem double_bit_term_modEq_rotate
    (n : ℕ) (hn : 0 < n) (k : ℕ) (i : Fin n) :
    2 * ((k.testBit i).toNat * 2 ^ (i : ℕ)) ≡
      (k.testBit i).toNat * 2 ^ ((finRotate n i : Fin n) : ℕ)
        [MOD 2 ^ n - 1] := by
  obtain ⟨m, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  by_cases hi : i = Fin.last m
  · subst i
    rw [finRotate_last]
    simp only [Fin.val_last, Fin.val_zero, pow_zero, mul_one]
    have hp := (two_pow_mod_two_pow_sub_one (m + 1) (Nat.succ_pos m)).mul_left
      (k.testBit (Fin.last m)).toNat
    simpa [pow_succ', Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hp
  · rw [coe_finRotate_of_ne_last hi]
    simp only [pow_succ']
    have heq :
        2 * ((k.testBit i).toNat * 2 ^ (i : ℕ)) =
          (k.testBit i).toNat * (2 * 2 ^ (i : ℕ)) := by ring
    rw [heq]

private theorem double_modEq_rotateBinaryExponent
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < 2 ^ n) :
    2 * k ≡ rotateBinaryExponent n k [MOD 2 ^ n - 1] := by
  have hkbits : Nat.ofBits (fun i : Fin n ↦ k.testBit i) = k := by
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hk]
  rw [rotateBinaryExponent, ofBits_eq_sum]
  have hsum := Nat.ModEq.sum (s := Finset.univ)
    (fun i _ ↦ double_bit_term_modEq_rotate n hn k i)
  rw [← Finset.mul_sum] at hsum
  have hreindex :
      (∑ i : Fin n,
        (k.testBit i).toNat * 2 ^ ((finRotate n i : Fin n) : ℕ)) =
        ∑ i : Fin n, (k.testBit ((finRotate n).symm i)).toNat * 2 ^ (i : ℕ) := by
    calc
      _ = ∑ i : Fin n,
          (k.testBit ((finRotate n).symm (finRotate n i))).toNat *
            2 ^ ((finRotate n i : Fin n) : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Equiv.symm_apply_apply]
      _ = _ := Equiv.sum_comp (finRotate n)
        (fun i : Fin n ↦
          (k.testBit ((finRotate n).symm i)).toNat * 2 ^ (i : ℕ))
  rw [hreindex] at hsum
  rw [← ofBits_eq_sum] at hsum
  rwa [hkbits] at hsum

private theorem rotateBinaryExponent_lt_modulus
    (n : ℕ) (_hn : 0 < n) (k : ℕ) (hk : k < 2 ^ n - 1) :
    rotateBinaryExponent n k < 2 ^ n - 1 := by
  have hlt : rotateBinaryExponent n k < 2 ^ n :=
    Nat.ofBits_lt_two_pow _
  by_contra hnot
  have heq : rotateBinaryExponent n k = 2 ^ n - 1 := by omega
  have hbits (i : Fin n) : k.testBit i = true := by
    have hout : (rotateBinaryExponent n k).testBit (finRotate n i : Fin n) = true := by
      rw [heq, Nat.testBit_two_pow_sub_succ
        (x := 0) (Nat.two_pow_pos n) (finRotate n i : ℕ)]
      simp
    change (Nat.ofBits (fun j : Fin n ↦ k.testBit ((finRotate n).symm j))).testBit
      (finRotate n i : ℕ) = true at hout
    rw [Nat.testBit_ofBits_lt _ _ (Fin.isLt _), Equiv.symm_apply_apply] at hout
    exact hout
  have hkeq : k = 2 ^ n - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · rw [hbits ⟨i, hi⟩]
      rw [Nat.testBit_two_pow_sub_succ
        (x := 0) (by positivity : 0 < 2 ^ n) i]
      simp [hi]
    · have hkpow : k < 2 ^ n := hk.trans (Nat.sub_lt (by positivity) (by omega))
      rw [Nat.testBit_eq_false_of_lt
        (hkpow.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))]
      exact (Nat.testBit_eq_false_of_lt
        ((Nat.sub_lt (by positivity : 0 < 2 ^ n) (by omega)).trans_le
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))).symm
  exact (Nat.ne_of_lt hk) hkeq

private theorem double_mod_eq_rotateBinaryExponent
    (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < 2 ^ n - 1) :
    (2 * k) % (2 ^ n - 1) = rotateBinaryExponent n k := by
  apply Nat.mod_eq_of_modEq
    (double_modEq_rotateBinaryExponent n hn k
      (hk.trans (Nat.sub_lt (Nat.two_pow_pos n) (by omega))))
  exact rotateBinaryExponent_lt_modulus n hn k hk

private def binaryCyclicExponent (n k s : ℕ) : ℕ :=
  (k * 2 ^ s) % (2 ^ n - 1)

private theorem binaryCyclicExponent_succ (n k s : ℕ) :
    binaryCyclicExponent n k (s + 1) =
      (2 * binaryCyclicExponent n k s) % (2 ^ n - 1) := by
  rw [binaryCyclicExponent, binaryCyclicExponent, pow_succ]
  let M := 2 ^ n - 1
  change (k * (2 ^ s * 2)) % M = (2 * ((k * 2 ^ s) % M)) % M
  calc
    _ = ((k * 2 ^ s) * 2) % M := by congr 1; ring
    _ = (2 * (k * 2 ^ s)) % M := by rw [Nat.mul_comm]
    _ = (2 * ((k * 2 ^ s) % M)) % M := by
      rw [Nat.mul_mod]
      convert (Nat.mul_mod 2 ((k * 2 ^ s) % M) M).symm using 1
      simp only [Nat.mod_mod]

private theorem binaryCyclicExponent_lt
    (n k : ℕ) (hn : 0 < n) (s : ℕ) :
    binaryCyclicExponent n k s < 2 ^ n - 1 := by
  apply Nat.mod_lt
  exact Nat.sub_pos_of_lt (by simpa using Nat.one_lt_two_pow hn.ne')

private theorem binaryWeight_binaryCyclicExponent
    (n k s : ℕ) (hn : 0 < n) (hk : k < 2 ^ n - 1) :
    binaryWeight (binaryCyclicExponent n k s) = binaryWeight k := by
  induction s with
  | zero => simp [binaryCyclicExponent, Nat.mod_eq_of_lt hk]
  | succ s ih =>
      calc
        binaryWeight (binaryCyclicExponent n k (s + 1)) =
            truncatedBinaryWeight n (binaryCyclicExponent n k (s + 1)) :=
          binaryWeight_eq_truncatedBinaryWeight n _
            ((binaryCyclicExponent_lt n k hn (s + 1)).trans
              (Nat.sub_lt (Nat.two_pow_pos n) (by omega)))
        _ = truncatedBinaryWeight n (binaryCyclicExponent n k s) := by
          rw [binaryCyclicExponent_succ,
            double_mod_eq_rotateBinaryExponent n hn _ (binaryCyclicExponent_lt n k hn s),
            rotateBinaryExponent_weight]
        _ = binaryWeight (binaryCyclicExponent n k s) :=
          (binaryWeight_eq_truncatedBinaryWeight n _
            ((binaryCyclicExponent_lt n k hn s).trans
              (Nat.sub_lt (Nat.two_pow_pos n) (by omega)))).symm
        _ = binaryWeight k := ih

private theorem binaryCyclicExponent_pos {n k : ℕ} (hn : 0 < n)
    (hk0 : 0 < k) (hk : k < 2 ^ n - 1) (s : ℕ) :
    0 < binaryCyclicExponent n k s := by
  have hqEven : Even (2 ^ n) := by
    rw [Nat.even_pow]
    exact ⟨by decide, Nat.ne_of_gt hn⟩
  have hmodOdd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (m := 2 ^ n) (n := 1)
      (pow_pos (by decide : 0 < 2) n) hqEven (by simp)
  have hcop : Nat.Coprime (2 ^ n - 1) (2 ^ s) :=
    hmodOdd.coprime_two_right.pow_right s
  rw [Nat.pos_iff_ne_zero]
  intro hz
  have hdvd : 2 ^ n - 1 ∣ k * 2 ^ s :=
    Nat.dvd_iff_mod_eq_zero.mpr hz
  have hdivk : 2 ^ n - 1 ∣ k := hcop.dvd_of_dvd_mul_right hdvd
  exact (Nat.not_dvd_of_pos_of_lt hk0 hk) hdivk

private theorem pow_binaryCyclicExponent {n k : ℕ} (hn : 0 < n)
    (hk0 : 0 < k) (hk : k < 2 ^ n - 1)
    (x : BinaryGaloisField n) (s : ℕ) :
    x ^ binaryCyclicExponent n k s = x ^ (k * 2 ^ s) := by
  by_cases hx : x = 0
  · subst x
    rw [zero_pow (Nat.ne_of_gt (binaryCyclicExponent_pos hn hk0 hk s)),
      zero_pow (Nat.ne_of_gt (Nat.mul_pos hk0 (pow_pos (by decide) s)))]
  · letI := Fintype.ofFinite (BinaryGaloisField n)
    have hcard : Fintype.card (BinaryGaloisField n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 n (Nat.ne_of_gt hn)
    have horder : x ^ (2 ^ n - 1) = 1 := by
      rw [← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx
    exact (pow_eq_pow_mod (a := x) (n := 2 ^ n - 1) (k * 2 ^ s) horder).symm

private noncomputable def traceMonomialOrbitPolynomial {n : ℕ}
    (a : BinaryGaloisField n) (k : ℕ) : (BinaryGaloisField n)[X] :=
  ∑ s ∈ Finset.range n,
    C (a ^ (2 ^ s)) * X ^ binaryCyclicExponent n k s

private theorem eval_traceMonomialOrbitPolynomial {n k : ℕ} (hn : 0 < n)
    (hk : k < 2 ^ n - 1) (a x : BinaryGaloisField n) :
    (traceMonomialOrbitPolynomial a k).eval x =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (absoluteTrace n (a * x ^ k)) := by
  rw [algebraMap_absoluteTrace_eq_sum_frobenius (Nat.ne_of_gt hn)]
  simp only [traceMonomialOrbitPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro s hs
  rw [mul_pow, ← pow_mul]
  by_cases hk0 : k = 0
  · simp [binaryCyclicExponent, hk0]
  · rw [pow_binaryCyclicExponent hn (Nat.pos_of_ne_zero hk0) hk]

private theorem degree_traceMonomialOrbitPolynomial_lt {n k : ℕ} (hn : 0 < n)
    (a : BinaryGaloisField n) :
    (traceMonomialOrbitPolynomial a k).degree < (2 ^ n : ℕ) := by
  have hmod : 0 < 2 ^ n - 1 := by
    have := Nat.one_lt_pow (Nat.ne_of_gt hn) (by decide : 1 < 2)
    omega
  have hnat : (traceMonomialOrbitPolynomial a k).natDegree ≤ 2 ^ n - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    exact (Polynomial.natDegree_C_mul_X_pow_le (a ^ 2 ^ s)
      (binaryCyclicExponent n k s)).trans
      (Nat.le_of_lt (Nat.mod_lt _ hmod))
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hnat m (by
    have hqpos : 0 < 2 ^ n := pow_pos (by decide) n
    omega)

private theorem support_traceMonomialOrbitPolynomial_subset {n k : ℕ}
    (a : BinaryGaloisField n) :
    (traceMonomialOrbitPolynomial a k).support ⊆
      (Finset.range n).image (binaryCyclicExponent n k) := by
  intro j hj
  rw [Polynomial.mem_support_iff] at hj
  rw [traceMonomialOrbitPolynomial, Polynomial.finsetSum_coeff] at hj
  simp only [Polynomial.coeff_C_mul_X_pow] at hj
  by_contra hnot
  have hzero : ∀ s ∈ Finset.range n,
      (if j = binaryCyclicExponent n k s then a ^ 2 ^ s else 0) = 0 := by
    intro s hs
    simp only [ite_eq_right_iff]
    intro heq
    exact (hnot (Finset.mem_image.mpr ⟨s, hs, heq.symm⟩)).elim
  exact hj (Finset.sum_eq_zero hzero)

private theorem traceMonomialOrbitPolynomial_ne_zero_of_function_ne_zero
    {n k : ℕ} (hn : 0 < n) (hk : k < 2 ^ n - 1)
    (a : BinaryGaloisField n)
    (hfun : (fun x : BinaryGaloisField n ↦ absoluteTrace n (a * x ^ k)) ≠ 0) :
    traceMonomialOrbitPolynomial a k ≠ 0 := by
  intro hzero
  apply hfun
  funext x
  change absoluteTrace n (a * x ^ k) = 0
  apply (algebraMap FABL.𝔽₂ (BinaryGaloisField n)).injective
  rw [map_zero, ← eval_traceMonomialOrbitPolynomial hn hk a x, hzero, Polynomial.eval_zero]

private theorem traceMonomialOrbitPolynomial_eq_univariateRepresentation
    {n k : ℕ} (hn : 0 < n) (hk : k < 2 ^ n - 1)
    (a : BinaryGaloisField n) :
    traceMonomialOrbitPolynomial a k =
      univariateRepresentation (fun x : BinaryGaloisField n ↦
        algebraMap FABL.𝔽₂ (BinaryGaloisField n)
          (absoluteTrace n (a * x ^ k))) := by
  have hUnique := existsUnique_univariateRepresentation
    (fun x : BinaryGaloisField n ↦
      algebraMap FABL.𝔽₂ (BinaryGaloisField n)
        (absoluteTrace n (a * x ^ k)))
  have hcard : Nat.card (BinaryGaloisField n) = 2 ^ n :=
    GaloisField.card 2 n (Nat.ne_of_gt hn)
  apply hUnique.unique
  · exact ⟨by
    rw [hcard]
    exact degree_traceMonomialOrbitPolynomial_lt hn a, fun x ↦
      eval_traceMonomialOrbitPolynomial hn hk a x⟩
  · exact ⟨degree_univariateRepresentation_lt_card _,
      eval_univariateRepresentation _⟩

private theorem field_traceMonomial_ne_zero_of_cube_ne_zero
    {n k : ℕ} (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n)
    (hfun : (fun x : FABL.F₂Cube n ↦
      absoluteTrace n (a * (θ x) ^ k)) ≠ 0) :
    (fun y : BinaryGaloisField n ↦ absoluteTrace n (a * y ^ k)) ≠ 0 := by
  intro hzero
  apply hfun
  funext x
  simpa using congrFun hzero (θ x)

/-- Carlet Proposition 3: a nonzero trace monomial has algebraic degree equal to the
binary Hamming weight of its exponent. -/
theorem functionAlgebraicDegree_traceMonomial
    {n k : ℕ} (hn : 0 < n) (hk : k < 2 ^ n - 1)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (a : BinaryGaloisField n)
    (hfun : (fun x : FABL.F₂Cube n ↦
      absoluteTrace n (a * (θ x) ^ k)) ≠ 0) :
    FABL.functionAlgebraicDegree
        (fun x : FABL.F₂Cube n ↦ absoluteTrace n (a * (θ x) ^ k)) =
      binaryWeight k := by
  let f : FABL.F₂BooleanFunction n :=
    fun x ↦ absoluteTrace n (a * (θ x) ^ k)
  calc
    FABL.functionAlgebraicDegree f =
        univariateBinaryDegree
          (univariateRepresentation fun z : BinaryGaloisField n ↦
            algebraMap FABL.𝔽₂ (BinaryGaloisField n)
              (absoluteTrace n (a * z ^ k))) := by
      simpa [f] using
        functionAlgebraicDegree_eq_univariateBinaryDegree (Nat.ne_of_gt hn) θ f
    _ = univariateBinaryDegree (traceMonomialOrbitPolynomial a k) := by
      rw [traceMonomialOrbitPolynomial_eq_univariateRepresentation hn hk a]
    _ = binaryWeight k := by
      rw [univariateBinaryDegree]
      have hfield := field_traceMonomial_ne_zero_of_cube_ne_zero θ a hfun
      have hpoly :=
        traceMonomialOrbitPolynomial_ne_zero_of_function_ne_zero hn hk a hfield
      have hsupp := Polynomial.support_nonempty.mpr hpoly
      rw [← Finset.sup'_eq_sup hsupp]
      apply Finset.sup'_eq_of_forall
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp
        (support_traceMonomialOrbitPolynomial_subset a hj)
      exact binaryWeight_binaryCyclicExponent n k s hn hk

end

end CryptBoolean
