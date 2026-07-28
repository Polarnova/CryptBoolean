/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.CompleteQuadratic
public import CryptBoolean.Carlet.Chapter06.KerdockFieldConstruction

/-!
# Self-dual normal-basis coordinates for the Kerdock trace quadratic

The conditional coordinate identity relating the complete quadratic function
to Carlet's finite-field trace formula.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

private theorem completeQuadraticPolar_eq_totalProduct_add_dot {n : ℕ}
    (a b : FABL.F₂Cube n) :
    quadraticPolarKernel
        (FABL.completeQuadraticBit : BooleanFunction n) a b =
      (∑ i, a i) * (∑ i, b i) + ∑ i, a i * b i := by
  rw [quadraticPolarKernel_completeQuadraticBit_eq_dotProduct,
    FABL.f₂DotProduct, dotProduct]
  simp only [completeQuadraticPolarFrequency]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_sum_compl ({i} : Finset (Fin n))]
  simp
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem completeQuadraticBit_single {n : ℕ} (i : Fin n) :
    FABL.completeQuadraticBit (Pi.single i 1) = 0 := by
  rw [FABL.completeQuadraticBit]
  apply Finset.sum_eq_zero
  intro j _hj
  by_cases hji : j = i
  · subst j
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hji]

private theorem completeQuadraticBit_zero {n : ℕ} :
    FABL.completeQuadraticBit (0 : FABL.F₂Cube n) = 0 := by
  rw [FABL.completeQuadraticBit]
  simp

private theorem append_single_eq_single_castAdd {m : ℕ} (i : Fin m) :
    Fin.append (Pi.single i 1) (0 : FABL.F₂Cube 1) =
      Pi.single (Fin.castAdd 1 i) 1 := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [Pi.single_apply]
  · intro k
    have hne : Fin.natAdd m k ≠ Fin.castAdd 1 i := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    simp [hne]

private theorem append_one_eq_single_natAdd {m : ℕ} :
    Fin.append (0 : FABL.F₂Cube m) (1 : FABL.F₂Cube 1) =
      Pi.single (Fin.natAdd m 0) 1 := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    have hne : Fin.castAdd 1 k ≠ Fin.natAdd m 0 := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    simp [hne]
  · intro k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp

private theorem kerdockTraceQuadratic_basis_eq_zero_of_selfDualNormalCoordinates
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (hnormal : ∀ x : FABL.F₂Cube (2 * t + 1),
      theta (fun i ↦ x (finRotate (2 * t + 1) i)) =
        (theta x) ^ 2)
    (hselfDual : ∀ x y : FABL.F₂Cube (2 * t + 1),
      absoluteTrace (2 * t + 1) (theta x * theta y) =
        ∑ i, x i * y i)
    (i : Fin (2 * t + 1)) :
    kerdockTraceQuadratic t (theta (Pi.single i 1)) = 0 := by
  let rotate : FABL.F₂Cube (2 * t + 1) →
      FABL.F₂Cube (2 * t + 1) :=
    fun x j ↦ x (finRotate (2 * t + 1) j)
  haveI : NeZero (2 * t + 1) := ⟨by omega⟩
  have hiterate (x : FABL.F₂Cube (2 * t + 1)) (k : ℕ) :
      theta (rotate^[k] x) = (theta x) ^ (2 ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', hnormal, ih]
        rw [Nat.pow_succ, pow_mul]
  have hrotateApply (x : FABL.F₂Cube (2 * t + 1)) (k : ℕ)
      (j : Fin (2 * t + 1)) :
      (rotate^[k] x) j = x ((finRotate (2 * t + 1))^[k] j) := by
    induction k generalizing j with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        change (rotate^[k] x) (finRotate (2 * t + 1) j) = _
        rw [ih, Function.iterate_succ_apply]
  have hshiftNe (i : Fin (2 * t + 1)) (k : ℕ)
      (hkpos : 0 < k) (hklt : k < 2 * t + 1) :
      (finRotate (2 * t + 1))^[k] i ≠ i := by
    let q : Fin (2 * t + 1) := ⟨k, hklt⟩
    have hcycle : i + q = (finRotate (2 * t + 1))^[k] i := by
      simpa only [finCycle_apply, q] using
        congrFun (finCycle_eq_finRotate_iterate (k := q)) i
    intro heq
    have hiq : i + q = i + 0 := by
      rw [hcycle, heq, add_zero]
    have hqzero : q = 0 := add_left_cancel hiq
    exact (Nat.ne_of_gt hkpos) (congrArg Fin.val hqzero)
  unfold kerdockTraceQuadratic oddQuadraticTracePart
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _hj
  simp only [one_mul, binaryFrobeniusLinear_apply]
  rw [← hiterate (Pi.single i 1) ((j : ℕ) + 1), hselfDual]
  apply Finset.sum_eq_zero
  intro k _hk
  by_cases hki : k = i
  · subst k
    rw [hrotateApply]
    simp only [Pi.single_apply, if_pos, mul_one]
    rw [if_neg]
    exact hshiftNe i ((j : ℕ) + 1) (by omega) (by omega)
  · simp [hki]

/-- Under self-dual normal-basis coordinates, Relation (56) is the
finite-field Kerdock trace formula. The hypotheses state the Frobenius
rotation, absolute-trace coordinate sum, and self-dual trace pairing. -/
theorem completeQuadraticBit_eq_kerdockFieldRepresentative_one_of_selfDualNormalCoordinates
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (hnormal : ∀ x : FABL.F₂Cube (2 * t + 1),
      theta (fun i ↦ x (finRotate (2 * t + 1) i)) =
        (theta x) ^ 2)
    (htrace : ∀ x : FABL.F₂Cube (2 * t + 1),
      absoluteTrace (2 * t + 1) (theta x) = ∑ i, x i)
    (hselfDual : ∀ x y : FABL.F₂Cube (2 * t + 1),
      absoluteTrace (2 * t + 1) (theta x * theta y) =
        ∑ i, x i * y i) :
    (FABL.completeQuadraticBit : BooleanFunction ((2 * t + 1) + 1)) =
      kerdockFieldRepresentative t theta 1 := by
  let split := cubeSplitLinearEquiv (2 * t + 1) 1
  let field := kerdockFieldRepresentative t theta 1
  let difference : BooleanFunction ((2 * t + 1) + 1) :=
    FABL.completeQuadraticBit + field
  have hpolar : ∀ a b, quadraticPolarKernel difference a b = 0 := by
    intro a b
    let x := (split a).1
    let z := (split a).2
    let y := (split b).1
    let r := (split b).2
    have ha : a = Fin.append x z := by
      apply split.injective
      simp [split, x, z, cubeSplitLinearEquiv]
    have hb : b = Fin.append y r := by
      apply split.injective
      simp [split, y, r, cubeSplitLinearEquiv]
    have hdifference :
        quadraticPolarKernel difference a b =
          quadraticPolarKernel
              (FABL.completeQuadraticBit :
                BooleanFunction ((2 * t + 1) + 1)) a b +
            quadraticPolarKernel field a b := by
      simp only [difference, quadraticPolarKernel_eq, Pi.add_apply]
      ring
    have hsumA :
        (∑ i, Fin.append x z i) = (∑ i, x i) + z 0 := by
      rw [Fin.sum_univ_add]
      simp
    have hsumB :
        (∑ i, Fin.append y r i) = (∑ i, y i) + r 0 := by
      rw [Fin.sum_univ_add]
      simp
    have hdot :
        (∑ i, Fin.append x z i * Fin.append y r i) =
          (∑ i, x i * y i) + z 0 * r 0 := by
      rw [Fin.sum_univ_add]
      simp
    have hfieldA :
        kerdockFieldCoordinateEquiv t theta (Fin.append x z) =
          (theta x, z 0) := by
      simp [kerdockFieldCoordinateEquiv, cubeSplitLinearEquiv]
    have hfieldB :
        kerdockFieldCoordinateEquiv t theta (Fin.append y r) =
          (theta y, r 0) := by
      simp [kerdockFieldCoordinateEquiv, cubeSplitLinearEquiv]
    rw [hdifference, ha, hb, completeQuadraticPolar_eq_totalProduct_add_dot]
    rw [hsumA, hsumB, hdot]
    rw [quadraticPolarKernel_kerdockFieldRepresentative]
    rw [hfieldA, hfieldB]
    simp only [one_mul, one_pow]
    rw [htrace, htrace, hselfDual]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  obtain ⟨c, frequency, haffine⟩ :=
    exists_affineFunction_of_quadraticPolarKernel_eq_zero difference hpolar
  have hc : c = 0 := by
    have hzero := congrFun haffine 0
    symm
    simpa [difference, field, kerdockFieldRepresentative,
      kerdockFieldQuadratic, kerdockTraceQuadratic, oddQuadraticTracePart,
      FABL.affineFunction, FABL.f₂DotProduct,
      completeQuadraticBit_zero] using hzero
  have hfieldSingle (i : Fin ((2 * t + 1) + 1)) :
      field (Pi.single i 1) = 0 := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [← append_single_eq_single_castAdd j]
      have hbasis :=
        kerdockTraceQuadratic_basis_eq_zero_of_selfDualNormalCoordinates
          t theta hnormal hselfDual j
      simp [field, kerdockFieldRepresentative, kerdockFieldCoordinateEquiv,
        cubeSplitLinearEquiv, kerdockFieldQuadratic, hbasis]
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [← append_one_eq_single_natAdd]
      dsimp only [field, kerdockFieldRepresentative]
      rw [show kerdockFieldCoordinateEquiv t theta
          (Fin.append (0 : FABL.F₂Cube (2 * t + 1))
            (1 : FABL.F₂Cube 1)) = (0, 1) by
        simp [kerdockFieldCoordinateEquiv, cubeSplitLinearEquiv]
        rfl]
      simp [kerdockFieldQuadratic, kerdockTraceQuadratic,
        oddQuadraticTracePart]
  have hfrequency : frequency = 0 := by
    funext i
    have hi := congrFun haffine (Pi.single i 1)
    have hcomplete := completeQuadraticBit_single i
    rw [hc] at hi
    simp only [difference, Pi.add_apply, hcomplete, hfieldSingle, zero_add,
      FABL.affineFunction, FABL.f₂DotProduct, zero_add] at hi
    rw [dotProduct_single] at hi
    simpa using hi.symm
  funext a
  have haffineA := congrFun haffine a
  rw [hc, hfrequency] at haffineA
  simp only [difference, Pi.add_apply, FABL.affineFunction,
    FABL.f₂DotProduct, zero_add, zero_dotProduct] at haffineA
  exact (add_eq_zero_iff_eq_neg.mp haffineA).trans
    (ZModModule.neg_eq_self _)

end CryptBoolean
