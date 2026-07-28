/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter05.QuadraticTraceRepresentation
public import CryptBoolean.Carlet.Chapter06.Kerdock
public import CryptBoolean.Carlet.Chapter06.QuadraticBent

/-!
# Finite-field construction of Kerdock representatives

The odd-dimensional trace quadratic, its one-coordinate extension, and the
resulting finite family of quadratic representatives with pairwise bent sums.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- The homogeneous trace quadratic used in the Kerdock construction. -/
noncomputable def kerdockTraceQuadratic (t : ℕ) :
    FieldBooleanFunction (2 * t + 1) :=
  oddQuadraticTracePart t (fun _ ↦ 1)

/-- The field-coordinate Kerdock representative indexed by `u`. -/
noncomputable def kerdockFieldQuadratic (t : ℕ)
    (u x : BinaryGaloisField (2 * t + 1)) (z : FABL.𝔽₂) : FABL.𝔽₂ :=
  kerdockTraceQuadratic t (u * x) + z * absoluteTrace (2 * t + 1) (u * x)

private theorem kerdockFrobeniusCoefficientSum (t : ℕ)
    (x : BinaryGaloisField (2 * t + 1)) :
    (∑ i : Fin t,
        (x ^ (2 ^ ((i : ℕ) + 1)) +
          x ^ (2 ^ ((2 * t + 1) - ((i : ℕ) + 1))))) =
      algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1))
          (absoluteTrace (2 * t + 1) x) + x := by
  rw [algebraMap_absoluteTrace_eq_sum_frobenius (by omega)]
  rw [Finset.sum_add_distrib]
  let f : ℕ → BinaryGaloisField (2 * t + 1) := fun i ↦ x ^ (2 ^ i)
  have hfirst :
      (∑ i : Fin t, x ^ (2 ^ ((i : ℕ) + 1))) =
        ∑ i ∈ Finset.range t, f (i + 1) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1)) t
  have hsecond :
      (∑ i : Fin t, x ^ (2 ^ ((2 * t + 1) - ((i : ℕ) + 1)))) =
        ∑ i ∈ Finset.range t, f ((2 * t + 1) - (i + 1)) :=
    Fin.sum_univ_eq_sum_range
      (fun i ↦ f ((2 * t + 1) - (i + 1))) t
  rw [hfirst, hsecond]
  change (∑ i ∈ Finset.range t, f (i + 1)) +
      (∑ i ∈ Finset.range t, f ((2 * t + 1) - (i + 1))) =
        (∑ i ∈ Finset.range (2 * t + 1), f i) + x
  have hreflect :
      (∑ i ∈ Finset.range t, f ((2 * t + 1) - (i + 1))) =
        ∑ i ∈ Finset.range t, f (t + 1 + i) := by
    calc
      (∑ i ∈ Finset.range t, f ((2 * t + 1) - (i + 1))) =
          ∑ i ∈ Finset.range t, f (t + 1 + (t - 1 - i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        have hit : i < t := Finset.mem_range.mp hi
        omega
      _ = ∑ i ∈ Finset.range t, f (t + 1 + i) :=
        Finset.sum_range_reflect (fun i ↦ f (t + 1 + i)) t
  rw [hreflect]
  have hrange :
      (∑ i ∈ Finset.range (2 * t + 1), f i) =
        (∑ i ∈ Finset.range (2 * t), f (i + 1)) + f 0 := by
    simpa only [Nat.succ_eq_add_one] using
      (Finset.sum_range_succ' f (2 * t))
  rw [hrange]
  have hsplit :
      (∑ i ∈ Finset.range (2 * t), f (i + 1)) =
        (∑ i ∈ Finset.range t, f (i + 1)) +
          ∑ i ∈ Finset.range t, f (t + 1 + i) := by
    simpa only [two_mul, add_assoc, add_comm, add_left_comm] using
      (Finset.sum_range_add (f := fun i ↦ f (i + 1)) t t)
  rw [hsplit]
  have hfzero : f 0 = x := by simp [f]
  rw [hfzero]
  change (∑ i ∈ Finset.range t, f (i + 1)) +
      (∑ i ∈ Finset.range t, f (t + 1 + i)) =
        ((∑ i ∈ Finset.range t, f (i + 1)) +
          (∑ i ∈ Finset.range t, f (t + 1 + i)) + x) + x
  rw [add_assoc, ZModModule.add_self, add_zero]

/-- The polar form of the odd-dimensional trace quadratic is the sum of the
trace-product form and the trace pairing. -/
theorem kerdockTraceQuadratic_polar (t : ℕ)
    (x y : BinaryGaloisField (2 * t + 1)) :
    kerdockTraceQuadratic t (x + y) +
        kerdockTraceQuadratic t x + kerdockTraceQuadratic t y =
      absoluteTrace (2 * t + 1) x * absoluteTrace (2 * t + 1) y +
        absoluteTrace (2 * t + 1) (x * y) := by
  have hpolar := oddQuadraticTracePart_polar_eq_sum t
    (fun _ ↦ 1) x y
  have hzero : oddQuadraticTracePart t (fun _ ↦ 1) 0 = 0 := by
    simp [oddQuadraticTracePart]
  rw [hzero, add_zero] at hpolar
  change oddQuadraticTracePart t (fun _ ↦ 1) (x + y) +
      oddQuadraticTracePart t (fun _ ↦ 1) x +
        oddQuadraticTracePart t (fun _ ↦ 1) y = _
  rw [hpolar]
  simp only [one_mul]
  have hadjoint (i : Fin t) :
      absoluteTrace (2 * t + 1)
          (x * y ^ (2 ^ ((i : ℕ) + 1))) =
        absoluteTrace (2 * t + 1)
          (x ^ (2 ^ ((2 * t + 1) - ((i : ℕ) + 1))) * y) := by
    exact absoluteTrace_mul_frobeniusPow
      (2 * t + 1) ((i : ℕ) + 1) (by omega) (by omega) x y
  calc
    (∑ i : Fin t, absoluteTrace (2 * t + 1)
        (x ^ (2 ^ ((i : ℕ) + 1)) * y +
          x * y ^ (2 ^ ((i : ℕ) + 1)))) =
        ∑ i : Fin t, absoluteTrace (2 * t + 1)
          ((x ^ (2 ^ ((i : ℕ) + 1)) +
              x ^ (2 ^ ((2 * t + 1) - ((i : ℕ) + 1)))) * y) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_add, hadjoint i, ← map_add, add_mul]
    _ = absoluteTrace (2 * t + 1)
        ((∑ i : Fin t,
            (x ^ (2 ^ ((i : ℕ) + 1)) +
              x ^ (2 ^ ((2 * t + 1) - ((i : ℕ) + 1))))) * y) := by
      rw [Finset.sum_mul, map_sum]
    _ = absoluteTrace (2 * t + 1)
        ((algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1))
            (absoluteTrace (2 * t + 1) x) + x) * y) := by
      rw [kerdockFrobeniusCoefficientSum]
    _ = absoluteTrace (2 * t + 1) x * absoluteTrace (2 * t + 1) y +
        absoluteTrace (2 * t + 1) (x * y) := by
      rw [add_mul, map_add, ← Algebra.smul_def, map_smul]
      rfl

/-- On an odd binary extension, the absolute trace restricts to the identity
on the prime field. -/
@[simp] theorem absoluteTrace_algebraMap_odd (t : ℕ) (c : FABL.𝔽₂) :
    absoluteTrace (2 * t + 1)
        (algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) c) = c := by
  rw [absoluteTrace, Algebra.trace_algebraMap,
    GaloisField.finrank 2 (by omega)]
  rw [nsmul_eq_mul]
  push_cast
  simp only [CharTwo.two_eq_zero, zero_mul, zero_add, one_mul]

/-- The odd-dimensional trace quadratic pulled back to binary coordinates. -/
noncomputable def kerdockTraceCube (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    BooleanFunction (2 * t + 1) :=
  fun x ↦ kerdockTraceQuadratic t (u * theta x)

/-- The linear trace character paired with the Kerdock field parameter. -/
noncomputable def kerdockTraceLinearCube (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    BooleanFunction (2 * t + 1) :=
  fun x ↦ absoluteTrace (2 * t + 1) (u * theta x)

/-- The binary-coordinate trace quadratic has algebraic degree at most two. -/
theorem functionAlgebraicDegree_kerdockTraceCube_le_two
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    FABL.functionAlgebraicDegree (kerdockTraceCube t theta u) ≤ 2 := by
  by_cases ht : t = 0
  · subst t
    have hzero : kerdockTraceCube 0 theta u = 0 := by
      funext x
      simp [kerdockTraceCube, kerdockTraceQuadratic,
        oddQuadraticTracePart]
    simp [hzero]
  · let term (i : Fin t) : BooleanFunction (2 * t + 1) :=
      fun x ↦ absoluteTrace (2 * t + 1)
        (u ^ (2 ^ ((i : ℕ) + 1) + 1) *
          (theta x) ^ (2 ^ ((i : ℕ) + 1) + 1))
    have hdecomposition :
        kerdockTraceCube t theta u = ∑ i, term i := by
      funext x
      simp only [kerdockTraceCube, kerdockTraceQuadratic,
        oddQuadraticTracePart, binaryFrobeniusLinear_apply, one_mul,
        map_sum, Finset.sum_apply, term]
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      rw [mul_pow, pow_add, pow_add, pow_one, pow_one]
      ring
    rw [hdecomposition]
    apply FABL.functionAlgebraicDegree_finset_sum_le Finset.univ term 2
    intro i _hi
    apply functionAlgebraicDegree_traceMonomial_two_pow_add_one_le_two
      (by omega : 0 < 2 * t + 1)
    exact two_pow_add_one_lt_odd_modulus t (Nat.pos_of_ne_zero ht)
      ⟨(i : ℕ) + 1, by omega⟩

/-- The trace character paired with `u` is affine-linear. -/
theorem functionAlgebraicDegree_kerdockTraceLinearCube_le_one
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    FABL.functionAlgebraicDegree
      (kerdockTraceLinearCube t theta u) ≤ 1 := by
  have hlinear : FABL.IsF₂Linear (kerdockTraceLinearCube t theta u) := by
    intro x y
    simp [kerdockTraceLinearCube, mul_add]
  obtain ⟨a, ha⟩ := (FABL.isF₂Linear_iff_exists_dotProduct _).mp hlinear
  have heq : kerdockTraceLinearCube t theta u =
      FABL.affineFunction 0 a := by
    funext x
    rw [ha x]
    simp [FABL.affineFunction]
  rw [heq]
  exact FABL.functionAlgebraicDegree_affineFunction_le_one 0 a

/-- Coordinates on the Kerdock ambient cube, split into the odd-dimensional
field coordinate and the final bit. -/
noncomputable def kerdockFieldCoordinateEquiv (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    FABL.F₂Cube ((2 * t + 1) + 1) ≃ₗ[FABL.𝔽₂]
      (BinaryGaloisField (2 * t + 1) × FABL.𝔽₂) :=
  (cubeSplitLinearEquiv (2 * t + 1) 1).trans
    (theta.prodCongr (LinearEquiv.funUnique (Fin 1) FABL.𝔽₂ FABL.𝔽₂))

/-- The Boolean representative obtained by transporting the field-coordinate
quadratic to the canonical binary cube. -/
noncomputable def kerdockFieldRepresentative (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    BooleanFunction ((2 * t + 1) + 1) :=
  fun a ↦
    let p := kerdockFieldCoordinateEquiv t theta a
    kerdockFieldQuadratic t u p.1 p.2

@[simp] theorem kerdockFieldRepresentative_coordinate
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u x : BinaryGaloisField (2 * t + 1)) (z : FABL.𝔽₂) :
    kerdockFieldRepresentative t theta u
        ((kerdockFieldCoordinateEquiv t theta).symm (x, z)) =
      kerdockFieldQuadratic t u x z := by
  simp [kerdockFieldRepresentative]

@[simp] theorem kerdockFieldRepresentative_zero
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    kerdockFieldRepresentative t theta 0 = 0 := by
  funext a
  simp [kerdockFieldRepresentative, kerdockFieldQuadratic,
    kerdockTraceQuadratic, oddQuadraticTracePart]

/-- Every finite-field Kerdock representative has algebraic degree at most
two. -/
theorem functionAlgebraicDegree_kerdockFieldRepresentative_le_two
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) :
    FABL.functionAlgebraicDegree
      (kerdockFieldRepresentative t theta u) ≤ 2 := by
  let e := kerdockFieldCoordinateEquiv t theta
  let fieldPart :=
    (LinearMap.fst FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) FABL.𝔽₂).comp
      e.toLinearMap
  let prefixMap :=
    theta.symm.toLinearMap.comp fieldPart
  let bitPart :=
    (LinearMap.snd FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) FABL.𝔽₂).comp
      e.toLinearMap
  let final :=
    (LinearEquiv.funUnique (Fin 1) FABL.𝔽₂ FABL.𝔽₂).symm.toLinearMap.comp
      bitPart
  let quadraticPull : BooleanFunction ((2 * t + 1) + 1) :=
    kerdockTraceCube t theta u ∘ prefixMap.toAffineMap
  let linearPull : BooleanFunction ((2 * t + 1) + 1) :=
    kerdockTraceLinearCube t theta u ∘ prefixMap.toAffineMap
  let lastBit : BooleanFunction ((2 * t + 1) + 1) :=
    fun a ↦ final a 0
  have hdecomposition :
      kerdockFieldRepresentative t theta u =
        quadraticPull + lastBit * linearPull := by
    funext a
    simp [kerdockFieldRepresentative, kerdockFieldQuadratic,
      quadraticPull, linearPull, lastBit, prefixMap, fieldPart, final, bitPart,
      e, kerdockTraceCube, kerdockTraceLinearCube]
  have hquadratic :
      FABL.functionAlgebraicDegree quadraticPull ≤ 2 :=
    (functionAlgebraicDegree_comp_affineMap_le_general
      (kerdockTraceCube t theta u) prefixMap.toAffineMap).trans
        (functionAlgebraicDegree_kerdockTraceCube_le_two t theta u)
  have hlinear :
      FABL.functionAlgebraicDegree linearPull ≤ 1 :=
    (functionAlgebraicDegree_comp_affineMap_le_general
      (kerdockTraceLinearCube t theta u) prefixMap.toAffineMap).trans
        (functionAlgebraicDegree_kerdockTraceLinearCube_le_one t theta u)
  have hlast : FABL.functionAlgebraicDegree lastBit ≤ 1 := by
    exact functionAlgebraicDegree_affineMap_coordinate_le_one_general
      final.toAffineMap 0
  rw [hdecomposition]
  apply (FABL.functionAlgebraicDegree_add_le_max quadraticPull
    (lastBit * linearPull)).trans
  apply max_le hquadratic
  exact (FABL.functionAlgebraicDegree_mul_le_add lastBit linearPull).trans
    (Nat.add_le_add hlast hlinear |>.trans (by omega))

/-- The polar form of one field-coordinate Kerdock representative. -/
theorem quadraticPolarKernel_kerdockFieldRepresentative
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1))
    (a b : FABL.F₂Cube ((2 * t + 1) + 1)) :
    let xz := kerdockFieldCoordinateEquiv t theta a
    let yr := kerdockFieldCoordinateEquiv t theta b
    quadraticPolarKernel (kerdockFieldRepresentative t theta u) a b =
      absoluteTrace (2 * t + 1) (u * xz.1) *
          absoluteTrace (2 * t + 1) (u * yr.1) +
        absoluteTrace (2 * t + 1) (u ^ 2 * (xz.1 * yr.1)) +
        xz.2 * absoluteTrace (2 * t + 1) (u * yr.1) +
        yr.2 * absoluteTrace (2 * t + 1) (u * xz.1) := by
  dsimp only
  rw [quadraticPolarKernel_eq]
  have hzero : kerdockTraceQuadratic t 0 = 0 := by
    simp [kerdockTraceQuadratic, oddQuadraticTracePart]
  simp only [kerdockFieldRepresentative, map_add, Prod.fst_add, Prod.snd_add,
    kerdockFieldQuadratic, map_zero, Prod.fst_zero, Prod.snd_zero, mul_zero,
    hzero, add_zero]
  rw [show u *
      ((kerdockFieldCoordinateEquiv t theta a).1 +
        (kerdockFieldCoordinateEquiv t theta b).1) =
      u * (kerdockFieldCoordinateEquiv t theta a).1 +
        u * (kerdockFieldCoordinateEquiv t theta b).1 by ring]
  simp only [map_add]
  have hpolar := kerdockTraceQuadratic_polar t
    (u * (kerdockFieldCoordinateEquiv t theta a).1)
    (u * (kerdockFieldCoordinateEquiv t theta b).1)
  have hproduct :
      (u * (kerdockFieldCoordinateEquiv t theta a).1) *
          (u * (kerdockFieldCoordinateEquiv t theta b).1) =
        u ^ 2 *
          ((kerdockFieldCoordinateEquiv t theta a).1 *
            (kerdockFieldCoordinateEquiv t theta b).1) := by
    ring
  let cross : FABL.𝔽₂ :=
    (kerdockFieldCoordinateEquiv t theta a).2 *
        absoluteTrace (2 * t + 1)
          (u * (kerdockFieldCoordinateEquiv t theta b).1) +
      (kerdockFieldCoordinateEquiv t theta b).2 *
        absoluteTrace (2 * t + 1)
          (u * (kerdockFieldCoordinateEquiv t theta a).1)
  have hwithCross := congrArg (fun c : FABL.𝔽₂ ↦ c + cross) hpolar
  rw [hproduct] at hwithCross
  dsimp only [cross] at hwithCross
  ring_nf at hwithCross ⊢
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero] at hwithCross ⊢
  exact hwithCross

/-- The polar form of the sum of two representatives, expressed through
their parameter sum. -/
theorem quadraticPolarKernel_kerdockFieldRepresentative_add
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u v : BinaryGaloisField (2 * t + 1))
    (a b : FABL.F₂Cube ((2 * t + 1) + 1)) :
    let xz := kerdockFieldCoordinateEquiv t theta a
    let yr := kerdockFieldCoordinateEquiv t theta b
    let w := u + v
    quadraticPolarKernel
        (kerdockFieldRepresentative t theta u +
          kerdockFieldRepresentative t theta v) a b =
      absoluteTrace (2 * t + 1) (u * xz.1) *
          absoluteTrace (2 * t + 1) (u * yr.1) +
        absoluteTrace (2 * t + 1) (v * xz.1) *
          absoluteTrace (2 * t + 1) (v * yr.1) +
        absoluteTrace (2 * t + 1) (w ^ 2 * (xz.1 * yr.1)) +
        xz.2 * absoluteTrace (2 * t + 1) (w * yr.1) +
        yr.2 * absoluteTrace (2 * t + 1) (w * xz.1) := by
  dsimp only
  have hadd : quadraticPolarKernel
      (kerdockFieldRepresentative t theta u +
        kerdockFieldRepresentative t theta v) a b =
      quadraticPolarKernel (kerdockFieldRepresentative t theta u) a b +
        quadraticPolarKernel (kerdockFieldRepresentative t theta v) a b := by
    simp only [quadraticPolarKernel_eq, Pi.add_apply]
    ring
  have hsquare : (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add]
  rw [hadd,
    quadraticPolarKernel_kerdockFieldRepresentative t theta u a b,
    quadraticPolarKernel_kerdockFieldRepresentative t theta v a b,
    hsquare]
  simp only [add_mul, map_add, mul_add]
  ring

/-- Distinct field parameters give a sum whose quadratic polar form has
trivial radical. -/
theorem eq_zero_of_forall_quadraticPolarKernel_kerdockFieldRepresentative_add
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u v : BinaryGaloisField (2 * t + 1)) (huv : u ≠ v)
    (a : FABL.F₂Cube ((2 * t + 1) + 1))
    (ha : ∀ b, quadraticPolarKernel
      (kerdockFieldRepresentative t theta u +
        kerdockFieldRepresentative t theta v) a b = 0) :
    a = 0 := by
  let e := kerdockFieldCoordinateEquiv t theta
  let w := u + v
  let x := (e a).1
  let z := (e a).2
  have hw : w ≠ 0 := by
    intro hwzero
    apply huv
    have h := congrArg (fun c ↦ c + v) hwzero
    simpa only [w, add_assoc, ZModModule.add_self, add_zero, zero_add] using h
  have htrace : absoluteTrace (2 * t + 1) (w * x) = 0 := by
    have h := ha (e.symm (0, 1))
    rw [quadraticPolarKernel_kerdockFieldRepresentative_add
      t theta u v a (e.symm (0, 1))] at h
    simpa [e, w, x] using h
  have htraceUV :
      absoluteTrace (2 * t + 1) (u * x) =
        absoluteTrace (2 * t + 1) (v * x) := by
    have hsum :
        absoluteTrace (2 * t + 1) (u * x) +
          absoluteTrace (2 * t + 1) (v * x) = 0 := by
      simpa [w, add_mul, map_add] using htrace
    have h := congrArg (fun c ↦ c +
      absoluteTrace (2 * t + 1) (v * x)) hsum
    simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using h
  have hforall (y : BinaryGaloisField (2 * t + 1)) :
      absoluteTrace (2 * t + 1) (u * x) *
          absoluteTrace (2 * t + 1) (u * y) +
        absoluteTrace (2 * t + 1) (v * x) *
          absoluteTrace (2 * t + 1) (v * y) +
        absoluteTrace (2 * t + 1) (w ^ 2 * (x * y)) +
        z * absoluteTrace (2 * t + 1) (w * y) = 0 := by
    have h := ha (e.symm (y, 0))
    rw [quadraticPolarKernel_kerdockFieldRepresentative_add
      t theta u v a (e.symm (y, 0))] at h
    simpa [e, w, x, z] using h
  let s := absoluteTrace (2 * t + 1) (u * x)
  let c : BinaryGaloisField (2 * t + 1) :=
    algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) s * w +
      w ^ 2 * x +
      algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) z * w
  have hpair (y : BinaryGaloisField (2 * t + 1)) :
      absoluteTrace (2 * t + 1) (c * y) = 0 := by
    calc
      absoluteTrace (2 * t + 1) (c * y) =
          s * absoluteTrace (2 * t + 1) (w * y) +
            absoluteTrace (2 * t + 1) (w ^ 2 * (x * y)) +
            z * absoluteTrace (2 * t + 1) (w * y) := by
        simp only [c, add_mul, map_add, mul_assoc]
        rw [← Algebra.smul_def, map_smul, ← Algebra.smul_def, map_smul]
        simp only [smul_eq_mul]
      _ = 0 := by
        simpa [s, w, add_mul, map_add, mul_add, htraceUV] using hforall y
  letI : Algebra.IsAlgebraic FABL.𝔽₂
      (BinaryGaloisField (2 * t + 1)) :=
    Algebra.IsIntegral.isAlgebraic
  letI : Algebra.IsSeparable FABL.𝔽₂
      (BinaryGaloisField (2 * t + 1)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hc : c = 0 := by
    apply (traceForm_nondegenerate FABL.𝔽₂
      (BinaryGaloisField (2 * t + 1))).1
    intro y
    rw [Algebra.traceForm_apply]
    exact hpair y
  have hfactor :
      w * (algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) s +
        w * x +
        algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) z) = 0 := by
    calc
      w * (algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) s +
          w * x +
          algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) z) = c := by
        dsimp only [c]
        ring
      _ = 0 := hc
  have hinner :
      algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) s +
        w * x +
        algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) z = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hw
  have hwx :
      w * x = algebraMap FABL.𝔽₂
        (BinaryGaloisField (2 * t + 1)) (s + z) := by
    rw [map_add]
    linear_combination
      (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hinner
  have hsz : s + z = 0 := by
    have h := congrArg (absoluteTrace (2 * t + 1)) hwx
    rw [htrace, absoluteTrace_algebraMap_odd] at h
    exact h.symm
  have hwxzero : w * x = 0 := by
    rw [hwx, hsz, map_zero]
  have hx : x = 0 := (mul_eq_zero.mp hwxzero).resolve_left hw
  have hs : s = 0 := by
    simp [s, hx]
  have hzMap :
      algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1)) z = 0 := by
    simpa [hs, hx] using hinner
  have hz : z = 0 := by
    apply (algebraMap FABL.𝔽₂ (BinaryGaloisField (2 * t + 1))).injective
    simpa using hzMap
  apply e.injective
  rw [map_zero]
  apply Prod.ext
  · simpa [x] using hx
  · simpa [z] using hz

/-- Distinct field parameters index representatives with bent pairwise sum. -/
theorem isBent_kerdockFieldRepresentative_add
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u v : BinaryGaloisField (2 * t + 1)) (huv : u ≠ v) :
    IsBent (kerdockFieldRepresentative t theta u +
      kerdockFieldRepresentative t theta v) := by
  let f := kerdockFieldRepresentative t theta u +
    kerdockFieldRepresentative t theta v
  have hdegree : FABL.functionAlgebraicDegree f ≤ 2 :=
    (FABL.functionAlgebraicDegree_add_le_max
      (kerdockFieldRepresentative t theta u)
      (kerdockFieldRepresentative t theta v)).trans
        (max_le
          (functionAlgebraicDegree_kerdockFieldRepresentative_le_two
            t theta u)
          (functionAlgebraicDegree_kerdockFieldRepresentative_le_two
            t theta v))
  apply (isBent_iff_quadraticRadical_eq_bot f hdegree).2
  ext a
  constructor
  · intro ha
    have hall := (mem_quadraticRadical_iff f hdegree a).mp ha
    have hazero :=
      eq_zero_of_forall_quadraticPolarKernel_kerdockFieldRepresentative_add
        t theta u v huv a hall
    simp [hazero]
  · intro ha
    have hazero : a = 0 := by simpa using ha
    subst a
    exact Submodule.zero_mem _

private theorem functionAlgebraicDegree_eq_two_of_isBent_of_le_two
    {n : ℕ} (f : BooleanFunction n) (hf : IsBent f)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) (hn : 2 ≤ n) :
    FABL.functionAlgebraicDegree f = 2 := by
  apply Nat.le_antisymm hdegree
  by_contra hnot
  have hdegreeOne : FABL.functionAlgebraicDegree f ≤ 1 := by omega
  obtain ⟨b, a, hfa⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      f hdegreeOne
  have hnonlinearity :=
    nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent f hf hn
  rw [hfa, nonlinearity_affineFunction] at hnonlinearity
  have hexponents : n / 2 - 1 < n - 1 := by
    rcases even_of_isBent f hf with ⟨k, rfl⟩
    omega
  have hpowers : 2 ^ (n / 2 - 1) < 2 ^ (n - 1) :=
    Nat.pow_lt_pow_right (by omega) hexponents
  omega

/-- A representative with nonzero field parameter is genuinely quadratic. -/
theorem functionAlgebraicDegree_kerdockFieldRepresentative_eq_two
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1))
    (u : BinaryGaloisField (2 * t + 1)) (hu : u ≠ 0) :
    FABL.functionAlgebraicDegree
      (kerdockFieldRepresentative t theta u) = 2 := by
  have hbent : IsBent (kerdockFieldRepresentative t theta u) := by
    simpa using isBent_kerdockFieldRepresentative_add t theta u 0 hu
  exact functionAlgebraicDegree_eq_two_of_isBent_of_le_two
    (kerdockFieldRepresentative t theta u) hbent
    (functionAlgebraicDegree_kerdockFieldRepresentative_le_two t theta u)
    (by omega)

/-- Distinct field parameters determine distinct Boolean representatives. -/
theorem kerdockFieldRepresentative_injective
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    Function.Injective (kerdockFieldRepresentative t theta) := by
  intro u v huv
  by_contra hne
  have hbent := isBent_kerdockFieldRepresentative_add t theta u v hne
  have hdegree := functionAlgebraicDegree_eq_two_of_isBent_of_le_two
    (kerdockFieldRepresentative t theta u +
      kerdockFieldRepresentative t theta v)
    hbent
    ((FABL.functionAlgebraicDegree_add_le_max
      (kerdockFieldRepresentative t theta u)
      (kerdockFieldRepresentative t theta v)).trans
        (max_le
          (functionAlgebraicDegree_kerdockFieldRepresentative_le_two
            t theta u)
          (functionAlgebraicDegree_kerdockFieldRepresentative_le_two
            t theta v)))
    (by omega)
  have hzero : kerdockFieldRepresentative t theta u +
      kerdockFieldRepresentative t theta v = 0 := by
    funext a
    simp only [Pi.add_apply]
    rw [huv, ZModModule.add_self]
    rfl
  rw [hzero, FABL.functionAlgebraicDegree_zero] at hdegree
  omega

/-- The finite set of all Kerdock representatives indexed by the odd binary
field. -/
noncomputable def kerdockFieldRepresentativeFamily (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    Finset (BooleanFunction ((2 * t + 1) + 1)) := by
  classical
  letI : Fintype (BinaryGaloisField (2 * t + 1)) := Fintype.ofFinite _
  exact Finset.univ.image (kerdockFieldRepresentative t theta)

/-- The finite-field representative set has one member for every field
parameter. -/
theorem card_kerdockFieldRepresentativeFamily
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    (kerdockFieldRepresentativeFamily t theta).card = 2 ^ (2 * t + 1) := by
  classical
  letI : Fintype (BinaryGaloisField (2 * t + 1)) := Fintype.ofFinite _
  rw [kerdockFieldRepresentativeFamily,
    Finset.card_image_of_injective]
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      GaloisField.card 2 (2 * t + 1) (by omega)]
  · exact kerdockFieldRepresentative_injective t theta

/-- The explicit finite-field family satisfies the Kerdock representative
conditions. -/
theorem isKerdockRepresentativeFamily_kerdockField
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    IsKerdockRepresentativeFamily
      (kerdockFieldRepresentativeFamily t theta) := by
  classical
  letI : Fintype (BinaryGaloisField (2 * t + 1)) := Fintype.ofFinite _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kerdockFieldRepresentativeFamily]
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_univ 0, kerdockFieldRepresentative_zero t theta⟩
  · intro f hf hfzero
    rw [kerdockFieldRepresentativeFamily] at hf
    obtain ⟨u, _huMem, rfl⟩ := Finset.mem_image.mp hf
    apply functionAlgebraicDegree_kerdockFieldRepresentative_eq_two
    intro hu
    subst u
    exact hfzero (kerdockFieldRepresentative_zero t theta)
  · intro f hf g hg hfg
    rw [kerdockFieldRepresentativeFamily] at hf hg
    obtain ⟨u, _huMem, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨v, _hvMem, rfl⟩ := Finset.mem_image.mp hg
    apply isBent_kerdockFieldRepresentative_add t theta u v
    intro huv
    subst v
    exact hfg rfl
  · rw [card_kerdockFieldRepresentativeFamily]
    congr 1

/-- The explicit field representatives and their first-order coset union
have the Kerdock parameters. -/
theorem kerdockFieldConstruction_parameters
    (t : ℕ)
    (theta : FABL.F₂Cube (2 * t + 1) ≃ₗ[FABL.𝔽₂]
      BinaryGaloisField (2 * t + 1)) :
    let F := kerdockFieldRepresentativeFamily t theta
    IsKerdockRepresentativeFamily F ∧
      F.offDiag.Nonempty ∧
      HasDistinctFirstOrderCosets F ∧
      (∀ c : BooleanFunction ((2 * t + 1) + 1),
        c ∈ reedMuller 1 ((2 * t + 1) + 1) →
          c ∈ kerdockCodeOfRepresentatives F) ∧
      (∀ c : BooleanFunction ((2 * t + 1) + 1),
        c ∈ kerdockCodeOfRepresentatives F →
          c ∈ reedMuller 2 ((2 * t + 1) + 1)) ∧
      (kerdockCodeOfRepresentatives F).card =
        2 ^ (2 * ((2 * t + 1) + 1)) ∧
      minimumHammingDistance (kerdockCodeOfRepresentatives F) =
        2 ^ (((2 * t + 1) + 1) - 1) -
          2 ^ (((2 * t + 1) + 1) / 2 - 1) := by
  dsimp only
  have hF := isKerdockRepresentativeFamily_kerdockField t theta
  refine ⟨hF, ?_⟩
  exact kerdockCodeOfRepresentatives_parameters hF
    ⟨t + 1, by omega⟩ (by omega)

end CryptBoolean
