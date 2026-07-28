/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.HyperBent

/-!
# Hyper-bent partial-spread functions

Carlet Proposition 25: the quadratic-extension partial-spread construction
and its power-trace proof of hyper-bentness.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable local instance hyperBentPartialSpreadFieldFintype {r : ℕ} :
    Fintype (BinaryGaloisField r) :=
  Fintype.ofFinite (BinaryGaloisField r)

/-- In a quadratic binary extension, the kernel of the relative trace is
exactly the embedded middle field. -/
theorem relativeTrace_eq_zero_iff_mem_quadraticSubfield {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) :
    letI := iota.toAlgebra
    Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m)) x = 0 ↔
      x ∈ Set.range iota := by
  letI := iota.toAlgebra
  let tr := Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
  let subfield := Algebra.linearMap (BinaryGaloisField m)
    (BinaryGaloisField (2 * m))
  have hfinrank : Module.finrank (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) = 2 :=
    quadraticTraceMiddle_finrank hm.ne' iota
  have htwo : (2 : BinaryGaloisField m) = 0 := by
    change ((2 : ℕ) : BinaryGaloisField m) = 0
    exact CharP.cast_eq_zero (BinaryGaloisField m) 2
  have hsubfieldKer : subfield.range ≤ tr.ker := by
    rintro y ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    change Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m))
      (algebraMap (BinaryGaloisField m) (BinaryGaloisField (2 * m)) z) = 0
    rw [Algebra.trace_algebraMap, hfinrank]
    simp [htwo]
  have hsubfieldFinrank : Module.finrank (BinaryGaloisField m) subfield.range = 1 := by
    rw [LinearMap.finrank_range_of_inj]
    · exact Module.finrank_self (BinaryGaloisField m)
    · intro y z hyz
      exact iota.toRingHom.injective hyz
  have hkerFinrank : Module.finrank (BinaryGaloisField m) tr.ker = 1 := by
    have h := tr.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective
      (BinaryGaloisField m) (BinaryGaloisField (2 * m))), hfinrank] at h
    rw [finrank_top, Module.finrank_self] at h
    omega
  have heq : subfield.range = tr.ker :=
    Submodule.eq_of_le_of_finrank_eq hsubfieldKer
      (hsubfieldFinrank.trans hkerFinrank.symm)
  constructor
  · intro hx
    have hxker : x ∈ tr.ker := (LinearMap.mem_ker).2 hx
    rw [← heq] at hxker
    obtain ⟨z, hz⟩ := hxker
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    change tr (algebraMap (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) z) = 0
    rw [Algebra.trace_algebraMap, hfinrank]
    simp [htwo]

/-- The absolute trace of a product with an embedded middle-field element
factors through the relative trace. -/
theorem absoluteTrace_mul_quadraticSubfield {m : ℕ}
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) (y : BinaryGaloisField m) :
    letI := iota.toAlgebra
    absoluteTrace (2 * m) (x * iota y) =
      absoluteTrace m
        (Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m)) x * y) := by
  letI := iota.toAlgebra
  letI : IsScalarTower FABL.𝔽₂ (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  change Algebra.trace FABL.𝔽₂ (BinaryGaloisField (2 * m))
      (x * algebraMap (BinaryGaloisField m) (BinaryGaloisField (2 * m)) y) =
    Algebra.trace FABL.𝔽₂ (BinaryGaloisField m)
      (Algebra.trace (BinaryGaloisField m) (BinaryGaloisField (2 * m)) x * y)
  rw [← Algebra.trace_trace (R := FABL.𝔽₂) (S := BinaryGaloisField m)
    (T := BinaryGaloisField (2 * m))]
  congr 1
  rw [mul_comm x, ← Algebra.smul_def, map_smul]
  simp [mul_comm]

/-- Every nontrivial absolute-trace additive character has zero sum over a binary field. -/
theorem sum_bitSignInt_absoluteTrace_mul_eq_zero {m : ℕ}
    (t : BinaryGaloisField m) (ht : t ≠ 0) :
    (∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace m (t * y))) = 0 := by
  classical
  obtain ⟨u, hu⟩ := exists_absoluteTrace_eq_one m
  let y0 : BinaryGaloisField m := t⁻¹ * u
  have hy0 : absoluteTrace m (t * y0) = 1 := by
    change absoluteTrace m (t * (t⁻¹ * u)) = 1
    rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul, hu]
  let S : ℤ := ∑ y : BinaryGaloisField m,
    bitSignInt (absoluteTrace m (t * y))
  have hshift : S = ∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace m (t * (y + y0))) := by
    exact (Equiv.sum_comp (Equiv.addRight y0)
      (fun y : BinaryGaloisField m ↦
        bitSignInt (absoluteTrace m (t * y)))).symm
  have hneg : (∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace m (t * (y + y0)))) = -S := by
    rw [show (∑ y : BinaryGaloisField m,
        bitSignInt (absoluteTrace m (t * (y + y0)))) =
        ∑ y : BinaryGaloisField m,
          -bitSignInt (absoluteTrace m (t * y)) by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [mul_add, map_add, hy0, bitSignInt_add]
      norm_num [bitSignInt]]
    simp [S]
  rw [hneg] at hshift
  omega

/-- A quadratic-extension trace character sums to the middle-field cardinality
when its coefficient lies in the middle field. -/
theorem sum_quadraticSubfieldTraceCharacter_of_mem {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) (hx : x ∈ Set.range iota) :
    (∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace (2 * m) (x * iota y))) = (2 ^ m : ℤ) := by
  letI := iota.toAlgebra
  have htrace : Algebra.trace (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) x = 0 :=
    (relativeTrace_eq_zero_iff_mem_quadraticSubfield hm iota x).2 hx
  simp_rw [absoluteTrace_mul_quadraticSubfield iota]
  rw [htrace]
  simp only [zero_mul, map_zero]
  rw [show bitSignInt 0 = 1 by norm_num [bitSignInt], Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    GaloisField.card 2 m hm.ne']
  simp

/-- A quadratic-extension trace character sums to zero when its coefficient
lies outside the middle field. -/
theorem sum_quadraticSubfieldTraceCharacter_of_not_mem {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (x : BinaryGaloisField (2 * m)) (hx : x ∉ Set.range iota) :
    (∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace (2 * m) (x * iota y))) = 0 := by
  letI := iota.toAlgebra
  have htrace : Algebra.trace (BinaryGaloisField m)
      (BinaryGaloisField (2 * m)) x ≠ 0 := by
    intro hzero
    exact hx ((relativeTrace_eq_zero_iff_mem_quadraticSubfield hm iota x).1 hzero)
  simp_rw [absoluteTrace_mul_quadraticSubfield iota]
  exact sum_bitSignInt_absoluteTrace_mul_eq_zero _ htrace

/-- Dillon's partial-spread function in quadratic-extension coordinates, with
field division defining the zero-denominator case. -/
noncomputable def psapFunction {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (g : FieldBooleanFunction m) : FieldBooleanFunction (2 * m) :=
  fun x ↦
    let p := (quadraticSubfieldBasisEquiv hm iota omega homega).symm x
    g (p.1 / p.2)

/-- The partial-spread function evaluates to the quotient rule in its defining
quadratic-extension coordinates. -/
@[simp] theorem psapFunction_coordinate {m : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (g : FieldBooleanFunction m) (y' y : BinaryGaloisField m) :
    psapFunction hm iota omega homega g (iota y' + omega * iota y) =
      g (y' / y) := by
  unfold psapFunction
  let coord := quadraticSubfieldBasisEquiv hm iota omega homega
  change g ((coord.symm (coord (y', y))).1 /
    (coord.symm (coord (y', y))).2) = g (y' / y)
  rw [coord.symm_apply_apply]

/-- The sign sum of a field Boolean function vanishes when its pullback to the
Boolean cube is balanced. -/
theorem sum_bitSignInt_field_eq_zero_of_balanced {m : ℕ}
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (g : FieldBooleanFunction m) (hg : IsBalanced (g ∘ theta)) :
    (∑ z : BinaryGaloisField m, bitSignInt (g z)) = 0 := by
  calc
    (∑ z : BinaryGaloisField m, bitSignInt (g z)) =
        ∑ x : FABL.F₂Cube m, bitSignInt (g (theta x)) :=
      (Equiv.sum_comp theta.toEquiv (fun z ↦ bitSignInt (g z))).symm
    _ = walshTransform (g ∘ theta) 0 := by
      symm
      unfold walshTransform
      apply Finset.sum_congr rfl
      intro x _hx
      rw [walshTerm_zero]
      rfl
    _ = 0 := (isBalanced_iff_walshTransform_zero_eq_zero _).1 hg

/-- The source-normalized power-trace transform used in the hyper-bent criterion. -/
noncomputable def fieldPowerTraceTransform {n : ℕ}
    (f : FieldBooleanFunction n) (i : ℕ) (a : BinaryGaloisField n) : ℤ :=
  ∑ x : BinaryGaloisField n,
    bitSignInt (f x + absoluteTrace n (a * x ^ i))

/-- The power-trace transform of a partial-spread function decomposes into
middle-field character sums. -/
theorem fieldPowerTraceTransform_psap_eq {m i : ℕ} (hm : 0 < m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (g : FieldBooleanFunction m) (hg0 : g 0 = 0)
    (hi : Nat.Coprime i (2 ^ (2 * m) - 1))
    (a : BinaryGaloisField (2 * m)) :
    fieldPowerTraceTransform
        (psapFunction hm iota omega homega g) i a =
      (∑ y : BinaryGaloisField m,
        bitSignInt (absoluteTrace (2 * m) (a * iota y))) +
      ∑ z : BinaryGaloisField m, bitSignInt (g z) *
        ((∑ y : BinaryGaloisField m,
          bitSignInt (absoluteTrace (2 * m)
            ((a * (iota z + omega) ^ i) * iota y))) - 1) := by
  classical
  let coord := quadraticSubfieldBasisEquiv hm iota omega homega
  let term (y' y : BinaryGaloisField m) : ℤ :=
    bitSignInt (g (y' / y) + absoluteTrace (2 * m)
      (a * (iota y' + omega * iota y) ^ i))
  have hcoordinate :
      fieldPowerTraceTransform
          (psapFunction hm iota omega homega g) i a =
        ∑ y : BinaryGaloisField m, ∑ y' : BinaryGaloisField m, term y' y := by
    rw [sum_comm]
    symm
    calc
      (∑ y' : BinaryGaloisField m, ∑ y : BinaryGaloisField m, term y' y) =
          ∑ p : BinaryGaloisField m × BinaryGaloisField m,
            bitSignInt
              (psapFunction hm iota omega homega g (coord p) +
                absoluteTrace (2 * m) (a * (coord p) ^ i)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro y' _hy'
        apply Finset.sum_congr rfl
        intro y _hy
        change term y' y = bitSignInt
          (psapFunction hm iota omega homega g
              (iota y' + omega * iota y) +
            absoluteTrace (2 * m)
              (a * (iota y' + omega * iota y) ^ i))
        rw [psapFunction_coordinate]
      _ = fieldPowerTraceTransform
          (psapFunction hm iota omega homega g) i a :=
        Equiv.sum_comp coord (fun x ↦ bitSignInt
          (psapFunction hm iota omega homega g x +
            absoluteTrace (2 * m) (a * x ^ i)))
  let powerK : BinaryGaloisField m ≃ BinaryGaloisField m :=
    Equiv.ofBijective (fun y ↦ y ^ i)
      (quadraticSubfield_powerMap_bijective hm iota hi)
  have hzeroLine : (∑ y' : BinaryGaloisField m, term y' 0) =
      ∑ y : BinaryGaloisField m,
        bitSignInt (absoluteTrace (2 * m) (a * iota y)) := by
    calc
      (∑ y' : BinaryGaloisField m, term y' 0) =
          ∑ y' : BinaryGaloisField m,
            bitSignInt (absoluteTrace (2 * m) (a * iota (y' ^ i))) := by
        apply Finset.sum_congr rfl
        intro y' _hy'
        simp only [term, div_zero, hg0, zero_add, map_zero, mul_zero, add_zero,
          map_pow]
      _ = ∑ y : BinaryGaloisField m,
          bitSignInt (absoluteTrace (2 * m) (a * iota y)) :=
        Equiv.sum_comp powerK (fun y ↦
          bitSignInt (absoluteTrace (2 * m) (a * iota y)))
  have hslope (y : BinaryGaloisField m) (hy : y ≠ 0) :
      (∑ y' : BinaryGaloisField m, term y' y) =
        ∑ z : BinaryGaloisField m, bitSignInt (g z) *
          bitSignInt (absoluteTrace (2 * m)
            ((a * (iota z + omega) ^ i) * iota (y ^ i))) := by
    calc
      (∑ y' : BinaryGaloisField m, term y' y) =
          ∑ z : BinaryGaloisField m, term (z * y) y :=
        (Equiv.sum_comp (Equiv.mulRight₀ y hy)
          (fun y' ↦ term y' y)).symm
      _ = ∑ z : BinaryGaloisField m, bitSignInt (g z) *
          bitSignInt (absoluteTrace (2 * m)
            ((a * (iota z + omega) ^ i) * iota (y ^ i))) := by
        apply Finset.sum_congr rfl
        intro z _hz
        unfold term
        rw [mul_div_cancel_right₀ z hy, map_mul iota z y]
        have hcoordinateProduct :
            iota z * iota y + omega * iota y =
              (iota z + omega) * iota y := by ring
        rw [hcoordinateProduct, mul_pow, map_pow iota y i]
        rw [show a * ((iota z + omega) ^ i * (iota y) ^ i) =
            (a * (iota z + omega) ^ i) * (iota y) ^ i by ring]
        rw [bitSignInt_add]
  have hpowerErase (lambda : BinaryGaloisField (2 * m)) :
      (∑ y ∈ Finset.univ.erase 0,
        bitSignInt (absoluteTrace (2 * m) (lambda * iota (y ^ i)))) =
      (∑ y : BinaryGaloisField m,
        bitSignInt (absoluteTrace (2 * m) (lambda * iota y))) - 1 := by
    have hfull :
        (∑ y : BinaryGaloisField m,
          bitSignInt (absoluteTrace (2 * m) (lambda * iota (y ^ i)))) =
        ∑ y : BinaryGaloisField m,
          bitSignInt (absoluteTrace (2 * m) (lambda * iota y)) :=
      Equiv.sum_comp powerK (fun y ↦
        bitSignInt (absoluteTrace (2 * m) (lambda * iota y)))
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun y : BinaryGaloisField m ↦
        bitSignInt (absoluteTrace (2 * m) (lambda * iota (y ^ i))))
      (Finset.mem_univ 0)
    have hzero : bitSignInt
        (absoluteTrace (2 * m) (lambda * iota ((0 : BinaryGaloisField m) ^ i))) = 1 := by
      have hiPos : 0 < i := by
        have hmodulus : 1 < 2 ^ (2 * m) - 1 := by
          have : 2 ≤ 2 * m := by omega
          have hpower : 2 ^ 2 ≤ 2 ^ (2 * m) :=
            Nat.pow_le_pow_right (by omega) this
          norm_num at hpower ⊢
          omega
        by_contra hiZero
        have : i = 0 := by omega
        subst i
        simp only [Nat.coprime_zero_left] at hi
        omega
      rw [zero_pow hiPos.ne', map_zero, mul_zero, map_zero]
      norm_num [bitSignInt]
    rw [hzero] at hsplit
    rw [hfull] at hsplit
    omega
  rw [hcoordinate]
  rw [← Finset.add_sum_erase Finset.univ
    (fun y : BinaryGaloisField m ↦ ∑ y' : BinaryGaloisField m, term y' y)
    (Finset.mem_univ 0), hzeroLine]
  rw [add_right_inj]
  rw [show (∑ y ∈ Finset.univ.erase 0,
      ∑ y' : BinaryGaloisField m, term y' y) =
      ∑ y ∈ Finset.univ.erase 0, ∑ z : BinaryGaloisField m,
        bitSignInt (g z) *
          bitSignInt (absoluteTrace (2 * m)
            ((a * (iota z + omega) ^ i) * iota (y ^ i))) by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hslope y (Finset.mem_erase.mp hy).1]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [← Finset.mul_sum, hpowerErase]

/-- Every coprime power-trace transform of a partial-spread function has bent magnitude. -/
theorem fieldPowerTraceTransform_psap_natAbs {m i : ℕ} (hm : 2 ≤ m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (g : FieldBooleanFunction m) (hg : IsBalanced (g ∘ theta)) (hg0 : g 0 = 0)
    (hi : Nat.Coprime i (2 ^ (2 * m) - 1))
    (a : BinaryGaloisField (2 * m)) :
    (fieldPowerTraceTransform
      (psapFunction (by omega) iota omega homega g) i a).natAbs = 2 ^ m := by
  classical
  let charSum (lambda : BinaryGaloisField (2 * m)) : ℤ :=
    ∑ y : BinaryGaloisField m,
      bitSignInt (absoluteTrace (2 * m) (lambda * iota y))
  have hsign : (∑ z : BinaryGaloisField m, bitSignInt (g z)) = 0 :=
    sum_bitSignInt_field_eq_zero_of_balanced theta g hg
  have hformula := fieldPowerTraceTransform_psap_eq (by omega : 0 < m)
    iota omega homega g hg0 hi a
  have hsimplified :
      fieldPowerTraceTransform
          (psapFunction (by omega) iota omega homega g) i a =
        charSum a + ∑ z : BinaryGaloisField m,
          bitSignInt (g z) * charSum (a * (iota z + omega) ^ i) := by
    rw [hformula]
    change charSum a + _ = charSum a + _
    rw [add_right_inj]
    calc
      (∑ z : BinaryGaloisField m, bitSignInt (g z) *
          (charSum (a * (iota z + omega) ^ i) - 1)) =
          ∑ z : BinaryGaloisField m,
            (bitSignInt (g z) * charSum (a * (iota z + omega) ^ i) -
              bitSignInt (g z)) := by
        apply Finset.sum_congr rfl
        intro z _hz
        ring
      _ = (∑ z : BinaryGaloisField m,
            bitSignInt (g z) * charSum (a * (iota z + omega) ^ i)) -
          ∑ z : BinaryGaloisField m, bitSignInt (g z) :=
        by rw [Finset.sum_sub_distrib]
      _ = ∑ z : BinaryGaloisField m,
          bitSignInt (g z) * charSum (a * (iota z + omega) ^ i) := by
        rw [hsign, sub_zero]
  rw [hsimplified]
  by_cases ha : a ∈ Set.range iota
  · have hline : charSum a = (2 ^ m : ℤ) := by
      simpa only [charSum] using
        sum_quadraticSubfieldTraceCharacter_of_mem (by omega) iota a ha
    obtain ⟨alpha, halpha⟩ := ha
    by_cases ha0 : a = 0
    · subst a
      have hcharZero : charSum 0 = (2 ^ m : ℤ) := by
        apply sum_quadraticSubfieldTraceCharacter_of_mem (by omega) iota
        exact ⟨0, by simp⟩
      have hmiddle : (∑ z : BinaryGaloisField m,
          bitSignInt (g z) * charSum (0 * (iota z + omega) ^ i)) = 0 := by
        simp only [zero_mul, hcharZero]
        rw [← Finset.sum_mul, hsign, zero_mul]
      rw [ha0, hcharZero, hmiddle, add_zero]
      simp
    · have halpha0 : alpha ≠ 0 := by
        intro hzero
        subst alpha
        simp at halpha
        exact ha0 halpha.symm
      have hnotmem (z : BinaryGaloisField m) :
          a * (iota z + omega) ^ i ∉ Set.range iota := by
        rintro ⟨k, hk⟩
        have hpow : (iota z + omega) ^ i ∈ Set.range iota := by
          refine ⟨alpha⁻¹ * k, ?_⟩
          calc
            iota (alpha⁻¹ * k) = (iota alpha)⁻¹ * iota k := by
              rw [map_mul, map_inv₀]
            _ = a⁻¹ * (a * (iota z + omega) ^ i) := by
              rw [halpha, hk]
            _ = (iota z + omega) ^ i := by
              rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
        obtain ⟨r, hr⟩ :=
          (pow_mem_quadraticSubfield_iff (by omega) iota hi
            (iota z + omega)).1 hpow
        apply homega
        refine ⟨r - z, ?_⟩
        rw [map_sub, hr]
        ring
      have hmiddle : (∑ z : BinaryGaloisField m,
          bitSignInt (g z) * charSum (a * (iota z + omega) ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro z _hz
        rw [show charSum (a * (iota z + omega) ^ i) = 0 by
          simpa only [charSum] using
            sum_quadraticSubfieldTraceCharacter_of_not_mem (by omega) iota _ (hnotmem z)]
        simp
      rw [hline, hmiddle, add_zero]
      simp
  · have hline : charSum a = 0 := by
      simpa only [charSum] using
        sum_quadraticSubfieldTraceCharacter_of_not_mem (by omega) iota a ha
    obtain ⟨z0, hz0, hunique⟩ :=
      existsUnique_subfield_power_intersection (by omega : 0 < m)
        iota a omega ha homega hi
    have hmem0 : a * (iota z0 + omega) ^ i ∈ Set.range iota := by
      obtain ⟨k, hk⟩ := hz0
      exact ⟨k, hk.symm⟩
    have hchar0 : charSum (a * (iota z0 + omega) ^ i) = (2 ^ m : ℤ) := by
      simpa only [charSum] using
        sum_quadraticSubfieldTraceCharacter_of_mem (by omega) iota _ hmem0
    have hnotmem (z : BinaryGaloisField m) (hz : z ≠ z0) :
        a * (iota z + omega) ^ i ∉ Set.range iota := by
      intro hmem
      apply hz
      apply hunique z
      obtain ⟨k, hk⟩ := hmem
      exact ⟨k, hk.symm⟩
    have hmiddle : (∑ z : BinaryGaloisField m,
        bitSignInt (g z) * charSum (a * (iota z + omega) ^ i)) =
        bitSignInt (g z0) * (2 ^ m : ℤ) := by
      rw [Finset.sum_eq_single z0]
      · rw [hchar0]
      · intro z _hz hzNe
        rw [show charSum (a * (iota z + omega) ^ i) = 0 by
          simpa only [charSum] using
            sum_quadraticSubfieldTraceCharacter_of_not_mem (by omega) iota _
              (hnotmem z hzNe)]
        simp
      · exact fun hz0NotMem ↦ (hz0NotMem (Finset.mem_univ z0)).elim
    rw [hline, hmiddle, zero_add, Int.natAbs_mul]
    have hsignAbs : (bitSignInt (g z0)).natAbs = 1 := by
      rw [bitSignInt_eq_if_one]
      split <;> norm_num
    rw [hsignAbs, one_mul]
    simp

/-- Constant bent magnitude for all coprime power-trace transforms implies hyper-bentness. -/
theorem isHyperBent_of_forall_fieldPowerTraceTransform {n : ℕ}
    (hn : 2 ≤ n) (hnEven : Even n) (f : FieldBooleanFunction n)
    (htransform : ∀ i : ℕ, Nat.Coprime i (2 ^ n - 1) →
      ∀ a : BinaryGaloisField n,
        (fieldPowerTraceTransform f i a).natAbs = 2 ^ (n / 2)) :
    IsHyperBent f := by
  classical
  refine ⟨hnEven, ?_⟩
  intro i hi a
  let modulus := 2 ^ n - 1
  have hmodulus : 1 < modulus := by
    have hpower : 2 ^ 2 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by omega) hn
    dsimp only [modulus]
    norm_num at hpower ⊢
    omega
  let u : (ZMod modulus)ˣ := ZMod.unitOfCoprime i hi
  let j : ℕ := ((u⁻¹ : (ZMod modulus)ˣ) : ZMod modulus).val
  have hj : Nat.Coprime j modulus :=
    ZMod.val_coe_unit_coprime (u⁻¹)
  have hmodulusNe : modulus ≠ 0 := by omega
  letI : NeZero modulus := ⟨hmodulusNe⟩
  have hij : Nat.ModEq modulus (i * j) 1 := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_mul, Nat.cast_one]
    rw [show (j : ZMod modulus) = ((u⁻¹ : (ZMod modulus)ˣ) : ZMod modulus) by
      exact ZMod.natCast_zmod_val _]
    exact Units.mul_inv u
  have hiPos : 0 < i := by
    by_contra hzero
    have : i = 0 := by omega
    subst i
    simp only [Nat.coprime_zero_left] at hi
    omega
  have hjPos : 0 < j := by
    by_contra hzero
    have hjzero : j = 0 := by omega
    have hmOne : modulus = 1 :=
      modulus.coprime_zero_left.mp (hjzero ▸ hj)
    omega
  have hinverse (x : BinaryGaloisField n) : (x ^ i) ^ j = x := by
    by_cases hx : x = 0
    · subst x
      simp [zero_pow hiPos.ne', zero_pow hjPos.ne']
    · rw [← pow_mul]
      have hxModulus : x ^ modulus = 1 := by
        have hxCard := FiniteField.pow_card_sub_one_eq_one x hx
        rw [← Nat.card_eq_fintype_card,
          GaloisField.card 2 n (by omega)] at hxCard
        exact hxCard
      rw [pow_eq_pow_of_modEq hij hxModulus, pow_one]
  have hWalsh : fieldWalshTransform (fieldPowerReindex f i) a =
      fieldPowerTraceTransform f j a := by
    unfold fieldWalshTransform fieldPowerReindex fieldPowerTraceTransform
    symm
    calc
      (∑ x : BinaryGaloisField n,
          bitSignInt (f x + absoluteTrace n (a * x ^ j))) =
          ∑ x : BinaryGaloisField n,
            bitSignInt (f (x ^ i) + absoluteTrace n (a * (x ^ i) ^ j)) :=
        (Equiv.sum_comp (fieldPowerEquiv hn hi)
          (fun x ↦ bitSignInt (f x + absoluteTrace n (a * x ^ j)))).symm
      _ = ∑ x : BinaryGaloisField n,
          bitSignInt (f (x ^ i) + absoluteTrace n (a * x)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hinverse]
  rw [hWalsh]
  exact htransform j (by simpa only [modulus] using hj) a

/-- Carlet Proposition 25: every partial-spread function of the stated quotient
form is hyper-bent. -/
theorem isHyperBent_psapFunction {m : ℕ} (hm : 2 ≤ m)
    (iota : BinaryGaloisField m →ₐ[FABL.𝔽₂]
      BinaryGaloisField (2 * m))
    (omega : BinaryGaloisField (2 * m)) (homega : omega ∉ Set.range iota)
    (theta : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] BinaryGaloisField m)
    (g : FieldBooleanFunction m) (hg : IsBalanced (g ∘ theta)) (hg0 : g 0 = 0) :
    IsHyperBent (psapFunction (by omega) iota omega homega g) := by
  apply isHyperBent_of_forall_fieldPowerTraceTransform
    (n := 2 * m) (by omega) ⟨m, by omega⟩
  intro i hi a
  have h := fieldPowerTraceTransform_psap_natAbs hm
    iota omega homega theta g hg hg0 hi a
  rw [show (2 * m) / 2 = m by omega]
  exact h

end CryptBoolean
