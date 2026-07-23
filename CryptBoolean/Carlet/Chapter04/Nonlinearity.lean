/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import FABL.Chapter06.LearningAndTesting.DerandomizedBLR

/-!
# Carlet Chapter 4 nonlinearity

Raw Hamming nonlinearity, its exact normalized FABL bridge, and Carlet's
Walsh-spectrum formula.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The minimum raw Hamming distance from a Boolean function to an affine function. -/
noncomputable def nonlinearity (f : BooleanFunction n) : ℕ :=
  (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
    Finset.univ_nonempty fun p ↦
      hammingDistance f (FABL.affineFunction p.1 p.2)

/-- The largest absolute value in Carlet's unnormalized integer Walsh spectrum. -/
noncomputable def maxWalshMagnitude (f : BooleanFunction n) : ℕ :=
  (Finset.univ : Finset (FABL.F₂Cube n)).sup'
    Finset.univ_nonempty fun a ↦ (walshTransform f a).natAbs

/-- Raw distance from an affine Boolean function is the cube size times the
relative distance from the corresponding affine sign. -/
theorem hammingDistance_cast_affineFunction
    (f : BooleanFunction n) (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    (hammingDistance f (FABL.affineFunction b a) : ℝ) =
      (2 ^ n : ℝ) * FABL.relativeHammingDist (realSignView f)
        (FABL.affineSignFunction (FABL.signEncode b) a) := by
  rw [hammingDistance_eq_two_pow_mul_relativeHammingDist]
  rw [← FABL.relativeHammingDist_realSignEncodedFunction]
  rw [FABL.realSignEncodedFunction_affineFunction]

/-- The real cast of Carlet's integer bit sign is FABL's additive character. -/
theorem bitSignInt_cast (b : FABL.𝔽₂) :
    (bitSignInt b : ℝ) = FABL.binarySign b := by
  rw [← FABL.signValue_signEncode_eq_binarySign]
  rfl

/-- Raw distance to an affine function in terms of its signed Walsh coefficient. -/
theorem hammingDistance_cast_affineFunction_eq
    (f : BooleanFunction n) (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    (hammingDistance f (FABL.affineFunction b a) : ℝ) =
      (2 ^ n : ℝ) / 2 -
        (bitSignInt b : ℝ) * (walshTransform f a : ℝ) / 2 := by
  rw [hammingDistance_cast_affineFunction]
  rw [FABL.relativeHammingDist_affineSignFunction
    (FABL.isSignValued_realSignEncodedFunction f)]
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff, bitSignInt_cast]
  rw [FABL.signValue_signEncode_eq_binarySign]
  ring

/-- Distance from a linear function is `2^n/2-W_f(a)/2`. -/
theorem hammingDistance_cast_linearFunction_eq
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (hammingDistance f (FABL.affineFunction 0 a) : ℝ) =
      (2 ^ n : ℝ) / 2 - (walshTransform f a : ℝ) / 2 := by
  simpa [bitSignInt] using hammingDistance_cast_affineFunction_eq f 0 a

/-- Distance from the complement of a linear function is `2^n/2+W_f(a)/2`. -/
theorem hammingDistance_cast_complementLinearFunction_eq
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    (hammingDistance f (FABL.affineFunction 1 a) : ℝ) =
      (2 ^ n : ℝ) / 2 + (walshTransform f a : ℝ) / 2 := by
  rw [hammingDistance_cast_affineFunction_eq]
  simp [bitSignInt]
  ring

/-- Carlet's raw nonlinearity is exactly the scaled FABL distance to affine signs. -/
theorem nonlinearity_cast_eq_distanceToAffineSigns
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
      (2 ^ n : ℝ) * FABL.distanceToAffineSigns (realSignView f) := by
  classical
  rw [nonlinearity, Nat.cast_finsetInf']
  unfold FABL.distanceToAffineSigns
  have hpow : 0 ≤ (2 ^ n : ℝ) := by positivity
  rw [Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty
    (fun x : ℝ ↦ (2 ^ n : ℝ) * x)
    (fun x y ↦ mul_min_of_nonneg x y hpow)]
  apply le_antisymm
  · apply Finset.le_inf'
    intro p _hp
    obtain ⟨b, hb⟩ := FABL.binarySignEquiv.surjective p.1
    change FABL.signEncode b = p.1 at hb
    have hle := Finset.inf'_le
      (fun q : FABL.𝔽₂ × FABL.F₂Cube n ↦
        (hammingDistance f (FABL.affineFunction q.1 q.2) : ℝ))
      (Finset.mem_univ (b, p.2))
    calc
      (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
          Finset.univ_nonempty
          (fun q ↦ (hammingDistance f (FABL.affineFunction q.1 q.2) : ℝ)) ≤
          (hammingDistance f (FABL.affineFunction b p.2) : ℝ) := hle
      _ = (2 ^ n : ℝ) * FABL.relativeHammingDist (realSignView f)
          (FABL.affineSignFunction p.1 p.2) := by
        rw [hammingDistance_cast_affineFunction, hb]
  · apply Finset.le_inf'
    intro p _hp
    have hle := Finset.inf'_le
      (fun q : FABL.Sign × FABL.F₂Cube n ↦
        (2 ^ n : ℝ) * FABL.relativeHammingDist (realSignView f)
          (FABL.affineSignFunction q.1 q.2))
      (Finset.mem_univ (FABL.signEncode p.1, p.2))
    calc
      (Finset.univ : Finset (FABL.Sign × FABL.F₂Cube n)).inf'
          Finset.univ_nonempty
          (fun q ↦ (2 ^ n : ℝ) * FABL.relativeHammingDist (realSignView f)
            (FABL.affineSignFunction q.1 q.2)) ≤
          (2 ^ n : ℝ) * FABL.relativeHammingDist (realSignView f)
            (FABL.affineSignFunction (FABL.signEncode p.1) p.2) := hle
      _ = (hammingDistance f (FABL.affineFunction p.1 p.2) : ℝ) := by
        rw [hammingDistance_cast_affineFunction]

/-- The raw maximum Walsh magnitude is the cube size times FABL's normalized
spectral infinity norm. -/
theorem maxWalshMagnitude_cast_eq_spectralInfinityNorm
    (f : BooleanFunction n) :
    (maxWalshMagnitude f : ℝ) =
      (2 ^ n : ℝ) * FABL.spectralInfinityNorm (realSignView f) := by
  classical
  rw [maxWalshMagnitude, Nat.cast_finsetSup']
  unfold FABL.spectralInfinityNorm
  have hpow : 0 ≤ (2 ^ n : ℝ) := by positivity
  rw [Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty
    (fun x : ℝ ↦ (2 ^ n : ℝ) * x)
    (fun x y ↦ mul_max_of_nonneg x y hpow)]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro a _ha
  rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [Function.comp_apply]
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  rw [abs_mul, abs_of_nonneg hpow]

/-- Division-free form of Carlet's Relation (35). -/
theorem two_mul_nonlinearity_add_maxWalshMagnitude
    (f : BooleanFunction n) :
    2 * nonlinearity f + maxWalshMagnitude f = 2 ^ n := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [nonlinearity_cast_eq_distanceToAffineSigns,
    maxWalshMagnitude_cast_eq_spectralInfinityNorm,
    FABL.distanceToAffineSigns_eq
      (FABL.isSignValued_realSignEncodedFunction f)]
  ring

/-- Carlet Relation (35), written over the reals to preserve the factor one half
in every dimension. -/
theorem nonlinearity_cast_eq_relation_35
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
      (2 ^ n : ℝ) / 2 - (maxWalshMagnitude f : ℝ) / 2 := by
  have h := congrArg (fun k : ℕ ↦ (k : ℝ))
    (two_mul_nonlinearity_add_maxWalshMagnitude f)
  push_cast at h
  linarith

/-- Hamming distance is invariant under a simultaneous affine reindexing of
its two arguments. -/
theorem hammingDistance_comp_affineEquiv
    (f g : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    hammingDistance (f ∘ L) (g ∘ L) = hammingDistance f g := by
  classical
  unfold hammingDistance hammingDist
  apply Finset.card_bij (fun x _hx ↦ L x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] using hx
  · intro x _hx y _hy hxy
    exact L.injective hxy
  · intro y hy
    refine ⟨L.symm y, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp_apply, L.apply_symm_apply] using hy
    · exact L.apply_symm_apply y

/-- Precomposition of an affine Boolean function by an affine equivalence is
again affine. -/
theorem exists_affineFunction_comp_affineEquiv
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    ∃ c d, FABL.affineFunction b a ∘ L = FABL.affineFunction c d := by
  apply FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
  exact (FABL.functionAlgebraicDegree_comp_affineMap_le
    (FABL.affineFunction b a) L.toAffineMap).trans
      (FABL.functionAlgebraicDegree_affineFunction_le_one b a)

/-- Affine reindexing cannot increase nonlinearity. -/
theorem nonlinearity_comp_affineEquiv_le
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    nonlinearity (f ∘ L) ≤ nonlinearity f := by
  classical
  unfold nonlinearity
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)))
    Finset.univ_nonempty
    (fun q ↦ hammingDistance f (FABL.affineFunction q.1 q.2))
  obtain ⟨c, d, haffine⟩ :=
    exists_affineFunction_comp_affineEquiv p.1 p.2 L
  calc
    (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
        Finset.univ_nonempty
        (fun q ↦ hammingDistance (f ∘ L)
          (FABL.affineFunction q.1 q.2)) ≤
        hammingDistance (f ∘ L) (FABL.affineFunction c d) :=
      Finset.inf'_le _ (Finset.mem_univ (c, d))
    _ = hammingDistance (f ∘ L)
        (FABL.affineFunction p.1 p.2 ∘ L) := by rw [haffine]
    _ = hammingDistance f (FABL.affineFunction p.1 p.2) :=
      hammingDistance_comp_affineEquiv f
        (FABL.affineFunction p.1 p.2) L
    _ = (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
        Finset.univ_nonempty
        (fun q ↦ hammingDistance f
          (FABL.affineFunction q.1 q.2)) := hmin.symm

/-- Carlet's nonlinearity is invariant under affine automorphisms of the
binary cube. -/
theorem nonlinearity_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    nonlinearity (f ∘ L) = nonlinearity f := by
  apply Nat.le_antisymm (nonlinearity_comp_affineEquiv_le f L)
  have h := nonlinearity_comp_affineEquiv_le (f ∘ L) L.symm
  simpa [Function.comp_def] using h

/-- Some normalized Fourier coefficient of a sign-valued function has
magnitude at least the reciprocal square root of the cube cardinality. -/
theorem exists_inv_sqrt_card_le_vectorFourierCoeff_abs
    {f : FABL.F₂Cube n → ℝ} (hf : FABL.IsSignValued f) :
    ∃ γ, (Real.sqrt ((2 : ℝ) ^ n))⁻¹ ≤
      |FABL.vectorFourierCoeff f γ| := by
  obtain ⟨γ, hγ⟩ := FABL.exists_inv_card_le_sq_vectorFourierCoeff hf
  refine ⟨γ, ?_⟩
  have hsqrt := Real.sqrt_le_sqrt hγ
  rwa [Real.sqrt_inv, Real.sqrt_sq_eq_abs] at hsqrt

/-- The Fourier infinity norm of a sign-valued function is at least the
reciprocal square root of the cube cardinality. -/
theorem spectralInfinityNorm_ge_inv_sqrt_card
    {f : FABL.F₂Cube n → ℝ} (hf : FABL.IsSignValued f) :
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ ≤ FABL.spectralInfinityNorm f := by
  obtain ⟨γ, hγ⟩ :=
    exists_inv_sqrt_card_le_vectorFourierCoeff_abs hf
  exact hγ.trans (Finset.le_sup'
    (fun δ : FABL.F₂Cube n ↦ |FABL.vectorFourierCoeff f δ|)
    (Finset.mem_univ γ))

/-- No sign-valued function is farther from affine signs than the flat-spectrum
bound, in arbitrary dimension. -/
theorem distanceToAffineSigns_le_coveringRadius
    {f : FABL.F₂Cube n → ℝ} (hf : FABL.IsSignValued f) :
    FABL.distanceToAffineSigns f ≤
      1 / 2 - (Real.sqrt ((2 : ℝ) ^ n))⁻¹ / 2 := by
  rw [FABL.distanceToAffineSigns_eq hf]
  have hspectral := spectralInfinityNorm_ge_inv_sqrt_card hf
  linarith

/-- Multiplying the reciprocal square root of the cube cardinality by the
cardinality recovers its square root. -/
theorem two_pow_mul_inv_sqrt :
    (2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ =
      Real.sqrt ((2 : ℝ) ^ n) := by
  have hsqrt_ne : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by positivity
  calc
    (2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ =
        Real.sqrt ((2 : ℝ) ^ n) ^ 2 *
          (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
      rw [Real.sq_sqrt (by positivity)]
    _ = Real.sqrt ((2 : ℝ) ^ n) := by
      rw [pow_two]
      field_simp

/-- The square root of the cube cardinality is `2^(n/2)` with a real
exponent. -/
theorem sqrt_two_pow_eq_rpow :
    Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The square-root covering-radius expression is the printed form of
Carlet's Relation (36). -/
theorem coveringRadius_eq_relation_36 :
    (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 =
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_natCast, ← sqrt_two_pow_eq_rpow]

/-- The raw nonlinearity covering-radius bound in a dimension-zero-safe
square-root form. -/
theorem nonlinearity_cast_le_coveringRadius
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := by
  rw [nonlinearity_cast_eq_distanceToAffineSigns]
  calc
    (2 : ℝ) ^ n * FABL.distanceToAffineSigns (realSignView f) ≤
        (2 : ℝ) ^ n *
          (1 / 2 - (Real.sqrt ((2 : ℝ) ^ n))⁻¹ / 2) :=
      mul_le_mul_of_nonneg_left
        (distanceToAffineSigns_le_coveringRadius
          (FABL.isSignValued_realSignEncodedFunction f)) (by positivity)
    _ = (2 : ℝ) ^ n / 2 -
        ((2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹) / 2 := by ring
    _ = (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := by
      rw [two_pow_mul_inv_sqrt]

/-- Carlet Relation (36): every Boolean function satisfies
`nl(f) ≤ 2^(n-1) - 2^(n/2-1)`. -/
theorem nonlinearity_cast_le_relation_36
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) - 1) -
        (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
  rw [← coveringRadius_eq_relation_36]
  exact nonlinearity_cast_le_coveringRadius f

/-- Equality in the Fourier-infinity lower bound forces every Fourier
magnitude to equal the reciprocal square root of the cube cardinality. -/
theorem vectorFourierCoeff_abs_eq_inv_sqrt_of_spectralInfinityNorm_eq
    {f : FABL.F₂Cube n → ℝ} (hf : FABL.IsSignValued f)
    (hspectral : FABL.spectralInfinityNorm f =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹) :
    ∀ γ, |FABL.vectorFourierCoeff f γ| =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
  classical
  intro γ
  let c : ℝ := (Real.sqrt ((2 : ℝ) ^ n))⁻¹
  have hc_nonneg : 0 ≤ c := by positivity
  have habs_le : |FABL.vectorFourierCoeff f γ| ≤ c := by
    have hle := Finset.le_sup'
      (fun δ : FABL.F₂Cube n ↦ |FABL.vectorFourierCoeff f δ|)
      (Finset.mem_univ γ)
    change |FABL.vectorFourierCoeff f γ| ≤
      FABL.spectralInfinityNorm f at hle
    simpa [c, hspectral] using hle
  apply le_antisymm habs_le
  by_contra hnot
  have habs_lt : |FABL.vectorFourierCoeff f γ| < c :=
    lt_of_not_ge hnot
  have hsq_le (δ : FABL.F₂Cube n) :
      FABL.vectorFourierCoeff f δ ^ 2 ≤ c ^ 2 := by
    have hδ : |FABL.vectorFourierCoeff f δ| ≤ c := by
      have hle := Finset.le_sup'
        (fun ε : FABL.F₂Cube n ↦ |FABL.vectorFourierCoeff f ε|)
        (Finset.mem_univ δ)
      change |FABL.vectorFourierCoeff f δ| ≤
        FABL.spectralInfinityNorm f at hle
      simpa [c, hspectral] using hle
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (FABL.vectorFourierCoeff f δ)) hc_nonneg).mpr hδ
    simpa only [sq_abs] using hsquare
  have hsq_lt : FABL.vectorFourierCoeff f γ ^ 2 < c ^ 2 := by
    have hsquare :=
      (sq_lt_sq₀ (abs_nonneg (FABL.vectorFourierCoeff f γ)) hc_nonneg).mpr habs_lt
    simpa only [sq_abs] using hsquare
  have hsum_lt :
      (∑ δ : FABL.F₂Cube n, FABL.vectorFourierCoeff f δ ^ 2) <
        ∑ _δ : FABL.F₂Cube n, c ^ 2 :=
    Finset.sum_lt_sum (fun δ _ ↦ hsq_le δ)
      ⟨γ, Finset.mem_univ γ, hsq_lt⟩
  have hconstant : (∑ _δ : FABL.F₂Cube n, c ^ 2) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [c]
    rw [inv_pow]
    have hsqrt_pos : 0 < Real.sqrt ((2 : ℝ) ^ n) :=
      Real.sqrt_pos.2 (by positivity)
    have hsquare : Real.sqrt ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ n :=
      Real.sq_sqrt (by positivity)
    calc
      (2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n) ^ 2)⁻¹ =
          Real.sqrt ((2 : ℝ) ^ n) ^ 2 *
            (Real.sqrt ((2 : ℝ) ^ n) ^ 2)⁻¹ := by rw [hsquare]
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hsqrt_pos.ne')
  rw [FABL.sum_sq_vectorFourierCoeff_eq_one hf, hconstant] at hsum_lt
  exact (lt_irrefl 1 hsum_lt)

/-- A flat normalized Fourier spectrum attains the Fourier-infinity lower
bound. -/
theorem spectralInfinityNorm_eq_inv_sqrt_of_forall_abs
    {f : FABL.F₂Cube n → ℝ}
    (hflat : ∀ γ, |FABL.vectorFourierCoeff f γ| =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹) :
    FABL.spectralInfinityNorm f =
      (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
  unfold FABL.spectralInfinityNorm
  apply Finset.sup'_eq_of_forall
  intro γ _hγ
  exact hflat γ

/-- Equality in the normalized covering-radius bound is equivalent to a flat
normalized Fourier spectrum. -/
theorem distanceToAffineSigns_eq_coveringRadius_iff
    {f : FABL.F₂Cube n → ℝ} (hf : FABL.IsSignValued f) :
    FABL.distanceToAffineSigns f =
        1 / 2 - (Real.sqrt ((2 : ℝ) ^ n))⁻¹ / 2 ↔
      ∀ γ, |FABL.vectorFourierCoeff f γ| =
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
  rw [FABL.distanceToAffineSigns_eq hf]
  constructor
  · intro h
    apply vectorFourierCoeff_abs_eq_inv_sqrt_of_spectralInfinityNorm_eq hf
    linarith
  · intro h
    rw [spectralInfinityNorm_eq_inv_sqrt_of_forall_abs h]

/-- Carlet's flat raw Walsh-spectrum condition. -/
def HasFlatWalshSpectrum (f : BooleanFunction n) : Prop :=
  ∀ a, |(walshTransform f a : ℝ)| = Real.sqrt ((2 : ℝ) ^ n)

/-- Flatness of Carlet's raw Walsh spectrum is equivalent to flatness of
FABL's normalized vector Fourier spectrum. -/
theorem hasFlatWalshSpectrum_iff_vectorFourierCoeff
    (f : BooleanFunction n) :
    HasFlatWalshSpectrum f ↔
      ∀ a, |FABL.vectorFourierCoeff (realSignView f) a| =
        (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
  have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
  constructor
  · intro hflat a
    have ha := hflat a
    rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
      abs_mul, abs_of_pos hpow_pos] at ha
    apply mul_left_cancel₀ hpow_pos.ne'
    calc
      (2 : ℝ) ^ n * |FABL.vectorFourierCoeff (realSignView f) a| =
          Real.sqrt ((2 : ℝ) ^ n) := ha
      _ = (2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
        rw [two_pow_mul_inv_sqrt]
  · intro hflat a
    rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
      abs_mul, abs_of_pos hpow_pos, hflat a,
      two_pow_mul_inv_sqrt]

/-- Equality in the raw covering-radius bound is equivalent to a flat raw
Walsh spectrum. -/
theorem nonlinearity_eq_coveringRadius_iff_flatWalshSpectrum
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 ↔
      HasFlatWalshSpectrum f := by
  rw [hasFlatWalshSpectrum_iff_vectorFourierCoeff]
  rw [← distanceToAffineSigns_eq_coveringRadius_iff
    (FABL.isSignValued_realSignEncodedFunction f)]
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  constructor <;> intro h
  · apply mul_left_cancel₀ hpow_ne
    calc
      (2 : ℝ) ^ n * FABL.distanceToAffineSigns (realSignView f) =
          (nonlinearity f : ℝ) :=
        (nonlinearity_cast_eq_distanceToAffineSigns f).symm
      _ = (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := h
      _ = (2 : ℝ) ^ n / 2 -
          ((2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹) / 2 := by
        rw [two_pow_mul_inv_sqrt]
      _ = (2 : ℝ) ^ n *
          (1 / 2 - (Real.sqrt ((2 : ℝ) ^ n))⁻¹ / 2) := by ring
  · calc
      (nonlinearity f : ℝ) =
          (2 : ℝ) ^ n * FABL.distanceToAffineSigns (realSignView f) :=
        nonlinearity_cast_eq_distanceToAffineSigns f
      _ = (2 : ℝ) ^ n *
          (1 / 2 - (Real.sqrt ((2 : ℝ) ^ n))⁻¹ / 2) := by rw [h]
      _ = (2 : ℝ) ^ n / 2 -
          ((2 : ℝ) ^ n * (Real.sqrt ((2 : ℝ) ^ n))⁻¹) / 2 := by ring
      _ = (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := by
        rw [two_pow_mul_inv_sqrt]

/-- Equality in Carlet's printed Relation (36) is equivalent to a flat raw
Walsh spectrum. -/
theorem nonlinearity_cast_eq_relation_36_iff_flatWalshSpectrum
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) ↔
      HasFlatWalshSpectrum f := by
  rw [← coveringRadius_eq_relation_36]
  exact nonlinearity_eq_coveringRadius_iff_flatWalshSpectrum f

/-- A flat integer Walsh spectrum can occur only in even dimension. -/
theorem even_of_hasFlatWalshSpectrum
    (f : BooleanFunction n) (hflat : HasFlatWalshSpectrum f) :
    Even n := by
  have hzero := hflat 0
  have hsquareReal := congrArg (fun x : ℝ ↦ x ^ 2) hzero
  rw [sq_abs, Real.sq_sqrt (by positivity)] at hsquareReal
  have hsquareInt : walshTransform f 0 ^ 2 = (2 ^ n : ℤ) := by
    exact_mod_cast hsquareReal
  have hsquareNat : (walshTransform f 0).natAbs ^ 2 = 2 ^ n := by
    simpa [Int.natAbs_pow] using congrArg Int.natAbs hsquareInt
  have hfactor := congrArg (fun k : ℕ ↦ k.factorization 2) hsquareNat
  rw [Nat.factorization_pow, Nat.factorization_pow_self (by norm_num)] at hfactor
  change 2 * (walshTransform f 0).natAbs.factorization 2 = n at hfactor
  exact ⟨(walshTransform f 0).natAbs.factorization 2, by omega⟩

/-- A cryptographic Boolean function is bent when its real sign view satisfies
FABL's canonical bent predicate. -/
abbrev IsBent (f : BooleanFunction n) : Prop :=
  FABL.IsBent (realSignView f)

/-- In even dimension the square root of the cube cardinality is the integer
power indexed by half the dimension. -/
theorem sqrt_two_pow_eq_pow_half (hn : Even n) :
    Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ (n / 2) := by
  obtain ⟨k, rfl⟩ := hn
  have hhalf : (k + k) / 2 = k := by omega
  rw [hhalf, pow_add, ← pow_two, Real.sqrt_sq (by positivity)]

/-- Every bent Boolean function has even dimension. -/
theorem even_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) : Even n := by
  have hparseval := FABL.sum_sq_vectorFourierCoeff_eq_one
    (FABL.isSignValued_realSignEncodedFunction f)
  have hsum :
      (∑ a : FABL.F₂Cube n,
          (((2 : ℝ) ^ (n / 2))⁻¹) ^ 2) = 1 := by
    calc
      (∑ a : FABL.F₂Cube n, (((2 : ℝ) ^ (n / 2))⁻¹) ^ 2) =
          ∑ a : FABL.F₂Cube n,
            FABL.vectorFourierCoeff (realSignView f) a ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [← hf a, sq_abs]
      _ = 1 := hparseval
  rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hpowersReal : (2 : ℝ) ^ n = (2 : ℝ) ^ (2 * (n / 2)) := by
    field_simp at hsum
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n / 2) * (2 : ℝ) ^ (n / 2) := by
        simpa [pow_two] using hsum
      _ = (2 : ℝ) ^ (2 * (n / 2)) := by
        rw [← pow_add]
        congr 1
        omega
  have hpowersNat : 2 ^ n = 2 ^ (2 * (n / 2)) := by
    exact_mod_cast hpowersReal
  have hn_eq : n = 2 * (n / 2) :=
    Nat.pow_right_injective (by omega : 2 ≤ 2) hpowersNat
  exact ⟨n / 2, by omega⟩

/-- Carlet's raw flat-spectrum characterization is equivalent to FABL
bentness. -/
theorem hasFlatWalshSpectrum_iff_isBent
    (f : BooleanFunction n) :
    HasFlatWalshSpectrum f ↔ IsBent f := by
  constructor
  · intro hflat
    have hn := even_of_hasFlatWalshSpectrum f hflat
    rw [hasFlatWalshSpectrum_iff_vectorFourierCoeff] at hflat
    intro a
    rw [hflat a, sqrt_two_pow_eq_pow_half hn]
  · intro hbent
    have hn := even_of_isBent f hbent
    rw [hasFlatWalshSpectrum_iff_vectorFourierCoeff]
    intro a
    rw [hbent a, sqrt_two_pow_eq_pow_half hn]

/-- Bent Boolean functions can exist only in even dimension. -/
theorem even_of_exists_isBent
    (h : ∃ f : BooleanFunction n, IsBent f) : Even n := by
  obtain ⟨f, hf⟩ := h
  exact even_of_isBent f hf

/-- A bent Boolean function is not balanced. -/
theorem not_isBalanced_of_isBent
    (f : BooleanFunction n) (hf : IsBent f) : ¬ IsBalanced f := by
  rw [isBalanced_iff_walshTransform_zero_eq_zero]
  intro hzero
  have hflat := (hasFlatWalshSpectrum_iff_isBent f).2 hf
  have h := hflat 0
  rw [hzero, Int.cast_zero, abs_zero] at h
  have hsqrt_pos : 0 < Real.sqrt ((2 : ℝ) ^ n) :=
    Real.sqrt_pos.2 (by positivity)
  linarith

/-- In even dimension, FABL's bent-distance theorem is exactly Carlet
Relation (36) after the raw-distance normalization bridge. -/
theorem isBent_iff_nonlinearity_cast_eq_relation_36_of_even
    (f : BooleanFunction n) (hn : Even n) :
    IsBent f ↔
      (nonlinearity f : ℝ) =
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) := by
  rw [← coveringRadius_eq_relation_36]
  have hfab := FABL.isBent_iff_distanceToAffineSigns_eq hn
    (FABL.isSignValued_realSignEncodedFunction f)
  change FABL.IsBent (realSignView f) ↔ _
  rw [hfab]
  rw [nonlinearity_cast_eq_distanceToAffineSigns]
  have hsqrt := sqrt_two_pow_eq_pow_half hn
  constructor
  · intro hdistance
    rw [hdistance]
    calc
      (2 : ℝ) ^ n *
          (1 / 2 - ((2 : ℝ) ^ (n / 2))⁻¹ / 2) =
          (2 : ℝ) ^ n / 2 -
            ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2))⁻¹) / 2 := by ring
      _ = (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := by
        rw [← hsqrt, two_pow_mul_inv_sqrt]
  · intro hscaled
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) ^ n ≠ 0)
    calc
      (2 : ℝ) ^ n * FABL.distanceToAffineSigns (realSignView f) =
          (2 : ℝ) ^ n / 2 - Real.sqrt ((2 : ℝ) ^ n) / 2 := hscaled
      _ = (2 : ℝ) ^ n / 2 -
          ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2))⁻¹) / 2 := by
        rw [← hsqrt, two_pow_mul_inv_sqrt]
      _ = (2 : ℝ) ^ n *
          (1 / 2 - ((2 : ℝ) ^ (n / 2))⁻¹ / 2) := by ring

/-- Equality in Carlet Relation (36) holds exactly for bent Boolean
functions. -/
theorem nonlinearity_cast_eq_relation_36_iff_isBent
    (f : BooleanFunction n) :
    (nonlinearity f : ℝ) =
        (2 : ℝ) ^ ((n : ℝ) - 1) -
          (2 : ℝ) ^ ((n : ℝ) / 2 - 1) ↔
      IsBent f := by
  constructor
  · intro h
    have hflat :=
      (nonlinearity_cast_eq_relation_36_iff_flatWalshSpectrum f).1 h
    have hn := even_of_hasFlatWalshSpectrum f hflat
    exact (isBent_iff_nonlinearity_cast_eq_relation_36_of_even f hn).2 h
  · intro hf
    have hn := even_of_isBent f hf
    exact (isBent_iff_nonlinearity_cast_eq_relation_36_of_even f hn).1 hf

end CryptBoolean
