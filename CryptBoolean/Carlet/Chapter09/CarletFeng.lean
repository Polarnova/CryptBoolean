/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.FiniteFieldAlgebraicDegree
public import CryptBoolean.Carlet.Chapter09.GeneralProperties
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The Carlet--Feng algebraic construction

Carlet Chapter 9: the consecutive-power support construction, balancedness,
and optimal algebraic immunity.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

noncomputable section

private def boundedBinarySupport (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ k.testBit i

private theorem card_boundedBinarySupport_eq_binaryWeight
    (n k : ℕ) (hk : k < 2 ^ n) :
    (boundedBinarySupport n k).card = binaryWeight k := by
  classical
  symm
  rw [binaryWeight, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  apply Finset.card_bij
    (fun i hi ↦ ⟨i, by
      by_contra hni
      have hfalse : k.testBit i = false := Nat.testBit_eq_false_of_lt
        (hk.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hni)))
      have htrue : k.testBit i := Nat.mem_bitIndices.mp (by simpa using hi)
      simp [hfalse] at htrue⟩)
  · intro i hi
    simp only [boundedBinarySupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.mem_bitIndices.mp (by simpa using hi)
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro i hi
    refine ⟨(i : ℕ), ?_, ?_⟩
    · simpa [boundedBinarySupport] using
        (Nat.mem_bitIndices.mpr
          (show k.testBit (i : ℕ) from (by simpa [boundedBinarySupport] using hi)))
    · apply Fin.ext
      rfl

private theorem boundedBinarySupport_injective_of_lt
    (n : ℕ) {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : boundedBinarySupport n a = boundedBinarySupport n b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hmem := Finset.ext_iff.mp h ⟨i, hi⟩
    simpa [boundedBinarySupport] using hmem
  · have hpow : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hpow),
      Nat.testBit_eq_false_of_lt (hb.trans_le hpow)]

private theorem binaryWeight_two_pow_sub_one (n : ℕ) :
    binaryWeight (2 ^ n - 1) = n := by
  have hlt : 2 ^ n - 1 < 2 ^ n := Nat.sub_lt (Nat.two_pow_pos n) (by omega)
  rw [← card_boundedBinarySupport_eq_binaryWeight n (2 ^ n - 1) hlt]
  have hfull : boundedBinarySupport n (2 ^ n - 1) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    rw [show 2 ^ n - 1 = 2 ^ n - (0 + 1) by omega,
      Nat.testBit_two_pow_sub_succ (Nat.two_pow_pos n) (i : ℕ)]
    simp
  rw [hfull, Finset.card_univ, Fintype.card_fin]

private theorem binaryWeight_two_pow_sub_two {n : ℕ} (hn : 1 ≤ n) :
    binaryWeight (2 ^ n - 2) = n - 1 := by
  have hsplit : n = (n - 1) + 1 := by omega
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (fun k : ℕ ↦ 2 ^ k) hsplit
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
  have hdouble : 2 ^ n - 2 = 2 * (2 ^ (n - 1) - 1) := by
    rw [hpow]
    omega
  rw [hdouble, binaryWeight, Nat.bitIndices_two_mul, List.length_map]
  simpa [binaryWeight] using binaryWeight_two_pow_sub_one (n - 1)

private theorem card_lowDegreeFourierFamily_le_half
    {n d : ℕ} (hn : 0 < n) (hd : d < (n + 1) / 2) :
    (FABL.lowDegreeFourierFamily n d).card ≤ 2 ^ (n - 1) := by
  classical
  let low := FABL.lowDegreeFourierFamily n d
  let high := (Finset.univ : Finset (Finset (Fin n))) \ low
  have hdoubleDegree : 2 * d < n := by omega
  have hmap : Set.MapsTo (fun S : Finset (Fin n) ↦ Sᶜ) (↑low) (↑high) := by
    intro S hS
    have hScard : S.card ≤ d := (FABL.mem_lowDegreeFourierFamily S d).mp hS
    change Sᶜ ∈ high
    simp only [high, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hcompl
    have hcomplCard : Sᶜ.card ≤ d :=
      (FABL.mem_lowDegreeFourierFamily Sᶜ d).mp hcompl
    rw [Finset.card_compl, Fintype.card_fin] at hcomplCard
    omega
  have hcard : low.card ≤ high.card :=
    Finset.card_le_card_of_injOn (fun S : Finset (Fin n) ↦ Sᶜ) hmap
      compl_injective.injOn
  have huniv : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have htwice : 2 * low.card ≤ 2 ^ n := by
    have hlowSubset : low ⊆ (Finset.univ : Finset (Finset (Fin n))) :=
      Finset.subset_univ low
    change low.card ≤ ((Finset.univ : Finset (Finset (Fin n))) \ low).card at hcard
    rw [Finset.card_sdiff_of_subset hlowSubset, huniv] at hcard
    omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hsplit : n = (n - 1) + 1 := by omega
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (fun k : ℕ ↦ 2 ^ k) hsplit
      _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [hpow] at htwice
  have hhalf : low.card ≤ 2 ^ (n - 1) := by omega
  simpa only [low] using hhalf

private theorem polynomial_support_card_le_lowDegreeFamily
    {n d : ℕ} {P : (BinaryGaloisField n)[X]}
    (hbound : ∀ j ∈ P.support, j < 2 ^ n)
    (hweight : ∀ j ∈ P.support, binaryWeight j ≤ d) :
    P.support.card ≤ (FABL.lowDegreeFourierFamily n d).card := by
  classical
  apply Finset.card_le_card_of_injOn (boundedBinarySupport n)
  · intro j hj
    change boundedBinarySupport n j ∈ FABL.lowDegreeFourierFamily n d
    rw [FABL.mem_lowDegreeFourierFamily,
      card_boundedBinarySupport_eq_binaryWeight n j (hbound j hj)]
    exact hweight j hj
  · intro a ha b hb hab
    exact boundedBinarySupport_injective_of_lt n (hbound a ha) (hbound b hb) hab

private theorem polynomial_support_card_lt_lowDegreeFamily_of_coeff_zero
    {n d : ℕ} {P : (BinaryGaloisField n)[X]}
    (hbound : ∀ j ∈ P.support, j < 2 ^ n)
    (hweight : ∀ j ∈ P.support, binaryWeight j ≤ d)
    (hcoeffZero : P.coeff 0 = 0) :
    P.support.card < (FABL.lowDegreeFourierFamily n d).card := by
  classical
  let imageSupport := P.support.image (boundedBinarySupport n)
  have himageSubset : imageSupport ⊆ FABL.lowDegreeFourierFamily n d := by
    intro S hS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
    rw [FABL.mem_lowDegreeFourierFamily,
      card_boundedBinarySupport_eq_binaryWeight n j (hbound j hj)]
    exact hweight j hj
  have hemptyMem : ∅ ∈ FABL.lowDegreeFourierFamily n d := by simp
  have hemptyNotMem : ∅ ∉ imageSupport := by
    intro hempty
    obtain ⟨j, hj, hzero⟩ := Finset.mem_image.mp hempty
    have hjZero : j = 0 := by
      apply boundedBinarySupport_injective_of_lt n (hbound j hj)
        (Nat.two_pow_pos n)
      simpa [boundedBinarySupport] using hzero
    subst j
    exact (Polynomial.mem_support_iff.mp hj) hcoeffZero
  have hproper : imageSupport ⊂ FABL.lowDegreeFourierFamily n d :=
    Finset.ssubset_iff_subset_ne.mpr ⟨himageSubset, fun heq ↦ hemptyNotMem (heq ▸ hemptyMem)⟩
  calc
    P.support.card = imageSupport.card := by
      symm
      exact Finset.card_image_of_injOn fun a ha b hb hab ↦
        boundedBinarySupport_injective_of_lt n (hbound a ha) (hbound b hb) hab
    _ < (FABL.lowDegreeFourierFamily n d).card := Finset.card_lt_card hproper

private noncomputable def booleanUnivariateRepresentation {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (g : BooleanFunction n) : (BinaryGaloisField n)[X] :=
  univariateRepresentation fun z ↦
    algebraMap FABL.𝔽₂ (BinaryGaloisField n) (g (θ.symm z))

@[simp] private theorem eval_booleanUnivariateRepresentation {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (g : BooleanFunction n) (z : BinaryGaloisField n) :
    (booleanUnivariateRepresentation θ g).eval z =
      algebraMap FABL.𝔽₂ (BinaryGaloisField n) (g (θ.symm z)) := by
  exact eval_univariateRepresentation _ z

private theorem booleanUnivariate_support_bounds {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (g : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree g < (n + 1) / 2) :
    let P := booleanUnivariateRepresentation θ g
    (∀ j ∈ P.support, j < 2 ^ n - 1) ∧
      P.support.card ≤ 2 ^ (n - 1) ∧
      (P.eval 0 = 0 → P.support.card ≤ 2 ^ (n - 1) - 1) := by
  classical
  let P := booleanUnivariateRepresentation θ g
  change (∀ j ∈ P.support, j < 2 ^ n - 1) ∧
    P.support.card ≤ 2 ^ (n - 1) ∧
    (P.eval 0 = 0 → P.support.card ≤ 2 ^ (n - 1) - 1)
  have hn0 : n ≠ 0 := by omega
  have hPdegree : P.degree < (2 ^ n : ℕ) := by
    simpa [P, booleanUnivariateRepresentation, GaloisField.card 2 n hn0] using
      degree_univariateRepresentation_lt_card
        (fun z : BinaryGaloisField n ↦
          algebraMap FABL.𝔽₂ (BinaryGaloisField n) (g (θ.symm z)))
  have hPnatDegree : P.natDegree < 2 ^ n := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
  have hbound : ∀ j ∈ P.support, j < 2 ^ n := by
    intro j hj
    exact (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hPnatDegree
  have hdegreeEq : FABL.functionAlgebraicDegree g = univariateBinaryDegree P := by
    simpa [P, booleanUnivariateRepresentation] using
      functionAlgebraicDegree_eq_univariateBinaryDegree hn0 θ g
  have hweight : ∀ j ∈ P.support,
      binaryWeight j ≤ FABL.functionAlgebraicDegree g := by
    intro j hj
    rw [hdegreeEq, univariateBinaryDegree]
    exact Finset.le_sup hj
  have hsupportOrder : ∀ j ∈ P.support, j < 2 ^ n - 1 := by
    intro j hj
    have hjBound := hbound j hj
    by_contra hjOrder
    have hjTop : j = 2 ^ n - 1 := by omega
    have hjWeight := hweight j hj
    rw [hjTop, binaryWeight_two_pow_sub_one] at hjWeight
    omega
  have hcardLow : P.support.card ≤
      (FABL.lowDegreeFourierFamily n (FABL.functionAlgebraicDegree g)).card :=
    polynomial_support_card_le_lowDegreeFamily hbound hweight
  have hfamilyHalf :
      (FABL.lowDegreeFourierFamily n (FABL.functionAlgebraicDegree g)).card ≤
        2 ^ (n - 1) :=
    card_lowDegreeFourierFamily_le_half (by omega) hdegree
  refine ⟨hsupportOrder, hcardLow.trans hfamilyHalf, ?_⟩
  intro hevalZero
  have hcoeffZero : P.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact hevalZero
  have hcardStrict : P.support.card <
      (FABL.lowDegreeFourierFamily n (FABL.functionAlgebraicDegree g)).card :=
    polynomial_support_card_lt_lowDegreeFamily_of_coeff_zero hbound hweight hcoeffZero
  omega

private theorem polynomial_eq_zero_of_consecutive_primitive_powers
    {K : Type*} [Field K] {N start count : ℕ} {alpha : K}
    (hN : 0 < N) (halpha : IsPrimitiveRoot alpha N) (P : K[X])
    (hsupport : ∀ j ∈ P.support, j < N)
    (hcard : P.support.card ≤ count)
    (hzero : ∀ j < count, P.eval (alpha ^ (start + j)) = 0) :
    P = 0 := by
  classical
  let e : Fin P.support.card ≃ ↑P.support := P.support.equivFin.symm
  let roots : Fin P.support.card → K := fun i ↦ alpha ^ (e i : ℕ)
  let values : Fin P.support.card → K :=
    fun i ↦ P.coeff (e i : ℕ) * roots i ^ start
  have hroots : Function.Injective roots := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact halpha.pow_inj (hsupport _ (e i).property)
      (hsupport _ (e j).property) hij
  have hsystem : ∀ i : Fin P.support.card,
      (∑ j, values j * roots j ^ (i : ℕ)) = 0 := by
    intro i
    have hiCount : (i : ℕ) < count := i.isLt.trans_le hcard
    rw [← hzero i hiCount, Polynomial.eval_eq_sum, Polynomial.sum_def]
    calc
      (∑ j, values j * roots j ^ (i : ℕ)) =
          ∑ j, P.coeff (e j : ℕ) *
            (alpha ^ (start + (i : ℕ))) ^ (e j : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [values, roots]
        rw [← pow_mul, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        ring
      _ = ∑ j : ↑P.support, P.coeff (j : ℕ) *
            (alpha ^ (start + (i : ℕ))) ^ (j : ℕ) :=
        by
          simpa only using e.sum_comp
            (fun j : ↑P.support ↦ P.coeff (j : ℕ) *
              (alpha ^ (start + (i : ℕ))) ^ (j : ℕ))
      _ = ∑ j ∈ P.support, P.coeff j *
            (alpha ^ (start + (i : ℕ))) ^ j := by
        symm
        exact Finset.sum_subtype P.support (fun j ↦ Iff.rfl) _
  have hvalues : values = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hroots hsystem
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_zero]
  by_cases hj : j ∈ P.support
  · let i : Fin P.support.card := P.support.equivFin ⟨j, hj⟩
    have hi := congrFun hvalues i
    have halphaNe : alpha ≠ 0 := (halpha.isUnit hN.ne').ne_zero
    change P.coeff (e i : ℕ) * roots i ^ start = 0 at hi
    have hei : (e i : ℕ) = j := by simp [e, i]
    simpa [hei] using
      (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (pow_ne_zero _ halphaNe))
  · by_contra hcoeff
    exact hj (Polynomial.mem_support_iff.mpr hcoeff)

/-- The Carlet--Feng support consists of zero and the first `2^(n-1)-1`
powers of a primitive element. -/
noncomputable def carletFengSupport {n : ℕ} (alpha : BinaryGaloisField n) :
    Finset (BinaryGaloisField n) := by
  classical
  exact insert 0 ((Finset.range (2 ^ (n - 1) - 1)).image fun i ↦ alpha ^ i)

/-- The field-domain Carlet--Feng Boolean function. -/
noncomputable def carletFengFieldFunction {n : ℕ}
    (alpha : BinaryGaloisField n) : FieldBooleanFunction n := by
  classical
  exact fun x ↦ if x ∈ carletFengSupport alpha then 1 else 0

/-- The scalar Carlet--Feng function after a binary linear identification with
the extension field. -/
noncomputable def carletFengBooleanFunction {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (alpha : BinaryGaloisField n) : BooleanFunction n :=
  fun x ↦ carletFengFieldFunction alpha (θ x)

@[simp] theorem carletFengFieldFunction_eq_one_iff {n : ℕ}
    (alpha x : BinaryGaloisField n) :
    carletFengFieldFunction alpha x = 1 ↔ x ∈ carletFengSupport alpha := by
  simp [carletFengFieldFunction]

theorem mem_carletFengSupport_iff {n : ℕ}
    (alpha x : BinaryGaloisField n) :
    x ∈ carletFengSupport alpha ↔
      x = 0 ∨ ∃ i < 2 ^ (n - 1) - 1, x = alpha ^ i := by
  classical
  simp [carletFengSupport, eq_comm]

@[simp] theorem zero_mem_carletFengSupport {n : ℕ}
    (alpha : BinaryGaloisField n) :
    0 ∈ carletFengSupport alpha := by
  exact (mem_carletFengSupport_iff alpha 0).mpr (Or.inl rfl)

theorem pow_mem_carletFengSupport_of_lt {n i : ℕ}
    (alpha : BinaryGaloisField n) (hi : i < 2 ^ (n - 1) - 1) :
    alpha ^ i ∈ carletFengSupport alpha := by
  exact (mem_carletFengSupport_iff alpha (alpha ^ i)).mpr
    (Or.inr ⟨i, hi, rfl⟩)

theorem pow_not_mem_carletFengSupport_of_mem_interval {n i : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1))
    (hiLower : 2 ^ (n - 1) - 1 ≤ i) (hiUpper : i < 2 ^ n - 1) :
    alpha ^ i ∉ carletFengSupport alpha := by
  classical
  intro hi
  rcases (mem_carletFengSupport_iff alpha (alpha ^ i)).mp hi with hzero | ⟨j, hj, hij⟩
  · have horder : 0 < 2 ^ n - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    exact (pow_ne_zero _ (halpha.isUnit horder.ne').ne_zero) hzero
  · have hjUpper : j < 2 ^ n - 1 := by
      have hsplit : n = (n - 1) + 1 := by omega
      have hpow : 2 ^ n = 2 ^ (n - 1) * 2 :=
        (congrArg (fun k : ℕ ↦ 2 ^ k) hsplit).trans (pow_succ 2 (n - 1))
      omega
    have := halpha.pow_inj hiUpper hjUpper hij
    omega

theorem carletFengSupport_card {n : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    (carletFengSupport alpha).card = 2 ^ (n - 1) := by
  classical
  have hsplit : n = (n - 1) + 1 := by omega
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    exact (congrArg (fun k : ℕ ↦ 2 ^ k) hsplit).trans (pow_succ 2 (n - 1))
  have horder : 0 < 2 ^ n - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have halphaNe : alpha ≠ 0 := (halpha.isUnit horder.ne').ne_zero
  have hinjective : Set.InjOn (fun i : ℕ ↦ alpha ^ i)
      (Finset.range (2 ^ (n - 1) - 1) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    apply halpha.pow_inj
    · omega
    · omega
    · exact hij
  have hzero : 0 ∉ (Finset.range (2 ^ (n - 1) - 1)).image
      (fun i ↦ alpha ^ i) := by
    simp [halphaNe]
  rw [carletFengSupport, Finset.card_insert_of_notMem hzero,
    Finset.card_image_of_injOn hinjective, Finset.card_range]
  omega

private theorem carletFeng_geometric_sum {n i : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1))
    (hi0 : 0 < i) (hi : i < 2 ^ n - 1) :
    (∑ j ∈ Finset.range (2 ^ (n - 1) - 1),
        (alpha ^ j) ^ (2 ^ n - 1 - i)) =
      alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1)) := by
  classical
  let H := 2 ^ (n - 1)
  let N := 2 ^ n - 1
  let L := H - 1
  let t : BinaryGaloisField n := alpha ^ i
  let r : BinaryGaloisField n := alpha ^ (N - i)
  let D : BinaryGaloisField n := (1 + t) ^ H
  have hn0 : n ≠ 0 := by omega
  have hsplit : n = (n - 1) + 1 := by omega
  have hpow : 2 ^ n = H * 2 := by
    exact (congrArg (fun k : ℕ ↦ 2 ^ k) hsplit).trans (pow_succ 2 (n - 1))
  have hN : N = H * 2 - 1 := by omega
  have hHL : H + L = N := by
    have hHPos : 0 < H := Nat.two_pow_pos (n - 1)
    omega
  have halphaNe : alpha ≠ 0 := by
    have hNPos : 0 < N := by
      dsimp [N]
      exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn0)
    exact (halpha.isUnit hNPos.ne').ne_zero
  have htNe : t ≠ 0 := pow_ne_zero _ halphaNe
  have htNeOne : t ≠ 1 := by
    exact halpha.pow_ne_one_of_pos_of_lt hi0.ne' hi
  have hrNeOne : r ≠ 1 := by
    apply halpha.pow_ne_one_of_pos_of_lt
    · dsimp [N]
      omega
    · dsimp [N]
      omega
  have hrt : r * t = 1 := by
    calc
      r * t = alpha ^ ((N - i) + i) := by
        simp only [r, t, ← pow_add]
      _ = alpha ^ N := by congr 1; omega
      _ = 1 := halpha.pow_eq_one
  have hrL : r ^ L = t ^ H := by
    apply mul_right_cancel₀ (pow_ne_zero L htNe)
    calc
      r ^ L * t ^ L = (r * t) ^ L := (mul_pow r t L).symm
      _ = 1 := by rw [hrt, one_pow]
      _ = t ^ H * t ^ L := by
        rw [← pow_add, hHL]
        dsimp [t]
        rw [pow_right_comm, halpha.pow_eq_one, one_pow]
  have hDadd : D = 1 + t ^ H := by
    dsimp [D, H]
    rw [add_pow_char_pow]
    simp
  have hfieldPow (x : BinaryGaloisField n) : x ^ (2 ^ n) = x := by
    letI := Fintype.ofFinite (BinaryGaloisField n)
    have hx := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0] at hx
    exact hx
  have hDsquare : D ^ 2 = 1 + t := by
    calc
      D ^ 2 = (1 + t) ^ (H * 2) := by
        simp only [D, ← pow_mul]
      _ = (1 + t) ^ (2 ^ n) := by rw [← hpow]
      _ = 1 + t := hfieldPow (1 + t)
  have hDNe : D ≠ 0 := by
    intro hzero
    have honeAdd : 1 + t = 0 := by
      rw [← hDsquare, hzero, zero_pow (by omega : 2 ≠ 0)]
    have htOne : t = 1 := by
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add, add_comm, honeAdd]
    exact htNeOne htOne
  have htMul : t * (1 - r) = 1 + t := by
    have htr : t * r = 1 := by simpa [mul_comm] using hrt
    calc
      t * (1 - r) = t - t * r := by simpa using mul_sub t 1 r
      _ = t - 1 := by rw [htr]
      _ = t + 1 := CharTwo.sub_eq_add t 1
      _ = 1 + t := add_comm _ _
  have hcoefficientMul : (t / D) * (1 - r) = D := by
    calc
      (t / D) * (1 - r) = (t * (1 - r)) / D := by
        simp only [div_eq_mul_inv]
        ring
      _ = (1 + t) / D := by rw [htMul]
      _ = D := by
        rw [div_eq_iff hDNe]
        simpa [pow_two] using hDsquare.symm
  have hfactor : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrNeOne)
  have hgeom :
      (∑ j ∈ Finset.range L, r ^ j) = t / D := by
    apply mul_right_cancel₀ hfactor
    calc
      (∑ j ∈ Finset.range L, r ^ j) * (1 - r) = 1 - r ^ L :=
        geom_sum_mul_neg r L
      _ = 1 + t ^ H := by rw [hrL, CharTwo.sub_eq_add]
      _ = D := hDadd.symm
      _ = (t / D) * (1 - r) := hcoefficientMul.symm
  calc
    (∑ j ∈ Finset.range (2 ^ (n - 1) - 1),
        (alpha ^ j) ^ (2 ^ n - 1 - i)) =
        ∑ j ∈ Finset.range L, r ^ j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [r, N]
      rw [← pow_mul, ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    _ = t / D := hgeom
    _ = alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1)) := rfl

/-- The canonical bounded univariate representation of the field-domain
Carlet--Feng function. -/
noncomputable def carletFengUnivariateRepresentation {n : ℕ}
    (alpha : BinaryGaloisField n) : (BinaryGaloisField n)[X] :=
  univariateRepresentation fun z ↦
    algebraMap FABL.𝔽₂ (BinaryGaloisField n) (carletFengFieldFunction alpha z)

theorem degree_carletFengUnivariateRepresentation_lt {n : ℕ} (hn : n ≠ 0)
    (alpha : BinaryGaloisField n) :
    (carletFengUnivariateRepresentation alpha).degree < (2 ^ n : ℕ) := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  have hfieldCard : Fintype.card (BinaryGaloisField n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn]
  simpa [carletFengUnivariateRepresentation, hfieldCard] using
    degree_univariateRepresentation_lt_card
      (fun z : BinaryGaloisField n ↦
        algebraMap FABL.𝔽₂ (BinaryGaloisField n) (carletFengFieldFunction alpha z))

@[simp] theorem coeff_zero_carletFengUnivariateRepresentation {n : ℕ}
    (alpha : BinaryGaloisField n) :
    (carletFengUnivariateRepresentation alpha).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, carletFengUnivariateRepresentation,
    eval_univariateRepresentation]
  simp [carletFengFieldFunction]

theorem coeff_carletFengUnivariateRepresentation {n i : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1))
    (hi0 : 0 < i) (hi : i < 2 ^ n - 1) :
    (carletFengUnivariateRepresentation alpha).coeff i =
      alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1)) := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  have hn0 : n ≠ 0 := by omega
  have hdegree := degree_carletFengUnivariateRepresentation_lt hn0 alpha
  rw [univariate_coefficient_eq_weighted_sum hn0
    (carletFengUnivariateRepresentation alpha) hdegree hi0 (by omega)]
  calc
    (∑ x : BinaryGaloisField n,
        (carletFengUnivariateRepresentation alpha).eval x *
          x ^ (2 ^ n - 1 - i)) =
        ∑ x : BinaryGaloisField n,
          algebraMap FABL.𝔽₂ (BinaryGaloisField n)
              (carletFengFieldFunction alpha x) * x ^ (2 ^ n - 1 - i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [carletFengUnivariateRepresentation, eval_univariateRepresentation]
    _ = ∑ x ∈ carletFengSupport alpha, x ^ (2 ^ n - 1 - i) := by
      simp [carletFengFieldFunction]
    _ = ∑ j ∈ Finset.range (2 ^ (n - 1) - 1),
          (alpha ^ j) ^ (2 ^ n - 1 - i) := by
      have hsplit : n = (n - 1) + 1 := by omega
      have hpow : 2 ^ n = 2 ^ (n - 1) * 2 :=
        (congrArg (fun k : ℕ ↦ 2 ^ k) hsplit).trans (pow_succ 2 (n - 1))
      have horder : 0 < 2 ^ n - 1 := by omega
      have halphaNe : alpha ≠ 0 := (halpha.isUnit horder.ne').ne_zero
      have hzero : 0 ∉ (Finset.range (2 ^ (n - 1) - 1)).image
          (fun j ↦ alpha ^ j) := by
        simp [halphaNe]
      have hinjective : Set.InjOn (fun j : ℕ ↦ alpha ^ j)
          (Finset.range (2 ^ (n - 1) - 1) : Set ℕ) := by
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_range] at ha hb
        apply halpha.pow_inj
        · omega
        · omega
        · exact hab
      rw [carletFengSupport, Finset.sum_insert hzero,
        zero_pow (by omega), zero_add, Finset.sum_image hinjective]
    _ = alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1)) :=
      carletFeng_geometric_sum hn halpha hi0 hi

theorem coeff_top_carletFengUnivariateRepresentation {n : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    (carletFengUnivariateRepresentation alpha).coeff (2 ^ n - 1) = 0 := by
  classical
  letI := Fintype.ofFinite (BinaryGaloisField n)
  have hn0 : n ≠ 0 := by omega
  have hdegree := degree_carletFengUnivariateRepresentation_lt hn0 alpha
  have hNPos : 0 < 2 ^ n - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn0)
  have hNLt : 2 ^ n - 1 < 2 ^ n :=
    Nat.sub_lt (Nat.two_pow_pos n) (by omega)
  rw [univariate_coefficient_eq_weighted_sum hn0
    (carletFengUnivariateRepresentation alpha) hdegree hNPos hNLt]
  simp only [Nat.sub_self, pow_zero, mul_one]
  calc
    (∑ x : BinaryGaloisField n,
        (carletFengUnivariateRepresentation alpha).eval x) =
        ∑ x : BinaryGaloisField n,
          algebraMap FABL.𝔽₂ (BinaryGaloisField n)
            (carletFengFieldFunction alpha x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [carletFengUnivariateRepresentation, eval_univariateRepresentation]
    _ = ∑ _x ∈ carletFengSupport alpha, (1 : BinaryGaloisField n) := by
      simp [carletFengFieldFunction]
    _ = 0 := by
      rw [Finset.sum_const, nsmul_eq_mul, carletFengSupport_card hn halpha]
      have hsplit : n - 1 = (n - 2) + 1 := by omega
      rw [congrArg (fun k : ℕ ↦ 2 ^ k) hsplit, pow_succ, Nat.cast_mul]
      simp [CharTwo.two_eq_zero]

/-- The coefficient at exponent `2^n-2` in Relation (70) is nonzero. -/
theorem coeff_two_pow_sub_two_carletFengUnivariateRepresentation_ne_zero
    {n : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    (carletFengUnivariateRepresentation alpha).coeff (2 ^ n - 2) ≠ 0 := by
  have hpowOne : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hpowFour : 4 ≤ 2 ^ n := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hn)
  have horderNe : 2 ^ n - 1 ≠ 0 := by omega
  have halphaNe : alpha ≠ 0 := (halpha.isUnit horderNe).ne_zero
  have hpowerNeOne : alpha ^ (2 ^ n - 2) ≠ 1 :=
    halpha.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have honeAddNe : 1 + alpha ^ (2 ^ n - 2) ≠ 0 := by
    intro hzero
    exact hpowerNeOne (CharTwo.add_eq_zero.mp hzero).symm
  rw [coeff_carletFengUnivariateRepresentation hn halpha (by omega) (by omega)]
  exact div_ne_zero (pow_ne_zero _ halphaNe) (pow_ne_zero _ honeAddNe)

/-- The polynomial displayed in Carlet Relation (70). -/
noncomputable def carletFengClosedPolynomial {n : ℕ}
    (alpha : BinaryGaloisField n) : (BinaryGaloisField n)[X] :=
  Polynomial.C 1 +
    ∑ i ∈ Finset.Ico 1 (2 ^ n - 1),
      Polynomial.monomial i
        (alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1)))

/-- Carlet Relation (70) as equality with the canonical bounded univariate
representation. -/
theorem carletFengUnivariateRepresentation_eq_closedPolynomial
    {n : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    carletFengUnivariateRepresentation alpha = carletFengClosedPolynomial alpha := by
  classical
  ext k
  by_cases hk0 : k = 0
  · subst k
    simp [carletFengClosedPolynomial, Polynomial.coeff_monomial]
  · by_cases hk : k < 2 ^ n - 1
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      rw [coeff_carletFengUnivariateRepresentation hn halpha hkPos hk]
      have hmem : k ∈ Finset.Ico 1 (2 ^ n - 1) := by
        exact Finset.mem_Ico.mpr ⟨by omega, hk⟩
      simp [carletFengClosedPolynomial, Polynomial.coeff_monomial,
        Polynomial.coeff_one, hk0, hmem]
    · have hkLower : 2 ^ n - 1 ≤ k := Nat.le_of_not_gt hk
      have hleft : (carletFengUnivariateRepresentation alpha).coeff k = 0 := by
        rcases hkLower.eq_or_lt with htop | habove
        · rw [← htop]
          exact coeff_top_carletFengUnivariateRepresentation hn halpha
        · have hn0 : n ≠ 0 := by omega
          apply Polynomial.coeff_eq_zero_of_degree_lt
          exact (degree_carletFengUnivariateRepresentation_lt hn0 alpha).trans_le
            (by exact_mod_cast (show 2 ^ n ≤ k by omega))
      rw [hleft]
      have hnotmem : k ∉ Finset.Ico 1 (2 ^ n - 1) := by simp [hk]
      simp [carletFengClosedPolynomial, Polynomial.coeff_monomial,
        Polynomial.coeff_one, hk0, hnotmem]

/-- Carlet Relation (70): the field-domain function is the displayed
univariate sum, with square root `u^(1/2) = u^(2^(n-1))`. -/
theorem carletFeng_relation_70 {n : ℕ} (hn : 2 ≤ n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1))
    (x : BinaryGaloisField n) :
    algebraMap FABL.𝔽₂ (BinaryGaloisField n) (carletFengFieldFunction alpha x) =
      1 + ∑ i ∈ Finset.Ico 1 (2 ^ n - 1),
        (alpha ^ i / (1 + alpha ^ i) ^ (2 ^ (n - 1))) * x ^ i := by
  have heval := congrArg (fun P : (BinaryGaloisField n)[X] ↦ P.eval x)
    (carletFengUnivariateRepresentation_eq_closedPolynomial hn halpha)
  rw [carletFengUnivariateRepresentation, eval_univariateRepresentation] at heval
  rw [carletFengClosedPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_finsetSum] at heval
  simpa only [Polynomial.eval_monomial] using heval

theorem support_carletFengBooleanFunction {n : ℕ}
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    (alpha : BinaryGaloisField n) :
    (support (carletFengBooleanFunction θ alpha)).map θ.toEquiv.toEmbedding =
      carletFengSupport alpha := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_map.mp hz
    subst z
    rw [mem_support] at hx
    exact (carletFengFieldFunction_eq_one_iff alpha (θ x)).mp hx
  · intro hz
    refine Finset.mem_map.mpr ⟨θ.symm z, ?_, θ.apply_symm_apply z⟩
    rw [mem_support]
    simpa [carletFengBooleanFunction] using
      (carletFengFieldFunction_eq_one_iff alpha z).mpr hz

theorem isBalanced_carletFengBooleanFunction {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    IsBalanced (carletFengBooleanFunction θ alpha) := by
  rw [isBalanced_iff_hammingWeight_eq_two_pow_pred _ (by omega),
    hammingWeight_eq_card_support,
    ← carletFengSupport_card hn halpha,
    ← support_carletFengBooleanFunction θ alpha,
    Finset.card_map]

/-- The algebraic-degree consequence of Carlet Relation (70): the balanced
Carlet--Feng function has the maximal possible degree `n-1`. -/
theorem functionAlgebraicDegree_carletFengBooleanFunction
    {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    FABL.functionAlgebraicDegree (carletFengBooleanFunction θ alpha) = n - 1 := by
  let f := carletFengBooleanFunction θ alpha
  have hn0 : n ≠ 0 := by omega
  have hdegreeEq :
      FABL.functionAlgebraicDegree f =
        univariateBinaryDegree (carletFengUnivariateRepresentation alpha) := by
    simpa [f, carletFengBooleanFunction, carletFengUnivariateRepresentation] using
      functionAlgebraicDegree_eq_univariateBinaryDegree hn0 θ f
  have hcoeff :=
    coeff_two_pow_sub_two_carletFengUnivariateRepresentation_ne_zero hn halpha
  have hmem : 2 ^ n - 2 ∈ (carletFengUnivariateRepresentation alpha).support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hlower : n - 1 ≤ FABL.functionAlgebraicDegree f := by
    calc
      n - 1 = binaryWeight (2 ^ n - 2) :=
        (binaryWeight_two_pow_sub_two (by omega)).symm
      _ ≤ univariateBinaryDegree (carletFengUnivariateRepresentation alpha) := by
        rw [univariateBinaryDegree]
        exact Finset.le_sup hmem
      _ = FABL.functionAlgebraicDegree f := hdegreeEq.symm
  have hupper : FABL.functionAlgebraicDegree f ≤ n - 1 := by
    have hdimension := FABL.functionAlgebraicDegree_le_dimension f
    by_contra hdegree
    have hdegreeFull : FABL.functionAlgebraicDegree f = n := by omega
    have hodd :=
      (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
        f (by omega)).mp hdegreeFull
    have hweight : hammingWeight f = 2 ^ (n - 1) :=
      (isBalanced_iff_hammingWeight_eq_two_pow_pred f (by omega)).mp
        (isBalanced_carletFengBooleanFunction hn θ halpha)
    have hcard : (support f).card = 2 ^ (n - 1) := by
      rw [← hammingWeight_eq_card_support]
      exact hweight
    rw [hcard] at hodd
    have hsplit : n - 1 = (n - 2) + 1 := by omega
    have hpowEven : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      calc
        2 ^ (n - 1) = 2 ^ ((n - 2) + 1) :=
          congrArg (fun k : ℕ ↦ 2 ^ k) hsplit
        _ = 2 ^ (n - 2) * 2 := pow_succ 2 (n - 2)
    rw [hpowEven] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact Nat.le_antisymm hupper hlower

/-- Carlet Theorem 15: the consecutive-power construction has optimal
algebraic immunity. -/
theorem algebraicImmunity_carletFengBooleanFunction {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    algebraicImmunity (carletFengBooleanFunction θ alpha) = (n + 1) / 2 := by
  let f := carletFengBooleanFunction θ alpha
  change algebraicImmunity f = (n + 1) / 2
  apply Nat.le_antisymm
  · exact algebraicImmunity_le_ceiling_half f
  · by_contra hbound
    obtain ⟨g, hgWitness, hgDegreeEq⟩ :=
      exists_witness_functionAlgebraicDegree_eq_algebraicImmunity f
    have hgDegree : FABL.functionAlgebraicDegree g < (n + 1) / 2 := by omega
    let P := booleanUnivariateRepresentation θ g
    obtain ⟨hPSupport, hPCard, hPCardZero⟩ :=
      booleanUnivariate_support_bounds hn θ g hgDegree
    have horder : 0 < 2 ^ n - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have hsplit : n = (n - 1) + 1 := by omega
    have hpow : 2 ^ n = 2 ^ (n - 1) * 2 :=
      (congrArg (fun k : ℕ ↦ 2 ^ k) hsplit).trans (pow_succ 2 (n - 1))
    have hgEqZeroOfPZero (hPZero : P = 0) : g = 0 := by
      funext x
      have heval := congrArg (fun Q : (BinaryGaloisField n)[X] ↦ Q.eval (θ x)) hPZero
      simpa [P] using heval
    rcases hgWitness with hg | hg
    · have hgZeroOfMem (z : BinaryGaloisField n)
          (hz : z ∈ carletFengSupport alpha) : g (θ.symm z) = 0 := by
        have hproduct := congrFun hg.2 (θ.symm z)
        have hfOne : f (θ.symm z) = 1 := by
          simpa [f, carletFengBooleanFunction] using
            (carletFengFieldFunction_eq_one_iff alpha z).mpr hz
        change f (θ.symm z) * g (θ.symm z) = 0 at hproduct
        rwa [hfOne, one_mul] at hproduct
      have hPEvalZero : P.eval 0 = 0 := by
        change (booleanUnivariateRepresentation θ g).eval 0 = 0
        rw [eval_booleanUnivariateRepresentation,
          hgZeroOfMem 0 (zero_mem_carletFengSupport alpha)]
        simp
      have hPShort : P.support.card ≤ 2 ^ (n - 1) - 1 :=
        hPCardZero hPEvalZero
      have hPZero : P = 0 := by
        apply polynomial_eq_zero_of_consecutive_primitive_powers
          (start := 0) (count := 2 ^ (n - 1) - 1)
          horder halpha P hPSupport hPShort
        intro j hj
        have hz := hgZeroOfMem (alpha ^ j)
          (pow_mem_carletFengSupport_of_lt alpha hj)
        change (booleanUnivariateRepresentation θ g).eval (alpha ^ (0 + j)) = 0
        rw [zero_add, eval_booleanUnivariateRepresentation, hz]
        simp
      exact hg.1 (hgEqZeroOfPZero hPZero)
    · have hgZeroOutside (z : BinaryGaloisField n)
          (hz : z ∉ carletFengSupport alpha) : g (θ.symm z) = 0 := by
        have hproduct := congrFun hg.2 (θ.symm z)
        have hfZero : f (θ.symm z) = 0 := by
          simp [f, carletFengBooleanFunction, carletFengFieldFunction, hz]
        change (f (θ.symm z) + 1) * g (θ.symm z) = 0 at hproduct
        rwa [hfZero, zero_add, one_mul] at hproduct
      have hPZero : P = 0 := by
        apply polynomial_eq_zero_of_consecutive_primitive_powers
          (start := 2 ^ (n - 1) - 1) (count := 2 ^ (n - 1))
          horder halpha P hPSupport hPCard
        intro j hj
        have hexponentLower : 2 ^ (n - 1) - 1 ≤
            2 ^ (n - 1) - 1 + j := Nat.le_add_right _ _
        have hexponentUpper : 2 ^ (n - 1) - 1 + j < 2 ^ n - 1 := by
          omega
        have hz := hgZeroOutside (alpha ^ (2 ^ (n - 1) - 1 + j))
          (pow_not_mem_carletFengSupport_of_mem_interval hn halpha
            hexponentLower hexponentUpper)
        change (booleanUnivariateRepresentation θ g).eval
          (alpha ^ (2 ^ (n - 1) - 1 + j)) = 0
        rw [eval_booleanUnivariateRepresentation, hz]
        simp
      exact hg.1 (hgEqZeroOfPZero hPZero)

/-- Carlet Theorem 15: for `n ≥ 2`, the function supported on zero and the
first `2^(n-1)-1` powers of a primitive element is balanced and has algebraic
immunity `⌈n/2⌉`. -/
theorem carletFeng_balanced_and_algebraicImmunity {n : ℕ} (hn : 2 ≤ n)
    (θ : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] BinaryGaloisField n)
    {alpha : BinaryGaloisField n} (halpha : IsPrimitiveRoot alpha (2 ^ n - 1)) :
    IsBalanced (carletFengBooleanFunction θ alpha) ∧
      algebraicImmunity (carletFengBooleanFunction θ alpha) = (n + 1) / 2 :=
  ⟨isBalanced_carletFengBooleanFunction hn θ halpha,
    algebraicImmunity_carletFengBooleanFunction hn θ halpha⟩

end

end CryptBoolean
