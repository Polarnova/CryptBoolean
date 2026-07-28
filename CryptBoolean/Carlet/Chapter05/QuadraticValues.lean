/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity
public import CryptBoolean.Carlet.Chapter05.QuadraticWeights
public import CryptBoolean.Carlet.Chapter05.RestrictionNonlinearity
public import FABL.Chapter06.F₂Polynomials.Examples

/-!
# Values of quadratic Boolean functions
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n i : ℕ}

/-- The exponent interval in Carlet's exact quadratic weight and nonlinearity sets. -/
def IsQuadraticOffsetExponent (n i : ℕ) : Prop :=
  (n - 1) / 2 ≤ i ∧ i ≤ n - 1

/-- The natural-number interval is Carlet's `ceil(n/2)-1 ≤ i ≤ n-1`. -/
theorem isQuadraticOffsetExponent_iff_ceilingHalf
    (hn : 0 < n) :
    IsQuadraticOffsetExponent n i ↔
      (n + 1) / 2 - 1 ≤ i ∧ i ≤ n - 1 := by
  have hceil : (n + 1) / 2 - 1 = (n - 1) / 2 := by omega
  simp only [IsQuadraticOffsetExponent, hceil]

/-- The interval predicate uses the natural ceiling division by two. -/
theorem isQuadraticOffsetExponent_iff_ceilDiv
    (hn : 0 < n) :
    IsQuadraticOffsetExponent n i ↔
      n ⌈/⌉ 2 - 1 ≤ i ∧ i ≤ n - 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have hnumerator : n + 2 - 1 = n + 1 := by omega
  rw [hnumerator]
  exact isQuadraticOffsetExponent_iff_ceilingHalf hn

/-- The admissible exponent interval is exactly the parameter range obtained
by adjoining dummy coordinates to an even-dimensional quadratic block. -/
theorem isQuadraticOffsetExponent_iff_exists_parameters
    (hn : 0 < n) :
    IsQuadraticOffsetExponent n i ↔
      ∃ d m : ℕ, n = d + (m + m) ∧ i = d + m - 1 := by
  constructor
  · rintro ⟨hlower, hupper⟩
    let m := n - i - 1
    let d := n - (m + m)
    refine ⟨d, m, ?_, ?_⟩
    · dsimp [d, m]
      omega
    · dsimp [d, m]
      omega
  · rintro ⟨d, m, rfl, rfl⟩
    rw [IsQuadraticOffsetExponent]
    constructor
    · omega
    · omega

/-- A balanced positive-dimensional Boolean function has weight `2^(n-1)`. -/
theorem hammingWeight_eq_two_pow_pred_of_isBalanced
    (f : BooleanFunction n) (hn : 0 < n) (hf : IsBalanced f) :
    hammingWeight f = 2 ^ (n - 1) := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  unfold IsBalanced at hf
  rw [hpow] at hf
  omega

/-- In positive dimension, the central weight is equivalent to balancedness. -/
theorem isBalanced_iff_hammingWeight_eq_two_pow_pred
    (f : BooleanFunction n) (hn : 0 < n) :
    IsBalanced f ↔ hammingWeight f = 2 ^ (n - 1) := by
  constructor
  · exact hammingWeight_eq_two_pow_pred_of_isBalanced f hn
  · intro hweight
    unfold IsBalanced
    rw [hweight]
    calc
      2 * 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((n - 1) + 1) := (pow_succ _ _).symm
      _ = 2 ^ n := by congr 1; omega

/-- Affine Boolean functions have zero nonlinearity. -/
theorem nonlinearity_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    nonlinearity (FABL.affineFunction b a) = 0 := by
  unfold nonlinearity
  apply Nat.eq_zero_of_le_zero
  calc
    (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube n)).inf'
        Finset.univ_nonempty
        (fun p ↦ hammingDistance (FABL.affineFunction b a)
          (FABL.affineFunction p.1 p.2)) ≤
        hammingDistance (FABL.affineFunction b a)
          (FABL.affineFunction b a) :=
      Finset.inf'_le _ (Finset.mem_univ (b, a))
    _ = 0 := hammingDist_self _

/-- Every affine Boolean function has maximum raw Walsh magnitude `2^n`. -/
theorem maxWalshMagnitude_affineFunction
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    maxWalshMagnitude (FABL.affineFunction b a) = 2 ^ n := by
  have hrelation :=
    two_mul_nonlinearity_add_maxWalshMagnitude (FABL.affineFunction b a)
  rw [nonlinearity_affineFunction] at hrelation
  simpa using hrelation

/-- Adding an affine Boolean function preserves nonlinearity. -/
theorem nonlinearity_add_affineFunction
    (f : BooleanFunction n) (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    nonlinearity (f + FABL.affineFunction b a) = nonlinearity f := by
  have hf := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hg := two_mul_nonlinearity_add_maxWalshMagnitude
    (f + FABL.affineFunction b a)
  rw [maxWalshMagnitude_add_affineFunction] at hg
  omega

/-- Adding the constant one complements the Hamming weight. -/
theorem hammingWeight_add_constant_one
    (f : BooleanFunction n) :
    hammingWeight (f + FABL.affineFunction 1 0) =
      2 ^ n - hammingWeight f := by
  have hf := walshTransform_zero_eq_two_pow_sub_two_weight f
  have hg := walshTransform_zero_eq_two_pow_sub_two_weight
    (f + FABL.affineFunction 1 0)
  have hmodulation := walshTransform_add_affineFunction f 1 0 0
  simp only [add_zero] at hmodulation
  have hone : bitSignInt (1 : FABL.𝔽₂) = -1 := by
    simp [bitSignInt]
  rw [hone, neg_one_mul] at hmodulation
  have hlinear :
      (2 ^ n : ℤ) -
          2 * (hammingWeight (f + FABL.affineFunction 1 0) : ℤ) =
        -((2 ^ n : ℤ) - 2 * (hammingWeight f : ℤ)) := by
    rw [← hg, hmodulation, hf]
  clear hf hg hmodulation
  have hsumInt :
      (hammingWeight (f + FABL.affineFunction 1 0) : ℤ) +
        (hammingWeight f : ℤ) = (2 : ℤ) ^ n := by
    omega
  have hsum : hammingWeight (f + FABL.affineFunction 1 0) +
      hammingWeight f = 2 ^ n := by
    exact_mod_cast hsumInt
  omega

private def quadraticValueSplitCubeLinearEquiv (d r : ℕ) :
    FABL.F₂Cube (d + r) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube d × FABL.F₂Cube r) where
  __ := (Fin.appendEquiv d r).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext j <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext j <;> rfl

private def quadraticValueTailLinearMap (d r : ℕ) :
    FABL.F₂Cube (d + r) →ₗ[FABL.𝔽₂] FABL.F₂Cube r :=
  (LinearMap.snd FABL.𝔽₂ (FABL.F₂Cube d) (FABL.F₂Cube r)).comp
    (quadraticValueSplitCubeLinearEquiv d r).toLinearMap

/-- A complete inner-product block with `d` dummy coordinates. -/
def quadraticOffsetWitness (d m : ℕ) :
    BooleanFunction (d + (m + m)) :=
  completeBentExtension (FABL.affineFunction 0 0 : BooleanFunction d) m

private theorem quadraticOffsetWitness_eq_comp (d m : ℕ) :
    quadraticOffsetWitness d m =
      FABL.innerProductModTwoBit ∘
        (quadraticValueTailLinearMap d (m + m)).toAffineMap := by
  funext z
  simp [quadraticOffsetWitness, completeBentExtension, booleanDirectSum,
    quadraticValueTailLinearMap, quadraticValueSplitCubeLinearEquiv,
    FABL.affineFunction, FABL.f₂DotProduct, dotProduct]

/-- The dummy-coordinate inner-product witness is quadratic. -/
theorem functionAlgebraicDegree_quadraticOffsetWitness_le_two
    (d m : ℕ) :
    FABL.functionAlgebraicDegree (quadraticOffsetWitness d m) ≤ 2 := by
  rw [quadraticOffsetWitness_eq_comp]
  apply (functionAlgebraicDegree_comp_affineMap_le_general
    FABL.innerProductModTwoBit
      (quadraticValueTailLinearMap d (m + m)).toAffineMap).trans
  by_cases hm : m = 0
  · subst m
    rw [FABL.innerProductModTwoBit_eq_sum_anfMonomial]
    simp
  · rw [FABL.functionAlgebraicDegree_innerProductModTwoBit m
      (Nat.pos_of_ne_zero hm)]

/-- The zero-frequency raw Walsh value of the complete inner-product block is `2^m`. -/
theorem walshTransform_innerProductModTwoBit_zero (m : ℕ) :
    walshTransform (FABL.innerProductModTwoBit : BooleanFunction (m + m)) 0 =
      2 ^ m := by
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff]
  rw [show realSignView
      (FABL.innerProductModTwoBit : BooleanFunction (m + m)) =
        FABL.innerProductModTwo m by rfl]
  have hzero : (0 : FABL.F₂Cube (m + m)) =
      FABL.joinF₂CubeBlocks (0 : FABL.F₂Cube m) 0 := by
    funext j
    refine Fin.addCases (m := m) (n := m) ?_ ?_ j
    · intro k
      simp
    · intro k
      simp
  rw [hzero, FABL.vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks]
  simp [FABL.f₂DotProduct, pow_add]

/-- The witness has positive zero-frequency Walsh value `2^(d+m)`. -/
theorem walshTransform_quadraticOffsetWitness_zero (d m : ℕ) :
    walshTransform (quadraticOffsetWitness d m) 0 = 2 ^ (d + m) := by
  have hzero :
      Fin.append (0 : FABL.F₂Cube d) (0 : FABL.F₂Cube (m + m)) =
        (0 : FABL.F₂Cube (d + (m + m))) := by
    funext j
    refine Fin.addCases (m := d) (n := m + m) ?_ ?_ j
    · intro k
      simp
    · intro k
      simp
  rw [← hzero]
  change walshTransform
      (booleanDirectSum (FABL.affineFunction 0 0 : BooleanFunction d)
        FABL.innerProductModTwoBit)
      (Fin.append (0 : FABL.F₂Cube d) (0 : FABL.F₂Cube (m + m))) = _
  rw [walshTransform_booleanDirectSum_append,
    walshTransform_affineFunction,
    walshTransform_innerProductModTwoBit_zero]
  simp [bitSignInt, pow_add]

/-- The witness realizes the lower quadratic weight at offset `d+m-1`. -/
theorem hammingWeight_quadraticOffsetWitness
    (d m : ℕ) (hpositive : 0 < d + m) :
    hammingWeight (quadraticOffsetWitness d m) =
      2 ^ (d + (m + m) - 1) - 2 ^ (d + m - 1) := by
  have hzero := walshTransform_zero_eq_two_pow_sub_two_weight
    (quadraticOffsetWitness d m)
  rw [walshTransform_quadraticOffsetWitness_zero] at hzero
  have hdimPositive : 0 < d + (m + m) := by omega
  have hdimPow : (2 : ℤ) ^ (d + (m + m)) =
      2 * (2 : ℤ) ^ (d + (m + m) - 1) := by
    calc
      (2 : ℤ) ^ (d + (m + m)) =
          2 ^ ((d + (m + m) - 1) + 1) := by congr 1; omega
      _ = 2 ^ (d + (m + m) - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (d + (m + m) - 1) := by ring
  have hoffsetPow : (2 : ℤ) ^ (d + m) =
      2 * (2 : ℤ) ^ (d + m - 1) := by
    calc
      (2 : ℤ) ^ (d + m) = 2 ^ ((d + m - 1) + 1) := by congr 1; omega
      _ = 2 ^ (d + m - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (d + m - 1) := by ring
  rw [hdimPow, hoffsetPow] at hzero
  have hweightInt :
      (hammingWeight (quadraticOffsetWitness d m) : ℤ) =
        (2 : ℤ) ^ (d + (m + m) - 1) -
          (2 : ℤ) ^ (d + m - 1) := by
    omega
  have hpowLe : 2 ^ (d + m - 1) ≤ 2 ^ (d + (m + m) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast hweightInt

/-- The complemented witness realizes the upper quadratic weight. -/
def quadraticOffsetWitnessComplement (d m : ℕ) :
    BooleanFunction (d + (m + m)) :=
  quadraticOffsetWitness d m + FABL.affineFunction 1 0

/-- Complementing the witness preserves quadratic degree. -/
theorem functionAlgebraicDegree_quadraticOffsetWitnessComplement_le_two
    (d m : ℕ) :
    FABL.functionAlgebraicDegree (quadraticOffsetWitnessComplement d m) ≤ 2 := by
  apply (FABL.functionAlgebraicDegree_add_le_max
    (quadraticOffsetWitness d m) (FABL.affineFunction 1 0)).trans
  exact max_le (functionAlgebraicDegree_quadraticOffsetWitness_le_two d m)
    ((FABL.functionAlgebraicDegree_affineFunction_le_one 1 0).trans (by omega))

/-- The complemented witness has the upper quadratic weight at offset `d+m-1`. -/
theorem hammingWeight_quadraticOffsetWitnessComplement
    (d m : ℕ) (hpositive : 0 < d + m) :
    hammingWeight (quadraticOffsetWitnessComplement d m) =
      2 ^ (d + (m + m) - 1) + 2 ^ (d + m - 1) := by
  rw [quadraticOffsetWitnessComplement, hammingWeight_add_constant_one,
    hammingWeight_quadraticOffsetWitness d m hpositive]
  have hdimPositive : 0 < d + (m + m) := by omega
  have hdimPow : 2 ^ (d + (m + m)) =
      2 * 2 ^ (d + (m + m) - 1) := by
    calc
      2 ^ (d + (m + m)) = 2 ^ ((d + (m + m) - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (d + (m + m) - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (d + (m + m) - 1) := Nat.mul_comm _ _
  have hpowLe : 2 ^ (d + m - 1) ≤ 2 ^ (d + (m + m) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hdimPow, two_mul,
    Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self hpowLe]

/-- The witness has maximum raw Walsh magnitude `2^(d+m)`. -/
theorem maxWalshMagnitude_quadraticOffsetWitness (d m : ℕ) :
    maxWalshMagnitude (quadraticOffsetWitness d m) = 2 ^ (d + m) := by
  rw [quadraticOffsetWitness, maxWalshMagnitude_completeBentExtension,
    maxWalshMagnitude_affineFunction, ← pow_add]

/-- The witness realizes the quadratic nonlinearity at offset `d+m-1`. -/
theorem nonlinearity_quadraticOffsetWitness
    (d m : ℕ) (hpositive : 0 < d + m) :
    nonlinearity (quadraticOffsetWitness d m) =
      2 ^ (d + (m + m) - 1) - 2 ^ (d + m - 1) := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude
    (quadraticOffsetWitness d m)
  rw [maxWalshMagnitude_quadraticOffsetWitness] at hrelation
  have hdimPositive : 0 < d + (m + m) := by omega
  have hdimPow : 2 ^ (d + (m + m)) =
      2 * 2 ^ (d + (m + m) - 1) := by
    calc
      2 ^ (d + (m + m)) = 2 ^ ((d + (m + m) - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (d + (m + m) - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (d + (m + m) - 1) := Nat.mul_comm _ _
  have hoffsetPow : 2 ^ (d + m) = 2 * 2 ^ (d + m - 1) := by
    calc
      2 ^ (d + m) = 2 ^ ((d + m - 1) + 1) := by congr 1; omega
      _ = 2 ^ (d + m - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (d + m - 1) := Nat.mul_comm _ _
  have hpowLe : 2 ^ (d + m - 1) ≤ 2 ^ (d + (m + m) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hdimPow, hoffsetPow] at hrelation
  omega

/-- The central balanced weight is realized by a quadratic Boolean function. -/
theorem exists_quadratic_hammingWeight_eq_two_pow_pred
    (hn : 0 < n) :
    ∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧
        hammingWeight f = 2 ^ (n - 1) := by
  let j : Fin n := ⟨0, hn⟩
  let a : FABL.F₂Cube n := Pi.single j 1
  have ha : a ≠ 0 := by
    intro hzero
    have hj := congrFun hzero j
    simp [a, j] at hj
  refine ⟨FABL.affineFunction 0 a, ?_,
    hammingWeight_affineFunction_of_ne_zero 0 a ha⟩
  exact (FABL.functionAlgebraicDegree_affineFunction_le_one 0 a).trans (by omega)

/-- Every admissible lower quadratic weight is realized. -/
theorem exists_quadratic_hammingWeight_eq_sub
    (hn : 0 < n) (hi : IsQuadraticOffsetExponent n i) :
    ∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧
        hammingWeight f = 2 ^ (n - 1) - 2 ^ i := by
  obtain ⟨d, m, hdim, hoffset⟩ :=
    (isQuadraticOffsetExponent_iff_exists_parameters hn).mp hi
  subst n
  have hpositive : 0 < d + m := by omega
  refine ⟨quadraticOffsetWitness d m,
    functionAlgebraicDegree_quadraticOffsetWitness_le_two d m, ?_⟩
  simpa only [hoffset] using
    hammingWeight_quadraticOffsetWitness d m hpositive

/-- Every admissible upper quadratic weight is realized. -/
theorem exists_quadratic_hammingWeight_eq_add
    (hn : 0 < n) (hi : IsQuadraticOffsetExponent n i) :
    ∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i := by
  obtain ⟨d, m, hdim, hoffset⟩ :=
    (isQuadraticOffsetExponent_iff_exists_parameters hn).mp hi
  subst n
  have hpositive : 0 < d + m := by omega
  refine ⟨quadraticOffsetWitnessComplement d m,
    functionAlgebraicDegree_quadraticOffsetWitnessComplement_le_two d m, ?_⟩
  simpa only [hoffset] using
    hammingWeight_quadraticOffsetWitnessComplement d m hpositive

/-- Every admissible quadratic nonlinearity is realized. -/
theorem exists_quadratic_nonlinearity_eq_sub
    (hn : 0 < n) (hi : IsQuadraticOffsetExponent n i) :
    ∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧
        nonlinearity f = 2 ^ (n - 1) - 2 ^ i := by
  obtain ⟨d, m, hdim, hoffset⟩ :=
    (isQuadraticOffsetExponent_iff_exists_parameters hn).mp hi
  subst n
  have hpositive : 0 < d + m := by omega
  refine ⟨quadraticOffsetWitness d m,
    functionAlgebraicDegree_quadraticOffsetWitness_le_two d m, ?_⟩
  simpa only [hoffset] using
    nonlinearity_quadraticOffsetWitness d m hpositive

/-- Every quadratic weight belongs to Carlet's displayed finite value set. -/
theorem quadratic_hammingWeight_value_restriction
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    hammingWeight f = 2 ^ (n - 1) ∨
      ∃ i : ℕ, IsQuadraticOffsetExponent n i ∧
        (hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
          hammingWeight f = 2 ^ (n - 1) + 2 ^ i) := by
  by_cases hbalanced : IsBalanced f
  · exact Or.inl (hammingWeight_eq_two_pow_pred_of_isBalanced f hn hbalanced)
  · let k := Module.finrank FABL.𝔽₂ (linearKernel f)
    have heven : Even (n + k) :=
      even_dimension_add_finrank_linearKernel_of_not_balanced
        f hdegree hbalanced
    obtain ⟨t, ht⟩ := heven
    have hhalf : (n + k) / 2 = t := by omega
    have hk : k ≤ n := by
      have h := Submodule.finrank_le (linearKernel f)
      simpa only [Module.finrank_pi, Fintype.card_fin] using h
    have htpositive : 0 < t := by omega
    have hinterval : IsQuadraticOffsetExponent n (t - 1) := by
      rw [IsQuadraticOffsetExponent]
      constructor <;> omega
    refine Or.inr ⟨t - 1, hinterval, ?_⟩
    simpa only [show Module.finrank FABL.𝔽₂ (linearKernel f) = k by rfl,
      hhalf] using
      quadratic_weight_eq_two_pow_sub_or_add f hn hdegree hbalanced

private theorem two_pow_sub_center_sub_offset
    (hn : 0 < n) (hi : i ≤ n - 1) :
    2 ^ n - (2 ^ (n - 1) - 2 ^ i) =
      2 ^ (n - 1) + 2 ^ i := by
  have hdimPow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have hpowLe : 2 ^ i ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hi
  rw [hdimPow, two_mul,
    Nat.add_sub_assoc (Nat.sub_le _ _), Nat.sub_sub_self hpowLe]

private theorem two_pow_sub_center_add_offset
    (hn : 0 < n) (_hi : i ≤ n - 1) :
    2 ^ n - (2 ^ (n - 1) + 2 ^ i) =
      2 ^ (n - 1) - 2 ^ i := by
  have hdimPow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [hdimPow, two_mul, Nat.add_sub_add_left]

/-- A displayed noncentral quadratic weight is not balanced. -/
theorem not_isBalanced_of_hammingWeight_eq_quadraticOffset
    (f : BooleanFunction n) (hn : 0 < n)
    (hi : IsQuadraticOffsetExponent n i)
    (hweight :
      hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i) :
    ¬ IsBalanced f := by
  intro hbalanced
  have hcenter := hammingWeight_eq_two_pow_pred_of_isBalanced f hn hbalanced
  have hoffsetPositive : 0 < 2 ^ i := pow_pos (by omega) _
  have hoffsetLe : 2 ^ i ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hi.2
  rcases hweight with hweight | hweight <;> omega

/-- Every affine shift of a quadratic function with offset exponent `i` has
one of the same two weights or is balanced. -/
theorem quadratic_affine_shift_hammingWeight_trichotomy
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hi : IsQuadraticOffsetExponent n i)
    (hweight :
      hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i)
    (b : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    hammingWeight (f + FABL.affineFunction b a) =
        2 ^ (n - 1) - 2 ^ i ∨
      hammingWeight (f + FABL.affineFunction b a) = 2 ^ (n - 1) ∨
      hammingWeight (f + FABL.affineFunction b a) =
        2 ^ (n - 1) + 2 ^ i := by
  let g : BooleanFunction n := f + FABL.affineFunction b a
  have hgdegree : FABL.functionAlgebraicDegree g ≤ 2 := by
    apply (FABL.functionAlgebraicDegree_add_le_max
      f (FABL.affineFunction b a)).trans
    exact max_le hdegree
      ((FABL.functionAlgebraicDegree_affineFunction_le_one b a).trans (by omega))
  have hfnotBalanced : ¬ IsBalanced f :=
    not_isBalanced_of_hammingWeight_eq_quadraticOffset f hn hi hweight
  by_cases hgbalanced : IsBalanced g
  · exact Or.inr (Or.inl
      (hammingWeight_eq_two_pow_pred_of_isBalanced g hn hgbalanced))
  · have hfsq :=
      walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
        f hdegree hfnotBalanced
    have hgsq :=
      walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
        g hgdegree hgbalanced
    have hkernel : linearKernel g = linearKernel f := by
      exact linearKernel_add_affineFunction f b a
    rw [hkernel] at hgsq
    have hsq : walshTransform g 0 ^ 2 = walshTransform f 0 ^ 2 :=
      hgsq.trans hfsq.symm
    have hzeroF := walshTransform_zero_eq_two_pow_sub_two_weight f
    have hzeroG := walshTransform_zero_eq_two_pow_sub_two_weight g
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hequal | hnegative
    · have hweightEqualInt : (hammingWeight g : ℤ) = hammingWeight f := by
        omega
      have hweightEqual : hammingWeight g = hammingWeight f := by
        exact_mod_cast hweightEqualInt
      rcases hweight with hweight | hweight
      · exact Or.inl (hweightEqual.trans hweight)
      · exact Or.inr (Or.inr (hweightEqual.trans hweight))
    · have hlinear :
          (2 : ℤ) ^ n - 2 * (hammingWeight g : ℤ) =
            -((2 : ℤ) ^ n - 2 * (hammingWeight f : ℤ)) := by
        rw [← hzeroG, hnegative, hzeroF]
      have hsumInt : (hammingWeight g : ℤ) +
          (hammingWeight f : ℤ) = (2 : ℤ) ^ n := by
        omega
      have hsum : hammingWeight g + hammingWeight f = 2 ^ n := by
        exact_mod_cast hsumInt
      have hgComplement : hammingWeight g = 2 ^ n - hammingWeight f :=
        Nat.eq_sub_of_add_eq hsum
      rcases hweight with hweight | hweight
      · right
        right
        have hcomplement := two_pow_sub_center_sub_offset hn hi.2
        rw [hgComplement, hweight, hcomplement]
      · left
        have hcomplement := two_pow_sub_center_add_offset hn hi.2
        rw [hgComplement, hweight, hcomplement]

/-- A nonbalanced quadratic function has no Walsh magnitude larger than its
zero-frequency magnitude. -/
theorem maxWalshMagnitude_eq_natAbs_walshTransform_zero_of_quadratic_notBalanced
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hnotBalanced : ¬ IsBalanced f) :
    maxWalshMagnitude f = (walshTransform f 0).natAbs := by
  unfold maxWalshMagnitude
  apply Nat.le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
      (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
    intro u _hu
    let g : BooleanFunction n :=
      f + FABL.affineFunction 0 u
    have hgdegree : FABL.functionAlgebraicDegree g ≤ 2 := by
      apply (FABL.functionAlgebraicDegree_add_le_max
        f (FABL.affineFunction 0 u)).trans
      exact max_le hdegree
        ((FABL.functionAlgebraicDegree_affineFunction_le_one 0 u).trans (by omega))
    have hshift : walshTransform g 0 = walshTransform f u :=
      walshTransform_add_linearFunction_zero f u
    rw [← hshift]
    by_cases hgbalanced : IsBalanced g
    · rw [(isBalanced_iff_walshTransform_zero_eq_zero g).mp hgbalanced]
      exact Nat.zero_le _
    · have hfsq :=
        walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
          f hdegree hnotBalanced
      have hgsq :=
        walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced
          g hgdegree hgbalanced
      have hkernel : linearKernel g = linearKernel f :=
        linearKernel_add_affineFunction f 0 u
      rw [hkernel] at hgsq
      have hsq : walshTransform g 0 ^ 2 = walshTransform f 0 ^ 2 :=
        hgsq.trans hfsq.symm
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hequal | hnegative
      · rw [hequal]
      · rw [hnegative, Int.natAbs_neg]
  · exact Finset.le_sup'
      (fun u : FABL.F₂Cube n ↦ (walshTransform f u).natAbs)
      (Finset.mem_univ (0 : FABL.F₂Cube n))

/-- A displayed quadratic weight determines the zero-frequency Walsh magnitude. -/
theorem natAbs_walshTransform_zero_eq_two_pow_succ_of_quadratic_weight
    (f : BooleanFunction n) (hn : 0 < n)
    (hi : IsQuadraticOffsetExponent n i)
    (hweight :
      hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i) :
    (walshTransform f 0).natAbs = 2 ^ (i + 1) := by
  have hoffsetLe : 2 ^ i ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hi.2
  have hdimPow : (2 : ℤ) ^ n =
      2 * (2 : ℤ) ^ (n - 1) := by
    calc
      (2 : ℤ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by ring
  have hoffsetPow : (2 : ℤ) ^ (i + 1) =
      2 * (2 : ℤ) ^ i := by
    rw [pow_succ]
    ring
  rcases hweight with hweight | hweight
  · have hweightInt : (hammingWeight f : ℤ) =
        (2 : ℤ) ^ (n - 1) - (2 : ℤ) ^ i := by
      exact_mod_cast hweight
    have hwalsh : walshTransform f 0 = (2 : ℤ) ^ (i + 1) := by
      rw [walshTransform_zero_eq_two_pow_sub_two_weight, hweightInt,
        hdimPow, hoffsetPow]
      ring
    rw [hwalsh]
    simp
  · have hweightInt : (hammingWeight f : ℤ) =
        (2 : ℤ) ^ (n - 1) + (2 : ℤ) ^ i := by
      exact_mod_cast hweight
    have hwalsh : walshTransform f 0 = -((2 : ℤ) ^ (i + 1)) := by
      rw [walshTransform_zero_eq_two_pow_sub_two_weight, hweightInt,
        hdimPow, hoffsetPow]
      ring
    rw [hwalsh, Int.natAbs_neg]
    simp

/-- A quadratic weight offset determines the maximum Walsh magnitude. -/
theorem maxWalshMagnitude_eq_two_pow_succ_of_quadratic_weight
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hi : IsQuadraticOffsetExponent n i)
    (hweight :
      hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i) :
    maxWalshMagnitude f = 2 ^ (i + 1) := by
  rw [maxWalshMagnitude_eq_natAbs_walshTransform_zero_of_quadratic_notBalanced
    f hdegree
      (not_isBalanced_of_hammingWeight_eq_quadraticOffset f hn hi hweight)]
  exact natAbs_walshTransform_zero_eq_two_pow_succ_of_quadratic_weight
    f hn hi hweight

/-- A quadratic weight offset determines its exact nonlinearity. -/
theorem quadratic_nonlinearity_eq_sub_of_hammingWeight_offset
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hi : IsQuadraticOffsetExponent n i)
    (hweight :
      hammingWeight f = 2 ^ (n - 1) - 2 ^ i ∨
        hammingWeight f = 2 ^ (n - 1) + 2 ^ i) :
    nonlinearity f = 2 ^ (n - 1) - 2 ^ i := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude f
  rw [maxWalshMagnitude_eq_two_pow_succ_of_quadratic_weight
    f hn hdegree hi hweight] at hrelation
  have hdimPow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have hoffsetPow : 2 ^ (i + 1) = 2 * 2 ^ i := by
    rw [pow_succ]
    exact Nat.mul_comm _ _
  rw [hdimPow, hoffsetPow] at hrelation
  have hsum : nonlinearity f + 2 ^ i = 2 ^ (n - 1) := by omega
  exact Nat.eq_sub_of_add_eq hsum

/-- Every quadratic nonlinearity belongs to Carlet's displayed value set. -/
theorem quadratic_nonlinearity_value_restriction
    (f : BooleanFunction n) (hn : 0 < n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ i : ℕ, IsQuadraticOffsetExponent n i ∧
      nonlinearity f = 2 ^ (n - 1) - 2 ^ i := by
  obtain ⟨u, hu⟩ := exists_walshTransform_ne_zero f
  let g : BooleanFunction n := f + FABL.affineFunction 0 u
  have hgdegree : FABL.functionAlgebraicDegree g ≤ 2 := by
    apply (FABL.functionAlgebraicDegree_add_le_max
      f (FABL.affineFunction 0 u)).trans
    exact max_le hdegree
      ((FABL.functionAlgebraicDegree_affineFunction_le_one 0 u).trans (by omega))
  have hgWalsh : walshTransform g 0 ≠ 0 := by
    rw [show walshTransform g 0 = walshTransform f u by
      exact walshTransform_add_linearFunction_zero f u]
    exact hu
  have hgnotBalanced : ¬ IsBalanced g := by
    rw [isBalanced_iff_walshTransform_zero_eq_zero]
    exact hgWalsh
  rcases quadratic_hammingWeight_value_restriction g hn hgdegree with
    hcenter | ⟨i, hi, hweight⟩
  · exact False.elim (hgnotBalanced
      ((isBalanced_iff_hammingWeight_eq_two_pow_pred g hn).mpr hcenter))
  · refine ⟨i, hi, ?_⟩
    calc
      nonlinearity f = nonlinearity g :=
        (nonlinearity_add_affineFunction f 0 u).symm
      _ = 2 ^ (n - 1) - 2 ^ i :=
        quadratic_nonlinearity_eq_sub_of_hammingWeight_offset
          g hn hgdegree hi hweight

/-- The set of quadratic weights is exactly Carlet's displayed set. -/
theorem exists_quadratic_hammingWeight_eq_iff
    (hn : 0 < n) (w : ℕ) :
    (∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧ hammingWeight f = w) ↔
      w = 2 ^ (n - 1) ∨
        ∃ i : ℕ, IsQuadraticOffsetExponent n i ∧
          (w = 2 ^ (n - 1) - 2 ^ i ∨
            w = 2 ^ (n - 1) + 2 ^ i) := by
  constructor
  · rintro ⟨f, hdegree, rfl⟩
    exact quadratic_hammingWeight_value_restriction f hn hdegree
  · rintro (hcenter | ⟨i, hi, hlower | hupper⟩)
    · obtain ⟨f, hdegree, hweight⟩ :=
        exists_quadratic_hammingWeight_eq_two_pow_pred hn
      exact ⟨f, hdegree, hweight.trans hcenter.symm⟩
    · obtain ⟨f, hdegree, hweight⟩ :=
        exists_quadratic_hammingWeight_eq_sub hn hi
      exact ⟨f, hdegree, hweight.trans hlower.symm⟩
    · obtain ⟨f, hdegree, hweight⟩ :=
        exists_quadratic_hammingWeight_eq_add hn hi
      exact ⟨f, hdegree, hweight.trans hupper.symm⟩

/-- The set of quadratic nonlinearities is exactly Carlet's displayed set. -/
theorem exists_quadratic_nonlinearity_eq_iff
    (hn : 0 < n) (v : ℕ) :
    (∃ f : BooleanFunction n,
      FABL.functionAlgebraicDegree f ≤ 2 ∧ nonlinearity f = v) ↔
      ∃ i : ℕ, IsQuadraticOffsetExponent n i ∧
        v = 2 ^ (n - 1) - 2 ^ i := by
  constructor
  · rintro ⟨f, hdegree, rfl⟩
    obtain ⟨i, hi, hvalue⟩ :=
      quadratic_nonlinearity_value_restriction f hn hdegree
    exact ⟨i, hi, hvalue⟩
  · rintro ⟨i, hi, hvalue⟩
    obtain ⟨f, hdegree, hnonlinearity⟩ :=
      exists_quadratic_nonlinearity_eq_sub hn hi
    exact ⟨f, hdegree, hnonlinearity.trans hvalue.symm⟩

end CryptBoolean
