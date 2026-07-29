/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.DegreeBounds
public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandDegree
public import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandUpper
public import CryptBoolean.Carlet.Chapter07.SarkarMaitra
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Fintype.Powerset

/-!
# Optimal general Maiorana--McFarland functions

Carlet Chapter 7: classification of general Maiorana--McFarland functions
that attain the resilient nonlinearity bound under the strict image-weight
hypothesis.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r s : ℕ}

/-- The quadratic product of the two coordinate functions. -/
def twoVariableProduct : BooleanFunction 2 :=
  FABL.anfMonomial (Finset.univ : Finset (Fin 2))

@[simp] theorem twoVariableProduct_apply (y : FABL.F₂Cube 2) :
    twoVariableProduct y = y 0 * y 1 := by
  simp [twoVariableProduct, FABL.anfMonomial]

/-- The two-coordinate product on a cube whose dimension is identified with
two. -/
def twoVariableProductAt {s : ℕ} (hs : s = 2) : BooleanFunction s :=
  fun y ↦ y ⟨0, by omega⟩ * y ⟨1, by omega⟩

private theorem k_lt_leftDimension_of_weight_gt
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card) :
    k < r := by
  exact (hweight 0).trans_le (by
    calc
      (FABL.f₂Support (φ 0)).card ≤
          (Finset.univ : Finset (Fin r)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = r := by simp)

/-- Equality in the resilient nonlinearity bound fixes the maximum Walsh
magnitude at `2^(k+2)`. -/
theorem maxWalshMagnitude_eq_of_maioranaMcFarland_optimal
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1)) :
    maxWalshMagnitude (booleanMaioranaMcFarlandGeneral φ g) =
      2 ^ (k + 2) := by
  apply maxWalshMagnitude_eq_two_pow_m_add_two_of_nonlinearity_eq
  · have hk := k_lt_leftDimension_of_weight_gt k φ hweight
    omega
  · exact hnonlinearity

private theorem one_le_maxMaioranaMcFarlandFiberCardinality
    (φ : FABL.F₂Cube s → FABL.F₂Cube r) :
    1 ≤ maxMaioranaMcFarlandFiberCardinality φ := by
  have hfiber : 1 ≤ maioranaMcFarlandFiberCardinality φ (φ 0) := by
    rw [maioranaMcFarlandFiberCardinality]
    exact Finset.one_le_card.mpr ⟨0, by simp⟩
  exact hfiber.trans (maioranaMcFarlandFiberCardinality_le_max φ (φ 0))

/-- Under the strict image-weight hypothesis, optimal nonlinearity forces
the left block dimension to be either `k+1` or `k+2`. -/
theorem leftDimension_eq_succ_or_add_two_of_maioranaMcFarland_optimal
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1)) :
    r = k + 1 ∨ r = k + 2 := by
  have hk : k < r := k_lt_leftDimension_of_weight_gt k φ hweight
  have hmax := maxWalshMagnitude_eq_of_maioranaMcFarland_optimal
    k φ g hs hweight hnonlinearity
  have hfiber := one_le_maxMaioranaMcFarlandFiberCardinality φ
  have hsqrt : 0 < Real.sqrt
      (maxMaioranaMcFarlandFiberCardinality φ : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hfiber)
  have hceil : 1 ≤
      ⌈Real.sqrt (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ := by
    exact (Nat.ceil_pos.mpr hsqrt)
  have hbound :=
    two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude φ g
  rw [hmax] at hbound
  have hpower : 2 ^ r ≤ 2 ^ (k + 2) := by
    calc
      2 ^ r = 2 ^ r * 1 := by omega
      _ ≤ 2 ^ r *
          ⌈Real.sqrt
            (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ :=
        Nat.mul_le_mul_left _ hceil
      _ ≤ 2 ^ (k + 2) := hbound
  have hr : r ≤ k + 2 :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpower
  omega

/-- The largest fiber of a constant frequency map is the entire domain. -/
theorem maxMaioranaMcFarlandFiberCardinality_const
    (a : FABL.F₂Cube r) :
    maxMaioranaMcFarlandFiberCardinality
        (fun _ : FABL.F₂Cube s ↦ a) = 2 ^ s := by
  apply Nat.le_antisymm
  · unfold maxMaioranaMcFarlandFiberCardinality
    apply Finset.sup'_le Finset.univ_nonempty
    intro b _hb
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  · calc
      2 ^ s = maioranaMcFarlandFiberCardinality
          (fun _ : FABL.F₂Cube s ↦ a) a := by
        simp [maioranaMcFarlandFiberCardinality]
      _ ≤ maxMaioranaMcFarlandFiberCardinality
          (fun _ : FABL.F₂Cube s ↦ a) :=
        maioranaMcFarlandFiberCardinality_le_max _ _

private theorem rightDimension_le_two_of_constant_optimal
    (k : ℕ) (g : BooleanFunction s) (hrank : r = k + 1)
    (hmax : maxWalshMagnitude
      (booleanMaioranaMcFarlandGeneral
        (fun _ : FABL.F₂Cube s ↦ (1 : FABL.F₂Cube r)) g) =
        2 ^ (k + 2)) :
    s ≤ 2 := by
  have hbound :=
    two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude
      (fun _ : FABL.F₂Cube s ↦ (1 : FABL.F₂Cube r)) g
  rw [maxMaioranaMcFarlandFiberCardinality_const, hmax] at hbound
  have hceil :
      ⌈Real.sqrt ((2 ^ s : ℕ) : ℝ)⌉₊ ≤ 2 := by
    rw [hrank] at hbound
    have hpow : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
    rw [show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]] at hbound
    exact Nat.le_of_mul_le_mul_left hbound hpow
  have hsqrt : Real.sqrt ((2 ^ s : ℕ) : ℝ) ≤ 2 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpowerReal : ((2 ^ s : ℕ) : ℝ) ≤ 2 ^ 2 :=
    (Real.sqrt_le_iff).mp hsqrt |>.2
  have hpower : 2 ^ s ≤ (2 : ℕ) ^ 2 := by
    exact_mod_cast hpowerReal
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpower

private theorem maxWalshMagnitude_coordinateSum_univ :
    maxWalshMagnitude
        (FABL.coordinateSum (Finset.univ : Finset (Fin r))) = 2 ^ r := by
  have hfunction :
      (FABL.coordinateSum (Finset.univ : Finset (Fin r)) :
          BooleanFunction r) =
        FABL.affineFunction 0
          (FABL.f₂CubeOfFinset (Finset.univ : Finset (Fin r))) := by
    funext x
    rw [FABL.affineFunction, zero_add,
      FABL.f₂DotProduct_f₂CubeOfFinset]
  rw [hfunction, maxWalshMagnitude_affineFunction]

private theorem maxWalshMagnitude_offset_eq_two_of_constant_optimal
    (k : ℕ) (g : BooleanFunction s)
    (hrank : r = k + 1)
    (hmax : maxWalshMagnitude
      (booleanMaioranaMcFarlandGeneral
        (fun _ : FABL.F₂Cube s ↦ (1 : FABL.F₂Cube r)) g) =
        2 ^ (k + 2)) :
    maxWalshMagnitude g = 2 := by
  rw [booleanMaioranaMcFarlandGeneral_constant_one_eq_directSum,
    maxWalshMagnitude_booleanDirectSum,
    maxWalshMagnitude_coordinateSum_univ] at hmax
  rw [hrank] at hmax
  have hpow : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  rw [show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]] at hmax
  exact Nat.eq_of_mul_eq_mul_left hpow hmax

private theorem isBent_of_twoVariable_maxWalshMagnitude_eq_two
    (g : BooleanFunction 2) (hmax : maxWalshMagnitude g = 2) :
    IsBent g := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude g
  rw [hmax] at hrelation
  have hnonlinearity : nonlinearity g = 1 := by norm_num at hrelation ⊢; omega
  apply (nonlinearity_cast_eq_relation_36_iff_isBent g).mp
  norm_num [hnonlinearity]

private theorem anfCoeff_univ_ne_zero_of_twoVariable_degree_eq_two
    (g : BooleanFunction 2)
    (hdegree : FABL.functionAlgebraicDegree g = 2) :
    FABL.anfCoeff g Finset.univ ≠ 0 := by
  intro htop
  have hle : FABL.functionAlgebraicDegree g ≤ 1 := by
    rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
    intro S hS
    have hne : S ≠ Finset.univ := by
      intro hSuniv
      subst S
      exact hS htop
    have hproper : S ⊂ (Finset.univ : Finset (Fin 2)) :=
      (Finset.ssubset_iff_subset_ne).2
        ⟨Finset.subset_univ S, hne⟩
    have hcard : S.card < 2 := by
      simpa using Finset.card_lt_card hproper
    omega
  omega

private theorem functionAlgebraicDegree_add_twoVariableProduct_le_one
    (g : BooleanFunction 2)
    (hdegree : FABL.functionAlgebraicDegree g = 2) :
    FABL.functionAlgebraicDegree (g + twoVariableProduct) ≤ 1 := by
  have htop :=
    anfCoeff_univ_ne_zero_of_twoVariable_degree_eq_two g hdegree
  have htopOne : FABL.anfCoeff g Finset.univ = 1 :=
    Fin.eq_one_of_ne_zero _ htop
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hS
  have hcardLe : S.card ≤ 2 := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin 2)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 2 := by simp
  by_contra hcard
  have hcardEq : S.card = 2 := by omega
  have hSuniv : S = (Finset.univ : Finset (Fin 2)) := by
    apply Finset.eq_univ_of_card
    simpa using hcardEq
  subst S
  apply hS
  rw [FABL.anfCoeff_add]
  simp [twoVariableProduct, FABL.anfCoeff_anfMonomial, htopOne]

/-- A two-variable Boolean function with maximum Walsh magnitude two is its
quadratic coordinate product plus an affine function. -/
theorem exists_eq_twoVariableProduct_add_affine_of_maxWalshMagnitude_eq_two
    (g : BooleanFunction 2) (hmax : maxWalshMagnitude g = 2) :
    ∃ c a, g = twoVariableProduct + FABL.affineFunction c a := by
  have hbent := isBent_of_twoVariable_maxWalshMagnitude_eq_two g hmax
  have hdegree := functionAlgebraicDegree_eq_two_of_isBent g hbent
  have hdegreeSum :=
    functionAlgebraicDegree_add_twoVariableProduct_le_one g hdegree
  obtain ⟨c, a, haffine⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (g + twoVariableProduct) hdegreeSum
  refine ⟨c, a, ?_⟩
  funext y
  have hy := congrFun haffine y
  simp only [Pi.add_apply] at hy ⊢
  calc
    g y = twoVariableProduct y +
        (g y + twoVariableProduct y) := by
      calc
        g y = g y + (twoVariableProduct y + twoVariableProduct y) := by
          rw [ZModModule.add_self, add_zero]
        _ = twoVariableProduct y +
            (g y + twoVariableProduct y) := by abel
    _ = twoVariableProduct y + FABL.affineFunction c a y := by rw [hy]

/-- The same quadratic-affine classification transported along an equality
of the domain dimension with two. -/
theorem exists_eq_twoVariableProductAt_add_affine_of_maxWalshMagnitude_eq_two
    (g : BooleanFunction s) (hsTwo : s = 2)
    (hmax : maxWalshMagnitude g = 2) :
    ∃ c a, g = twoVariableProductAt hsTwo + FABL.affineFunction c a := by
  subst s
  obtain ⟨c, a, hg⟩ :=
    exists_eq_twoVariableProduct_add_affine_of_maxWalshMagnitude_eq_two g hmax
  refine ⟨c, a, ?_⟩
  rw [hg]
  congr 2
  funext y
  simp [twoVariableProductAt]

/-- In the `r=k+1` branch, the frequency map is constant all-one, the right
block has at most two variables, and the binary endpoint is quadratic up to
an affine function. -/
theorem maioranaMcFarland_optimal_constant_branch
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1))
    (hrank : r = k + 1) :
    φ = (fun _ ↦ 1) ∧
      r + s ≤ k + 3 ∧
      (s = 1 ∨ ∃ hsTwo : s = 2, ∃ c a,
        g = twoVariableProductAt hsTwo + FABL.affineFunction c a) := by
  have hmap : φ = fun _ ↦ 1 := by
    apply map_eq_one_of_weight_gt_natPred φ hr
    intro y
    have hy := hweight y
    omega
  have hmax := maxWalshMagnitude_eq_of_maioranaMcFarland_optimal
    k φ g hs hweight hnonlinearity
  have hmaxConst := hmax
  rw [hmap] at hmaxConst
  have hsLe := rightDimension_le_two_of_constant_optimal
    k g hrank hmaxConst
  refine ⟨hmap, by omega, ?_⟩
  have hsCases : s = 1 ∨ s = 2 := by omega
  rcases hsCases with hsOne | hsTwo
  · exact Or.inl hsOne
  · right
    refine ⟨hsTwo, ?_⟩
    apply exists_eq_twoVariableProductAt_add_affine_of_maxWalshMagnitude_eq_two
    exact maxWalshMagnitude_offset_eq_two_of_constant_optimal
      k g hrank hmaxConst

private theorem maxMaioranaMcFarlandFiberCardinality_le_one_of_add_two_optimal
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hrank : r = k + 2)
    (hmax : maxWalshMagnitude
      (booleanMaioranaMcFarlandGeneral φ g) = 2 ^ (k + 2)) :
    maxMaioranaMcFarlandFiberCardinality φ ≤ 1 := by
  have hbound :=
    two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude φ g
  rw [hmax, ← hrank] at hbound
  have hpow : 0 < 2 ^ r := pow_pos (by omega) _
  have hceil :
      ⌈Real.sqrt
        (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ ≤ 1 := by
    have hbound' :
        2 ^ r *
            ⌈Real.sqrt
              (maxMaioranaMcFarlandFiberCardinality φ : ℝ)⌉₊ ≤
          2 ^ r * 1 := by simpa using hbound
    exact Nat.le_of_mul_le_mul_left hbound' hpow
  have hsqrt :
      Real.sqrt (maxMaioranaMcFarlandFiberCardinality φ : ℝ) ≤ 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hmaxReal :
      (maxMaioranaMcFarlandFiberCardinality φ : ℝ) ≤ 1 :=
    Real.sqrt_le_one.mp hsqrt
  exact_mod_cast hmaxReal

private theorem injective_of_maxMaioranaMcFarlandFiberCardinality_le_one
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (hmax : maxMaioranaMcFarlandFiberCardinality φ ≤ 1) :
    Function.Injective φ := by
  intro y z hyz
  have hcard : maioranaMcFarlandFiberCardinality φ (φ y) ≤ 1 :=
    (maioranaMcFarlandFiberCardinality_le_max φ (φ y)).trans hmax
  rw [maioranaMcFarlandFiberCardinality] at hcard
  apply (Finset.card_le_one_iff.mp hcard)
  · simp
  · simp [hyz]

/-- In the `r=k+2` branch, every frequency-map fiber is a singleton or
empty, so the frequency map is injective. -/
theorem injective_of_maioranaMcFarland_optimal_add_two_branch
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1))
    (hrank : r = k + 2) :
    Function.Injective φ := by
  have hmax := maxWalshMagnitude_eq_of_maioranaMcFarland_optimal
    k φ g hs hweight hnonlinearity
  apply injective_of_maxMaioranaMcFarlandFiberCardinality_le_one φ
  exact maxMaioranaMcFarlandFiberCardinality_le_one_of_add_two_optimal
    k φ g hrank hmax

/-- There are exactly `r+1` binary vectors of length `r` and weight strictly
greater than `r-2`. -/
theorem card_highWeightCube (hr : 2 ≤ r) :
    Fintype.card {a : FABL.F₂Cube r //
      r - 2 < (FABL.f₂Support a).card} = r + 1 := by
  let e₁ :
      {a : FABL.F₂Cube r // r - 2 < (FABL.f₂Support a).card} ≃
        {S : Finset (Fin r) // r - 2 < S.card} :=
    Equiv.subtypeEquiv (FABL.f₂CubeEquivFinset r) (fun a ↦ by rfl)
  let e₂ :
      {S : Finset (Fin r) // r - 2 < S.card} ≃
        {S : Finset (Fin r) // S.card = r - 1 ∨ S.card = r} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun S ↦ by
      simp only [Equiv.refl_apply]
      have hcard : S.card ≤ r := by
        calc
          S.card ≤ (Finset.univ : Finset (Fin r)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = r := by simp
      omega)
  calc
    Fintype.card {a : FABL.F₂Cube r //
        r - 2 < (FABL.f₂Support a).card} =
        Fintype.card {S : Finset (Fin r) // r - 2 < S.card} :=
      Fintype.card_congr e₁
    _ = Fintype.card {S : Finset (Fin r) //
          S.card = r - 1 ∨ S.card = r} :=
      Fintype.card_congr e₂
    _ = Fintype.card {S : Finset (Fin r) // S.card = r - 1} +
          Fintype.card {S : Finset (Fin r) // S.card = r} := by
      apply Fintype.card_subtype_or_disjoint
      exact Set.disjoint_left.2 (by
        intro S hfirst hsecond
        change S.card = r - 1 at hfirst
        change S.card = r at hsecond
        omega)
    _ = Nat.choose r (r - 1) + Nat.choose r r := by
      rw [Fintype.card_finset_len, Fintype.card_finset_len]
      simp
    _ = r + 1 := by
      have hchoose : Nat.choose r (r - 1) = r := by
        obtain ⟨q, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
        simp
      rw [hchoose, Nat.choose_self]

/-- Injectivity into the two highest-weight layers gives the sharp finite
dimension inequality `2^s ≤ k+3` in the `r=k+2` branch. -/
theorem two_pow_rightDimension_le_k_add_three_of_add_two_branch
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hinjective : Function.Injective φ)
    (hrank : r = k + 2) :
    2 ^ s ≤ k + 3 := by
  have hrTwo : 2 ≤ r := by omega
  let intoHighWeight : FABL.F₂Cube s →
      {a : FABL.F₂Cube r // r - 2 < (FABL.f₂Support a).card} :=
    fun y ↦ ⟨φ y, by
      have hy := hweight y
      omega⟩
  have hinto : Function.Injective intoHighWeight := by
    intro y z hyz
    apply hinjective
    exact congrArg Subtype.val hyz
  have hcard := Fintype.card_le_of_injective intoHighWeight hinto
  rw [card_f₂Cube, card_highWeightCube hrTwo] at hcard
  omega

/-- The finite power inequality `2^s ≤ k+3` implies Carlet's printed
real-valued logarithmic dimension bound. -/
theorem rightDimension_cast_le_logb_two_k_add_three
    (k s : ℕ) (hpower : 2 ^ s ≤ k + 3) :
    (s : ℝ) ≤ Real.logb 2 ((k + 3 : ℕ) : ℝ) := by
  apply (Real.le_logb_iff_rpow_le
    (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (k + 3 : ℕ))).2
  rw [Real.rpow_natCast]
  exact_mod_cast hpower

/-- In the `r=k+2` branch, the frequency map is injective and both the
dimension and algebraic degree satisfy Carlet's real logarithmic bounds. -/
theorem maioranaMcFarland_optimal_injective_branch
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1))
    (hrank : r = k + 2) :
    Function.Injective φ ∧
      ((r + s : ℕ) : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) +
          Real.logb 2 ((k + 3 : ℕ) : ℝ) ∧
      (FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) : ℝ) ≤
        1 + Real.logb 2 ((k + 3 : ℕ) : ℝ) := by
  have hinjective :=
    injective_of_maioranaMcFarland_optimal_add_two_branch
      k φ g hs hweight hnonlinearity hrank
  have hpower :=
    two_pow_rightDimension_le_k_add_three_of_add_two_branch
      k φ hweight hinjective hrank
  have hlog := rightDimension_cast_le_logb_two_k_add_three k s hpower
  refine ⟨hinjective, ?_, ?_⟩
  · calc
      ((r + s : ℕ) : ℝ) =
          ((k + 2 : ℕ) : ℝ) + (s : ℝ) := by
        norm_num [hrank]
      _ ≤ ((k + 2 : ℕ) : ℝ) +
          Real.logb 2 ((k + 3 : ℕ) : ℝ) :=
        add_le_add (le_refl _) hlog
  · have hdegreeNat :=
      functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le φ g
    have hdegreeReal :
        (FABL.functionAlgebraicDegree
            (booleanMaioranaMcFarlandGeneral φ g) : ℝ) ≤
          ((s + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdegreeNat
    calc
      (FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) : ℝ) ≤
          ((s + 1 : ℕ) : ℝ) := hdegreeReal
      _ = (s : ℝ) + 1 := by norm_num
      _ ≤ 1 + Real.logb 2 ((k + 3 : ℕ) : ℝ) := by linarith

/-- Carlet's optimal-parameter classification for the general
Maiorana--McFarland construction under the strict image-weight hypothesis. -/
theorem maioranaMcFarland_optimal_classification
    (k : ℕ) (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s) (hr : 0 < r) (hs : 0 < s)
    (hweight : ∀ y, k < (FABL.f₂Support (φ y)).card)
    (hnonlinearity :
      nonlinearity (booleanMaioranaMcFarlandGeneral φ g) =
        2 ^ (r + s - 1) - 2 ^ (k + 1)) :
    (r = k + 1 ∧
      φ = (fun _ ↦ 1) ∧
      r + s ≤ k + 3 ∧
      (s = 1 ∨ ∃ hsTwo : s = 2, ∃ c a,
        g = twoVariableProductAt hsTwo + FABL.affineFunction c a)) ∨
    (r = k + 2 ∧
      Function.Injective φ ∧
      ((r + s : ℕ) : ℝ) ≤
        ((k + 2 : ℕ) : ℝ) +
          Real.logb 2 ((k + 3 : ℕ) : ℝ) ∧
      (FABL.functionAlgebraicDegree
          (booleanMaioranaMcFarlandGeneral φ g) : ℝ) ≤
        1 + Real.logb 2 ((k + 3 : ℕ) : ℝ)) := by
  rcases
      leftDimension_eq_succ_or_add_two_of_maioranaMcFarland_optimal
        k φ g hs hweight hnonlinearity with hrank | hrank
  · left
    exact ⟨hrank,
      maioranaMcFarland_optimal_constant_branch
        k φ g hr hs hweight hnonlinearity hrank⟩
  · right
    exact ⟨hrank,
      maioranaMcFarland_optimal_injective_branch
        k φ g hs hweight hnonlinearity hrank⟩

end CryptBoolean
