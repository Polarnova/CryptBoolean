/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenRankSevenPatterns
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenOrbitSums

/-!
# Canonical rank-seven pattern orbit sums

The complete affine-map character sums of the three projective self-dual
length-sixteen support patterns, reduced to explicit nonnegative normal forms.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The character product obtained by mapping a canonical rank-seven pattern
into an ambient binary cube. -/
noncomputable def rankSevenWeightSixteenPatternAffineProduct
    (σ : FABL.F₂Cube n → ℝ)
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n) : ℝ :=
  ∏ x ∈ rankSevenWeightSixteenPattern c,
    σ (sevenVariableAffinePoint d x)

/-- The complete affine-map character sum of a canonical rank-seven pattern. -/
noncomputable def rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ)
    (c : RankSevenWeightSixteenPatternClass) : ℝ :=
  ∑ d : SevenVariableAffineMapData n,
    rankSevenWeightSixteenPatternAffineProduct σ c d

/-- The product of a real function on a parametrized affine binary cube. -/
noncomputable def affineCubeProduct
    (σ : FABL.F₂Cube n → ℝ) {k : ℕ}
    (u : FABL.F₂Cube n) (v : Fin k → FABL.F₂Cube n) : ℝ :=
  ∏ x : FABL.F₂Cube k, σ (u + ∑ i, x i • v i)

/-- Affine-map data for a three-dimensional binary cube. -/
abbrev ThreeVariableAffineMapData (n : ℕ) :=
  FABL.F₂Cube n × (Fin 3 → FABL.F₂Cube n)

/-- The complete affine-map product sum of a three-dimensional cube. -/
noncomputable def threeVariableCompleteAffineMapProductSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ d : ThreeVariableAffineMapData n, affineCubeProduct σ d.1 d.2

/-- The `2E₈` complete affine-map character sum in square normal form. -/
noncomputable def twoE8CanonicalCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  threeVariableCompleteAffineMapProductSum σ ^ 2

/-- The `2E₈` square normal form is nonnegative. -/
theorem twoE8CanonicalCompleteAffineMapCharacterSum_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ twoE8CanonicalCompleteAffineMapCharacterSum σ := by
  unfold twoE8CanonicalCompleteAffineMapCharacterSum
  positivity

private def twoE8FirstDirections
    (d : SevenVariableAffineMapData n) : Fin 3 → FABL.F₂Cube n :=
  ![d.2 0, d.2 1, d.2 2]

private def twoE8SecondDirections
    (d : SevenVariableAffineMapData n) : Fin 3 → FABL.F₂Cube n :=
  ![d.2 3, d.2 4, d.2 5]

private def twoE8PatternPoint
    (p : Fin 2 × FABL.F₂Cube 3) : FABL.F₂Cube 7 :=
  if p.1 = 0 then
    ![p.2 0, p.2 1, p.2 2, 0, 0, 0, 0]
  else
    ![0, 0, 0, p.2 0, p.2 1, p.2 2, 1]

private theorem image_twoE8PatternPoint :
    Finset.univ.image twoE8PatternPoint =
      rankSevenWeightSixteenPattern .twoE8 := by
  decide

private theorem injective_twoE8PatternPoint :
    Function.Injective twoE8PatternPoint := by
  decide

private theorem sevenVariableAffinePoint_twoE8_first
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 3) :
    sevenVariableAffinePoint d (twoE8PatternPoint (0, x)) =
      d.1 + ∑ i, x i • twoE8FirstDirections d i := by
  simp [sevenVariableAffinePoint, twoE8PatternPoint,
    twoE8FirstDirections, Fin.sum_univ_succ]

private theorem sevenVariableAffinePoint_twoE8_second
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 3) :
    sevenVariableAffinePoint d (twoE8PatternPoint (1, x)) =
      (d.1 + d.2 6) + ∑ i, x i • twoE8SecondDirections d i := by
  simp [sevenVariableAffinePoint, twoE8PatternPoint,
    twoE8SecondDirections, Fin.sum_univ_succ]
  abel

private theorem rankSevenWeightSixteenPatternAffineProduct_twoE8
    (σ : FABL.F₂Cube n → ℝ) (d : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternAffineProduct σ .twoE8 d =
      affineCubeProduct σ d.1 (twoE8FirstDirections d) *
        affineCubeProduct σ (d.1 + d.2 6) (twoE8SecondDirections d) := by
  unfold rankSevenWeightSixteenPatternAffineProduct
  rw [← image_twoE8PatternPoint,
    Finset.prod_image injective_twoE8PatternPoint.injOn]
  rw [Fintype.prod_prod_type]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.prod_insert, Finset.mem_singleton, Fin.zero_ne_one,
    not_false_eq_true, Finset.prod_singleton]
  simp_rw [sevenVariableAffinePoint_twoE8_first,
    sevenVariableAffinePoint_twoE8_second]
  rfl

private def twoE8AffineDataEquiv (n : ℕ) :
    SevenVariableAffineMapData n ≃
      ThreeVariableAffineMapData n × ThreeVariableAffineMapData n where
  toFun d :=
    ((d.1, twoE8FirstDirections d),
      (d.1 + d.2 6, twoE8SecondDirections d))
  invFun p :=
    (p.1.1,
      ![p.1.2 0, p.1.2 1, p.1.2 2,
        p.2.2 0, p.2.2 1, p.2.2 2, p.1.1 + p.2.1])
  left_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [twoE8FirstDirections, twoE8SecondDirections,
          ← add_assoc, ZModModule.add_self]
  right_inv := by
    rintro ⟨⟨u, v⟩, ⟨w, z⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp [twoE8FirstDirections]
    · apply Prod.ext
      · simp [← add_assoc, ZModModule.add_self]
      · funext i
        fin_cases i <;> simp [twoE8SecondDirections]

/-- The canonical `2E₈` pattern sum is the square of the complete
three-flat affine-map product sum. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_twoE8
    (σ : FABL.F₂Cube n → ℝ) :
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .twoE8 =
      twoE8CanonicalCompleteAffineMapCharacterSum σ := by
  unfold rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
  rw [Fintype.sum_equiv (twoE8AffineDataEquiv n)
    (fun d ↦ rankSevenWeightSixteenPatternAffineProduct σ .twoE8 d)
    (fun p ↦ affineCubeProduct σ p.1.1 p.1.2 *
      affineCubeProduct σ p.2.1 p.2.2)]
  · rw [Fintype.sum_prod_type]
    unfold twoE8CanonicalCompleteAffineMapCharacterSum
    unfold threeVariableCompleteAffineMapProductSum
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  · intro d
    exact rankSevenWeightSixteenPatternAffineProduct_twoE8 σ d

/-- The complete affine-map character sum of the canonical `2E₈` pattern
is nonnegative. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_twoE8_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .twoE8 := by
  rw [rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_twoE8]
  exact twoE8CanonicalCompleteAffineMapCharacterSum_nonneg σ

private def d16DirectionSum
    (d : SevenVariableAffineMapData n) : FABL.F₂Cube n :=
  ∑ i, d.2 i

private def d16FirstSixDirections
    (d : SevenVariableAffineMapData n) : Fin 6 → FABL.F₂Cube n :=
  ![d.2 0, d.2 1, d.2 2, d.2 3, d.2 4, d.2 5]

private def d16AffineBasisPoint (i : Fin 8) : FABL.F₂Cube 7 :=
  Fin.cases 0 (fun j ↦ Pi.single j 1) i

private def d16PatternPoint
    (p : Fin 2 × Fin 8) : FABL.F₂Cube 7 :=
  if p.1 = 0 then d16AffineBasisPoint p.2
  else 1 + d16AffineBasisPoint p.2

private theorem image_d16PatternPoint :
    Finset.univ.image d16PatternPoint =
      rankSevenWeightSixteenPattern .d16Plus := by
  decide

private theorem injective_d16PatternPoint :
    Function.Injective d16PatternPoint := by
  decide

private theorem sevenVariableAffinePoint_add_one
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 7) :
    sevenVariableAffinePoint d (1 + x) =
      sevenVariableAffinePoint d x + d16DirectionSum d := by
  simp only [sevenVariableAffinePoint, d16DirectionSum, Pi.add_apply,
    Pi.one_apply, add_smul, one_smul, Finset.sum_add_distrib]
  abel

private theorem sevenVariableAffinePoint_d16AffineBasisPoint
    (d : SevenVariableAffineMapData n) (i : Fin 8) :
    sevenVariableAffinePoint d (d16AffineBasisPoint i) =
      Fin.cases d.1 (fun j ↦ d.1 + d.2 j) i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [sevenVariableAffinePoint, d16AffineBasisPoint]
  · simp [sevenVariableAffinePoint, d16AffineBasisPoint]

private theorem orbitSignDerivative_add_right_self
    (σ : FABL.F₂Cube n → ℝ) (a x : FABL.F₂Cube n) :
    orbitSignDerivative σ a (x + a) = orbitSignDerivative σ a x := by
  unfold orbitSignDerivative
  rw [add_assoc, ZModModule.add_self, add_zero]
  ring

private theorem rankSevenWeightSixteenPatternAffineProduct_d16
    (σ : FABL.F₂Cube n → ℝ) (d : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternAffineProduct σ .d16Plus d =
      orbitSignDerivative σ (d16DirectionSum d) d.1 *
        ∏ i, orbitSignDerivative σ (d16DirectionSum d) (d.1 + d.2 i) := by
  unfold rankSevenWeightSixteenPatternAffineProduct
  rw [← image_d16PatternPoint,
    Finset.prod_image injective_d16PatternPoint.injOn]
  rw [Fintype.prod_prod_type]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.prod_insert, Finset.mem_singleton, Fin.zero_ne_one,
    not_false_eq_true, Finset.prod_singleton]
  simp only [d16PatternPoint, show (1 : Fin 2) ≠ 0 by decide,
    ↓reduceIte]
  simp_rw [sevenVariableAffinePoint_add_one,
    sevenVariableAffinePoint_d16AffineBasisPoint]
  rw [show
    (∏ x : Fin 8, σ (Fin.cases d.1 (fun j ↦ d.1 + d.2 j) x)) =
        σ d.1 * ∏ i : Fin 7, σ (d.1 + d.2 i) by
      rw [Fin.prod_univ_succ]
      rfl]
  rw [show
    (∏ x : Fin 8,
        σ (Fin.cases d.1 (fun j ↦ d.1 + d.2 j) x +
          d16DirectionSum d)) =
        σ (d.1 + d16DirectionSum d) *
          ∏ i : Fin 7, σ (d.1 + d.2 i + d16DirectionSum d) by
      rw [Fin.prod_univ_succ]
      rfl]
  unfold orbitSignDerivative
  simp_rw [show ∀ i : Fin 7,
      d.1 + d.2 i + d16DirectionSum d =
        d.1 + d16DirectionSum d + d.2 i by
    intro i
    abel]
  rw [Finset.prod_mul_distrib]
  ring

private abbrev D16ReducedAffineMapData (n : ℕ) :=
  FABL.F₂Cube n × FABL.F₂Cube n × (Fin 6 → FABL.F₂Cube n)

private def d16ReducedAffineMapDataEquiv (n : ℕ) :
    SevenVariableAffineMapData n ≃ D16ReducedAffineMapData n where
  toFun d := (d16DirectionSum d, d.1, d16FirstSixDirections d)
  invFun p :=
    (p.2.1,
      ![p.2.2 0, p.2.2 1, p.2.2 2, p.2.2 3, p.2.2 4, p.2.2 5,
        p.1 - ∑ i, p.2.2 i])
  left_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [d16DirectionSum, d16FirstSixDirections, Fin.sum_univ_succ]
  right_inv := by
    rintro ⟨s, u, w⟩
    apply Prod.ext
    · simp [d16DirectionSum, Fin.sum_univ_succ]
      abel
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp [d16FirstSixDirections]

private noncomputable def d16ReducedFiberCharacterSum
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n) : ℝ :=
  ∑ u : FABL.F₂Cube n,
    ∑ w : Fin 6 → FABL.F₂Cube n,
    orbitSignDerivative σ s u *
      (∏ i, orbitSignDerivative σ s (u + w i)) *
        orbitSignDerivative σ s (u + ∑ i, w i)

private noncomputable def d16ReducedCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ s, d16ReducedFiberCharacterSum σ s

private theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16_reduced
    (σ : FABL.F₂Cube n → ℝ) :
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .d16Plus =
      d16ReducedCompleteAffineMapCharacterSum σ := by
  unfold rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
  rw [Fintype.sum_equiv (d16ReducedAffineMapDataEquiv n)
    (fun d ↦ rankSevenWeightSixteenPatternAffineProduct σ .d16Plus d)
    (fun p ↦
      orbitSignDerivative σ p.1 p.2.1 *
        (∏ i, orbitSignDerivative σ p.1 (p.2.1 + p.2.2 i)) *
          orbitSignDerivative σ p.1 (p.2.1 + ∑ i, p.2.2 i))]
  · simp only [Fintype.sum_prod_type]
    unfold d16ReducedCompleteAffineMapCharacterSum
      d16ReducedFiberCharacterSum
    rfl
  · rintro ⟨u, v⟩
    rw [rankSevenWeightSixteenPatternAffineProduct_d16]
    simp only [d16ReducedAffineMapDataEquiv, d16FirstSixDirections,
      d16DirectionSum]
    rw [Fin.prod_univ_seven, Fin.prod_univ_six, Fin.sum_univ_six]
    have hlast :
        orbitSignDerivative σ (∑ i, v i)
            (u + v 6) =
          orbitSignDerivative σ (∑ i, v i)
            (u + (v 0 + v 1 + v 2 + v 3 + v 4 + v 5)) := by
      have hv6 : v 6 = (∑ i, v i) +
          (v 0 + v 1 + v 2 + v 3 + v 4 + v 5) := by
        rw [Fin.sum_univ_seven]
        let t := v 0 + v 1 + v 2 + v 3 + v 4 + v 5
        change v 6 = (t + v 6) + t
        calc
          v 6 = (t + t) + v 6 := by
            rw [ZModModule.add_self, zero_add]
          _ = (t + v 6) + t := by abel
      rw [hv6]
      convert orbitSignDerivative_add_right_self σ (∑ i, v i)
        (u + (v 0 + v 1 + v 2 + v 3 + v 4 + v 5)) using 1
      abel
    rw [hlast]
    ac_rfl

private def finThreeArrowEquiv (G : Type*) :
    (Fin 3 → G) ≃ G × G × G where
  toFun q := (q 0, q 1, q 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro q
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨x, y, z⟩
    rfl

private def d16FourfoldProduct
    (σ : FABL.F₂Cube n → ℝ)
    (s b : FABL.F₂Cube n) (q : Fin 3 → FABL.F₂Cube n) : ℝ :=
  orbitSignDerivative σ s (q 2) *
    orbitSignDerivative σ s (q 0 + q 2) *
      (orbitSignDerivative σ s (q 1) *
        orbitSignDerivative σ s (b + q 0 + q 1))

private theorem weightSixteenFourfoldConvolution_eq_sum_d16FourfoldProduct
    (σ : FABL.F₂Cube n → ℝ) (s b : FABL.F₂Cube n) :
    weightSixteenFourfoldConvolution σ s b =
      ∑ q : Fin 3 → FABL.F₂Cube n, d16FourfoldProduct σ s b q := by
  change
    rawConvolution
        (rawConvolution (orbitSignDerivative σ s) (orbitSignDerivative σ s))
        (rawConvolution (orbitSignDerivative σ s) (orbitSignDerivative σ s)) b = _
  simp only [rawConvolution]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_equiv (finThreeArrowEquiv (FABL.F₂Cube n))
    (fun q ↦ d16FourfoldProduct σ s b q)
    (fun p ↦
      orbitSignDerivative σ s p.2.2 *
        orbitSignDerivative σ s (p.1 + p.2.2) *
          (orbitSignDerivative σ s p.2.1 *
            orbitSignDerivative σ s (b + p.1 + p.2.1)))]
  · simp only [Fintype.sum_prod_type]
  · intro q
    rfl

private abbrev D16ReducedFiberData (n : ℕ) :=
  FABL.F₂Cube n × (Fin 6 → FABL.F₂Cube n)

private abbrev D16ConvolutionFiberData (n : ℕ) :=
  FABL.F₂Cube n ×
    ((Fin 3 → FABL.F₂Cube n) × (Fin 3 → FABL.F₂Cube n))

private def d16ReducedConvolutionFiberEquiv (n : ℕ) :
    D16ReducedFiberData n ≃ D16ConvolutionFiberData n where
  toFun p :=
    (p.2 0 + p.2 1 + p.2 2,
      (![p.2 0, p.1 + p.2 1, p.1],
        ![p.2 3 + p.2 4, p.1 + p.2 5, p.1 + p.2 3]))
  invFun p :=
    (p.2.1 2,
      ![p.2.1 0,
        p.2.1 1 - p.2.1 2,
        p.1 - p.2.1 0 - (p.2.1 1 - p.2.1 2),
        p.2.2 2 - p.2.1 2,
        p.2.2 0 - (p.2.2 2 - p.2.1 2),
        p.2.2 1 - p.2.1 2])
  left_inv := by
    rintro ⟨u, w⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp
      all_goals abel
  right_inv := by
    rintro ⟨b, q, r⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp
      · funext i
        fin_cases i <;> simp

private noncomputable def d16ReducedFiberIntegrand
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n)
    (p : D16ReducedFiberData n) : ℝ :=
  orbitSignDerivative σ s p.1 *
    (∏ i, orbitSignDerivative σ s (p.1 + p.2 i)) *
      orbitSignDerivative σ s (p.1 + ∑ i, p.2 i)

private def d16ConvolutionFiberIntegrand
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n)
    (p : D16ConvolutionFiberData n) : ℝ :=
  d16FourfoldProduct σ s p.1 p.2.1 *
    d16FourfoldProduct σ s p.1 p.2.2

private theorem d16ReducedConvolutionFiberEquiv_integrand
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n)
    (p : D16ReducedFiberData n) :
    d16ReducedFiberIntegrand σ s p =
      d16ConvolutionFiberIntegrand σ s
        (d16ReducedConvolutionFiberEquiv n p) := by
  rcases p with ⟨u, w⟩
  unfold d16ReducedFiberIntegrand d16ConvolutionFiberIntegrand
  rw [Fin.prod_univ_six, Fin.sum_univ_six]
  have hq0 : w 0 + u = u + w 0 := add_comm _ _
  have hq3 : w 0 + w 1 + w 2 + w 0 + (u + w 1) = u + w 2 := by
    calc
      w 0 + w 1 + w 2 + w 0 + (u + w 1) =
          (w 0 + w 0) + (w 1 + w 1) + (u + w 2) := by abel
      _ = u + w 2 := by simp only [ZModModule.add_self, zero_add]
  have hr1 : w 3 + w 4 + (u + w 3) = u + w 4 := by
    calc
      w 3 + w 4 + (u + w 3) = (w 3 + w 3) + (u + w 4) := by abel
      _ = u + w 4 := by simp only [ZModModule.add_self, zero_add]
  have hr3 :
      w 0 + w 1 + w 2 + (w 3 + w 4) + (u + w 5) =
        u + (w 0 + w 1 + w 2 + w 3 + w 4 + w 5) := by abel
  change
    orbitSignDerivative σ s u *
        (orbitSignDerivative σ s (u + w 0) *
          orbitSignDerivative σ s (u + w 1) *
          orbitSignDerivative σ s (u + w 2) *
          orbitSignDerivative σ s (u + w 3) *
          orbitSignDerivative σ s (u + w 4) *
          orbitSignDerivative σ s (u + w 5)) *
        orbitSignDerivative σ s
          (u + (w 0 + w 1 + w 2 + w 3 + w 4 + w 5)) =
      d16FourfoldProduct σ s (w 0 + w 1 + w 2)
          ![w 0, u + w 1, u] *
        d16FourfoldProduct σ s (w 0 + w 1 + w 2)
          ![w 3 + w 4, u + w 5, u + w 3]
  simp only [d16FourfoldProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [hq0, hq3, hr1, hr3]
  ring

private noncomputable def d16ConvolutionPairCharacterSum
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n) : ℝ :=
  ∑ b : FABL.F₂Cube n,
    ∑ q : Fin 3 → FABL.F₂Cube n,
      ∑ r : Fin 3 → FABL.F₂Cube n,
    d16FourfoldProduct σ s b q * d16FourfoldProduct σ s b r

private theorem d16ReducedConvolutionFiberSum_eq
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n) :
    (∑ p : D16ReducedFiberData n, d16ReducedFiberIntegrand σ s p) =
      ∑ p : D16ConvolutionFiberData n,
        d16ConvolutionFiberIntegrand σ s p := by
  calc
    (∑ p : D16ReducedFiberData n, d16ReducedFiberIntegrand σ s p) =
        ∑ p : D16ReducedFiberData n,
          d16ConvolutionFiberIntegrand σ s
            (d16ReducedConvolutionFiberEquiv n p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact d16ReducedConvolutionFiberEquiv_integrand σ s p
    _ = ∑ p : D16ConvolutionFiberData n,
          d16ConvolutionFiberIntegrand σ s p :=
      (d16ReducedConvolutionFiberEquiv n).sum_comp _

private theorem d16ReducedFiberCharacterSum_eq_convolutionPair
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n) :
    d16ReducedFiberCharacterSum σ s =
      d16ConvolutionPairCharacterSum σ s := by
  unfold d16ReducedFiberCharacterSum d16ConvolutionPairCharacterSum
  calc
    (∑ u : FABL.F₂Cube n,
        ∑ w : Fin 6 → FABL.F₂Cube n,
        orbitSignDerivative σ s u *
          (∏ i, orbitSignDerivative σ s (u + w i)) *
            orbitSignDerivative σ s (u + ∑ i, w i)) =
        ∑ p : D16ReducedFiberData n,
          d16ReducedFiberIntegrand σ s p := by
      rw [Fintype.sum_prod_type]
      unfold d16ReducedFiberIntegrand
      rfl
    _ = ∑ p : D16ConvolutionFiberData n,
          d16ConvolutionFiberIntegrand σ s p :=
      d16ReducedConvolutionFiberSum_eq σ s
    _ = ∑ b : FABL.F₂Cube n,
          ∑ q : Fin 3 → FABL.F₂Cube n,
            ∑ r : Fin 3 → FABL.F₂Cube n,
          d16FourfoldProduct σ s b q *
            d16FourfoldProduct σ s b r := by
      unfold d16ConvolutionFiberIntegrand
      simp only [Fintype.sum_prod_type]

private theorem d16ConvolutionPairCharacterSum_eq_squareSum
    (σ : FABL.F₂Cube n → ℝ) (s : FABL.F₂Cube n) :
    d16ConvolutionPairCharacterSum σ s =
      ∑ b, weightSixteenFourfoldConvolution σ s b ^ 2 := by
  unfold d16ConvolutionPairCharacterSum
  apply Finset.sum_congr rfl
  intro b _
  rw [weightSixteenFourfoldConvolution_eq_sum_d16FourfoldProduct]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]

private theorem d16ReducedCompleteAffineMapCharacterSum_eq_canonical
    (σ : FABL.F₂Cube n → ℝ) :
    d16ReducedCompleteAffineMapCharacterSum σ =
      d16CanonicalCompleteAffineMapCharacterSum σ := by
  unfold d16ReducedCompleteAffineMapCharacterSum
  unfold d16CanonicalCompleteAffineMapCharacterSum
  apply Finset.sum_congr rfl
  intro s _
  rw [d16ReducedFiberCharacterSum_eq_convolutionPair,
    d16ConvolutionPairCharacterSum_eq_squareSum]

/-- The complete affine-map character sum of the canonical `D₁₆⁺` pattern
is the fourfold-convolution square normal form. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16Plus
    (σ : FABL.F₂Cube n → ℝ) :
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .d16Plus =
      d16CanonicalCompleteAffineMapCharacterSum σ := by
  rw [rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16_reduced,
    d16ReducedCompleteAffineMapCharacterSum_eq_canonical]

/-- The complete affine-map character sum of the canonical `D₁₆⁺` pattern
is nonnegative. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16Plus_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .d16Plus := by
  rw [rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16Plus]
  exact d16CanonicalCompleteAffineMapCharacterSum_nonneg σ

private def f16AffineBasisA : Fin 4 → FABL.F₂Cube 7 :=
  ![f₂CubeOfNat 7 0, f₂CubeOfNat 7 2,
    f₂CubeOfNat 7 4, f₂CubeOfNat 7 17]

private def f16AffineBasisB : Fin 4 → FABL.F₂Cube 7 :=
  ![f₂CubeOfNat 7 8, f₂CubeOfNat 7 32,
    f₂CubeOfNat 7 64, f₂CubeOfNat 7 105]

private def f16PatternPoint
    (p : Fin 4 × Fin 4) : FABL.F₂Cube 7 :=
  ![f16AffineBasisA p.1,
    f16AffineBasisB p.1,
    f16AffineBasisA p.1 + ∑ j, f16AffineBasisB j,
    f16AffineBasisB p.1 + ∑ j, f16AffineBasisA j] p.2

private theorem image_f16PatternPoint :
    Finset.univ.image f16PatternPoint =
      rankSevenWeightSixteenPattern .f16 := by
  decide

private theorem injective_f16PatternPoint :
    Function.Injective f16PatternPoint := by
  decide

private def f16AffineBasisCoordinates
    (d : SevenVariableAffineMapData n) :
    (Fin 4 → FABL.F₂Cube n) × (Fin 4 → FABL.F₂Cube n) :=
  ((fun i ↦ sevenVariableAffinePoint d (f16AffineBasisA i)),
    fun i ↦ sevenVariableAffinePoint d (f16AffineBasisB i))

private theorem sevenVariableAffinePoint_add_sum_four
    (d : SevenVariableAffineMapData n) (x : FABL.F₂Cube 7)
    (y : Fin 4 → FABL.F₂Cube 7) :
    sevenVariableAffinePoint d (x + ∑ i, y i) =
      sevenVariableAffinePoint d x +
        ∑ i, sevenVariableAffinePoint d (y i) := by
  let L := Fintype.linearCombination FABL.𝔽₂ d.2
  change d.1 + L (x + ∑ i, y i) =
    (d.1 + L x) + ∑ i, (d.1 + L (y i))
  rw [map_add, map_sum]
  simp_rw [Fin.sum_univ_four]
  have hfour : d.1 + d.1 + d.1 + d.1 = 0 := by
    calc
      d.1 + d.1 + d.1 + d.1 =
          (d.1 + d.1) + (d.1 + d.1) := by abel
      _ = 0 := by
        simp only [ZModModule.add_self]
  calc
    d.1 + (L x + (L (y 0) + L (y 1) + L (y 2) + L (y 3))) =
        (d.1 + d.1 + d.1 + d.1) +
          (d.1 + L x + L (y 0) + L (y 1) + L (y 2) + L (y 3)) := by
      rw [hfour, zero_add]
      abel
    _ = (d.1 + L x) +
          ((d.1 + L (y 0)) + (d.1 + L (y 1)) +
            (d.1 + L (y 2)) + (d.1 + L (y 3))) := by
      abel

private theorem sevenVariableAffinePoint_f16_aCycle
    (d : SevenVariableAffineMapData n) (i : Fin 4) :
    sevenVariableAffinePoint d
        (f16AffineBasisA i + ∑ j, f16AffineBasisB j) =
      (f16AffineBasisCoordinates d).1 i +
        ∑ j, (f16AffineBasisCoordinates d).2 j := by
  simpa only [f16AffineBasisCoordinates] using
    sevenVariableAffinePoint_add_sum_four d (f16AffineBasisA i)
      f16AffineBasisB

private theorem sevenVariableAffinePoint_f16_bCycle
    (d : SevenVariableAffineMapData n) (i : Fin 4) :
    sevenVariableAffinePoint d
        (f16AffineBasisB i + ∑ j, f16AffineBasisA j) =
      (f16AffineBasisCoordinates d).2 i +
        ∑ j, (f16AffineBasisCoordinates d).1 j := by
  simpa only [f16AffineBasisCoordinates] using
    sevenVariableAffinePoint_add_sum_four d (f16AffineBasisB i)
      f16AffineBasisA

private theorem rankSevenWeightSixteenPatternAffineProduct_f16
    (σ : FABL.F₂Cube n → ℝ) (d : SevenVariableAffineMapData n) :
    rankSevenWeightSixteenPatternAffineProduct σ .f16 d =
      ∏ i,
        σ ((f16AffineBasisCoordinates d).1 i) *
          σ ((f16AffineBasisCoordinates d).2 i) *
          σ ((f16AffineBasisCoordinates d).1 i +
            ∑ j, (f16AffineBasisCoordinates d).2 j) *
          σ ((f16AffineBasisCoordinates d).2 i +
            ∑ j, (f16AffineBasisCoordinates d).1 j) := by
  unfold rankSevenWeightSixteenPatternAffineProduct
  rw [← image_f16PatternPoint,
    Finset.prod_image injective_f16PatternPoint.injOn]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.prod_univ_four]
  change
    σ (sevenVariableAffinePoint d (f16AffineBasisA i)) *
          σ (sevenVariableAffinePoint d (f16AffineBasisB i)) *
          σ (sevenVariableAffinePoint d
            (f16AffineBasisA i + ∑ j, f16AffineBasisB j)) *
          σ (sevenVariableAffinePoint d
            (f16AffineBasisB i + ∑ j, f16AffineBasisA j)) = _
  rw [sevenVariableAffinePoint_f16_aCycle,
    sevenVariableAffinePoint_f16_bCycle]
  rfl

private def f16AffineDataOfBasisCoordinates
    (p : (Fin 4 → FABL.F₂Cube n) × (Fin 4 → FABL.F₂Cube n)) :
    SevenVariableAffineMapData n :=
  let u := p.1 0
  let v₁ := p.1 1 - u
  let v₂ := p.1 2 - u
  let v₃ := p.2 0 - u
  let v₅ := p.2 1 - u
  let v₆ := p.2 2 - u
  let v₀ := p.2 3 - u - v₃ - v₅ - v₆
  let v₄ := p.1 3 - u - v₀
  (u, ![v₀, v₁, v₂, v₃, v₄, v₅, v₆])

private def f16AffineBasisCoordinatesEquiv (n : ℕ) :
    SevenVariableAffineMapData n ≃
      ((Fin 4 → FABL.F₂Cube n) × (Fin 4 → FABL.F₂Cube n)) where
  toFun := f16AffineBasisCoordinates
  invFun := f16AffineDataOfBasisCoordinates
  left_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · simp [f16AffineDataOfBasisCoordinates, f16AffineBasisCoordinates,
        f16AffineBasisA, sevenVariableAffinePoint, f₂CubeOfNat]
    · funext i
      fin_cases i <;>
        simp [f16AffineDataOfBasisCoordinates, f16AffineBasisCoordinates,
          f16AffineBasisA, f16AffineBasisB, sevenVariableAffinePoint,
          f₂CubeOfNat, Fin.sum_univ_succ, Nat.testBit,
          ZModModule.add_self]
      all_goals abel
  right_inv := by
    rintro ⟨U, V⟩
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [f16AffineDataOfBasisCoordinates, f16AffineBasisCoordinates,
          f16AffineBasisA, sevenVariableAffinePoint, f₂CubeOfNat,
          Fin.sum_univ_succ, Nat.testBit, ZModModule.add_self]
    · funext i
      fin_cases i <;>
        simp [f16AffineDataOfBasisCoordinates, f16AffineBasisCoordinates,
          f16AffineBasisB, sevenVariableAffinePoint, f₂CubeOfNat,
          Fin.sum_univ_succ, Nat.testBit, ZModModule.add_self]
      all_goals abel

private noncomputable def f16FourCycleCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ U : Fin 4 → FABL.F₂Cube n,
    ∑ V : Fin 4 → FABL.F₂Cube n,
      ∏ i,
        σ (U i) * σ (V i) * σ (U i + ∑ j, V j) *
          σ (V i + ∑ j, U j)

private theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16_cycle
    (σ : FABL.F₂Cube n → ℝ) :
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .f16 =
      f16FourCycleCompleteAffineMapCharacterSum σ := by
  unfold rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum
  rw [Fintype.sum_equiv (f16AffineBasisCoordinatesEquiv n)
    (fun d ↦ rankSevenWeightSixteenPatternAffineProduct σ .f16 d)
    (fun p ↦ ∏ i,
      σ (p.1 i) * σ (p.2 i) * σ (p.1 i + ∑ j, p.2 j) *
        σ (p.2 i + ∑ j, p.1 j))]
  · simp only [Fintype.sum_prod_type]
    rfl
  · exact rankSevenWeightSixteenPatternAffineProduct_f16 σ

private abbrev F16CycleData (n : ℕ) :=
  (Fin 4 → FABL.F₂Cube n) × (Fin 4 → FABL.F₂Cube n)

private abbrev F16ConvolutionData (n : ℕ) :=
  FABL.F₂Cube n × FABL.F₂Cube n ×
    ((Fin 3 → FABL.F₂Cube n) × (Fin 3 → FABL.F₂Cube n))

private def f16CycleConvolutionDataEquiv (n : ℕ) :
    F16CycleData n ≃ F16ConvolutionData n where
  toFun p :=
    (∑ i, p.2 i, ∑ i, p.1 i,
      (![p.1 0 + p.1 1, p.1 2, p.1 0],
        ![p.2 0 + p.2 1, p.2 2, p.2 0]))
  invFun p :=
    (![p.2.2.1 2, p.2.2.1 0 - p.2.2.1 2,
        p.2.2.1 1, p.2.1 - p.2.2.1 0 - p.2.2.1 1],
      ![p.2.2.2 2, p.2.2.2 0 - p.2.2.2 2,
        p.2.2.2 1, p.1 - p.2.2.2 0 - p.2.2.2 1])
  left_inv := by
    rintro ⟨U, V⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [Fin.sum_univ_four]
    all_goals abel
  right_inv := by
    rintro ⟨a, b, q, r⟩
    apply Prod.ext
    · simp [Fin.sum_univ_four]
    · apply Prod.ext
      · simp [Fin.sum_univ_four]
      · apply Prod.ext <;> funext i <;> fin_cases i <;>
          simp

private theorem f16CycleConvolutionDataEquiv_apply
    (U V : Fin 4 → FABL.F₂Cube n) :
    f16CycleConvolutionDataEquiv n (U, V) =
      (∑ i, V i, ∑ i, U i,
        (![U 0 + U 1, U 2, U 0],
          ![V 0 + V 1, V 2, V 0])) :=
  rfl

private noncomputable def f16CycleIntegrand
    (σ : FABL.F₂Cube n → ℝ) (p : F16CycleData n) : ℝ :=
  ∏ i, σ (p.1 i) * σ (p.2 i) *
    σ (p.1 i + ∑ j, p.2 j) * σ (p.2 i + ∑ j, p.1 j)

private def f16ConvolutionIntegrand
    (σ : FABL.F₂Cube n → ℝ) (p : F16ConvolutionData n) : ℝ :=
  d16FourfoldProduct σ p.1 p.2.1 p.2.2.1 *
    d16FourfoldProduct σ p.2.1 p.1 p.2.2.2

private theorem f16CycleConvolutionDataEquiv_integrand
    (σ : FABL.F₂Cube n → ℝ)
    (p : F16CycleData n) :
    f16CycleIntegrand σ p =
      f16ConvolutionIntegrand σ (f16CycleConvolutionDataEquiv n p) := by
  rcases p with ⟨U, V⟩
  unfold f16CycleIntegrand f16ConvolutionIntegrand
  rw [Fin.prod_univ_four]
  simp_rw [Fin.sum_univ_four]
  have hU₁ : U 0 + U 1 + U 0 = U 1 := by
    calc
      U 0 + U 1 + U 0 = (U 0 + U 0) + U 1 := by abel
      _ = U 1 := by simp only [ZModModule.add_self, zero_add]
  have hU₃ :
      U 0 + U 1 + U 2 + U 3 + (U 0 + U 1) + U 2 = U 3 := by
    calc
      U 0 + U 1 + U 2 + U 3 + (U 0 + U 1) + U 2 =
          (U 0 + U 0) + (U 1 + U 1) + (U 2 + U 2) + U 3 := by
        abel
      _ = U 3 := by simp only [ZModModule.add_self, zero_add]
  have hV₁ : V 0 + V 1 + V 0 = V 1 := by
    calc
      V 0 + V 1 + V 0 = (V 0 + V 0) + V 1 := by abel
      _ = V 1 := by simp only [ZModModule.add_self, zero_add]
  have hV₃ :
      V 0 + V 1 + V 2 + V 3 + (V 0 + V 1) + V 2 = V 3 := by
    calc
      V 0 + V 1 + V 2 + V 3 + (V 0 + V 1) + V 2 =
          (V 0 + V 0) + (V 1 + V 1) + (V 2 + V 2) + V 3 := by
        abel
      _ = V 3 := by simp only [ZModModule.add_self, zero_add]
  rw [f16CycleConvolutionDataEquiv_apply]
  simp only [d16FourfoldProduct, orbitSignDerivative, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  rw [hU₁, hU₃, hV₁, hV₃]
  ring

private theorem f16CycleConvolutionSum_eq
    (σ : FABL.F₂Cube n → ℝ) :
    (∑ p : F16CycleData n, f16CycleIntegrand σ p) =
      ∑ p : F16ConvolutionData n, f16ConvolutionIntegrand σ p := by
  calc
    (∑ p : F16CycleData n, f16CycleIntegrand σ p) =
        ∑ p : F16CycleData n,
          f16ConvolutionIntegrand σ
            (f16CycleConvolutionDataEquiv n p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact f16CycleConvolutionDataEquiv_integrand σ p
    _ = ∑ p : F16ConvolutionData n, f16ConvolutionIntegrand σ p :=
      (f16CycleConvolutionDataEquiv n).sum_comp _

private noncomputable def f16ConvolutionPairCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ a : FABL.F₂Cube n,
    ∑ b : FABL.F₂Cube n,
      ∑ q : Fin 3 → FABL.F₂Cube n,
        ∑ r : Fin 3 → FABL.F₂Cube n,
          d16FourfoldProduct σ a b q * d16FourfoldProduct σ b a r

private theorem f16FourCycleCompleteAffineMapCharacterSum_eq_convolutionPair
    (σ : FABL.F₂Cube n → ℝ) :
    f16FourCycleCompleteAffineMapCharacterSum σ =
      f16ConvolutionPairCharacterSum σ := by
  unfold f16FourCycleCompleteAffineMapCharacterSum
    f16ConvolutionPairCharacterSum
  calc
    (∑ U : Fin 4 → FABL.F₂Cube n,
        ∑ V : Fin 4 → FABL.F₂Cube n,
          ∏ i, σ (U i) * σ (V i) * σ (U i + ∑ j, V j) *
            σ (V i + ∑ j, U j)) =
        ∑ p : F16CycleData n, f16CycleIntegrand σ p := by
      rw [Fintype.sum_prod_type]
      unfold f16CycleIntegrand
      rfl
    _ = ∑ p : F16ConvolutionData n,
          f16ConvolutionIntegrand σ p :=
      f16CycleConvolutionSum_eq σ
    _ = ∑ a : FABL.F₂Cube n,
          ∑ b : FABL.F₂Cube n,
            ∑ q : Fin 3 → FABL.F₂Cube n,
              ∑ r : Fin 3 → FABL.F₂Cube n,
                d16FourfoldProduct σ a b q *
                  d16FourfoldProduct σ b a r := by
      unfold f16ConvolutionIntegrand
      simp only [Fintype.sum_prod_type]

private theorem f16WeightProduct_eq_convolutionPair
    (σ : FABL.F₂Cube n → ℝ) (a b : FABL.F₂Cube n) :
    weightSixteenFourfoldConvolution σ a b *
        weightSixteenFourfoldConvolution σ b a =
      ∑ q : Fin 3 → FABL.F₂Cube n,
        ∑ r : Fin 3 → FABL.F₂Cube n,
          d16FourfoldProduct σ a b q * d16FourfoldProduct σ b a r := by
  rw [weightSixteenFourfoldConvolution_eq_sum_d16FourfoldProduct,
    weightSixteenFourfoldConvolution_eq_sum_d16FourfoldProduct,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]

private theorem f16ConvolutionPairCharacterSum_eq_canonical
    (σ : FABL.F₂Cube n → ℝ) :
    f16ConvolutionPairCharacterSum σ =
      f16CanonicalCompleteAffineMapCharacterSum σ := by
  unfold f16ConvolutionPairCharacterSum
    f16CanonicalCompleteAffineMapCharacterSum
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (f16WeightProduct_eq_convolutionPair σ a b).symm

private theorem f16FourCycleCompleteAffineMapCharacterSum_eq_canonical
    (σ : FABL.F₂Cube n → ℝ) :
    f16FourCycleCompleteAffineMapCharacterSum σ =
      f16CanonicalCompleteAffineMapCharacterSum σ := by
  rw [f16FourCycleCompleteAffineMapCharacterSum_eq_convolutionPair,
    f16ConvolutionPairCharacterSum_eq_canonical]

/-- The complete affine-map character sum of the canonical `F₁₆` pattern
is its four-cycle convolution normal form. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16
    (σ : FABL.F₂Cube n → ℝ) :
    rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .f16 =
      f16CanonicalCompleteAffineMapCharacterSum σ := by
  rw [rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16_cycle,
    f16FourCycleCompleteAffineMapCharacterSum_eq_canonical]

/-- The complete affine-map character sum of the canonical `F₁₆` pattern
is nonnegative. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ .f16 := by
  rw [rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16]
  exact f16CanonicalCompleteAffineMapCharacterSum_nonneg σ

/-- Every canonical rank-seven weight-sixteen pattern has a nonnegative
complete affine-map character sum. -/
theorem rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_nonneg
    (σ : FABL.F₂Cube n → ℝ)
    (c : RankSevenWeightSixteenPatternClass) :
    0 ≤ rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum σ c := by
  cases c with
  | twoE8 =>
      exact rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_twoE8_nonneg σ
  | d16Plus =>
      exact rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_d16Plus_nonneg σ
  | f16 =>
      exact rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_f16_nonneg σ

end CryptBoolean
