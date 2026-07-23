/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenAffineMaps
public import CryptBoolean.Carlet.Chapter02.FourierOperations

/-!
# Rank-seven weight-sixteen orbit sums

Complete affine-map character sums for the two indecomposable rank-seven
weight-sixteen support patterns.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The multiplicative derivative of a real function on the binary cube. -/
def orbitSignDerivative
    (σ : FABL.F₂Cube n → ℝ) (a x : FABL.F₂Cube n) : ℝ :=
  σ x * σ (x + a)

/-- The unnormalized fourfold additive convolution of a multiplicative
derivative. -/
noncomputable def weightSixteenFourfoldConvolution
    (σ : FABL.F₂Cube n → ℝ) (a b : FABL.F₂Cube n) : ℝ :=
  rawConvolution
    (rawConvolution (orbitSignDerivative σ a) (orbitSignDerivative σ a))
    (rawConvolution (orbitSignDerivative σ a) (orbitSignDerivative σ a)) b

/-- The complete affine-map character sum of the `D₁₆⁺` support
pattern, in its fourfold-convolution normal form. -/
noncomputable def d16CanonicalCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ a, ∑ b, weightSixteenFourfoldConvolution σ a b ^ 2

/-- The complete `D₁₆⁺` affine-map character sum is nonnegative. -/
theorem d16CanonicalCompleteAffineMapCharacterSum_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ d16CanonicalCompleteAffineMapCharacterSum σ := by
  unfold d16CanonicalCompleteAffineMapCharacterSum
  positivity

/-- The complete affine-map character sum of the indecomposable Type-I
`F₁₆` support pattern, in its four-cycle normal form. -/
noncomputable def f16CanonicalCompleteAffineMapCharacterSum
    (σ : FABL.F₂Cube n → ℝ) : ℝ :=
  ∑ a, ∑ b,
    weightSixteenFourfoldConvolution σ a b *
      weightSixteenFourfoldConvolution σ b a

/-- The raw Walsh transform of a multiplicative derivative. -/
noncomputable def orbitDerivativeWalsh
    (σ : FABL.F₂Cube n → ℝ) (a ξ : FABL.F₂Cube n) : ℝ :=
  rawFourierTransform (orbitSignDerivative σ a) ξ

/-- The four-point block appearing in the `F₁₆` sum-of-squares
decomposition. -/
def f16FourPointBlock
    (σ : FABL.F₂Cube n → ℝ)
    (a d e x : FABL.F₂Cube n) : ℝ :=
  σ x * σ (x + d) * σ (x + e) * σ (x + a + d + e)

/-- The Walsh transform of the four-point `F₁₆` block. -/
noncomputable def f16FourPointBlockWalsh
    (σ : FABL.F₂Cube n → ℝ)
    (a ξ d e : FABL.F₂Cube n) : ℝ :=
  rawFourierTransform (f16FourPointBlock σ a d e) ξ

private theorem rawFourierTransform_weightSixteenFourfoldConvolution
    (σ : FABL.F₂Cube n → ℝ) (a ξ : FABL.F₂Cube n) :
    rawFourierTransform (weightSixteenFourfoldConvolution σ a) ξ =
      orbitDerivativeWalsh σ a ξ ^ 4 := by
  change rawFourierTransform
      (rawConvolution
        (rawConvolution (orbitSignDerivative σ a) (orbitSignDerivative σ a))
        (rawConvolution (orbitSignDerivative σ a) (orbitSignDerivative σ a))) ξ = _
  rw [rawFourierTransform_rawConvolution,
    rawFourierTransform_rawConvolution]
  unfold orbitDerivativeWalsh
  ring

private theorem weightSixteenFourfoldConvolution_eq_sum_rawConvolution_blocks
    (σ : FABL.F₂Cube n → ℝ) (a b : FABL.F₂Cube n) :
    weightSixteenFourfoldConvolution σ b a =
      ∑ d, ∑ e,
        rawConvolution (f16FourPointBlock σ a d e)
          (f16FourPointBlock σ a d e) b := by
  let reindex :
      (FABL.F₂Cube n × FABL.F₂Cube n × FABL.F₂Cube n) ≃
        (FABL.F₂Cube n × FABL.F₂Cube n × FABL.F₂Cube n) :=
    { toFun := fun p ↦ (p.1, p.2.2 + p.2.1, p.2.2)
      invFun := fun p ↦ (p.1, p.2.2 + p.2.1, p.2.2)
      left_inv := by
        rintro ⟨y, z, x⟩
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · simp only [← add_assoc, ZModModule.add_self, zero_add]
          · rfl
      right_inv := by
        rintro ⟨d, e, t⟩
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · simp only [← add_assoc, ZModModule.add_self, zero_add]
          · rfl }
  change
    rawConvolution
        (rawConvolution (orbitSignDerivative σ b) (orbitSignDerivative σ b))
        (rawConvolution (orbitSignDerivative σ b) (orbitSignDerivative σ b)) a = _
  simp only [rawConvolution]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ y, ∑ z, ∑ x,
        orbitSignDerivative σ b x * orbitSignDerivative σ b (y + x) *
          (orbitSignDerivative σ b z *
            orbitSignDerivative σ b (a + y + z))) =
        ∑ p : FABL.F₂Cube n × FABL.F₂Cube n × FABL.F₂Cube n,
          orbitSignDerivative σ b p.2.2 *
            orbitSignDerivative σ b (p.1 + p.2.2) *
            (orbitSignDerivative σ b p.2.1 *
              orbitSignDerivative σ b (a + p.1 + p.2.1)) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ p : FABL.F₂Cube n × FABL.F₂Cube n × FABL.F₂Cube n,
          f16FourPointBlock σ a p.1 p.2.1 p.2.2 *
            f16FourPointBlock σ a p.1 p.2.1 (p.2.2 + b) := by
      apply Fintype.sum_equiv reindex
      rintro ⟨y, z, x⟩
      rw [show reindex (y, z, x) = (y, x + z, x) by rfl]
      simp only [orbitSignDerivative, f16FourPointBlock]
      have hxy : x + y = y + x := add_comm _ _
      have hxxz : x + (x + z) = z := by
        rw [← add_assoc, ZModModule.add_self, zero_add]
      have haxyz : x + a + y + (x + z) = a + y + z := by
        calc
          x + a + y + (x + z) = (x + x) + (a + y + z) := by abel
          _ = a + y + z := by rw [ZModModule.add_self, zero_add]
      have hbxy : x + b + y = y + x + b := by abel
      have hbxz : x + b + (x + z) = z + b := by
        calc
          x + b + (x + z) = (x + x) + (z + b) := by abel
          _ = z + b := by rw [ZModModule.add_self, zero_add]
      have hbaxyz : x + b + a + y + (x + z) = a + y + z + b := by
        calc
          x + b + a + y + (x + z) = (x + x) + (a + y + z + b) := by abel
          _ = a + y + z + b := by rw [ZModModule.add_self, zero_add]
      rw [hxy, hxxz, haxyz, hbxy, hbxz, hbaxyz]
      ring
    _ = ∑ d, ∑ e, ∑ x,
          f16FourPointBlock σ a d e x *
            f16FourPointBlock σ a d e (b + x) := by
      simp only [Fintype.sum_prod_type, add_comm]

private theorem rawFourierTransform_weightSixteenFourfoldConvolution_swapped
    (σ : FABL.F₂Cube n → ℝ) (a ξ : FABL.F₂Cube n) :
    rawFourierTransform (fun b ↦ weightSixteenFourfoldConvolution σ b a) ξ =
      ∑ d, ∑ e, f16FourPointBlockWalsh σ a ξ d e ^ 2 := by
  rw [show (fun b ↦ weightSixteenFourfoldConvolution σ b a) =
      fun b ↦ ∑ d, ∑ e,
        rawConvolution (f16FourPointBlock σ a d e)
          (f16FourPointBlock σ a d e) b by
    funext b
    exact weightSixteenFourfoldConvolution_eq_sum_rawConvolution_blocks σ a b]
  simp only [rawFourierTransform]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← rawFourierTransform]
  rw [rawFourierTransform_rawConvolution]
  simp [f16FourPointBlockWalsh, pow_two]

/-- The complete `F₁₆` affine-map character sum has a division-free
Fourier sum-of-squares decomposition. -/
theorem two_pow_mul_f16CanonicalCompleteAffineMapCharacterSum_eq_sum_sq
    (σ : FABL.F₂Cube n → ℝ) :
    (2 ^ n : ℝ) * f16CanonicalCompleteAffineMapCharacterSum σ =
      ∑ a, ∑ ξ, ∑ d, ∑ e,
        (orbitDerivativeWalsh σ a ξ ^ 2 *
          f16FourPointBlockWalsh σ a ξ d e) ^ 2 := by
  unfold f16CanonicalCompleteAffineMapCharacterSum
  rw [Finset.mul_sum]
  calc
    (∑ a, (2 ^ n : ℝ) * ∑ b,
        weightSixteenFourfoldConvolution σ a b *
          weightSixteenFourfoldConvolution σ b a) =
        ∑ a, ∑ ξ,
          rawFourierTransform (weightSixteenFourfoldConvolution σ a) ξ *
            rawFourierTransform
              (fun b ↦ weightSixteenFourfoldConvolution σ b a) ξ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (sum_rawFourierTransform_mul
        (weightSixteenFourfoldConvolution σ a)
        (fun b ↦ weightSixteenFourfoldConvolution σ b a)).symm
    _ = ∑ a, ∑ ξ,
          orbitDerivativeWalsh σ a ξ ^ 4 *
            (∑ d, ∑ e, f16FourPointBlockWalsh σ a ξ d e ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro ξ _
      rw [rawFourierTransform_weightSixteenFourfoldConvolution,
        rawFourierTransform_weightSixteenFourfoldConvolution_swapped]
    _ = ∑ a, ∑ ξ, ∑ d, ∑ e,
          (orbitDerivativeWalsh σ a ξ ^ 2 *
            f16FourPointBlockWalsh σ a ξ d e) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro ξ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- The complete `F₁₆` affine-map character sum is nonnegative. -/
theorem f16CanonicalCompleteAffineMapCharacterSum_nonneg
    (σ : FABL.F₂Cube n → ℝ) :
    0 ≤ f16CanonicalCompleteAffineMapCharacterSum σ := by
  have hscaled :
      0 ≤ (2 ^ n : ℝ) * f16CanonicalCompleteAffineMapCharacterSum σ := by
    rw [two_pow_mul_f16CanonicalCompleteAffineMapCharacterSum_eq_sum_sq]
    positivity
  have hpow : 0 < (2 ^ n : ℝ) := by positivity
  nlinarith

end CryptBoolean
