/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# Hadamard matrices and difference sets from bent functions

Carlet Section 6: the translation sign matrix and the support difference set
characterize bent Boolean functions.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The translation sign matrix `H[x,y] = (-1)^(f(x+y))`. -/
def bentSignMatrix (f : BooleanFunction n) :
    Matrix (FABL.F₂Cube n) (FABL.F₂Cube n) ℝ :=
  fun x y ↦ realSignView f (x + y)

/-- A Gram-matrix entry of the translation sign matrix is the corresponding
autocorrelation coefficient. -/
theorem bentSignMatrix_mul_conjTranspose_apply
    (f : BooleanFunction n) (x z : FABL.F₂Cube n) :
    (bentSignMatrix f * Matrix.conjTranspose (bentSignMatrix f)) x z =
      autocorrelation f (x + z) := by
  classical
  rw [Matrix.mul_apply, autocorrelation]
  simp only [Matrix.conjTranspose_apply, bentSignMatrix, star_trivial]
  simp_rw [realSignView_booleanDerivative]
  change
    (∑ y, realSignView f (x + y) * realSignView f (z + y)) =
      ∑ y, realSignView f y * realSignView f (y + (x + z))
  calc
    (∑ y, realSignView f (x + y) * realSignView f (z + y)) =
        ∑ y, realSignView f (x + (y + x)) *
          realSignView f (z + (y + x)) :=
      (Equiv.sum_comp (Equiv.addRight x)
        (fun y : FABL.F₂Cube n ↦
          realSignView f (x + y) * realSignView f (z + y))).symm
    _ = ∑ y, realSignView f y * realSignView f (y + (x + z)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      have hcancel : x + (y + x) = y := by
        calc
          x + (y + x) = (x + x) + y := by ac_rfl
          _ = y := by rw [ZModModule.add_self, zero_add]
      rw [hcancel]
      congr 1
      ac_rfl

private theorem bentSignMatrix_entry_mem_unitary
    (f : BooleanFunction n) (x y : FABL.F₂Cube n) :
    bentSignMatrix f x y ∈ unitary ℝ := by
  apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
  unfold bentSignMatrix realSignView FABL.realSignEncodedFunction
    FABL.signEncodedFunction
  rcases FABL.signValue_eq_neg_one_or_one (FABL.signEncode (f (x + y))) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Bentness is equivalent to the Hadamard property of the translation sign
matrix. -/
theorem isBent_iff_bentSignMatrix_isHadamard (f : BooleanFunction n) :
    IsBent f ↔ (bentSignMatrix f).IsHadamard := by
  constructor
  · intro hf
    apply Matrix.IsHadamard.of_mul_conjTranspose
      (bentSignMatrix_entry_mem_unitary f)
    · ext x z
      rw [bentSignMatrix_mul_conjTranspose_apply]
      by_cases hxz : x = z
      · subst z
        rw [ZModModule.add_self, autocorrelation_zero]
        simp
      · have hdirection : x + z ≠ 0 := by
          intro hzero
          apply hxz
          exact (add_eq_zero_iff_eq_neg.mp hzero).trans
            (ZModModule.neg_eq_self z)
        have hbalanced :=
          (isBent_iff_forall_nonzero_derivative_isBalanced f).mp hf
            (x + z) hdirection
        have hzero :=
          (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
            f (x + z)).mp hbalanced
        rw [hzero]
        simp [hxz]
    · exact IsRegular.of_ne_zero (by positivity)
  · intro hhadamard
    apply (isBent_iff_forall_nonzero_derivative_isBalanced f).mpr
    intro a ha
    apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f a).mpr
    have hentry := congrFun (congrFun hhadamard.mul_conjTranspose 0) a
    rw [bentSignMatrix_mul_conjTranspose_apply] at hentry
    have hzeroNe : (0 : FABL.F₂Cube n) ≠ a := fun h ↦ ha h.symm
    simpa [hzeroNe] using hentry

/-- The multiplicity of a nonzero group difference inside a finite subset of
the binary cube. -/
def differenceMultiplicity
    (D : Finset (FABL.F₂Cube n)) (a : FABL.F₂Cube n) : ℕ :=
  (D.filter fun x ↦ x + a ∈ D).card

/-- The Hadamard difference-set parameters appropriate to a subset of the
binary cube. -/
def IsHadamardDifferenceSet (D : Finset (FABL.F₂Cube n)) : Prop :=
  2 ^ (n - 2) ≤ D.card ∧
    ∀ a : FABL.F₂Cube n, a ≠ 0 →
      differenceMultiplicity D a = D.card - 2 ^ (n - 2)

/-- On a Boolean support, difference multiplicity is the Hamming weight of
the translated function restricted to the original support. -/
theorem differenceMultiplicity_support_eq_hammingNorm_restriction
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    differenceMultiplicity (support f) a =
      hammingNorm (fun x : {x : FABL.F₂Cube n // f x ≠ 0} ↦ f (x.1 + a)) := by
  classical
  unfold differenceMultiplicity hammingNorm
  apply Finset.card_bij
      (fun x hx ↦ ⟨x, by
        have hxSupport := (Finset.mem_filter.mp hx).1
        rw [mem_support] at hxSupport
        simp [hxSupport]⟩)
  · intro x hx
    rw [Finset.mem_filter]
    have hxShift := (mem_support f (x + a)).mp
      (Finset.mem_filter.mp hx).2
    exact ⟨Finset.mem_univ _, by simp [hxShift]⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val hxy
  · intro y hy
    have hyShift : f (y.1 + a) = 1 :=
      Fin.eq_one_of_ne_zero _ (Finset.mem_filter.mp hy).2
    have hyOne : f y.1 = 1 := Fin.eq_one_of_ne_zero _ y.2
    refine ⟨y.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨(mem_support f y.1).mpr hyOne,
        (mem_support f (y.1 + a)).mpr hyShift⟩
    · exact Subtype.ext rfl

/-- Derivative weight plus twice the support difference multiplicity equals
twice the support size. -/
theorem hammingWeight_booleanDerivative_add_two_mul_differenceMultiplicity
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    hammingWeight (FABL.booleanDerivative f a) +
        2 * differenceMultiplicity (support f) a =
      2 * hammingWeight f := by
  have hidentity := hammingNorm_add_restrictSupport_identity
    f (fun x ↦ f (x + a))
  rw [← differenceMultiplicity_support_eq_hammingNorm_restriction,
    ] at hidentity
  have htranslate := hammingWeight_translate f a
  change hammingNorm (fun x ↦ f (x + a)) = hammingNorm f at htranslate
  rw [htranslate] at hidentity
  change hammingNorm (FABL.booleanDerivative f a) +
      2 * differenceMultiplicity (support f) a = 2 * hammingNorm f
  change hammingNorm (f + fun x ↦ f (x + a)) +
      2 * differenceMultiplicity (support f) a = 2 * hammingNorm f
  omega

private theorem exists_nonzero_f₂Cube (hn : 0 < n) :
    ∃ a : FABL.F₂Cube n, a ≠ 0 := by
  let i : Fin n := ⟨0, hn⟩
  let a : FABL.F₂Cube n := Pi.single i 1
  refine ⟨a, ?_⟩
  intro hzero
  have hvalue := congrFun hzero i
  simp [a, i] at hvalue

/-- In positive even dimension, bentness is equivalent to the support being
a Hadamard difference set in the additive binary cube. -/
theorem isBent_iff_support_isHadamardDifferenceSet
    (f : BooleanFunction n) (_hnEven : Even n) (hn : 2 ≤ n) :
    IsBent f ↔ IsHadamardDifferenceSet (support f) := by
  have hpower : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    omega
  constructor
  · intro hf
    have hbalanced :=
      (isBent_iff_forall_nonzero_derivative_isBalanced f).mp hf
    have hmultiplicity (a : FABL.F₂Cube n) (ha : a ≠ 0) :
        differenceMultiplicity (support f) a + 2 ^ (n - 2) =
          hammingWeight f := by
      have hderivative := hbalanced a ha
      rw [IsBalanced] at hderivative
      have hidentity :=
        hammingWeight_booleanDerivative_add_two_mul_differenceMultiplicity f a
      omega
    obtain ⟨a, ha⟩ := exists_nonzero_f₂Cube (by omega : 0 < n)
    have hle : 2 ^ (n - 2) ≤ hammingWeight f := by
      have := hmultiplicity a ha
      omega
    rw [IsHadamardDifferenceSet, ← hammingWeight_eq_card_support]
    refine ⟨hle, fun a ha ↦ ?_⟩
    have := hmultiplicity a ha
    omega
  · rw [IsHadamardDifferenceSet, ← hammingWeight_eq_card_support]
    rintro ⟨hle, hmultiplicity⟩
    apply (isBent_iff_forall_nonzero_derivative_isBalanced f).mpr
    intro a ha
    rw [IsBalanced]
    have hidentity :=
      hammingWeight_booleanDerivative_add_two_mul_differenceMultiplicity f a
    have hmultiplicity' := hmultiplicity a ha
    omega

end CryptBoolean
