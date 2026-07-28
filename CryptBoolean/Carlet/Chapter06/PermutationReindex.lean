/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness

/-!
# Bent functions from arbitrary permutations

Carlet Proposition 21 for reindexing the binary cube by an arbitrary
permutation.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Simultaneous precomposition by a permutation preserves Hamming distance. -/
theorem hammingDistance_comp_perm
    (f g : BooleanFunction n) (σ : Equiv.Perm (FABL.F₂Cube n)) :
    hammingDistance (f ∘ σ) (g ∘ σ) = hammingDistance f g := by
  classical
  unfold hammingDistance hammingDist
  rw [Finset.card_filter, Finset.card_filter]
  change
    (∑ x : FABL.F₂Cube n, if f (σ x) ≠ g (σ x) then 1 else 0) =
      ∑ x : FABL.F₂Cube n, if f x ≠ g x then 1 else 0
  exact Equiv.sum_comp σ (fun x ↦ if f x ≠ g x then 1 else 0)

/-- Reindexing by `σ⁻¹` converts distance from a linear function into
distance from its pullback along the arbitrary permutation `σ`. -/
theorem hammingDistance_comp_perm_symm_linearFunction
    (f : BooleanFunction n) (σ : Equiv.Perm (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    hammingDistance (f ∘ σ.symm) (FABL.affineFunction 0 a) =
      hammingDistance f (fun x ↦ FABL.f₂DotProduct a (σ x)) := by
  let g : BooleanFunction n := fun x ↦ FABL.f₂DotProduct a (σ x)
  have hlinear : g ∘ σ.symm = FABL.affineFunction 0 a := by
    funext x
    simp [g, FABL.affineFunction]
  change hammingDistance (f ∘ σ.symm) (FABL.affineFunction 0 a) =
    hammingDistance f g
  rw [← hlinear]
  exact hammingDistance_comp_perm f g σ.symm

/-- The Walsh coefficient after an arbitrary permutation is the signed
distance from the corresponding pulled-back linear function. -/
theorem walshTransform_comp_perm_symm_eq_two_pow_sub_two_hammingDistance
    (f : BooleanFunction n) (σ : Equiv.Perm (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) :
    walshTransform (f ∘ σ.symm) a =
      (2 ^ n : ℤ) - 2 *
        (hammingDistance f
          (fun x ↦ FABL.f₂DotProduct a (σ x)) : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  have hdistance :=
    hammingDistance_cast_linearFunction_eq (f ∘ σ.symm) a
  rw [hammingDistance_comp_perm_symm_linearFunction f σ a] at hdistance
  linarith

/-- Carlet Proposition 21, first assertion: if the distance from `f` to every
permutation-pulled-back linear function differs from `2^(n-1)` by exactly
`2^(n/2-1)`, then reindexing `f` by the inverse permutation is bent. -/
theorem isBent_comp_perm_symm_of_hammingDistance
    (f : BooleanFunction n) (σ : Equiv.Perm (FABL.F₂Cube n))
    (hnEven : Even n) (hnTwo : 2 ≤ n)
    (hdistance : ∀ a : FABL.F₂Cube n,
      |(hammingDistance f
          (fun x ↦ FABL.f₂DotProduct a (σ x)) : ℝ) -
        (2 : ℝ) ^ (n - 1)| =
      (2 : ℝ) ^ (n / 2 - 1)) :
    IsBent (f ∘ σ.symm) := by
  have hnEq : n = (n - 1) + 1 := by omega
  have hnPower : (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ (n - 1) := by
    apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hnEq
      _ = (2 : ℝ) ^ (n - 1) * 2 := pow_succ _ _
  have hhalfEq : n / 2 = (n / 2 - 1) + 1 := by omega
  have hhalfPower :
      (2 : ℝ) ^ (n / 2) / 2 = (2 : ℝ) ^ (n / 2 - 1) := by
    apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      (2 : ℝ) ^ (n / 2) = (2 : ℝ) ^ ((n / 2 - 1) + 1) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hhalfEq
      _ = (2 : ℝ) ^ (n / 2 - 1) * 2 := pow_succ _ _
  apply (hasFlatWalshSpectrum_iff_isBent (f ∘ σ.symm)).1
  intro a
  rw [sqrt_two_pow_eq_pow_half hnEven]
  have hdistanceAt := hdistance a
  rw [← hnPower, ← hhalfPower] at hdistanceAt
  have hwalshInt :=
    walshTransform_comp_perm_symm_eq_two_pow_sub_two_hammingDistance f σ a
  have hwalsh := congrArg (fun z : ℤ ↦ (z : ℝ)) hwalshInt
  push_cast at hwalsh
  rw [hwalsh]
  calc
    |(2 : ℝ) ^ n -
        2 * hammingDistance f
          (fun x ↦ FABL.f₂DotProduct a (σ x))| =
        2 *
          |(hammingDistance f
              (fun x ↦ FABL.f₂DotProduct a (σ x)) : ℝ) -
            (2 : ℝ) ^ n / 2| := by
      rw [show
        (2 : ℝ) ^ n -
              2 * hammingDistance f
                (fun x ↦ FABL.f₂DotProduct a (σ x)) =
            (-2 : ℝ) *
              ((hammingDistance f
                  (fun x ↦ FABL.f₂DotProduct a (σ x)) : ℝ) -
                (2 : ℝ) ^ n / 2) by ring,
        abs_mul]
      norm_num
    _ = 2 * ((2 : ℝ) ^ (n / 2) / 2) := by rw [hdistanceAt]
    _ = (2 : ℝ) ^ (n / 2) := by ring

end CryptBoolean
