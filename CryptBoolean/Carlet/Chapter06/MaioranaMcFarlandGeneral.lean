/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Bentness
public import CryptBoolean.Carlet.Chapter06.MaioranaMcFarland

/-!
# General Maiorana--McFarland functions

Carlet relation (49) and its exact bentness criterion for unequal coordinate
blocks.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n r s : ℕ}

/-- The signed character sum over a fiber in the general
Maiorana--McFarland construction. -/
def maioranaMcFarlandFiberCharacterSum
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) : ℤ :=
  ∑ y with φ y = a, bitSignInt (g y + FABL.f₂DotProduct b y)

/-- Carlet relation (49): the raw Walsh coefficient of a general
Maiorana--McFarland function is the corresponding fiber character sum
multiplied by the size of the first coordinate block. -/
theorem walshTransform_maioranaMcFarlandGeneral
    (f : BooleanFunction (r + s))
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hf : ∀ x y,
      f (Fin.append x y) = FABL.f₂DotProduct x (φ y) + g y)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
    walshTransform f (Fin.append a b) =
      (2 ^ r : ℤ) * maioranaMcFarlandFiberCharacterSum φ g a b := by
  classical
  rw [walshTransform]
  calc
    ∑ z : FABL.F₂Cube (r + s), walshTerm f (Fin.append a b) z =
        ∑ p : FABL.F₂Cube r × FABL.F₂Cube s,
          walshTerm f (Fin.append a b) (Fin.append p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.appendEquiv r s)
        (fun p ↦ walshTerm f (Fin.append a b) (Fin.append p.1 p.2))
        (fun z ↦ walshTerm f (Fin.append a b) z)
        (fun _ ↦ rfl)).symm
    _ = ∑ x : FABL.F₂Cube r, ∑ y : FABL.F₂Cube s,
          bitSignInt
            (FABL.f₂DotProduct x (φ y) + g y +
              (FABL.f₂DotProduct a x + FABL.f₂DotProduct b y)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      simp only [walshTerm, hf, FABL.f₂DotProduct_append]
    _ = ∑ y : FABL.F₂Cube s, ∑ x : FABL.F₂Cube r,
          bitSignInt
            (FABL.f₂DotProduct x (φ y) + g y +
              (FABL.f₂DotProduct a x + FABL.f₂DotProduct b y)) := by
      rw [Finset.sum_comm]
    _ = ∑ y : FABL.F₂Cube s,
          walshTransform
            (FABL.affineFunction
              (g y + FABL.f₂DotProduct b y) (φ y)) a := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [walshTransform]
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [walshTerm, FABL.affineFunction]
      congr 1
      rw [show FABL.f₂DotProduct x (φ y) =
          FABL.f₂DotProduct (φ y) x by
        exact dotProduct_comm x (φ y)]
      abel
    _ = ∑ y : FABL.F₂Cube s,
          if a = φ y then
            bitSignInt (g y + FABL.f₂DotProduct b y) * (2 ^ r : ℤ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [walshTransform_affineFunction]
    _ = (2 ^ r : ℤ) * maioranaMcFarlandFiberCharacterSum φ g a b := by
      rw [maioranaMcFarlandFiberCharacterSum, Finset.mul_sum]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hy : φ y = a
      · simp [hy, mul_comm]
      · simp [hy, Ne.symm hy]

/-- Under the source's even-dimension hypothesis, a general
Maiorana--McFarland function is bent exactly when the first block fits within
half the dimension and every fiber character sum has the stated magnitude. -/
theorem isBent_iff_maioranaMcFarlandFiberCharacterSum_natAbs
    (f : BooleanFunction (r + s))
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hf : ∀ x y,
      f (Fin.append x y) = FABL.f₂DotProduct x (φ y) + g y)
    (_heven : Even (r + s)) :
    IsBent f ↔
      r ≤ (r + s) / 2 ∧
        ∀ a b,
          (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs =
            2 ^ ((r + s) / 2 - r) := by
  constructor
  · intro hbent
    have hmag (a : FABL.F₂Cube r) (b : FABL.F₂Cube s) :
        2 ^ r * (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs =
          2 ^ ((r + s) / 2) := by
      have h := natAbs_walshTransform_eq_two_pow_half_of_isBent
        f hbent (Fin.append a b)
      rw [walshTransform_maioranaMcFarlandGeneral f φ g hf a b,
        Int.natAbs_mul] at h
      simpa using h
    have hzero := hmag (0 : FABL.F₂Cube r) (0 : FABL.F₂Cube s)
    have hsumNe :
        (maioranaMcFarlandFiberCharacterSum φ g
          (0 : FABL.F₂Cube r) (0 : FABL.F₂Cube s)).natAbs ≠ 0 := by
      intro hsumZero
      rw [hsumZero, mul_zero] at hzero
      exact (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hzero.symm
    have hpowers : 2 ^ r ≤ 2 ^ ((r + s) / 2) := by
      calc
        2 ^ r = 2 ^ r * 1 := by rw [mul_one]
        _ ≤ 2 ^ r *
              (maioranaMcFarlandFiberCharacterSum φ g
                (0 : FABL.F₂Cube r) (0 : FABL.F₂Cube s)).natAbs :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hsumNe)
        _ = 2 ^ ((r + s) / 2) := hzero
    have hle : r ≤ (r + s) / 2 :=
      (Nat.pow_le_pow_iff_right (by omega : 1 < (2 : ℕ))).mp hpowers
    refine ⟨hle, ?_⟩
    intro a b
    apply Nat.mul_left_cancel (pow_pos (by omega : 0 < (2 : ℕ)) r)
    calc
      2 ^ r * (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs =
          2 ^ ((r + s) / 2) := hmag a b
      _ = 2 ^ r * 2 ^ ((r + s) / 2 - r) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
  · rintro ⟨hle, hmag⟩
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half f).mpr
    intro u
    let p := (Fin.appendEquiv r s).symm u
    have hu : Fin.append p.1 p.2 = u :=
      (Fin.appendEquiv r s).apply_symm_apply u
    rw [← hu,
      walshTransform_maioranaMcFarlandGeneral f φ g hf p.1 p.2,
      Int.natAbs_mul]
    have htwo : Int.natAbs (2 : ℤ) = 2 := by norm_num
    rw [Int.natAbs_pow, htwo]
    rw [hmag, ← pow_add, Nat.add_sub_of_le hle]

/-- For equal coordinate blocks, bijectivity of the frequency map is both
necessary and sufficient for the Maiorana--McFarland function to be bent. -/
theorem isBent_iff_bijective_maioranaMcFarland
    (f : BooleanFunction (n + n))
    (φ : FABL.F₂Cube n → FABL.F₂Cube n)
    (g : BooleanFunction n)
    (hf : ∀ x y,
      f (Fin.append x y) = FABL.f₂DotProduct x (φ y) + g y) :
    IsBent f ↔ Function.Bijective φ := by
  constructor
  · intro hbent
    have hcriterion :=
      (isBent_iff_maioranaMcFarlandFiberCharacterSum_natAbs
        f φ g hf (by exact ⟨n, rfl⟩)).1 hbent
    have hsurjective : Function.Surjective φ := by
      intro a
      have hmag := hcriterion.2 a (0 : FABL.F₂Cube n)
      have hexponent : (n + n) / 2 - n = 0 := by omega
      rw [hexponent, pow_zero] at hmag
      by_contra hpreimage
      have hnone : ∀ y, φ y ≠ a := by
        intro y hy
        exact hpreimage ⟨y, hy⟩
      have hzero : maioranaMcFarlandFiberCharacterSum φ g a 0 = 0 := by
        rw [maioranaMcFarlandFiberCharacterSum]
        simp [hnone]
      rw [hzero] at hmag
      norm_num at hmag
    exact (Fintype.bijective_iff_surjective_and_card φ).2
      ⟨hsurjective, rfl⟩
  · intro hbijective
    let π : Equiv.Perm (FABL.F₂Cube n) := Equiv.ofBijective φ hbijective
    apply isBent_of_maioranaMcFarlandPermutation f g π
    intro x y
    exact hf x y

private theorem maioranaMcFarlandFiberCharacterSum_eq_affineFiberWalshZero
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (a : FABL.F₂Cube r) (b : FABL.F₂Cube s)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube s))
    (z : FABL.F₂Cube s)
    (e : FABL.F₂Cube (s - r) ≃ₗ[FABL.𝔽₂] E)
    (hfiber : ∀ y, φ y = a ↔
      ∃ x, y = (e x).1 + z) :
    maioranaMcFarlandFiberCharacterSum φ g a b =
      walshTransform
        (coordinateAffineSubspaceRestriction
          (g + FABL.affineFunction 0 b) E z e) 0 := by
  classical
  rw [maioranaMcFarlandFiberCharacterSum, walshTransform]
  symm
  apply Finset.sum_bij
    (fun x (_ : x ∈ (Finset.univ : Finset (FABL.F₂Cube (s - r)))) ↦
      (e x).1 + z)
  · intro x _hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hfiber _).mpr ⟨x, rfl⟩⟩
  · intro x₁ _hx₁ x₂ _hx₂ hpoint
    apply e.injective
    apply Subtype.ext
    exact add_right_cancel hpoint
  · intro y hy
    obtain ⟨x, hx⟩ := (hfiber y).mp (Finset.mem_filter.mp hy).2
    exact ⟨x, Finset.mem_univ _, hx.symm⟩
  · intro x _hx
    simp [walshTerm_zero, coordinateAffineSubspaceRestriction_apply,
      FABL.affineFunction]

private theorem isBent_affineFiberRestriction_add_linear
    (g : BooleanFunction s) (b z : FABL.F₂Cube s)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube s))
    (e : FABL.F₂Cube (s - r) ≃ₗ[FABL.𝔽₂] E)
    (hbent : IsBent (coordinateAffineSubspaceRestriction g E z e)) :
    IsBent
      (coordinateAffineSubspaceRestriction
        (g + FABL.affineFunction 0 b) E z e) := by
  let h := coordinateAffineSubspaceRestriction g E z e
  have heq :
      coordinateAffineSubspaceRestriction
          (g + FABL.affineFunction 0 b) E z e =
        h + FABL.affineFunction (FABL.affineFunction 0 b z)
          (coordinateRestrictedAffineFrequency E e b) := by
    funext x
    simp only [h, coordinateAffineSubspaceRestriction_apply, Pi.add_apply]
    rw [show (e x).1 + z = z + (e x).1 by abel]
    rw [affineFunction_coordinateAffineSubspaceRestriction
      E e z b 0 x]
  rw [heq, isBent_add_affineFunction_iff]
  exact hbent

/-- Carlet Proposition 20: if the fibers of `φ` are affine subspaces of
dimension `s - r` and the restrictions of `g` to the positive-dimensional
fibers are bent, then the associated general Maiorana--McFarland function is
bent. -/
theorem isBent_maioranaMcFarlandGeneral_of_affineFibers
    (f : BooleanFunction (r + s))
    (φ : FABL.F₂Cube s → FABL.F₂Cube r)
    (g : BooleanFunction s)
    (hf : ∀ x y,
      f (Fin.append x y) = FABL.f₂DotProduct x (φ y) + g y)
    (hrle : r ≤ s) (heven : Even (r + s))
    (E : FABL.F₂Cube r → Submodule FABL.𝔽₂ (FABL.F₂Cube s))
    (z : FABL.F₂Cube r → FABL.F₂Cube s)
    (e : ∀ a, FABL.F₂Cube (s - r) ≃ₗ[FABL.𝔽₂] E a)
    (hfiber : ∀ a y, φ y = a ↔
      ∃ x, y = (e a x).1 + z a)
    (hbent : r < s → ∀ a,
      IsBent (coordinateAffineSubspaceRestriction g (E a) (z a) (e a))) :
    IsBent f := by
  have hle : r ≤ (r + s) / 2 := by omega
  have hexponent : (s - r) / 2 = (r + s) / 2 - r := by
    rcases heven with ⟨k, hk⟩
    omega
  apply (isBent_iff_maioranaMcFarlandFiberCharacterSum_natAbs
    f φ g hf heven).mpr
  refine ⟨hle, ?_⟩
  intro a b
  have hrestriction :
      IsBent (coordinateAffineSubspaceRestriction g (E a) (z a) (e a)) := by
    by_cases hrs : r < s
    · exact hbent hrs a
    · apply (isBent_iff_forall_nonzero_derivative_isBalanced _).mpr
      intro d hd
      exfalso
      apply hd
      funext i
      have hi := i.isLt
      omega
  have hlinear := isBent_affineFiberRestriction_add_linear
    g b (z a) (E a) (e a) hrestriction
  calc
    (maioranaMcFarlandFiberCharacterSum φ g a b).natAbs =
        (walshTransform
          (coordinateAffineSubspaceRestriction
            (g + FABL.affineFunction 0 b) (E a) (z a) (e a)) 0).natAbs :=
      congrArg Int.natAbs
        (maioranaMcFarlandFiberCharacterSum_eq_affineFiberWalshZero
          φ g a b (E a) (z a) (e a) (hfiber a))
    _ = 2 ^ ((s - r) / 2) :=
      natAbs_walshTransform_eq_two_pow_half_of_isBent _ hlinear 0
    _ = 2 ^ ((r + s) / 2 - r) := by rw [hexponent]

end CryptBoolean
