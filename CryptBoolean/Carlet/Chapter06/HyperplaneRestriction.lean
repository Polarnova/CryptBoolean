/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.NestedBent
public import CryptBoolean.Carlet.Chapter06.PlateauedSupport

/-!
# Hyperplane restrictions of bent functions

Carlet Theorem 11: the complementary plateaued spectra of the two restrictions
to a linear hyperplane and its other coset characterize bentness.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The one-dimensional binary cube point with prescribed coordinate. -/
def singletonF₂Cube (b : FABL.𝔽₂) : FABL.F₂Cube 1 :=
  fun _ ↦ b

@[simp] theorem singletonF₂Cube_apply (b : FABL.𝔽₂) (i : Fin 1) :
    singletonF₂Cube b i = b :=
  rfl

def singletonF₂CubeLinearEquiv :
    FABL.𝔽₂ ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 1 where
  toFun := singletonF₂Cube
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    funext i
    fin_cases i
    rfl

theorem sum_singletonF₂Cube
    {R : Type*} [AddCommMonoid R] (g : FABL.F₂Cube 1 → R) :
    (∑ y, g y) = g (singletonF₂Cube 0) + g (singletonF₂Cube 1) := by
  calc
    (∑ y, g y) = ∑ b : FABL.𝔽₂, g (singletonF₂Cube b) := by
      exact (Fintype.sum_equiv singletonF₂CubeLinearEquiv.toEquiv
        (fun b ↦ g (singletonF₂Cube b)) g (fun _ ↦ rfl)).symm
    _ = g (singletonF₂Cube 0) + g (singletonF₂Cube 1) := by
      have huniv : (Finset.univ : Finset FABL.𝔽₂) = {0, 1} := rfl
      rw [huniv]
      simp

/-- Splitting the last coordinate expresses an ambient Walsh coefficient as
the signed sum of the Walsh coefficients of the two hyperplane restrictions. -/
theorem walshTransform_append_singletonF₂Cube
    (f : BooleanFunction (n + 1)) (a : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    walshTransform f (Fin.append a (singletonF₂Cube b)) =
      walshTransform (firstBlockSlice f (singletonF₂Cube 0)) a +
        bitSignInt b *
          walshTransform (firstBlockSlice f (singletonF₂Cube 1)) a := by
  classical
  rw [walshTransform]
  calc
    ∑ z : FABL.F₂Cube (n + 1),
        walshTerm f (Fin.append a (singletonF₂Cube b)) z =
      ∑ p : FABL.F₂Cube n × FABL.F₂Cube 1,
        walshTerm f (Fin.append a (singletonF₂Cube b))
          (Fin.append p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.appendEquiv n 1)
        (fun p ↦ walshTerm f (Fin.append a (singletonF₂Cube b))
          (Fin.append p.1 p.2))
        (fun z ↦ walshTerm f (Fin.append a (singletonF₂Cube b)) z)
        (fun _ ↦ rfl)).symm
    _ = ∑ y : FABL.F₂Cube 1, ∑ x : FABL.F₂Cube n,
        bitSignInt (FABL.f₂DotProduct (singletonF₂Cube b) y) *
          walshTerm (firstBlockSlice f y) a x := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      rw [walshTerm, walshTerm, FABL.f₂DotProduct_append]
      rw [show
        f (Fin.append x y) +
              (FABL.f₂DotProduct a x +
                FABL.f₂DotProduct (singletonF₂Cube b) y) =
            FABL.f₂DotProduct (singletonF₂Cube b) y +
              (firstBlockSlice f y x + FABL.f₂DotProduct a x) by
        simp only [firstBlockSlice]
        abel,
        bitSignInt_add]
    _ = ∑ y : FABL.F₂Cube 1,
        bitSignInt (FABL.f₂DotProduct (singletonF₂Cube b) y) *
          walshTransform (firstBlockSlice f y) a := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [walshTransform, Finset.mul_sum]
    _ = walshTransform (firstBlockSlice f (singletonF₂Cube 0)) a +
        bitSignInt b *
          walshTransform (firstBlockSlice f (singletonF₂Cube 1)) a := by
      rw [sum_singletonF₂Cube]
      simp [singletonF₂Cube, FABL.f₂DotProduct, dotProduct,
        bitSignInt_eq_if_one]

/-- The two coordinate restrictions determined by a linear change of
variables represent a linear hyperplane and its complementary affine coset. -/
def linearHyperplaneRestriction
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1))
    (b : FABL.𝔽₂) : BooleanFunction n :=
  firstBlockSlice (f ∘ L) (singletonF₂Cube b)

/-- The two hyperplane restrictions have complementary spectra of amplitude
`2^((n+1)/2)` when at every frequency exactly one coefficient is nonzero and
that coefficient has this magnitude. -/
def HasComplementaryHyperplaneRestrictionSpectra
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1)) : Prop :=
  ∀ a : FABL.F₂Cube n,
    (walshTransform (linearHyperplaneRestriction f L 0) a = 0 ∧
        (walshTransform (linearHyperplaneRestriction f L 1) a).natAbs =
          2 ^ ((n + 1) / 2)) ∨
      ((walshTransform (linearHyperplaneRestriction f L 0) a).natAbs =
          2 ^ ((n + 1) / 2) ∧
        walshTransform (linearHyperplaneRestriction f L 1) a = 0)

/-- Carlet Theorem 11 for a fixed linear hyperplane: in even ambient
dimension at least four, bentness is equivalent to complementary restriction
spectra with values `0` and `±2^((n+1)/2)`. -/
theorem isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1))
    (_hnEven : Even (n + 1)) (_hnFour : 4 ≤ n + 1) :
    IsBent f ↔ HasComplementaryHyperplaneRestrictionSpectra f L := by
  let g : BooleanFunction (n + 1) := f ∘ L
  have hbentReindex : IsBent g ↔ IsBent f := by
    simpa [g] using isBent_comp_affineEquiv_iff f L.toAffineEquiv
  constructor
  · intro hf a
    have hg : IsBent g := hbentReindex.mpr hf
    have hzero := walshTransform_append_singletonF₂Cube g a 0
    have hone := walshTransform_append_singletonF₂Cube g a 1
    simp [bitSignInt_eq_if_one] at hzero hone
    have hzeroMagnitude :=
      natAbs_walshTransform_eq_two_pow_half_of_isBent g hg
        (Fin.append a (singletonF₂Cube 0))
    have honeMagnitude :=
      natAbs_walshTransform_eq_two_pow_half_of_isBent g hg
        (Fin.append a (singletonF₂Cube 1))
    have hpowCast :
        ((2 ^ ((n + 1) / 2) : ℕ) : ℤ) =
          (2 : ℤ) ^ ((n + 1) / 2) := by
      norm_num
    rcases Int.natAbs_eq_iff.mp hzeroMagnitude with hzeroPos | hzeroNeg
    · rcases Int.natAbs_eq_iff.mp honeMagnitude with honePos | honeNeg
      · right
        rw [hpowCast] at hzeroPos honePos
        clear hzeroMagnitude honeMagnitude
        constructor
        · rw [show walshTransform (linearHyperplaneRestriction f L 0) a =
              (2 ^ ((n + 1) / 2) : ℤ) by
            change walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a = _
            omega]
          simp
        · change walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a = 0
          omega
      · left
        rw [hpowCast] at hzeroPos honeNeg
        clear hzeroMagnitude honeMagnitude
        constructor
        · change walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a = 0
          omega
        · rw [show walshTransform (linearHyperplaneRestriction f L 1) a =
              (2 ^ ((n + 1) / 2) : ℤ) by
            change walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a = _
            omega]
          simp
    · rcases Int.natAbs_eq_iff.mp honeMagnitude with honePos | honeNeg
      · left
        rw [hpowCast] at hzeroNeg honePos
        clear hzeroMagnitude honeMagnitude
        constructor
        · change walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a = 0
          omega
        · rw [show walshTransform (linearHyperplaneRestriction f L 1) a =
              -((2 ^ ((n + 1) / 2) : ℤ)) by
            change walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a = _
            omega]
          simp
      · right
        rw [hpowCast] at hzeroNeg honeNeg
        clear hzeroMagnitude honeMagnitude
        constructor
        · rw [show walshTransform (linearHyperplaneRestriction f L 0) a =
              -((2 ^ ((n + 1) / 2) : ℤ)) by
            change walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a = _
            omega]
          simp
        · change walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a = 0
          omega
  · intro hrestrictions
    apply hbentReindex.mp
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half g).2
    intro u
    let p := (Fin.appendEquiv n 1).symm u
    let a : FABL.F₂Cube n := p.1
    let b : FABL.𝔽₂ := p.2 0
    have htail : p.2 = singletonF₂Cube b := by
      funext i
      fin_cases i
      rfl
    have hu : Fin.append a (singletonF₂Cube b) = u := by
      rw [← htail]
      exact (Fin.appendEquiv n 1).apply_symm_apply u
    rw [← hu, walshTransform_append_singletonF₂Cube]
    rcases hrestrictions a with hright | hleft
    · change
        walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a = 0 ∧
          (walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a).natAbs =
            2 ^ ((n + 1) / 2) at hright
      rw [hright.1, zero_add, Int.natAbs_mul, hright.2]
      rw [bitSignInt_eq_if_one]
      split <;> simp
    · change
        (walshTransform (firstBlockSlice g (singletonF₂Cube 0)) a).natAbs =
            2 ^ ((n + 1) / 2) ∧
          walshTransform (firstBlockSlice g (singletonF₂Cube 1)) a = 0 at hleft
      rw [hleft.2, mul_zero, add_zero, hleft.1]

/-- The Boolean function obtained by placing `h₀` and `h₁` on the two
cosets of the standard coordinate hyperplane. -/
def hyperplaneExtension
    (h₀ h₁ : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun z ↦
    let p := (Fin.appendEquiv n 1).symm z
    if p.2 0 = 0 then h₀ p.1 else h₁ p.1

@[simp] theorem hyperplaneExtension_append_singletonF₂Cube
    (h₀ h₁ : BooleanFunction n) (x : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    hyperplaneExtension h₀ h₁ (Fin.append x (singletonF₂Cube b)) =
      if b = 0 then h₀ x else h₁ x := by
  simp [hyperplaneExtension, singletonF₂Cube]

@[simp] theorem linearHyperplaneRestriction_hyperplaneExtension_refl
    (h₀ h₁ : BooleanFunction n) (b : FABL.𝔽₂) :
    linearHyperplaneRestriction (hyperplaneExtension h₀ h₁)
        (LinearEquiv.refl FABL.𝔽₂ _) b =
      if b = 0 then h₀ else h₁ := by
  funext x
  by_cases hb : b = 0 <;>
    simp [linearHyperplaneRestriction, firstBlockSlice, hb]

/-- Complementary Walsh spectra of amplitude `2^((n+1)/2)` give a bent
extension across the standard hyperplane. -/
theorem isBent_hyperplaneExtension_of_complementaryWalshSpectra
    (h₀ h₁ : BooleanFunction n)
    (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1)
    (hspectra : ∀ a : FABL.F₂Cube n,
      (walshTransform h₀ a = 0 ∧
          (walshTransform h₁ a).natAbs = 2 ^ ((n + 1) / 2)) ∨
        ((walshTransform h₀ a).natAbs = 2 ^ ((n + 1) / 2) ∧
          walshTransform h₁ a = 0)) :
    IsBent (hyperplaneExtension h₀ h₁) := by
  apply (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
    (hyperplaneExtension h₀ h₁) (LinearEquiv.refl FABL.𝔽₂ _)
      hnEven hnFour).2
  intro a
  simpa using hspectra a

/-- In Theorem 11, a bent function has the complementary restriction property
for every linear hyperplane coordinate system. -/
theorem isBent_iff_forall_hasComplementaryHyperplaneRestrictionSpectra
    (f : BooleanFunction (n + 1))
    (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1) :
    IsBent f ↔
      ∀ L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1),
        HasComplementaryHyperplaneRestrictionSpectra f L := by
  constructor
  · intro hf L
    exact (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
      f L hnEven hnFour).mp hf
  · intro h
    exact (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
      f (LinearEquiv.refl FABL.𝔽₂ _) hnEven hnFour).mpr
        (h (LinearEquiv.refl FABL.𝔽₂ _))

/-- In Theorem 11, it is enough that one linear hyperplane coordinate system
has complementary restriction spectra. -/
theorem isBent_iff_exists_hasComplementaryHyperplaneRestrictionSpectra
    (f : BooleanFunction (n + 1))
    (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1) :
    IsBent f ↔
      ∃ L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1),
        HasComplementaryHyperplaneRestrictionSpectra f L := by
  constructor
  · intro hf
    refine ⟨LinearEquiv.refl FABL.𝔽₂ _, ?_⟩
    exact (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
      f (LinearEquiv.refl FABL.𝔽₂ _) hnEven hnFour).mp hf
  · rintro ⟨L, hL⟩
    exact (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
      f L hnEven hnFour).mpr hL

/-- Each affine-hyperplane restriction of a bent function in even ambient
dimension at least four is plateaued with the optimal odd-dimensional
amplitude. -/
theorem hasPlateauedWalshAmplitude_linearHyperplaneRestriction_of_isBent
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1))
    (hf : IsBent f) (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1)
    (b : FABL.𝔽₂) :
    HasPlateauedWalshAmplitude (linearHyperplaneRestriction f L b)
      (2 ^ ((n + 1) / 2)) := by
  refine ⟨by positivity, fun a ↦ ?_⟩
  have hspectra :=
    (isBent_iff_hasComplementaryHyperplaneRestrictionSpectra
      f L hnEven hnFour).mp hf a
  fin_cases b
  · exact hspectra.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  · exact hspectra.elim (fun h ↦ Or.inr h.2) (fun h ↦ Or.inl h.2)

/-- Every affine-hyperplane restriction of a bent function is plateaued. -/
theorem isPlateaued_linearHyperplaneRestriction_of_isBent
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1))
    (hf : IsBent f) (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1)
    (b : FABL.𝔽₂) :
    IsPlateaued (linearHyperplaneRestriction f L b) :=
  ⟨2 ^ ((n + 1) / 2),
    hasPlateauedWalshAmplitude_linearHyperplaneRestriction_of_isBent
      f L hf hnEven hnFour b⟩

/-- The affine-hyperplane restrictions of an even-dimensional bent function
have optimal odd-dimensional nonlinearity. -/
theorem nonlinearity_linearHyperplaneRestriction_of_isBent
    (f : BooleanFunction (n + 1))
    (L : FABL.F₂Cube (n + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (n + 1))
    (hf : IsBent f) (hnEven : Even (n + 1)) (hnFour : 4 ≤ n + 1)
    (b : FABL.𝔽₂) :
    nonlinearity (linearHyperplaneRestriction f L b) =
      2 ^ (n - 1) - 2 ^ ((n - 1) / 2) := by
  let h := linearHyperplaneRestriction f L b
  have hamplitude :=
    hasPlateauedWalshAmplitude_linearHyperplaneRestriction_of_isBent
      f L hf hnEven hnFour b
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude h
  rw [maxWalshMagnitude_eq_of_hasPlateauedWalshAmplitude h
    (2 ^ ((n + 1) / 2)) hamplitude] at hrelation
  rcases hnEven with ⟨k, hk⟩
  have hhalf : (n + 1) / 2 = (n - 1) / 2 + 1 := by
    omega
  have hdim : n = (n - 1) + 1 := by omega
  have hpowHalf :
      2 ^ ((n + 1) / 2) = 2 * 2 ^ ((n - 1) / 2) := by
    rw [hhalf, pow_succ]
    omega
  have hpowDimension : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [hdim, pow_succ]
    omega
  rw [hpowHalf, hpowDimension] at hrelation
  change nonlinearity h = 2 ^ (n - 1) - 2 ^ ((n - 1) / 2)
  omega

end CryptBoolean
