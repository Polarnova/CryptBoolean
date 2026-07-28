/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.LinearStructureNormalForm
public import CryptBoolean.Carlet.Chapter04.QuadraticPolar
public import CryptBoolean.Carlet.Chapter06.FourierUncertainty
public import CryptBoolean.Carlet.Chapter06.Plateaued

/-!
# Partially bent functions

Carlet Proposition 26: the support sizes of the autocorrelation and Walsh
spectra satisfy an uncertainty bound, with equality exactly for partially
bent functions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n m k : ℕ}

/-- The directions with nonzero autocorrelation. -/
noncomputable def autocorrelationSupport (f : BooleanFunction n) :
    Finset (FABL.F₂Cube n) :=
  pseudoBooleanSupport (autocorrelation f)

@[simp] theorem mem_autocorrelationSupport
    (f : BooleanFunction n) (b : FABL.F₂Cube n) :
    b ∈ autocorrelationSupport f ↔ autocorrelation f b ≠ 0 := by
  simp [autocorrelationSupport]

/-- Carlet's quantity `N_Δf`, the number of nonzero autocorrelation
coefficients. -/
noncomputable def nonzeroAutocorrelationCount (f : BooleanFunction n) : ℕ :=
  (autocorrelationSupport f).card

/-- Wiener--Khintchine identifies the Fourier support of the autocorrelation
with the raw Walsh support. -/
theorem rawFourierSupport_autocorrelation (f : BooleanFunction n) :
    rawFourierSupport (autocorrelation f) = walshSupport f := by
  classical
  ext u
  rw [mem_rawFourierSupport, mem_walshSupport,
    rawFourierTransform_autocorrelation]
  constructor
  · intro hsquare hzero
    rw [hzero, Int.cast_zero, zero_pow (by norm_num)] at hsquare
    exact hsquare rfl
  · intro hwalsh hsquare
    have hcast : (walshTransform f u : ℝ) = 0 := sq_eq_zero_iff.mp hsquare
    exact hwalsh (by exact_mod_cast hcast)

private theorem autocorrelation_ne_zero (f : BooleanFunction n) :
    autocorrelation f ≠ 0 := by
  apply Function.ne_iff.mpr
  refine ⟨0, ?_⟩
  rw [Pi.zero_apply, autocorrelation_zero]
  positivity

/-- Carlet Proposition 26, inequality (53). -/
theorem two_pow_le_nonzeroAutocorrelationCount_mul_card_walshSupport
    (f : BooleanFunction n) :
    2 ^ n ≤ nonzeroAutocorrelationCount f * (walshSupport f).card := by
  simpa only [nonzeroAutocorrelationCount, autocorrelationSupport,
    rawFourierSupport_autocorrelation] using
    two_pow_le_card_pseudoBooleanSupport_mul_card_rawFourierSupport
      (autocorrelation f) (autocorrelation_ne_zero f)

/-- A Boolean function is partially bent when every directional derivative
is balanced or constant. -/
def IsPartiallyBent (f : BooleanFunction n) : Prop :=
  ∀ b : FABL.F₂Cube n,
    IsBalanced (FABL.booleanDerivative f b) ∨ IsLinearStructure f b

/-- Every quadratic Boolean function is partially bent. -/
theorem isPartiallyBent_of_functionAlgebraicDegree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsPartiallyBent f := by
  intro a
  by_cases ha : a ∈ quadraticRadical f hdegree
  · right
    rw [← mem_linearKernel,
      ← quadraticRadical_eq_linearKernel f hdegree]
    exact ha
  · left
    exact isBalanced_booleanDerivative_of_not_mem_quadraticRadical
      f hdegree a ha

/-- A coordinate-free form of Carlet's complementary-subspace
decomposition. The second summand is affine with its constant absorbed into
the bent summand. -/
def HasBentAffineComplementDecomposition
    (f : BooleanFunction n) (m k : ℕ) : Prop :=
  ∃ (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
      (_hcomplement : IsCompl E E')
      (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
      (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E')
      (g : BooleanFunction m) (ε : FABL.F₂Cube k),
    IsBent g ∧
      ∀ (x : FABL.F₂Cube m) (y : FABL.F₂Cube k),
        f (eE x + eE' y) = g x + FABL.f₂DotProduct ε y

private noncomputable def complementCoordinateEquiv
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcomplement : IsCompl E E')
    (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
    (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E') :
    (FABL.F₂Cube m × FABL.F₂Cube k) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube n :=
  (LinearEquiv.prodCongr eE eE').trans
    (E.prodEquivOfIsCompl E' hcomplement)

@[simp] private theorem complementCoordinateEquiv_apply
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcomplement : IsCompl E E')
    (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
    (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E')
    (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
    complementCoordinateEquiv E E' hcomplement eE eE' (x, y) =
      eE x + eE' y :=
  rfl

private theorem booleanDerivative_complementRepresentation
    (f : BooleanFunction n)
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
    (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E')
    (g : BooleanFunction m) (ε : FABL.F₂Cube k)
    (hrepresentation :
      ∀ (x : FABL.F₂Cube m) (y : FABL.F₂Cube k),
        f (eE x + eE' y) = g x + FABL.f₂DotProduct ε y)
    (d : FABL.F₂Cube m) (z : FABL.F₂Cube k)
    (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
    FABL.booleanDerivative f (eE d + eE' z) (eE x + eE' y) =
      FABL.booleanDerivative g d x + FABL.f₂DotProduct ε z := by
  rw [FABL.booleanDerivative, FABL.booleanDerivative,
    hrepresentation x y]
  have hargument :
      (eE x : FABL.F₂Cube n) + (eE' y : FABL.F₂Cube n) +
          ((eE d : FABL.F₂Cube n) + (eE' z : FABL.F₂Cube n)) =
          (eE (x + d) : FABL.F₂Cube n) +
          (eE' (y + z) : FABL.F₂Cube n) := by
    simp only [map_add, Submodule.coe_add]
    abel
  rw [hargument, hrepresentation (x + d) (y + z)]
  simp only [FABL.f₂DotProduct, dotProduct_add]
  change
    (g x + ε ⬝ᵥ y) + (g (x + d) + (ε ⬝ᵥ y + ε ⬝ᵥ z)) =
      (g x + g (x + d)) + ε ⬝ᵥ z
  calc
    (g x + ε ⬝ᵥ y) + (g (x + d) + (ε ⬝ᵥ y + ε ⬝ᵥ z)) =
        (g x + g (x + d)) + ((ε ⬝ᵥ y + ε ⬝ᵥ y) + ε ⬝ᵥ z) := by
      abel
    _ = (g x + g (x + d)) + ε ⬝ᵥ z := by
      rw [ZModModule.add_self, zero_add]

private theorem autocorrelation_complementRepresentation
    (f : BooleanFunction n)
    (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hcomplement : IsCompl E E')
    (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
    (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E')
    (g : BooleanFunction m) (ε : FABL.F₂Cube k)
    (hrepresentation :
      ∀ (x : FABL.F₂Cube m) (y : FABL.F₂Cube k),
        f (eE x + eE' y) = g x + FABL.f₂DotProduct ε y)
    (d : FABL.F₂Cube m) (z : FABL.F₂Cube k) :
    autocorrelation f (eE d + eE' z) =
      (2 : ℝ) ^ k * FABL.vectorWalshCharacter ε z *
        autocorrelation g d := by
  classical
  let L := complementCoordinateEquiv E E' hcomplement eE eE'
  have hsign (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
      realSignView (FABL.booleanDerivative f (eE d + eE' z))
          (eE x + eE' y) =
        realSignView (FABL.booleanDerivative g d) x *
          FABL.vectorWalshCharacter ε z := by
    change FABL.signValue (FABL.signEncode
        (FABL.booleanDerivative f (eE d + eE' z) (eE x + eE' y))) =
      FABL.signValue (FABL.signEncode (FABL.booleanDerivative g d x)) *
        FABL.vectorWalshCharacter ε z
    rw [booleanDerivative_complementRepresentation
      f E E' eE eE' g ε hrepresentation d z x y]
    rw [FABL.signValue_signEncode_eq_binarySign,
      FABL.signValue_signEncode_eq_binarySign,
      AddChar.map_add_eq_mul, FABL.vectorWalshCharacter_apply]
  rw [autocorrelation]
  calc
    (∑ p, realSignView (FABL.booleanDerivative f (eE d + eE' z)) p) =
        ∑ q : FABL.F₂Cube m × FABL.F₂Cube k,
          realSignView (FABL.booleanDerivative f (eE d + eE' z)) (L q) := by
      symm
      exact Fintype.sum_equiv L.toEquiv
        (fun q ↦ realSignView
          (FABL.booleanDerivative f (eE d + eE' z)) (L q))
        (fun p ↦ realSignView
          (FABL.booleanDerivative f (eE d + eE' z)) p)
        (fun _ ↦ rfl)
    _ = ∑ x : FABL.F₂Cube m, ∑ y : FABL.F₂Cube k,
          realSignView (FABL.booleanDerivative f (eE d + eE' z))
            (eE x + eE' y) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ x : FABL.F₂Cube m, ∑ _y : FABL.F₂Cube k,
          realSignView (FABL.booleanDerivative g d) x *
            FABL.vectorWalshCharacter ε z := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact hsign x y
    _ = ∑ x : FABL.F₂Cube m,
          (2 : ℝ) ^ k *
            (realSignView (FABL.booleanDerivative g d) x *
              FABL.vectorWalshCharacter ε z) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_const, Finset.card_univ, card_f₂Cube,
        nsmul_eq_mul]
      norm_num
    _ = ∑ x : FABL.F₂Cube m,
          ((2 : ℝ) ^ k * FABL.vectorWalshCharacter ε z) *
            realSignView (FABL.booleanDerivative g d) x := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = (2 : ℝ) ^ k * FABL.vectorWalshCharacter ε z *
        ∑ x, realSignView (FABL.booleanDerivative g d) x := by
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ k * FABL.vectorWalshCharacter ε z *
        autocorrelation g d := rfl

/-- Every bent-plus-affine complementary decomposition is partially bent. -/
theorem HasBentAffineComplementDecomposition.isPartiallyBent
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) :
    IsPartiallyBent f := by
  classical
  rcases hf with
    ⟨E, E', hcomplement, eE, eE', g, ε, hg, hrepresentation⟩
  let L := complementCoordinateEquiv E E' hcomplement eE eE'
  intro b
  let q := L.symm b
  have hb : b = eE q.1 + eE' q.2 := by
    calc
      b = L q := (L.apply_symm_apply b).symm
      _ = eE q.1 + eE' q.2 := rfl
  by_cases hd : q.1 = 0
  · right
    refine ⟨FABL.f₂DotProduct ε q.2, fun p ↦ ?_⟩
    let r := L.symm p
    have hp : p = eE r.1 + eE' r.2 := by
      calc
        p = L r := (L.apply_symm_apply p).symm
        _ = eE r.1 + eE' r.2 := rfl
    rw [hp, hb]
    have hderivative := booleanDerivative_complementRepresentation
      f E E' eE eE' g ε hrepresentation q.1 q.2 r.1 r.2
    rw [hd] at hderivative
    simp only [FABL.booleanDerivative, add_zero] at hderivative
    rw [ZModModule.add_self, zero_add] at hderivative
    simpa [hd, FABL.booleanDerivative] using hderivative
  · left
    apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f b).mpr
    rw [hb, autocorrelation_complementRepresentation
      f E E' hcomplement eE eE' g ε hrepresentation q.1 q.2]
    have hbalanced :=
      (isBent_iff_forall_nonzero_derivative_isBalanced g).mp hg q.1 hd
    rw [(isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
      g q.1).mp hbalanced, mul_zero]

/-- In a bent-plus-affine complementary decomposition, the affine summand is
exactly the linear kernel. -/
theorem HasBentAffineComplementDecomposition.linearKernel_eq_affineSubspace
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) :
    ∃ (E E' : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
        (_hcomplement : IsCompl E E')
        (eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E)
        (eE' : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] E')
        (g : BooleanFunction m) (ε : FABL.F₂Cube k),
      IsBent g ∧ linearKernel f = E' ∧
        ∀ (x : FABL.F₂Cube m) (y : FABL.F₂Cube k),
          f (eE x + eE' y) = g x + FABL.f₂DotProduct ε y := by
  classical
  rcases hf with
    ⟨E, E', hcomplement, eE, eE', g, ε, hg, hrepresentation⟩
  let L := complementCoordinateEquiv E E' hcomplement eE eE'
  have hkernel : linearKernel f = E' := by
    apply le_antisymm
    · intro b hb
      let q := L.symm b
      have hbCoordinates : b = eE q.1 + eE' q.2 := by
        calc
          b = L q := (L.apply_symm_apply b).symm
          _ = eE q.1 + eE' q.2 := rfl
      have hqzero : q.1 = 0 := by
        by_contra hq
        have hbalanced :=
          (isBent_iff_forall_nonzero_derivative_isBalanced g).mp hg q.1 hq
        have hzeroG :=
          (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
            g q.1).mp hbalanced
        have hfactor := autocorrelation_complementRepresentation
          f E E' hcomplement eE eE' g ε hrepresentation q.1 q.2
        rw [hzeroG, mul_zero] at hfactor
        have hzeroF : autocorrelation f b = 0 := by
          rw [hbCoordinates]
          exact hfactor
        have hsquare := autocorrelation_sq_of_mem_linearKernel f b hb
        rw [hzeroF, zero_pow (by norm_num)] at hsquare
        exact (by positivity : (0 : ℝ) ≠ (2 : ℝ) ^ (2 * n)) hsquare
      rw [hbCoordinates, hqzero]
      simp
    · intro b hb
      obtain ⟨z, hz⟩ := eE'.surjective ⟨b, hb⟩
      have hzValue := congrArg Subtype.val hz
      have hzValue' : (eE' z : FABL.F₂Cube n) = b := by
        simpa using hzValue
      rw [← hzValue']
      refine ⟨FABL.f₂DotProduct ε z, fun p ↦ ?_⟩
      let q := L.symm p
      have hp : p = eE q.1 + eE' q.2 := by
        calc
          p = L q := (L.apply_symm_apply p).symm
          _ = eE q.1 + eE' q.2 := rfl
      rw [hp]
      have hderivative := booleanDerivative_complementRepresentation
        f E E' eE eE' g ε hrepresentation 0 z q.1 q.2
      simp only [map_zero, Submodule.coe_zero, zero_add,
        FABL.booleanDerivative, add_zero] at hderivative
      rw [ZModModule.add_self, zero_add] at hderivative
      exact hderivative
  exact ⟨E, E', hcomplement, eE, eE', g, ε, hg,
    hkernel, hrepresentation⟩

/-- Complementary coordinate dimensions add to the ambient dimension. -/
theorem HasBentAffineComplementDecomposition.dimensions_add
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) :
    m + k = n := by
  rcases hf with
    ⟨E, E', hcomplement, eE, eE', g, ε, hg, hrepresentation⟩
  let L := complementCoordinateEquiv E E' hcomplement eE eE'
  simpa [L, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card] using L.finrank_eq

/-- The bent summand has even dimension. -/
theorem HasBentAffineComplementDecomposition.even_bentDimension
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) : Even m := by
  rcases hf with
    ⟨E, E', hcomplement, eE, eE', g, ε, hg, hrepresentation⟩
  exact even_of_isBent g hg

/-- Every partially bent function decomposes over complementary subspaces as
a bent function plus an affine function. -/
theorem exists_hasBentAffineComplementDecomposition_of_isPartiallyBent
    (f : BooleanFunction n) (hf : IsPartiallyBent f) :
    ∃ m k : ℕ, HasBentAffineComplementDecomposition f m k := by
  classical
  let H := linearKernel f
  obtain ⟨E, hHE⟩ := H.exists_isCompl
  have hcomplement : IsCompl E H := hHE.symm
  let m := Module.finrank FABL.𝔽₂ E
  let k := Module.finrank FABL.𝔽₂ H
  let eE : FABL.F₂Cube m ≃ₗ[FABL.𝔽₂] E :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [m, Module.finrank_fintype_fun_eq_card])
  let eH : FABL.F₂Cube k ≃ₗ[FABL.𝔽₂] H :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [k, Module.finrank_fintype_fun_eq_card])
  let g : BooleanFunction m := fun x ↦ f (eE x)
  let q : FABL.F₂Cube k → FABL.𝔽₂ :=
    fun y ↦ f (eH y) + f 0
  have hq : FABL.IsF₂Linear q := by
    intro y z
    obtain ⟨δ, hδ⟩ :=
      (mem_linearKernel f (eH z)).mp (eH z).property
    have hderivative := (hδ (eH y)).trans (hδ 0).symm
    rw [FABL.booleanDerivative, FABL.booleanDerivative] at hderivative
    simp only [zero_add] at hderivative
    change f (eH (y + z)) + f 0 =
      (f (eH y) + f 0) + (f (eH z) + f 0)
    rw [map_add]
    calc
      f (eH y + eH z) + f 0 =
          (f (eH y) + f (eH y)) + (f (eH y + eH z) + f 0) := by
        rw [ZModModule.add_self, zero_add]
      _ = f (eH y) + (f (eH y) + f (eH y + eH z)) + f 0 := by
        abel
      _ = f (eH y) + (f 0 + f (eH z)) + f 0 := by
        rw [hderivative]
      _ = (f (eH y) + f 0) + (f (eH z) + f 0) := by
        abel
  obtain ⟨ε, hε⟩ := (FABL.isF₂Linear_iff_exists_dotProduct q).mp hq
  have hrepresentation
      (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
      f (eE x + eH y) = g x + FABL.f₂DotProduct ε y := by
    obtain ⟨δ, hδ⟩ :=
      (mem_linearKernel f (eH y)).mp (eH y).property
    have hderivative := (hδ (eE x)).trans (hδ 0).symm
    rw [FABL.booleanDerivative, FABL.booleanDerivative] at hderivative
    simp only [zero_add] at hderivative
    change f (eE x + eH y) = f (eE x) + FABL.f₂DotProduct ε y
    rw [← hε y]
    change f (eE x + eH y) = f (eE x) + (f (eH y) + f 0)
    calc
      f (eE x + eH y) =
          (f (eE x) + f (eE x)) + f (eE x + eH y) := by
        rw [ZModModule.add_self, zero_add]
      _ = f (eE x) + (f (eE x) + f (eE x + eH y)) := by
        abel
      _ = f (eE x) + (f 0 + f (eH y)) := by
        rw [hderivative]
      _ = f (eE x) + (f (eH y) + f 0) := by
        abel
  have hg : IsBent g := by
    apply (isBent_iff_forall_nonzero_derivative_isBalanced g).mpr
    intro d hd
    have hdirectionNe : (eE d : FABL.F₂Cube n) ≠ 0 := by
      intro hzero
      apply hd
      apply eE.injective
      exact Subtype.ext (by simpa using hzero)
    have hdirectionNotKernel : (eE d : FABL.F₂Cube n) ∉ H := by
      intro hkernel
      have hintersection : (eE d : FABL.F₂Cube n) ∈ E ⊓ H :=
        ⟨(eE d).property, hkernel⟩
      have hbot : (eE d : FABL.F₂Cube n) ∈ (⊥ :
          Submodule FABL.𝔽₂ (FABL.F₂Cube n)) := by
        rw [← hcomplement.inf_eq_bot]
        exact hintersection
      exact hdirectionNe (by simpa using hbot)
    rcases hf (eE d) with hbalanced | hlinear
    · apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero g d).mpr
      have hzero :=
        (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
          f (eE d)).mp hbalanced
      have hfactor := autocorrelation_complementRepresentation
        f E H hcomplement eE eH g ε hrepresentation d 0
      simp only [map_zero, Submodule.coe_zero, add_zero] at hfactor
      rw [AddChar.map_zero_eq_one, mul_one] at hfactor
      rw [hzero] at hfactor
      have hpower : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      nlinarith
    · exact (hdirectionNotKernel hlinear).elim
  exact ⟨m, k, E, H, hcomplement, eE, eH, g, ε, hg, hrepresentation⟩

/-- Carlet Proposition 26's structural characterization. -/
theorem isPartiallyBent_iff_exists_bentAffineComplementDecomposition
    (f : BooleanFunction n) :
    IsPartiallyBent f ↔
      ∃ m k : ℕ, HasBentAffineComplementDecomposition f m k := by
  constructor
  · exact exists_hasBentAffineComplementDecomposition_of_isPartiallyBent f
  · rintro ⟨m, k, h⟩
    exact h.isPartiallyBent

private theorem booleanFunction_eq_one_of_hammingWeight_eq_two_pow
    (g : BooleanFunction n) (hweight : hammingWeight g = 2 ^ n) :
    g = 1 := by
  have hsupportCard : (support g).card = Fintype.card (FABL.F₂Cube n) := by
    simpa only [hammingWeight_eq_card_support, card_f₂Cube] using hweight
  have hsupport : support g = Finset.univ :=
    Finset.eq_univ_of_card (s := support g) hsupportCard
  funext x
  have hx : x ∈ support g := by rw [hsupport]; exact Finset.mem_univ x
  exact (mem_support g x).mp hx

/-- A direction is a linear structure exactly when its autocorrelation has
maximal absolute value. -/
theorem isLinearStructure_iff_abs_autocorrelation_eq_two_pow
    (f : BooleanFunction n) (b : FABL.F₂Cube n) :
    IsLinearStructure f b ↔ |autocorrelation f b| = (2 : ℝ) ^ n := by
  constructor
  · intro hlinear
    have hsquare := autocorrelation_sq_of_mem_linearKernel f b hlinear
    have hsquare' :
        autocorrelation f b ^ 2 = ((2 : ℝ) ^ n) ^ 2 := by
      calc
        autocorrelation f b ^ 2 = (2 : ℝ) ^ (2 * n) := hsquare
        _ = ((2 : ℝ) ^ n) ^ 2 := by rw [two_mul, pow_add, pow_two]
    rw [← sq_abs] at hsquare'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare' with heq | heq
    · exact heq
    · nlinarith [abs_nonneg (autocorrelation f b),
        show 0 < (2 : ℝ) ^ n by positivity]
  · intro habs
    rcases eq_or_eq_neg_of_abs_eq habs with hpositive | hnegative
    · have hformula := autocorrelation_eq_two_pow_sub_two_derivative_weight f b
      have hweightReal :
          (hammingWeight (FABL.booleanDerivative f b) : ℝ) = 0 := by
        rw [hpositive] at hformula
        nlinarith
      have hweight : hammingWeight (FABL.booleanDerivative f b) = 0 := by
        exact_mod_cast hweightReal
      have hzero : FABL.booleanDerivative f b = 0 :=
        hammingNorm_eq_zero.mp hweight
      exact ⟨0, fun x ↦ congrFun hzero x⟩
    · have hformula := autocorrelation_eq_two_pow_sub_two_derivative_weight f b
      have hweightReal :
          (hammingWeight (FABL.booleanDerivative f b) : ℝ) =
            (2 : ℝ) ^ n := by
        rw [hnegative] at hformula
        nlinarith
      have hweight :
          hammingWeight (FABL.booleanDerivative f b) = 2 ^ n := by
        exact_mod_cast hweightReal
      have hone : FABL.booleanDerivative f b = 1 :=
        booleanFunction_eq_one_of_hammingWeight_eq_two_pow _ hweight
      exact ⟨1, fun x ↦ congrFun hone x⟩

/-- Equality in Carlet's support inequality forces every derivative to be
balanced or constant. -/
theorem isPartiallyBent_of_nonzeroAutocorrelationCount_mul_card_walshSupport_eq
    (f : BooleanFunction n)
    (hproduct :
      nonzeroAutocorrelationCount f * (walshSupport f).card = 2 ^ n) :
    IsPartiallyBent f := by
  classical
  have hproduct' :
      (pseudoBooleanSupport (autocorrelation f)).card *
          (rawFourierSupport (autocorrelation f)).card = 2 ^ n := by
    simpa only [nonzeroAutocorrelationCount, autocorrelationSupport,
      rawFourierSupport_autocorrelation] using hproduct
  obtain ⟨c, hc, H, a, u, hrepresentation⟩ :=
    isModulatedAffineFlatIndicator_of_card_support_mul_card_rawFourierSupport_eq
      (autocorrelation f) (autocorrelation_ne_zero f) hproduct'
  have hzeroFlat :
      0 ∈ FABL.binaryAffineSubspace H a := by
    by_contra hnot
    have hzero := congrFun hrepresentation 0
    rw [autocorrelation_zero] at hzero
    simp [FABL.setIndicator, hnot] at hzero
  have hcValue : c = (2 : ℝ) ^ n := by
    have hzero := congrFun hrepresentation 0
    rw [autocorrelation_zero] at hzero
    simpa [FABL.setIndicator, hzeroFlat] using hzero.symm
  intro b
  by_cases hzero : autocorrelation f b = 0
  · exact Or.inl
      ((isBalanced_booleanDerivative_iff_autocorrelation_eq_zero f b).mpr hzero)
  · right
    apply (isLinearStructure_iff_abs_autocorrelation_eq_two_pow f b).mpr
    have hbFlat : b ∈ FABL.binaryAffineSubspace H a := by
      by_contra hnot
      have hb := congrFun hrepresentation b
      have hindicator : FABL.setIndicator
          (FABL.binaryAffineSubspace H a : Set (FABL.F₂Cube n)) b = 0 := by
        exact Set.indicator_of_notMem hnot _
      rw [hindicator, mul_zero] at hb
      exact hzero hb
    rw [congrFun hrepresentation b, hcValue]
    simp [FABL.setIndicator, hbFlat, abs_mul]

private theorem card_autocorrelationSupport_eq_natCard_linearKernel_of_isPartiallyBent
    (f : BooleanFunction n) (hf : IsPartiallyBent f) :
    (autocorrelationSupport f).card = Nat.card (linearKernel f) := by
  classical
  let kernelDirections :=
    Finset.univ.filter (fun b : FABL.F₂Cube n ↦ b ∈ linearKernel f)
  have hsupport : autocorrelationSupport f = kernelDirections := by
    ext b
    simp only [mem_autocorrelationSupport, kernelDirections,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hnonzero
      rcases hf b with hbalanced | hlinear
      · exact (hnonzero
          ((isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
            f b).mp hbalanced)).elim
      · exact hlinear
    · intro hlinear hzero
      have habs :=
        (isLinearStructure_iff_abs_autocorrelation_eq_two_pow f b).mp hlinear
      rw [hzero, abs_zero] at habs
      exact (by positivity : (0 : ℝ) ≠ (2 : ℝ) ^ n) habs
  rw [hsupport]
  simp [kernelDirections, Fintype.card_subtype,
    Nat.card_eq_fintype_card]

private theorem card_walshSupport_le_natCard_perpendicular_linearKernel
    (f : BooleanFunction n) :
    (walshSupport f).card ≤
      Nat.card (FABL.perpendicularSubspace (linearKernel f)) := by
  classical
  have hlower :=
    two_pow_le_nonzeroAutocorrelationCount_mul_card_walshSupport f
  have hwalshPositive : 0 < (walshSupport f).card := by
    by_contra hnot
    have hzero : (walshSupport f).card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, mul_zero] at hlower
    have hpow : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hwalshPositive
  have hshiftMem (v : walshSupport f) :
      u + v.1 ∈ FABL.perpendicularSubspace (linearKernel f) := by
    rw [FABL.mem_perpendicularSubspace_iff]
    intro b hb
    by_cases hbzero : b = 0
    · subst b
      simp [FABL.f₂DotProduct]
    obtain ⟨ε, hε⟩ := (mem_linearKernel f b).mp hb
    by_cases hεzero : ε = 0
    · have hderivative : FABL.booleanDerivative f b = 0 := by
        funext x
        simpa [hεzero] using hε x
      have hsubset :=
        (booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane
          f b hbzero).mp hderivative
      have hdotU : FABL.f₂DotProduct u b = 0 :=
        (mem_walshHyperplane_iff b u).mp (hsubset hu)
      have hdotV : FABL.f₂DotProduct v.1 b = 0 :=
        (mem_walshHyperplane_iff b v.1).mp (hsubset v.2)
      rw [FABL.f₂DotProduct, add_dotProduct]
      change FABL.f₂DotProduct u b + FABL.f₂DotProduct v.1 b = 0
      rw [hdotU, hdotV, add_zero]
    · have hεone : ε = 1 := Fin.eq_one_of_ne_zero ε hεzero
      have hderivative : FABL.booleanDerivative f b = 1 := by
        funext x
        simpa [hεone] using hε x
      have hsubset :=
        (booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl
          f b hbzero).mp hderivative
      have hdotU : FABL.f₂DotProduct u b = 1 := by
        apply Fin.eq_one_of_ne_zero
        intro hzero
        exact (hsubset hu) ((mem_walshHyperplane_iff b u).mpr hzero)
      have hdotV : FABL.f₂DotProduct v.1 b = 1 := by
        apply Fin.eq_one_of_ne_zero
        intro hzero
        exact (hsubset v.2) ((mem_walshHyperplane_iff b v.1).mpr hzero)
      rw [FABL.f₂DotProduct, add_dotProduct]
      change FABL.f₂DotProduct u b + FABL.f₂DotProduct v.1 b = 0
      rw [hdotU, hdotV, ZModModule.add_self]
  let toPerpendicular : walshSupport f →
      FABL.perpendicularSubspace (linearKernel f) :=
    fun v ↦ ⟨u + v.1, hshiftMem v⟩
  have hinjective : Function.Injective toPerpendicular := by
    intro v w hvw
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hvw)
  letI : Fintype (FABL.perpendicularSubspace (linearKernel f)) :=
    Fintype.ofFinite _
  have hcard : Fintype.card (walshSupport f) ≤
      Fintype.card (FABL.perpendicularSubspace (linearKernel f)) :=
    Fintype.card_le_of_injective toPerpendicular hinjective
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hcard

/-- If every derivative is balanced or constant, equality holds in Carlet's
support inequality. -/
theorem nonzeroAutocorrelationCount_mul_card_walshSupport_eq_of_isPartiallyBent
    (f : BooleanFunction n) (hf : IsPartiallyBent f) :
    nonzeroAutocorrelationCount f * (walshSupport f).card = 2 ^ n := by
  have hcount :=
    card_autocorrelationSupport_eq_natCard_linearKernel_of_isPartiallyBent f hf
  have hwalsh :=
    card_walshSupport_le_natCard_perpendicular_linearKernel f
  have hlower :=
    two_pow_le_nonzeroAutocorrelationCount_mul_card_walshSupport f
  have hupper :
      nonzeroAutocorrelationCount f * (walshSupport f).card ≤ 2 ^ n := by
    rw [nonzeroAutocorrelationCount, hcount]
    calc
      Nat.card (linearKernel f) * (walshSupport f).card ≤
          Nat.card (linearKernel f) *
            Nat.card (FABL.perpendicularSubspace (linearKernel f)) :=
        Nat.mul_le_mul_left _ hwalsh
      _ = 2 ^ n := by
        have hrank : Module.finrank FABL.𝔽₂ (linearKernel f) ≤ n := by
          simpa using (linearKernel f).finrank_le
        rw [FABL.card_submodule_eq_two_pow_finrank,
          FABL.card_submodule_eq_two_pow_finrank,
          FABL.finrank_perpendicularSubspace, ← pow_add,
          Nat.add_sub_of_le hrank]
  omega

/-- Carlet Proposition 26: equality in (53) is equivalent to partial
bentness. -/
theorem nonzeroAutocorrelationCount_mul_card_walshSupport_eq_two_pow_iff
    (f : BooleanFunction n) :
    nonzeroAutocorrelationCount f * (walshSupport f).card = 2 ^ n ↔
      IsPartiallyBent f := by
  constructor
  · exact
      isPartiallyBent_of_nonzeroAutocorrelationCount_mul_card_walshSupport_eq f
  · exact
      nonzeroAutocorrelationCount_mul_card_walshSupport_eq_of_isPartiallyBent f

/-- The autocorrelation support has the cardinality of the affine summand. -/
theorem HasBentAffineComplementDecomposition.nonzeroAutocorrelationCount_eq
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) :
    nonzeroAutocorrelationCount f = 2 ^ k := by
  classical
  rcases hf.linearKernel_eq_affineSubspace with
    ⟨E, E', hcomplement, eE, eE', g, ε, hg, hkernel, hrepresentation⟩
  letI : Fintype E' := Fintype.ofFinite E'
  have hcount :=
    card_autocorrelationSupport_eq_natCard_linearKernel_of_isPartiallyBent
      f hf.isPartiallyBent
  rw [nonzeroAutocorrelationCount, hcount, hkernel]
  calc
    Nat.card E' = Fintype.card E' := Nat.card_eq_fintype_card
    _ = Fintype.card (FABL.F₂Cube k) :=
      (Fintype.card_congr eE'.toEquiv).symm
    _ = 2 ^ k := card_f₂Cube k

/-- Every partially bent function has a flat nonzero Walsh spectrum. -/
theorem hasPlateauedWalshSpectrum_of_isPartiallyBent
    (f : BooleanFunction n) (hf : IsPartiallyBent f) :
    HasPlateauedWalshSpectrum f := by
  classical
  have hindicator :
      sumOfSquaresIndicator f =
        (nonzeroAutocorrelationCount f : ℝ) * ((2 : ℝ) ^ n) ^ 2 := by
    rw [sumOfSquaresIndicator]
    calc
      (∑ b, autocorrelation f b ^ 2) =
          ∑ b ∈ autocorrelationSupport f, autocorrelation f b ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b _hb hnot
        have hzero : autocorrelation f b = 0 := by
          exact not_ne_iff.mp
            (by simpa only [mem_autocorrelationSupport] using hnot)
        simp [hzero]
      _ = ∑ _b ∈ autocorrelationSupport f, ((2 : ℝ) ^ n) ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        have hnonzero : autocorrelation f b ≠ 0 :=
          (mem_autocorrelationSupport f b).mp hb
        have hlinear : IsLinearStructure f b := by
          rcases hf b with hbalanced | hlinear
          · exact (hnonzero
              ((isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
                f b).mp hbalanced)).elim
          · exact hlinear
        have habs :=
          (isLinearStructure_iff_abs_autocorrelation_eq_two_pow f b).mp hlinear
        rw [← sq_abs, habs]
      _ = (nonzeroAutocorrelationCount f : ℝ) *
          ((2 : ℝ) ^ n) ^ 2 := by
        simp [nonzeroAutocorrelationCount]
  have hcountNat :=
    nonzeroAutocorrelationCount_mul_card_walshSupport_eq_of_isPartiallyBent
      f hf
  have hcountReal :
      (nonzeroAutocorrelationCount f : ℝ) *
          ((walshSupport f).card : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hcountNat
  apply (sumOfSquaresIndicator_mul_card_walshSupport_eq_two_pow_three_mul_n_iff_plateaued
    f).mp
  rw [hindicator]
  calc
    ((nonzeroAutocorrelationCount f : ℝ) * ((2 : ℝ) ^ n) ^ 2) *
        ((walshSupport f).card : ℝ) =
        ((nonzeroAutocorrelationCount f : ℝ) *
          ((walshSupport f).card : ℝ)) * ((2 : ℝ) ^ n) ^ 2 := by
      ring
    _ = (2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ 2 := by
      rw [hcountReal]
    _ = (2 : ℝ) ^ (3 * n) := by
      rw [show 3 * n = n * 3 by omega, pow_mul]
      ring

/-- Every partially bent function is plateaued. -/
theorem IsPartiallyBent.isPlateaued
    {f : BooleanFunction n} (hf : IsPartiallyBent f) :
    IsPlateaued f :=
  (isPlateaued_iff_hasPlateauedWalshSpectrum f).2
    (hasPlateauedWalshSpectrum_of_isPartiallyBent f hf)

/-- In particular, every quadratic Boolean function is plateaued. -/
theorem isPlateaued_of_functionAlgebraicDegree_le_two
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    IsPlateaued f :=
  (isPartiallyBent_of_functionAlgebraicDegree_le_two f hdegree).isPlateaued

/-- In a decomposition with bent dimension `m` and affine dimension `k`,
every nonzero Walsh coefficient has magnitude `2^(k + m/2)`. -/
theorem HasBentAffineComplementDecomposition.hasPlateauedWalshAmplitude
    {f : BooleanFunction n} {m k : ℕ}
    (hf : HasBentAffineComplementDecomposition f m k) :
    HasPlateauedWalshAmplitude f (2 ^ (k + m / 2)) := by
  have hpartial := hf.isPartiallyBent
  have hplateaued : IsPlateaued f :=
    (isPlateaued_iff_hasPlateauedWalshSpectrum f).mpr
      (hasPlateauedWalshSpectrum_of_isPartiallyBent f hpartial)
  rcases hplateaued with ⟨amplitude, hamplitude⟩
  have hdimension := hf.dimensions_add
  have hcount := hf.nonzeroAutocorrelationCount_eq
  have hsupportProduct :=
    nonzeroAutocorrelationCount_mul_card_walshSupport_eq_of_isPartiallyBent
      f hpartial
  rw [hcount] at hsupportProduct
  have hsupport : (walshSupport f).card = 2 ^ m := by
    have heq : 2 ^ k * (walshSupport f).card = 2 ^ k * 2 ^ m := by
      calc
        2 ^ k * (walshSupport f).card = 2 ^ n := hsupportProduct
        _ = 2 ^ (m + k) := by rw [hdimension]
        _ = 2 ^ k * 2 ^ m := by rw [pow_add, mul_comm]
    exact Nat.mul_left_cancel (by positivity) heq
  have hamplitudeProduct :=
    card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul
      f amplitude hamplitude
  rw [hsupport] at hamplitudeProduct
  rcases hf.even_bentDimension with ⟨r, hr⟩
  have hhalf : m / 2 = r := by omega
  have htargetProduct :
      2 ^ (2 * n) = 2 ^ m * (2 ^ (k + m / 2)) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    rw [hhalf]
    omega
  have hmul :
      2 ^ m * amplitude ^ 2 = 2 ^ m * (2 ^ (k + m / 2)) ^ 2 :=
    hamplitudeProduct.trans htargetProduct
  have hsquare : amplitude ^ 2 = (2 ^ (k + m / 2)) ^ 2 :=
    Nat.mul_left_cancel (by positivity) hmul
  have heq : amplitude = 2 ^ (k + m / 2) :=
    Nat.pow_left_injective (by norm_num) hsquare
  simpa [heq] using hamplitude

end CryptBoolean
