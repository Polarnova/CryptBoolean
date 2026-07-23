/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.Nonlinearity

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Carlet Chapter 4 odd-weighting subspaces

Maximal odd-weighting subspaces are represented by Carlet's equivalent coset condition: every
affine coset has odd restriction weight. This formulation applies to arbitrary binary subspaces.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n d : ℕ}

/-- The weight of the restriction of `f` to the affine coset `a + E`, parameterized by `E`. -/
noncomputable def subspaceCosetWeight
    (f : BooleanFunction n) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) : ℕ :=
  Nat.card {e : E // f (a + e.1) = 1}

/-- A maximal odd-weighting subspace in Carlet's equivalent all-cosets formulation. -/
def IsMaximalOddWeightingSubspace
    (f : BooleanFunction n) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Prop :=
  ∀ a, Odd (subspaceCosetWeight f E a)

private theorem subspaceCosetWeight_cast
    (f : BooleanFunction n) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    [Fintype E]
    (a : FABL.F₂Cube n) :
    (subspaceCosetWeight f E a : FABL.𝔽₂) =
      ∑ e : E, f (a + e.1) := by
  classical
  rw [subspaceCosetWeight, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  calc
    ((Finset.univ.filter fun e : E ↦ f (a + e.1) = 1).card : FABL.𝔽₂) =
        ∑ e : E, if f (a + e.1) = 1 then 1 else 0 := by
      simp
    _ = ∑ e : E, f (a + e.1) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : f (a + e.1) = 1
      · simp [h]
      · have hz : f (a + e.1) = 0 := by
          by_contra hnz
          exact h (Fin.eq_one_of_ne_zero _ hnz)
        simp [hz]

/-- Carlet Chapter 3, Remark 2: a maximal odd-weighting subspace forces a weight lower bound. -/
theorem hammingWeight_lower_bound_of_isMaximalOddWeightingSubspace
    (f : BooleanFunction n) (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hE : IsMaximalOddWeightingSubspace f E) :
    2 ^ (n - Module.finrank FABL.𝔽₂ E) ≤ hammingWeight f := by
  letI : Fintype ((FABL.F₂Cube n) ⧸ E) := Fintype.ofFinite _
  let π : ↥(support f) → (FABL.F₂Cube n) ⧸ E :=
    fun x ↦ E.mkQ x.1
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨a, rfl⟩ := E.mkQ_surjective q
    have hpositive : 0 < subspaceCosetWeight f E a :=
      (hE a).pos
    have hnonempty : Nonempty {e : E // f (a + e.1) = 1} := by
      rw [← Finite.card_pos_iff]
      exact hpositive
    obtain ⟨⟨e, hvalue⟩⟩ := hnonempty
    refine ⟨⟨a + e.1, (mem_support f (a + e.1)).mpr hvalue⟩, ?_⟩
    change E.mkQ (a + e.1) = E.mkQ a
    simp
  have hcard_le :
      Fintype.card ((FABL.F₂Cube n) ⧸ E) ≤ Fintype.card ↥(support f) :=
    Fintype.card_le_of_surjective π hπ
  rw [Fintype.card_coe] at hcard_le
  rw [hammingWeight_eq_card_support]
  calc
    2 ^ (n - Module.finrank FABL.𝔽₂ E) =
        Fintype.card ((FABL.F₂Cube n) ⧸ E) := by
      rw [← Nat.card_eq_fintype_card,
        Module.natCard_eq_pow_finrank (K := FABL.𝔽₂), Nat.card_zmod]
      have htotal :
          Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp
      have hquotient := E.finrank_quotient_add_finrank
      rw [htotal] at hquotient
      have hquotient' :
          Module.finrank FABL.𝔽₂ ((FABL.F₂Cube n) ⧸ E) =
            n - Module.finrank FABL.𝔽₂ E := by
        omega
      rw [hquotient']
    _ ≤ (support f).card := by simpa using hcard_le

private noncomputable def subspaceCoordinateEquiv
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :
    FABL.F₂Cube (Module.finrank FABL.𝔽₂ E) ≃ₗ[FABL.𝔽₂] E :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fintype_fun_eq_card]
    simp)

private noncomputable def restrictedAffineFrequency
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (c : FABL.F₂Cube n) :
    FABL.F₂Cube (Module.finrank FABL.𝔽₂ E) :=
  (dotProductEquiv FABL.𝔽₂ (Fin (Module.finrank FABL.𝔽₂ E))).symm
    (((dotProductEquiv FABL.𝔽₂ (Fin n)) c).comp
      (E.subtype.comp (subspaceCoordinateEquiv E).toLinearMap))

private theorem f₂DotProduct_restrictedAffineFrequency
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (c : FABL.F₂Cube n)
    (y : FABL.F₂Cube (Module.finrank FABL.𝔽₂ E)) :
    FABL.f₂DotProduct (restrictedAffineFrequency E c) y =
      FABL.f₂DotProduct c ((subspaceCoordinateEquiv E y).1) := by
  change
    dotProduct (restrictedAffineFrequency E c) y =
      dotProduct c ((subspaceCoordinateEquiv E y).1)
  calc
    dotProduct (restrictedAffineFrequency E c) y =
        ((dotProductEquiv FABL.𝔽₂
          (Fin (Module.finrank FABL.𝔽₂ E)))
            (restrictedAffineFrequency E c)) y :=
      (dotProductEquiv_apply_apply FABL.𝔽₂ _ _ _).symm
    _ = (((dotProductEquiv FABL.𝔽₂ (Fin n)) c).comp
          (E.subtype.comp (subspaceCoordinateEquiv E).toLinearMap)) y := by
      exact DFunLike.congr_fun
        ((dotProductEquiv FABL.𝔽₂
          (Fin (Module.finrank FABL.𝔽₂ E))).apply_symm_apply _) y
    _ = ((dotProductEquiv FABL.𝔽₂ (Fin n)) c)
        ((subspaceCoordinateEquiv E y).1) := rfl
    _ = dotProduct c ((subspaceCoordinateEquiv E y).1) :=
      dotProductEquiv_apply_apply FABL.𝔽₂ _ _ _

private theorem affineFunction_subspaceCoordinate
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a c : FABL.F₂Cube n) (b : FABL.𝔽₂)
    (y : FABL.F₂Cube (Module.finrank FABL.𝔽₂ E)) :
    FABL.affineFunction b c (a + (subspaceCoordinateEquiv E y).1) =
      FABL.affineFunction (FABL.affineFunction b c a)
        (restrictedAffineFrequency E c) y := by
  rw [FABL.affineFunction, FABL.affineFunction,
    FABL.affineFunction, f₂DotProduct_restrictedAffineFrequency]
  change b + dotProduct c (a + (subspaceCoordinateEquiv E y).1) =
    (b + dotProduct c a) + dotProduct c (subspaceCoordinateEquiv E y).1
  rw [dotProduct_add]
  ac_rfl

private theorem subspaceCosetWeight_affineFunction_eq_hammingWeight
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (a c : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    subspaceCosetWeight (FABL.affineFunction b c) E a =
      hammingWeight
        (FABL.affineFunction (FABL.affineFunction b c a)
          (restrictedAffineFrequency E c)) := by
  classical
  let q : BooleanFunction (Module.finrank FABL.𝔽₂ E) :=
    FABL.affineFunction (FABL.affineFunction b c a)
      (restrictedAffineFrequency E c)
  let e :
      {x : E // FABL.affineFunction b c (a + x.1) = 1} ≃
        {y : FABL.F₂Cube (Module.finrank FABL.𝔽₂ E) // q y = 1} :=
    Equiv.subtypeEquiv (subspaceCoordinateEquiv E).symm.toEquiv fun x ↦ by
      have h := affineFunction_subspaceCoordinate E a c b
        ((subspaceCoordinateEquiv E).symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      simpa [q] using congrArg (fun z ↦ z = 1) h
  rw [subspaceCosetWeight]
  calc
    Nat.card {x : E // FABL.affineFunction b c (a + x.1) = 1} =
        Nat.card
          {y : FABL.F₂Cube (Module.finrank FABL.𝔽₂ E) // q y = 1} :=
      Nat.card_congr e
    _ = hammingWeight q := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
        hammingWeight_eq_card_support]
      rfl

private theorem even_hammingWeight_affineFunction
    {m : ℕ} (hm : 2 ≤ m) (b : FABL.𝔽₂) (c : FABL.F₂Cube m) :
    Even (hammingWeight (FABL.affineFunction b c)) := by
  by_cases hc : c = 0
  · subst c
    by_cases hb : b = 0
    · subst b
      simp [hammingWeight_eq_card_support, support,
        FABL.f₂OneSupport, FABL.affineFunction, FABL.f₂DotProduct]
    · have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
      subst b
      have hweight :
          hammingWeight
            (FABL.affineFunction (1 : FABL.𝔽₂) (0 : FABL.F₂Cube m)) =
              2 ^ m := by
        rw [hammingWeight_eq_card_support]
        simp [support, FABL.f₂OneSupport, FABL.affineFunction,
          FABL.f₂DotProduct]
      rw [hweight]
      exact Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) (by omega)
  · rw [hammingWeight_affineFunction_of_ne_zero b c hc]
    exact Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) (by omega)

private theorem even_subspaceCosetWeight_affineFunction
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hE : 2 ≤ Module.finrank FABL.𝔽₂ E)
    (a c : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    Even (subspaceCosetWeight (FABL.affineFunction b c) E a) := by
  rw [subspaceCosetWeight_affineFunction_eq_hammingWeight]
  exact even_hammingWeight_affineFunction hE _ _

private theorem odd_subspaceCosetWeight_add_of_odd_even
    (f g : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (a : FABL.F₂Cube n)
    (hf : Odd (subspaceCosetWeight f E a))
    (hg : Even (subspaceCosetWeight g E a)) :
    Odd (subspaceCosetWeight (f + g) E a) := by
  classical
  letI : Fintype E := Fintype.ofFinite _
  rw [← ZMod.natCast_eq_one_iff_odd]
  rw [subspaceCosetWeight_cast (f + g) E a]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [← subspaceCosetWeight_cast f E a,
    ← subspaceCosetWeight_cast g E a,
    (ZMod.natCast_eq_one_iff_odd.mpr hf),
    (ZMod.natCast_eq_zero_iff_even.mpr hg), add_zero]

/-- Adding an affine function preserves a maximal odd-weighting subspace of dimension at least
two. -/
theorem isMaximalOddWeightingSubspace_add_affineFunction
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hfinrank : 2 ≤ Module.finrank FABL.𝔽₂ E)
    (hE : IsMaximalOddWeightingSubspace f E)
    (b : FABL.𝔽₂) (c : FABL.F₂Cube n) :
    IsMaximalOddWeightingSubspace (f + FABL.affineFunction b c) E := by
  intro a
  exact odd_subspaceCosetWeight_add_of_odd_even f
    (FABL.affineFunction b c) E a (hE a)
      (even_subspaceCosetWeight_affineFunction E hfinrank a c b)

/-- The dimension-indexed form of Carlet Chapter 3, Remark 2. -/
theorem hammingWeight_lower_bound_of_maximalOddWeightingSubspace
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hdim : Module.finrank FABL.𝔽₂ E = d)
    (hE : IsMaximalOddWeightingSubspace f E) :
    2 ^ (n - d) ≤ hammingWeight f := by
  simpa [hdim] using
    hammingWeight_lower_bound_of_isMaximalOddWeightingSubspace f E hE

/-- Carlet Chapter 4: a `d`-dimensional maximal odd-weighting subspace with `d ≥ 2`
forces nonlinearity at least `2^(n-d)`. -/
theorem nonlinearity_lower_bound_of_maximalOddWeightingSubspace
    (f : BooleanFunction n)
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
    (hdim : Module.finrank FABL.𝔽₂ E = d)
    (hd : 2 ≤ d)
    (hE : IsMaximalOddWeightingSubspace f E) :
    2 ^ (n - d) ≤ nonlinearity f := by
  classical
  rw [nonlinearity]
  apply Finset.le_inf'
  intro p _hp
  rw [hammingDistance_eq_hammingWeight_add]
  apply hammingWeight_lower_bound_of_maximalOddWeightingSubspace
    (f + FABL.affineFunction p.1 p.2) E hdim
  apply isMaximalOddWeightingSubspace_add_affineFunction f E
  · simpa [hdim] using hd
  · exact hE

end CryptBoolean
