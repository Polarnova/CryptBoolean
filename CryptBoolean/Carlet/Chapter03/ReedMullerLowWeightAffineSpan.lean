/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerDuality
public import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine-span control for low-weight dual Reed--Muller words

After translating one support point to zero and deleting that zero column,
evaluation of ambient linear forms produces a self-orthogonal binary code of
length one less than the Hamming weight.  Its dimension is the affine-span
dimension of the support.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A canonical finite enumeration of the support after deleting one chosen
basepoint. -/
noncomputable def supportAwayEquiv
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Fin ((support h).erase p).card ≃
      {x // x ∈ (support h).erase p} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe])

/-- Evaluation of an ambient linear form on the non-basepoint support
differences of a Boolean function. -/
noncomputable def supportDifferenceEvaluation
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    FABL.F₂Cube n →ₗ[FABL.𝔽₂]
      FABL.F₂Cube ((support h).erase p).card where
  toFun a j := FABL.f₂DotProduct a ((supportAwayEquiv h p j).1 + p)
  map_add' a b := by
    funext j
    simp only [FABL.f₂DotProduct, add_dotProduct, Pi.add_apply]
  map_smul' c a := by
    funext j
    simp only [FABL.f₂DotProduct, smul_dotProduct, Pi.smul_apply,
      RingHom.id_apply]

@[simp] theorem supportDifferenceEvaluation_apply
    (h : BooleanFunction n) (p a : FABL.F₂Cube n)
    (j : Fin ((support h).erase p).card) :
    supportDifferenceEvaluation h p a j =
      FABL.f₂DotProduct a ((supportAwayEquiv h p j).1 + p) :=
  rfl

/-- The direction space canonically recovered from the support-difference
evaluation map. -/
noncomputable def supportDifferenceSpan
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.perpendicularSubspace (LinearMap.ker (supportDifferenceEvaluation h p))

/-- The support differences away from a chosen basepoint. -/
def supportDifferences
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Set (FABL.F₂Cube n) :=
  {v | ∃ x ∈ (support h).erase p, v = x + p}

/-- The recovered support-difference space is exactly the linear span of the
actual support differences. -/
theorem supportDifferenceSpan_eq_span_supportDifferences
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    supportDifferenceSpan h p =
      Submodule.span FABL.𝔽₂ (supportDifferences h p) := by
  classical
  have hker :
      LinearMap.ker (supportDifferenceEvaluation h p) =
        FABL.perpendicularSubspace
          (Submodule.span FABL.𝔽₂ (supportDifferences h p)) := by
    ext a
    rw [LinearMap.mem_ker, FABL.mem_perpendicularSubspace_iff]
    constructor
    · intro ha v hv
      have hspanLe :
          Submodule.span FABL.𝔽₂ (supportDifferences h p) ≤
            LinearMap.ker (FABL.f₂DotProductBilin n a) := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨x, hx, rfl⟩ := hw
        let xAway : {y // y ∈ (support h).erase p} := ⟨x, hx⟩
        let j : Fin ((support h).erase p).card :=
          (supportAwayEquiv h p).symm xAway
        have hj := congrFun ha j
        have hpoint : (supportAwayEquiv h p j).1 = x := by
          change ((supportAwayEquiv h p)
            ((supportAwayEquiv h p).symm xAway)).1 = x
          rw [Equiv.apply_symm_apply]
        change FABL.f₂DotProductBilin n a (x + p) = 0
        simpa only [FABL.f₂DotProductBilin_apply,
          supportDifferenceEvaluation_apply, Pi.zero_apply, hpoint] using hj
      exact LinearMap.mem_ker.mp (hspanLe hv)
    · intro ha
      funext j
      have hgenerator :
          (supportAwayEquiv h p j).1 + p ∈ supportDifferences h p := by
        exact ⟨(supportAwayEquiv h p j).1,
          (supportAwayEquiv h p j).2, rfl⟩
      have hspan :
          (supportAwayEquiv h p j).1 + p ∈
            Submodule.span FABL.𝔽₂ (supportDifferences h p) :=
        Submodule.subset_span hgenerator
      simpa only [supportDifferenceEvaluation_apply, Pi.zero_apply] using
        ha ((supportAwayEquiv h p j).1 + p) hspan
  rw [supportDifferenceSpan, hker,
    FABL.perpendicularSubspace_perpendicularSubspace]

/-- If the support-difference span has dimension `r`, then `r` actual
support differences form a basis of that span. -/
theorem exists_supportDifferenceBasis_of_finrank_eq
    (h : BooleanFunction n) (p : FABL.F₂Cube n) {r : ℕ}
    (hrank : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) = r) :
    ∃ v : Fin r → FABL.F₂Cube n,
      (∀ i, v i ∈ supportDifferences h p) ∧
        Submodule.span FABL.𝔽₂ (Set.range v) =
          supportDifferenceSpan h p ∧
        LinearIndependent FABL.𝔽₂ v := by
  rw [supportDifferenceSpan_eq_span_supportDifferences] at hrank ⊢
  have hex := Submodule.exists_fun_fin_finrank_span_eq
    FABL.𝔽₂ (supportDifferences h p)
  rw [hrank] at hex
  exact hex

/-- Every support point lies in the affine flat through the chosen basepoint
with direction `supportDifferenceSpan`. -/
theorem support_subset_binaryAffineSubspace_supportDifferenceSpan
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    (support h : Set (FABL.F₂Cube n)) ⊆
      FABL.binaryAffineSubspace (supportDifferenceSpan h p) p := by
  intro x hx
  change x ∈ FABL.binaryAffineSubspace (supportDifferenceSpan h p) p
  rw [FABL.mem_binaryAffineSubspace_iff_add_mem]
  rw [supportDifferenceSpan, FABL.mem_perpendicularSubspace_iff]
  intro a ha
  rw [LinearMap.mem_ker] at ha
  by_cases hxp : x = p
  · subst x
    rw [ZModModule.add_self]
    simp [FABL.f₂DotProduct, dotProduct]
  · let xAway : {y // y ∈ (support h).erase p} :=
      ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩⟩
    let j : Fin ((support h).erase p).card :=
      (supportAwayEquiv h p).symm xAway
    have hxzero := congrFun ha j
    have hxzero' : FABL.f₂DotProduct a (x + p) = 0 := by
      have hj : (supportAwayEquiv h p j).1 = x := by
        change ((supportAwayEquiv h p)
          ((supportAwayEquiv h p).symm xAway)).1 = x
        rw [Equiv.apply_symm_apply]
      simpa only [supportDifferenceEvaluation_apply, Pi.zero_apply,
        hj] using hxzero
    rw [show FABL.f₂DotProduct (x + p) a =
      FABL.f₂DotProduct a (x + p) by exact dotProduct_comm _ _]
    exact hxzero'

/-- The recovered support-difference span has the same dimension as the
range of its evaluation map. -/
theorem finrank_supportDifferenceSpan_eq_finrank_range
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) =
      Module.finrank FABL.𝔽₂
        (LinearMap.range (supportDifferenceEvaluation h p)) := by
  rw [supportDifferenceSpan, FABL.finrank_perpendicularSubspace]
  have hrank := (supportDifferenceEvaluation h p).finrank_range_add_finrank_ker
  have htotal : Module.finrank FABL.𝔽₂ (FABL.F₂Cube n) = n := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [htotal] at hrank
  omega

/-- The affine linear form whose value at `x` is the dot product with the
translated point `x + p`. -/
noncomputable def translatedLinearBooleanFunction
    (p a : FABL.F₂Cube n) : BooleanFunction n :=
  FABL.affineFunction (FABL.f₂DotProduct a p) a

@[simp] theorem translatedLinearBooleanFunction_apply
    (p a x : FABL.F₂Cube n) :
    translatedLinearBooleanFunction p a x =
      FABL.f₂DotProduct a (x + p) := by
  simp only [translatedLinearBooleanFunction, FABL.affineFunction,
    FABL.f₂DotProduct, dotProduct_add]
  ac_rfl

/-- A product of two translated linear forms belongs to `RM(2,n)`. -/
theorem translatedLinearBooleanFunction_mul_mem_reedMuller_two
    (p a b : FABL.F₂Cube n) :
    translatedLinearBooleanFunction p a *
        translatedLinearBooleanFunction p b ∈
      reedMuller 2 n := by
  rw [mem_reedMuller_iff]
  have ha : FABL.functionAlgebraicDegree
      (translatedLinearBooleanFunction p a) ≤ 1 := by
    simpa only [translatedLinearBooleanFunction, mem_reedMuller_iff] using
      (affineFunction_mem_reedMuller_one
        (FABL.f₂DotProduct a p) a)
  have hb : FABL.functionAlgebraicDegree
      (translatedLinearBooleanFunction p b) ≤ 1 := by
    simpa only [translatedLinearBooleanFunction, mem_reedMuller_iff] using
      (affineFunction_mem_reedMuller_one
        (FABL.f₂DotProduct b p) b)
  exact (FABL.functionAlgebraicDegree_mul_le_add _ _).trans (by omega)

/-- The dot product of two support-difference evaluation words is the
pairing of the original word with the corresponding quadratic function. -/
theorem dotProduct_supportDifferenceEvaluation_eq_pairing
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (a b : FABL.F₂Cube n) :
    dotProduct (supportDifferenceEvaluation h p a)
        (supportDifferenceEvaluation h p b) =
      booleanFunctionPairing n
        (translatedLinearBooleanFunction p a *
          translatedLinearBooleanFunction p b) h := by
  classical
  rw [booleanFunctionPairing_apply]
  let q : BooleanFunction n :=
    translatedLinearBooleanFunction p a *
      translatedLinearBooleanFunction p b
  rw [dotProduct]
  simp only [supportDifferenceEvaluation_apply,
    ← translatedLinearBooleanFunction_apply]
  change
    (∑ j : Fin ((support h).erase p).card,
      q ((supportAwayEquiv h p j).1)) =
        ∑ x : FABL.F₂Cube n, q x * h x
  calc
    (∑ j : Fin ((support h).erase p).card,
        q ((supportAwayEquiv h p j).1)) =
        ∑ x : {x // x ∈ (support h).erase p}, q x.1 := by
      exact Fintype.sum_equiv (supportAwayEquiv h p)
        (fun j ↦ q ((supportAwayEquiv h p j).1))
        (fun x ↦ q x.1) (fun _j ↦ rfl)
    _ = ∑ x ∈ (support h).erase p, q x := by
      symm
      exact Finset.sum_subtype ((support h).erase p)
        (fun x ↦ by simp) (fun x ↦ q x)
    _ = ∑ x ∈ support h, q x := by
      have hdecomp := Finset.sum_erase_add
        (s := support h) (f := fun x ↦ q x) hp
      have hqp : q p = 0 := by
        simp [q, translatedLinearBooleanFunction_apply,
          ZModModule.add_self, FABL.f₂DotProduct, dotProduct]
      simpa only [hqp, add_zero] using hdecomp
    _ = ∑ x : FABL.F₂Cube n, q x * h x := by
      rw [support, FABL.f₂OneSupport, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : h x = 1
      · simp [hx]
      · have hxzero : h x = 0 := by
          by_contra hne
          exact hx (Fin.eq_one_of_ne_zero _ hne)
        simp [hxzero]

/-- For a word orthogonal to `RM(2,n)`, the support-difference evaluation
code is self-orthogonal. -/
theorem range_supportDifferenceEvaluation_le_perpendicular
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n) :
    LinearMap.range (supportDifferenceEvaluation h p) ≤
      FABL.perpendicularSubspace
        (LinearMap.range (supportDifferenceEvaluation h p)) := by
  intro y hy
  rw [FABL.mem_perpendicularSubspace_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  change dotProduct (supportDifferenceEvaluation h p a)
    (supportDifferenceEvaluation h p b) = 0
  rw [dotProduct_supportDifferenceEvaluation_eq_pairing h p hp]
  rw [reedMullerDual,
    LinearMap.BilinForm.mem_orthogonal_iff] at hdual
  exact hdual
    (translatedLinearBooleanFunction p a *
      translatedLinearBooleanFunction p b)
    (translatedLinearBooleanFunction_mul_mem_reedMuller_two p a b)

/-- Deleting the translated zero column makes the standard
self-orthogonal-code bound sharp enough: twice the affine-span dimension is
at most one less than the Hamming weight. -/
theorem two_mul_finrank_supportDifferenceSpan_le_hammingWeight_sub_one
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n) :
    2 * Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤
      hammingWeight h - 1 := by
  have hself := range_supportDifferenceEvaluation_le_perpendicular
    h p hp hdual
  have hfinrank := Submodule.finrank_mono hself
  rw [FABL.finrank_perpendicularSubspace] at hfinrank
  have hrange := finrank_supportDifferenceSpan_eq_finrank_range h p
  have hcard := Finset.card_erase_add_one hp
  rw [hammingWeight_eq_card_support]
  omega

/-- Codimension-three Reed--Muller membership supplies the orthogonality
hypothesis in the affine-span bound. -/
theorem two_mul_finrank_supportDifferenceSpan_le_of_mem_codimension_three
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hn : 3 ≤ n) (hmem : h ∈ reedMuller (n - 3) n) :
    2 * Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤
      hammingWeight h - 1 := by
  have hdual : h ∈ reedMullerDual 2 n := by
    rw [reedMullerDual_eq (r := 2) (n := n) (by omega)]
    simpa only [show n - 2 - 1 = n - 3 by omega] using hmem
  exact two_mul_finrank_supportDifferenceSpan_le_hammingWeight_sub_one
    h p hp hdual

/-- A weight-twelve codimension-three word is contained in an affine flat of
dimension at most five. -/
theorem finrank_supportDifferenceSpan_le_five_of_weight_twelve
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hn : 3 ≤ n) (hmem : h ∈ reedMuller (n - 3) n)
    (hweight : hammingWeight h = 12) :
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤ 5 := by
  have hbound :=
    two_mul_finrank_supportDifferenceSpan_le_of_mem_codimension_three
      h p hp hn hmem
  rw [hweight] at hbound
  omega

/-- A weight-fourteen codimension-three word is contained in an affine flat
of dimension at most six. -/
theorem finrank_supportDifferenceSpan_le_six_of_weight_fourteen
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hn : 3 ≤ n) (hmem : h ∈ reedMuller (n - 3) n)
    (hweight : hammingWeight h = 14) :
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤ 6 := by
  have hbound :=
    two_mul_finrank_supportDifferenceSpan_le_of_mem_codimension_three
      h p hp hn hmem
  rw [hweight] at hbound
  omega

/-- A weight-sixteen codimension-three word is contained in an affine flat
of dimension at most seven. -/
theorem finrank_supportDifferenceSpan_le_seven_of_weight_sixteen
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hn : 3 ≤ n) (hmem : h ∈ reedMuller (n - 3) n)
    (hweight : hammingWeight h = 16) :
    Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤ 7 := by
  have hbound :=
    two_mul_finrank_supportDifferenceSpan_le_of_mem_codimension_three
      h p hp hn hmem
  rw [hweight] at hbound
  omega

end CryptBoolean
