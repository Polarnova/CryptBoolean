/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.HyperplaneRestriction
public import CryptBoolean.Carlet.Chapter07.AddingVariable
public import CryptBoolean.Carlet.Chapter07.DirectSumDegree

/-!
# Tarannikov's elementary construction

Carlet Section 7.5.2: the elementary linear-shear construction and its exact
Walsh spectrum.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r m : ℕ}

/-- The penultimate coordinate in an `(r + 2)`-dimensional cube. -/
def tarannikovPenultimateIndex (r : ℕ) : Fin (r + 2) :=
  Fin.castSucc (Fin.last r)

/-- The last coordinate in an `(r + 2)`-dimensional cube. -/
def tarannikovLastIndex (r : ℕ) : Fin (r + 2) :=
  Fin.last (r + 1)

/-- The linear endomorphism underlying the Tarannikov shear. -/
def tarannikovShearLinearMap (r : ℕ) :
    FABL.F₂Cube (r + 2) →ₗ[FABL.𝔽₂] FABL.F₂Cube (r + 2) where
  toFun x i :=
    if i = tarannikovPenultimateIndex r then
      x i + x (tarannikovLastIndex r)
    else x i
  map_add' x y := by
    funext i
    by_cases hi : i = tarannikovPenultimateIndex r
    · simp [hi]
      abel
    · simp [hi]
  map_smul' c x := by
    funext i
    by_cases hi : i = tarannikovPenultimateIndex r
    · simp only [Pi.smul_apply, hi, if_pos, RingHom.id_apply]
      exact (mul_add c _ _).symm
    · simp [hi]

/-- The Tarannikov shear is an involution. -/
theorem tarannikovShearLinearMap_involutive (r : ℕ) :
    Function.Involutive (tarannikovShearLinearMap r) := by
  intro x
  funext i
  have hindices :
      tarannikovLastIndex r ≠ tarannikovPenultimateIndex r := by
    exact (Fin.castSucc_ne_last (Fin.last r)).symm
  by_cases hi : i = tarannikovPenultimateIndex r
  · subst i
    simp only [tarannikovShearLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      if_pos, hindices, if_false]
    calc
      (x (tarannikovPenultimateIndex r) + x (tarannikovLastIndex r)) +
          x (tarannikovLastIndex r) =
        x (tarannikovPenultimateIndex r) +
          (x (tarannikovLastIndex r) + x (tarannikovLastIndex r)) := by abel
      _ = x (tarannikovPenultimateIndex r) := by
        rw [ZModModule.add_self, add_zero]
  · simp only [tarannikovShearLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      hi, hindices, if_false]

/-- The involutive shear that adds the final coordinate to the penultimate
coordinate. -/
def tarannikovShearLinearEquiv (r : ℕ) :
    FABL.F₂Cube (r + 2) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (r + 2) :=
  LinearEquiv.ofInvolutive
    (tarannikovShearLinearMap r)
    (tarannikovShearLinearMap_involutive r)

@[simp] theorem tarannikovShearLinearEquiv_apply
    (r : ℕ) (x : FABL.F₂Cube (r + 2)) (i : Fin (r + 2)) :
    tarannikovShearLinearEquiv r x i =
      if i = tarannikovPenultimateIndex r then
        x i + x (tarannikovLastIndex r)
      else x i :=
  rfl

/-- The coordinate tuple consisting of an `r`-bit prefix and two final bits. -/
def tarannikovCoordinates
    (x : FABL.F₂Cube r) (a z : FABL.𝔽₂) : FABL.F₂Cube (r + 2) :=
  Fin.snoc (Fin.snoc x a) z

/-- Evaluation of the Tarannikov shear on the prefix and final two bits. -/
@[simp] theorem tarannikovShearLinearEquiv_append
    (x : FABL.F₂Cube r) (a z : FABL.𝔽₂) :
    tarannikovShearLinearEquiv r
        (tarannikovCoordinates x a z) =
      tarannikovCoordinates x (a + z) z := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hlast :
        Fin.last (r + 1) ≠ Fin.castSucc (Fin.last r) :=
      (Fin.castSucc_ne_last (Fin.last r)).symm
    simp [tarannikovCoordinates, tarannikovShearLinearEquiv_apply,
      tarannikovPenultimateIndex, hlast]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [tarannikovCoordinates, tarannikovShearLinearEquiv_apply,
        tarannikovPenultimateIndex, tarannikovLastIndex]
    · have hk :
          k.castSucc.castSucc ≠ (Fin.last r).castSucc := by
        intro h
        exact Fin.castSucc_ne_last k (Fin.castSucc_inj.mp h)
      simp [tarannikovCoordinates, tarannikovShearLinearEquiv_apply,
        tarannikovPenultimateIndex, hk]

/-- The tuple notation agrees with nested binary-cube append. -/
theorem tarannikovCoordinates_eq_append
    (x : FABL.F₂Cube r) (a z : FABL.𝔽₂) :
    tarannikovCoordinates x a z =
      Fin.append (Fin.append x (singletonF₂Cube a))
        (singletonF₂Cube z) := by
  have ha :
      (Fin.cons a Fin.elim0 : FABL.F₂Cube 1) =
        singletonF₂Cube a := by
    funext i
    fin_cases i
    rfl
  have hz :
      (Fin.cons z Fin.elim0 : FABL.F₂Cube 1) =
        singletonF₂Cube z := by
    funext i
    fin_cases i
    rfl
  rw [tarannikovCoordinates, Fin.snoc_eq_append,
    Fin.snoc_eq_append, ha, hz]

/-- Tarannikov's elementary function is adding a parity variable followed by
the penultimate-coordinate shear. -/
def tarannikovElementaryConstruction
    (g : BooleanFunction (r + 1)) : BooleanFunction (r + 2) :=
  addingVariable g ∘ tarannikovShearLinearEquiv r

/-- Source evaluation formula
`h(x,a,z) = z ⊕ g(x,a ⊕ z)`. -/
@[simp] theorem tarannikovElementaryConstruction_append
    (g : BooleanFunction (r + 1))
    (x : FABL.F₂Cube r) (a z : FABL.𝔽₂) :
    tarannikovElementaryConstruction g
        (tarannikovCoordinates x a z) =
      z + g (Fin.append x (singletonF₂Cube (a + z))) := by
  rw [tarannikovElementaryConstruction]
  change addingVariable g
      (tarannikovShearLinearEquiv r (tarannikovCoordinates x a z)) = _
  rw [tarannikovShearLinearEquiv_append,
    tarannikovCoordinates_eq_append]
  simp [add_comm]

private theorem f₂_eq_zero_or_one (b : FABL.𝔽₂) :
    b = 0 ∨ b = 1 := by
  have hb := ZMod.val_lt b
  have hval : b.val = 0 ∨ b.val = 1 := by omega
  rcases hval with hzero | hone
  · exact Or.inl ((ZMod.val_eq_zero b).mp hzero)
  · right
    rw [← ZMod.natCast_zmod_val b, hone]
    rfl

/-- The one-variable parity spectrum in bit coordinates. -/
theorem walshTransform_oneVariableParity_singletonF₂Cube
    (b : FABL.𝔽₂) :
    walshTransform oneVariableParity (singletonF₂Cube b) =
      if b = 1 then 2 else 0 := by
  rcases f₂_eq_zero_or_one b with rfl | rfl
  · rw [walshTransform, sum_singletonF₂Cube]
    simp [walshTerm, oneVariableParity, FABL.coordinateSum,
      singletonF₂Cube, FABL.f₂DotProduct, dotProduct,
      bitSignInt_eq_if_one]
  · rw [walshTransform, sum_singletonF₂Cube]
    simp [walshTerm, oneVariableParity, FABL.coordinateSum,
      singletonF₂Cube, FABL.f₂DotProduct, dotProduct,
      bitSignInt_eq_if_one]

/-- Dot products split over Tarannikov coordinates. -/
theorem f₂DotProduct_tarannikovCoordinates
    (a x : FABL.F₂Cube r) (aᵣ aₙ xᵣ xₙ : FABL.𝔽₂) :
    FABL.f₂DotProduct (tarannikovCoordinates a aᵣ aₙ)
        (tarannikovCoordinates x xᵣ xₙ) =
      FABL.f₂DotProduct a x + aᵣ * xᵣ + aₙ * xₙ := by
  rw [tarannikovCoordinates_eq_append,
    tarannikovCoordinates_eq_append,
    FABL.f₂DotProduct_append, FABL.f₂DotProduct_append]
  simp [FABL.f₂DotProduct, dotProduct, singletonF₂Cube]

/-- Every vector has a prefix-and-two-bits presentation. -/
theorem exists_eq_tarannikovCoordinates
    (u : FABL.F₂Cube (r + 2)) :
    ∃ x : FABL.F₂Cube r, ∃ xᵣ xₙ : FABL.𝔽₂,
      tarannikovCoordinates x xᵣ xₙ = u := by
  refine ⟨Fin.init (Fin.init u), (Fin.init u) (Fin.last r),
    u (Fin.last (r + 1)), ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [tarannikovCoordinates]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j <;>
      simp [tarannikovCoordinates, Fin.init]

/-- The dual-frequency shear for the Tarannikov coordinate change. -/
theorem f₂DotProduct_tarannikovShear
    (a : FABL.F₂Cube r) (aᵣ aₙ : FABL.𝔽₂)
    (u : FABL.F₂Cube (r + 2)) :
    FABL.f₂DotProduct (tarannikovCoordinates a aᵣ (aₙ + aᵣ))
        (tarannikovShearLinearEquiv r u) =
      FABL.f₂DotProduct (tarannikovCoordinates a aᵣ aₙ) u := by
  obtain ⟨x, xᵣ, xₙ, rfl⟩ := exists_eq_tarannikovCoordinates u
  rw [tarannikovShearLinearEquiv_append,
    f₂DotProduct_tarannikovCoordinates,
    f₂DotProduct_tarannikovCoordinates]
  ring_nf
  rw [show (2 : FABL.𝔽₂) = 0 by decide]
  simp

private theorem walshTransform_tarannikov_transport
    (g : BooleanFunction (r + 1))
    (a : FABL.F₂Cube r) (aᵣ aₙ : FABL.𝔽₂) :
    walshTransform (tarannikovElementaryConstruction g)
        (tarannikovCoordinates a aᵣ aₙ) =
      walshTransform (addingVariable g)
        (tarannikovCoordinates a aᵣ (aₙ + aᵣ)) := by
  classical
  rw [walshTransform, walshTransform]
  apply Fintype.sum_equiv (tarannikovShearLinearEquiv r).toEquiv
  intro u
  rw [walshTerm, walshTerm]
  change bitSignInt
      (addingVariable g (tarannikovShearLinearEquiv r u) +
        FABL.f₂DotProduct (tarannikovCoordinates a aᵣ aₙ) u) =
    bitSignInt
      (addingVariable g (tarannikovShearLinearEquiv r u) +
        FABL.f₂DotProduct (tarannikovCoordinates a aᵣ (aₙ + aᵣ))
          (tarannikovShearLinearEquiv r u))
  rw [f₂DotProduct_tarannikovShear]

/-- Tarannikov's exact two-branch Walsh spectrum. -/
theorem walshTransform_tarannikovElementaryConstruction
    (g : BooleanFunction (r + 1))
    (a : FABL.F₂Cube r) (aᵣ aₙ : FABL.𝔽₂) :
    walshTransform (tarannikovElementaryConstruction g)
        (tarannikovCoordinates a aᵣ aₙ) =
      if aₙ = aᵣ then 0 else
        2 * walshTransform g
          (Fin.append a (singletonF₂Cube aᵣ)) := by
  rw [walshTransform_tarannikov_transport, addingVariable,
    tarannikovCoordinates_eq_append, walshTransform_directSum,
    walshTransform_oneVariableParity_singletonF₂Cube]
  rcases f₂_eq_zero_or_one aᵣ with rfl | rfl <;>
    rcases f₂_eq_zero_or_one aₙ with rfl | rfl <;>
    simp [mul_comm]

/-- Tarannikov's construction doubles nonlinearity. -/
theorem nonlinearity_tarannikovElementaryConstruction
    (g : BooleanFunction (r + 1)) :
    nonlinearity (tarannikovElementaryConstruction g) =
      2 * nonlinearity g := by
  calc
    nonlinearity (tarannikovElementaryConstruction g) =
        nonlinearity (addingVariable g) := by
      change nonlinearity
          (addingVariable g ∘
            (tarannikovShearLinearEquiv r).toAffineEquiv) = _
      exact nonlinearity_comp_affineEquiv
        (addingVariable g) (tarannikovShearLinearEquiv r).toAffineEquiv
    _ = 2 * nonlinearity g := nonlinearity_addingVariable g

/-- Support weight splits over Tarannikov coordinates. -/
theorem card_f₂Support_tarannikovCoordinates
    (a : FABL.F₂Cube r) (aᵣ aₙ : FABL.𝔽₂) :
    #(FABL.f₂Support (tarannikovCoordinates a aᵣ aₙ)) =
      #(FABL.f₂Support a) +
        #(FABL.f₂Support (singletonF₂Cube aᵣ)) +
        #(FABL.f₂Support (singletonF₂Cube aₙ)) := by
  rw [tarannikovCoordinates_eq_append,
    card_f₂Support_append, card_f₂Support_append]

/-- A singleton binary cube has support weight equal to its bit. -/
theorem card_f₂Support_singletonF₂Cube
    (b : FABL.𝔽₂) :
    #(FABL.f₂Support (singletonF₂Cube b)) =
      if b = 1 then 1 else 0 := by
  rcases f₂_eq_zero_or_one b with rfl | rfl <;>
    simp [FABL.f₂Support, singletonF₂Cube]

private theorem card_f₂Support_singletons_add_eq_one_of_ne
    {aᵣ aₙ : FABL.𝔽₂} (hne : aₙ ≠ aᵣ) :
    #(FABL.f₂Support (singletonF₂Cube aᵣ)) +
        #(FABL.f₂Support (singletonF₂Cube aₙ)) = 1 := by
  rw [card_f₂Support_singletonF₂Cube,
    card_f₂Support_singletonF₂Cube]
  rcases f₂_eq_zero_or_one aᵣ with rfl | rfl <;>
    rcases f₂_eq_zero_or_one aₙ with rfl | rfl <;>
    simp_all

/-- Tarannikov's construction preserves every resilient order of the source. -/
theorem isResilient_tarannikovElementaryConstruction
    {g : BooleanFunction (r + 1)}
    (hm : m < r + 1) (hg : IsResilient m g) :
    IsResilient m (tarannikovElementaryConstruction g) := by
  apply (theorem_3_resilient_iff_walshTransform_eq_zero
    m (tarannikovElementaryConstruction g) (by omega) (by omega)).2
  intro u hu
  obtain ⟨a, aᵣ, aₙ, rfl⟩ := exists_eq_tarannikovCoordinates u
  rw [walshTransform_tarannikovElementaryConstruction]
  by_cases heq : aₙ = aᵣ
  · simp [heq]
  · rw [if_neg heq]
    have hsourceWeight :
        #(FABL.f₂Support
            (Fin.append a (singletonF₂Cube aᵣ))) ≤ m := by
      rw [card_f₂Support_append]
      have htotal := hu
      rw [card_f₂Support_tarannikovCoordinates] at htotal
      omega
    have hzero :=
      (theorem_3_resilient_iff_walshTransform_eq_zero
        m g (by omega) hm).1 hg
        (Fin.append a (singletonF₂Cube aᵣ)) hsourceWeight
    rw [hzero]
    norm_num

/-- Under Carlet's extra last-frequency vanishing hypothesis, Tarannikov's
construction gains one resilient order. -/
theorem isResilient_succ_tarannikovElementaryConstruction
    {g : BooleanFunction (r + 1)}
    (hm : m < r + 1) (hg : IsResilient m g)
    (hlast : ∀ a : FABL.F₂Cube r,
      #(FABL.f₂Support a) ≤ m →
        walshTransform g
          (Fin.append a (singletonF₂Cube 1)) = 0) :
    IsResilient (m + 1) (tarannikovElementaryConstruction g) := by
  apply (theorem_3_resilient_iff_walshTransform_eq_zero
    (m + 1) (tarannikovElementaryConstruction g)
      (by omega) (by omega)).2
  intro u hu
  obtain ⟨a, aᵣ, aₙ, rfl⟩ := exists_eq_tarannikovCoordinates u
  rw [walshTransform_tarannikovElementaryConstruction]
  by_cases heq : aₙ = aᵣ
  · simp [heq]
  · rw [if_neg heq]
    have hpair := card_f₂Support_singletons_add_eq_one_of_ne heq
    have htotal := hu
    rw [card_f₂Support_tarannikovCoordinates] at htotal
    have ha : #(FABL.f₂Support a) ≤ m := by omega
    rcases f₂_eq_zero_or_one aᵣ with hzero | hone
    · subst aᵣ
      have hfrequencyWeight :
          #(FABL.f₂Support
            (Fin.append a (singletonF₂Cube 0))) ≤ m := by
        rw [card_f₂Support_append,
          card_f₂Support_singletonF₂Cube]
        simpa using ha
      have hwalsh :=
        (theorem_3_resilient_iff_walshTransform_eq_zero
          m g (by omega) hm).1 hg
          (Fin.append a (singletonF₂Cube 0)) hfrequencyWeight
      rw [hwalsh]
      norm_num
    · subst aᵣ
      rw [hlast a ha]
      norm_num

/-- If the source is nonconstant, Tarannikov's construction preserves its
algebraic degree. -/
theorem functionAlgebraicDegree_tarannikovElementaryConstruction
    (g : BooleanFunction (r + 1))
    (hdegree : 1 ≤ FABL.functionAlgebraicDegree g) :
    FABL.functionAlgebraicDegree
        (tarannikovElementaryConstruction g) =
      FABL.functionAlgebraicDegree g := by
  calc
    FABL.functionAlgebraicDegree
        (tarannikovElementaryConstruction g) =
        FABL.functionAlgebraicDegree (addingVariable g) := by
      change FABL.functionAlgebraicDegree
          (addingVariable g ∘
            (tarannikovShearLinearEquiv r).toAffineEquiv) = _
      exact FABL.functionAlgebraicDegree_comp_affineEquiv
        (addingVariable g) (tarannikovShearLinearEquiv r).toAffineEquiv
    _ = FABL.functionAlgebraicDegree g := by
      rw [addingVariable, functionAlgebraicDegree_booleanDirectSum,
        functionAlgebraicDegree_oneVariableParity,
        Nat.max_eq_left hdegree]

/-- The direction with zero prefix and both final coordinates equal to one. -/
def tarannikovLinearStructureDirection (r : ℕ) :
    FABL.F₂Cube (r + 2) :=
  tarannikovCoordinates 0 1 1

/-- The Tarannikov direction is nonzero. -/
theorem tarannikovLinearStructureDirection_ne_zero (r : ℕ) :
    tarannikovLinearStructureDirection r ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (Fin.last (r + 1))
  simp [tarannikovLinearStructureDirection,
    tarannikovCoordinates] at hcoordinate

/-- The shear sends `(0,…,0,1,1)` to the newly added coordinate direction. -/
@[simp] theorem tarannikovShearLinearEquiv_direction (r : ℕ) :
    tarannikovShearLinearEquiv r
        (tarannikovLinearStructureDirection r) =
      addedVariableDirection (r + 1) := by
  rw [tarannikovLinearStructureDirection,
    tarannikovShearLinearEquiv_append, ZModModule.add_self]
  rw [tarannikovCoordinates_eq_append]
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [Fin.append_left]
    unfold addedVariableDirection
    rw [Fin.append_left]
    change Fin.append (0 : FABL.F₂Cube r)
        (singletonF₂Cube 0) j = 0
    have hinner :
        Fin.append (0 : FABL.F₂Cube r) (singletonF₂Cube 0) =
          (0 : FABL.F₂Cube (r + 1)) := by
      funext k
      refine Fin.addCases (fun ℓ ↦ ?_) (fun ℓ ↦ ?_) k
      · rw [Fin.append_left]
        rfl
      · rw [Fin.append_right]
        rfl
    exact congrFun hinner j
  · rw [Fin.append_right]
    unfold addedVariableDirection
    rw [Fin.append_right]
    rfl

/-- The final-two-coordinate direction is a nonzero linear structure of
Tarannikov's construction. -/
theorem tarannikovLinearStructureDirection_isNonzeroLinearStructure
    (g : BooleanFunction (r + 1)) :
    tarannikovLinearStructureDirection r ≠ 0 ∧
      IsLinearStructure (tarannikovElementaryConstruction g)
        (tarannikovLinearStructureDirection r) := by
  refine ⟨tarannikovLinearStructureDirection_ne_zero r, ?_⟩
  obtain ⟨ε, hε⟩ :=
    (addedVariableDirection_isNonzeroLinearStructure g).2
  refine ⟨ε, ?_⟩
  intro x
  simpa only [FABL.booleanDerivative,
    tarannikovElementaryConstruction, Function.comp_apply,
    (tarannikovShearLinearEquiv r).map_add,
    tarannikovShearLinearEquiv_direction] using
      hε (tarannikovShearLinearEquiv r x)

end CryptBoolean
