/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.Concatenation
public import CryptBoolean.Carlet.Chapter07.AddingVariable
public import CryptBoolean.Carlet.Chapter07.IndirectSumDegree

/-!
# Algebraic structure of Boolean concatenation

The polynomial representation, derivative formula, and block-preserving
linear structures of Carlet's concatenation.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem two_eq_zero_f₂_forConcatenation :
    (2 : FABL.𝔽₂) = 0 := by
  decide

/-- Concatenation is `f(x) + z(f+g)(x)` in polynomial form. -/
theorem hyperplaneExtension_append_eq_add_mul_difference
    (f g : BooleanFunction n) (x : FABL.F₂Cube n) (z : FABL.𝔽₂) :
    hyperplaneExtension f g (Fin.append x (singletonF₂Cube z)) =
      f x + z * (f + g) x := by
  by_cases hz : z = 0
  · subst z
    simp [Pi.add_apply]
  · have hzOne : z = 1 := Fin.eq_one_of_ne_zero z hz
    rw [hzOne]
    simp only [hyperplaneExtension_append_singletonF₂Cube, one_ne_zero,
      if_false, Pi.add_apply, one_mul]
    calc
      g x = (f x + f x) + g x := by
        rw [ZModModule.add_self, zero_add]
      _ = f x + (f x + g x) := by abel

/-- Polynomial decomposition of concatenation into a lifted restriction and
the product of the difference with the last coordinate. -/
theorem hyperplaneExtension_eq_booleanDirectSum_add_booleanBlockProduct
    (f g : BooleanFunction n) :
    hyperplaneExtension f g =
      booleanDirectSum f (0 : BooleanFunction 1) +
        booleanBlockProduct (f + g) oneVariableParity := by
  funext u
  let p := (Fin.appendEquiv n 1).symm u
  have hu : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv n 1).apply_symm_apply u
  rw [← hu]
  change
    hyperplaneExtension f g (Fin.append p.1 p.2) =
      booleanDirectSum f (0 : BooleanFunction 1) (Fin.append p.1 p.2) +
        booleanBlockProduct (f + g) oneVariableParity
          (Fin.append p.1 p.2)
  rw [show p.2 = singletonF₂Cube (p.2 0) by
    funext i
    fin_cases i
    rfl]
  rw [hyperplaneExtension_append_eq_add_mul_difference]
  simp [booleanDirectSum, booleanBlockProduct, mul_comm]

private theorem append_singletonF₂Cube_add
    (x a : FABL.F₂Cube n) (z c : FABL.𝔽₂) :
    Fin.append x (singletonF₂Cube z) +
        Fin.append a (singletonF₂Cube c) =
      Fin.append (x + a) (singletonF₂Cube (z + c)) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [Pi.add_apply]
  · fin_cases j
    simp [Pi.add_apply]

/-- The derivative of a concatenation in a split direction, in the source's
four-term form. -/
theorem booleanDerivative_hyperplaneExtension_append
    (f g : BooleanFunction n)
    (a x : FABL.F₂Cube n) (c z : FABL.𝔽₂) :
    FABL.booleanDerivative (hyperplaneExtension f g)
        (Fin.append a (singletonF₂Cube c))
        (Fin.append x (singletonF₂Cube z)) =
      FABL.booleanDerivative f a x +
        c * (f + g) x +
        z * FABL.booleanDerivative (f + g) a x +
        c * FABL.booleanDerivative (f + g) a x := by
  simp only [FABL.booleanDerivative, append_singletonF₂Cube_add,
    hyperplaneExtension_append_eq_add_mul_difference, Pi.add_apply]
  ring_nf
  simp only [two_eq_zero_f₂_forConcatenation, mul_zero, add_zero]

/-- Two Boolean functions have the same constant derivative in direction
`a`. -/
def HaveEqualConstantDerivative
    (f g : BooleanFunction n) (a : FABL.F₂Cube n) : Prop :=
  ∃ ε : FABL.𝔽₂,
    (∀ x, FABL.booleanDerivative f a x = ε) ∧
      ∀ x, FABL.booleanDerivative g a x = ε

/-- A direction contained in the original coordinate block is a linear
structure of the concatenation exactly when the two restrictions have the
same constant derivative in that direction. -/
theorem isLinearStructure_hyperplaneExtension_append_zero_iff
    (f g : BooleanFunction n) (a : FABL.F₂Cube n) :
    IsLinearStructure (hyperplaneExtension f g)
        (Fin.append a (singletonF₂Cube 0)) ↔
      HaveEqualConstantDerivative f g a := by
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε, ?_, ?_⟩
    · intro x
      have hx := hε (Fin.append x (singletonF₂Cube 0))
      simpa [FABL.booleanDerivative, append_singletonF₂Cube_add] using hx
    · intro x
      have hx := hε (Fin.append x (singletonF₂Cube 1))
      simpa [FABL.booleanDerivative, append_singletonF₂Cube_add] using hx
  · rintro ⟨ε, hf, hg⟩
    refine ⟨ε, ?_⟩
    intro u
    let p := (Fin.appendEquiv n 1).symm u
    have hu : Fin.append p.1 p.2 = u :=
      (Fin.appendEquiv n 1).apply_symm_apply u
    have hpTail : p.2 = singletonF₂Cube (p.2 0) := by
      funext i
      fin_cases i
      rfl
    rw [← hu, hpTail]
    by_cases hb : p.2 0 = 0
    · simpa [FABL.booleanDerivative, append_singletonF₂Cube_add, hb] using
        hf p.1
    · have hbOne : p.2 0 = 1 := Fin.eq_one_of_ne_zero _ hb
      simpa [FABL.booleanDerivative, append_singletonF₂Cube_add, hbOne] using
        hg p.1

/-- If the two restrictions differ in their highest-degree terms, the
concatenation gains one algebraic degree. -/
theorem functionAlgebraicDegree_hyperplaneExtension_eq_succ_max
    (f g : BooleanFunction n)
    (hdifference : f + g ≠ 0)
    (hdegree :
      FABL.functionAlgebraicDegree (f + g) =
        max (FABL.functionAlgebraicDegree f)
          (FABL.functionAlgebraicDegree g)) :
    FABL.functionAlgebraicDegree (hyperplaneExtension f g) =
      1 + max (FABL.functionAlgebraicDegree f)
        (FABL.functionAlgebraicDegree g) := by
  by_cases hone : f + g = 1
  · have hdegreeDifference :
        FABL.functionAlgebraicDegree (f + g) = 0 := by
      rw [hone, FABL.functionAlgebraicDegree_one]
    have hfzero : FABL.functionAlgebraicDegree f = 0 := by
      rw [hdegree] at hdegreeDifference
      omega
    have heq :
        hyperplaneExtension f g =
          booleanDirectSum f oneVariableParity := by
      funext u
      let p := (Fin.appendEquiv n 1).symm u
      have hu : Fin.append p.1 p.2 = u :=
        (Fin.appendEquiv n 1).apply_symm_apply u
      rw [← hu]
      rw [show p.2 = singletonF₂Cube (p.2 0) by
        funext i
        fin_cases i
        rfl]
      rw [hyperplaneExtension_append_eq_add_mul_difference, hone]
      simp [booleanDirectSum]
    rw [heq, functionAlgebraicDegree_booleanDirectSum,
      functionAlgebraicDegree_oneVariableParity, hfzero]
    omega
  · have hparity : oneVariableParity ≠ 0 := by
      intro hzero
      have hvalue := congrFun hzero (singletonF₂Cube 1)
      simp at hvalue
    have hproduct :=
      functionAlgebraicDegree_booleanBlockProduct
        (f + g) oneVariableParity hdifference hparity
    have hlift :
        FABL.functionAlgebraicDegree
            (booleanDirectSum f (0 : BooleanFunction 1)) =
          FABL.functionAlgebraicDegree f := by
      rw [functionAlgebraicDegree_booleanDirectSum,
        FABL.functionAlgebraicDegree_zero, Nat.max_zero]
    have hpositive :
        0 < FABL.functionAlgebraicDegree (f + g) := by
      rw [Nat.pos_iff_ne_zero]
      intro hzero
      have hconstant :=
        (functionAlgebraicDegree_eq_zero_iff_exists_constant (f + g)).mp hzero
      obtain ⟨c, hc⟩ := hconstant
      by_cases hcZero : c = 0
      · subst c
        apply hdifference
        exact hc.trans (by rfl)
      · have hcOne : c = 1 := Fin.eq_one_of_ne_zero _ hcZero
        subst c
        apply hone
        exact hc.trans (by rfl)
    have hlowerDegree :
        FABL.functionAlgebraicDegree
            (booleanDirectSum f (0 : BooleanFunction 1)) <
          FABL.functionAlgebraicDegree
            (booleanBlockProduct (f + g) oneVariableParity) := by
      rw [hlift, hproduct, functionAlgebraicDegree_oneVariableParity]
      rw [hdegree]
      omega
    rw [hyperplaneExtension_eq_booleanDirectSum_add_booleanBlockProduct,
      functionAlgebraicDegree_add_eq_right_of_lt _ _ hlowerDegree,
      hproduct, functionAlgebraicDegree_oneVariableParity, hdegree]
    omega

/-- Under the source's positive-degree hypothesis, no direction crossing the
two restrictions can be a linear structure. -/
theorem not_isLinearStructure_hyperplaneExtension_append_one
    (f g : BooleanFunction n) (a : FABL.F₂Cube n)
    (hpositive : 0 < FABL.functionAlgebraicDegree (f + g))
    (hdegree :
      FABL.functionAlgebraicDegree f ≤
        FABL.functionAlgebraicDegree (f + g)) :
    ¬ IsLinearStructure (hyperplaneExtension f g)
        (Fin.append a (singletonF₂Cube 1)) := by
  rintro ⟨ε, hε⟩
  have hvalue (x : FABL.F₂Cube n) :
      FABL.booleanDerivative f a x + (f + g) x = ε := by
    have hx := hε (Fin.append x (singletonF₂Cube 1))
    rw [booleanDerivative_hyperplaneExtension_append] at hx
    ring_nf at hx
    simp only [two_eq_zero_f₂_forConcatenation, mul_zero, add_zero] at hx
    exact hx
  have hdifference :
      f + g = FABL.booleanDerivative f a + fun _ ↦ ε := by
    funext x
    have hx := hvalue x
    change (f + g) x =
      FABL.booleanDerivative f a x + ε
    calc
      (f + g) x =
          (f + g) x +
            (FABL.booleanDerivative f a x +
              FABL.booleanDerivative f a x) := by
        rw [ZModModule.add_self, add_zero]
      _ = FABL.booleanDerivative f a x +
          (FABL.booleanDerivative f a x + (f + g) x) := by abel
      _ = FABL.booleanDerivative f a x + ε := by rw [hx]
  have hderivative :=
    FABL.functionAlgebraicDegree_booleanDerivative_le f a
  have hdegreeDifference :
      FABL.functionAlgebraicDegree (f + g) =
        FABL.functionAlgebraicDegree (FABL.booleanDerivative f a) := by
    rw [hdifference, functionAlgebraicDegree_add_constant_eq]
  rw [hdegreeDifference] at hpositive hdegree
  omega

/-- If neither a crossing direction nor a nonzero common constant-derivative
direction is available, the concatenation has no nonzero linear structure. -/
theorem no_nonzero_linearStructure_hyperplaneExtension
    (f g : BooleanFunction n)
    (hpositive : 0 < FABL.functionAlgebraicDegree (f + g))
    (hdegree :
      FABL.functionAlgebraicDegree f ≤
        FABL.functionAlgebraicDegree (f + g))
    (hcommon : ∀ a : FABL.F₂Cube n, a ≠ 0 →
      ¬ HaveEqualConstantDerivative f g a) :
    ∀ u : FABL.F₂Cube (n + 1), u ≠ 0 →
      ¬ IsLinearStructure (hyperplaneExtension f g) u := by
  intro u hu
  let p := (Fin.appendEquiv n 1).symm u
  have hp : Fin.append p.1 p.2 = u :=
    (Fin.appendEquiv n 1).apply_symm_apply u
  rw [← hp]
  have htail : p.2 = singletonF₂Cube (p.2 0) := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  by_cases hzero : p.2 0 = 0
  · rw [hzero,
      isLinearStructure_hyperplaneExtension_append_zero_iff]
    apply hcommon p.1
    intro hpzero
    apply hu
    rw [← hp, htail, hzero, hpzero]
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  · have hone : p.2 0 = 1 := Fin.eq_one_of_ne_zero _ hzero
    rw [hone]
    exact not_isLinearStructure_hyperplaneExtension_append_one
      f g p.1 hpositive hdegree

end CryptBoolean
