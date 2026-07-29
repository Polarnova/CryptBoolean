/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.AlgebraicImmunityBounds
public import CryptBoolean.Carlet.Chapter05.QuadraticValues
public import CryptBoolean.Carlet.Chapter07.AlgebraicDegree
public import CryptBoolean.Carlet.Chapter07.DirectSum
public import FABL.Chapter06.F₂Polynomials.Examples

/-!
# Adding one variable to a resilient Boolean function

Carlet Section 7.5.2: the one-variable parity specialization of the direct-sum
construction.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {r t : ℕ}

/-- The parity function on the unique coordinate of the one-dimensional
binary cube. -/
def oneVariableParity : BooleanFunction 1 :=
  FABL.coordinateSum Finset.univ

/-- One-variable parity is the identity function. -/
@[simp] theorem oneVariableParity_apply (z : FABL.F₂Cube 1) :
    oneVariableParity z = z 0 := by
  simp [oneVariableParity, FABL.coordinateSum]

/-- The binary one-variable parity is the canonical encoding of FABL's
sign-valued parity. -/
theorem oneVariableParity_eq_booleanFunctionF₂Encoding :
    oneVariableParity =
      FABL.booleanFunctionF₂Encoding
        (FABL.parityFunction (Finset.univ : Finset (Fin 1))) := by
  rw [FABL.booleanFunctionF₂Encoding_parityFunction]
  rfl

/-- One-variable parity is the nonconstant linear function with all-one
coefficient. -/
theorem oneVariableParity_eq_affineFunction :
    oneVariableParity =
      FABL.affineFunction 0 (FABL.f₂CubeOfFinset Finset.univ) := by
  funext z
  rw [oneVariableParity, FABL.affineFunction, zero_add,
    FABL.f₂DotProduct_f₂CubeOfFinset]

/-- One-variable parity is zero-resilient. -/
theorem oneVariableParity_isResilient :
    IsResilient 0 oneVariableParity := by
  apply (isResilient_iff_fabl 0 oneVariableParity).2
  have hsign :
      signCubeView oneVariableParity =
        FABL.parityFunction (Finset.univ : Finset (Fin 1)) := by
    rw [oneVariableParity_eq_booleanFunctionF₂Encoding]
    funext x
    unfold signCubeView FABL.booleanFunctionF₂Encoding
    rw [(FABL.binaryCubeSignEquiv 1).apply_symm_apply]
    exact FABL.binarySignEquiv.apply_symm_apply _
  rw [hsign]
  exact FABL.parityFunction_isResilient Finset.univ 0 (by simp)

/-- One-variable parity is affine and hence has zero nonlinearity. -/
@[simp] theorem nonlinearity_oneVariableParity :
    nonlinearity oneVariableParity = 0 := by
  rw [oneVariableParity_eq_affineFunction,
    nonlinearity_affineFunction]

/-- One-variable parity has algebraic degree one. -/
@[simp] theorem functionAlgebraicDegree_oneVariableParity :
    FABL.functionAlgebraicDegree oneVariableParity = 1 :=
  FABL.functionAlgebraicDegree_coordinateSum_univ (by omega)

/-- Adding a variable is the Boolean direct sum with one-variable parity. -/
def addingVariable (f : BooleanFunction r) : BooleanFunction (r + 1) :=
  booleanDirectSum f oneVariableParity

/-- Adding a variable evaluates as `f(x) ⊕ z`. -/
@[simp] theorem addingVariable_append
    (f : BooleanFunction r) (x : FABL.F₂Cube r) (z : FABL.F₂Cube 1) :
    addingVariable f (Fin.append x z) = f x + z 0 := by
  simp [addingVariable, booleanDirectSum]

/-- Adding a variable raises the resilient order by one. -/
theorem isResilient_addingVariable
    {f : BooleanFunction r} (ht : t < r) (hf : IsResilient t f) :
    IsResilient (t + 1) (addingVariable f) := by
  simpa [addingVariable] using
    isResilient_booleanDirectSum (s := 1) (m := 0)
      ht (by omega) hf oneVariableParity_isResilient

/-- Adding a variable doubles nonlinearity. -/
theorem nonlinearity_addingVariable
    (f : BooleanFunction r) :
    nonlinearity (addingVariable f) = 2 * nonlinearity f := by
  rw [addingVariable, nonlinearity_booleanDirectSum,
    nonlinearity_oneVariableParity]
  norm_num

/-- The direction of the newly added final coordinate. -/
def addedVariableDirection (r : ℕ) : FABL.F₂Cube (r + 1) :=
  Fin.append 0 (fun _ ↦ 1)

/-- The newly added coordinate direction is nonzero. -/
theorem addedVariableDirection_ne_zero (r : ℕ) :
    addedVariableDirection r ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (Fin.natAdd r (0 : Fin 1))
  simp [addedVariableDirection] at hcoordinate

private theorem oneVariableParity_one_isLinearStructure :
    IsLinearStructure oneVariableParity (fun _ ↦ 1) := by
  refine ⟨1, ?_⟩
  intro z
  simp [FABL.booleanDerivative, ← add_assoc, ZModModule.add_self]

/-- The newly added final coordinate is a nonzero linear structure. -/
theorem addedVariableDirection_isNonzeroLinearStructure
    (f : BooleanFunction r) :
    addedVariableDirection r ≠ 0 ∧
      IsLinearStructure (addingVariable f) (addedVariableDirection r) := by
  refine ⟨addedVariableDirection_ne_zero r, ?_⟩
  exact (isLinearStructure_booleanDirectSum_append
    f oneVariableParity 0 (fun _ ↦ 1)).2
      ⟨isLinearStructure_zero f, oneVariableParity_one_isLinearStructure⟩

private def appendZeroLinearMap (r : ℕ) :
    FABL.F₂Cube r →ₗ[FABL.𝔽₂] FABL.F₂Cube (r + 1) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Pi.add_apply, Fin.append_left]
    · simp
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Pi.smul_apply, Fin.append_left, RingHom.id_apply]
    · simp

/-- In the source parameter range, adding a variable preserves algebraic
degree. -/
theorem functionAlgebraicDegree_addingVariable_eq
    {f : BooleanFunction r}
    (ht : t < r - 1) (hf : IsResilient t f)
    (hdegree : r - t - 1 ≤ FABL.functionAlgebraicDegree f) :
    FABL.functionAlgebraicDegree (addingVariable f) =
      FABL.functionAlgebraicDegree f := by
  have ht' : t < r := by omega
  have hresilient := isResilient_addingVariable ht' hf
  have hupper := functionAlgebraicDegree_le_sub_sub_one_of_isResilient
    (addingVariable f) (t + 1) hresilient (by omega)
  have hupper' :
      FABL.functionAlgebraicDegree (addingVariable f) ≤ r - t - 1 := by
    convert hupper using 1
    omega
  have hrestriction :
      addingVariable f ∘ (appendZeroLinearMap r).toAffineMap = f := by
    funext x
    change addingVariable f (Fin.append x 0) = f x
    simp
  have hlower := functionAlgebraicDegree_comp_affineMap_le_general
    (addingVariable f) (appendZeroLinearMap r).toAffineMap
  rw [hrestriction] at hlower
  exact le_antisymm (hupper'.trans hdegree) hlower

/-- In Carlet's sharp source case, the preserved degree is `r - t - 1`. -/
theorem functionAlgebraicDegree_addingVariable_eq_source
    {f : BooleanFunction r}
    (ht : t < r - 1) (hf : IsResilient t f)
    (hdegree : FABL.functionAlgebraicDegree f = r - t - 1) :
    FABL.functionAlgebraicDegree (addingVariable f) = r - t - 1 := by
  rw [functionAlgebraicDegree_addingVariable_eq ht hf hdegree.ge,
    hdegree]

/-- The sharp source lower bound on nonlinearity is preserved with the
expected doubled scale. -/
theorem nonlinearity_addingVariable_ge_source
    (f : BooleanFunction r) (ht : t < r - 1)
    (hnonlinearity :
      2 ^ (r - 1) - 2 ^ (t + 1) ≤ nonlinearity f) :
    2 ^ r - 2 ^ (t + 2) ≤ nonlinearity (addingVariable f) := by
  rw [nonlinearity_addingVariable]
  have hr : r = (r - 1) + 1 := by omega
  have htPow : t + 2 = (t + 1) + 1 := by omega
  have hrPow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := congrArg (fun q : ℕ ↦ 2 ^ q) hr
      _ = 2 * 2 ^ (r - 1) := by rw [pow_succ]; omega
  have htPow' : 2 ^ (t + 2) = 2 * 2 ^ (t + 1) := by
    calc
      2 ^ (t + 2) = 2 ^ ((t + 1) + 1) :=
        congrArg (fun q : ℕ ↦ 2 ^ q) htPow
      _ = 2 * 2 ^ (t + 1) := by rw [pow_succ]; omega
  omega

end CryptBoolean
