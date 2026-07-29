/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Affine
public import CryptBoolean.Carlet.Chapter04.Resiliency
public import FABL.Chapter06.F₂Polynomials.Siegenthaler

/-!
# Algebraic degree of resilient Boolean functions

Carlet Chapter 7: Siegenthaler's algebraic-degree bounds for resilient and
correlation-immune Boolean functions, including the highest resilient order.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Encoding the sign-cube view of a bit-valued Boolean function recovers the
original function. -/
@[simp] theorem booleanFunctionF₂Encoding_signCubeView
    (f : BooleanFunction n) :
    FABL.booleanFunctionF₂Encoding (signCubeView f) = f := by
  funext x
  unfold FABL.booleanFunctionF₂Encoding signCubeView
  rw [(FABL.binaryCubeSignEquiv n).symm_apply_apply]
  change FABL.binarySignEquiv.symm (FABL.binarySignEquiv (f x)) = f x
  rw [FABL.binarySignEquiv.symm_apply_apply]

/-- Siegenthaler's bound: an `m`-resilient Boolean function has algebraic
degree at most `n - m - 1` when `m < n - 1`. -/
theorem functionAlgebraicDegree_le_sub_sub_one_of_isResilient
    (f : BooleanFunction n) (m : ℕ) (hf : IsResilient m f)
    (hm : m < n - 1) :
    FABL.functionAlgebraicDegree f ≤ n - m - 1 := by
  simpa using
    FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient
      (signCubeView f) m (isResilient_iff_fabl m f |>.mp hf) hm

/-- Siegenthaler's correlation-immunity bound: an `m`th-order
correlation-immune Boolean function has algebraic degree at most `n - m` when
`m < n`. -/
theorem functionAlgebraicDegree_le_sub_of_isCorrelationImmune
    (f : BooleanFunction n) (m : ℕ) (hf : IsCorrelationImmune m f)
    (hm : m < n) :
    FABL.functionAlgebraicDegree f ≤ n - m := by
  simpa using
    FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isCorrelationImmune
      (signCubeView f) m (isCorrelationImmune_iff_fabl m f |>.mp hf) hm

/-- At the highest meaningful resilient order, the algebraic degree is at
most one. -/
theorem functionAlgebraicDegree_le_one_of_isResilient_natPred
    (f : BooleanFunction n) (hn : 0 < n)
    (hf : IsResilient (n - 1) f) :
    FABL.functionAlgebraicDegree f ≤ 1 := by
  have hdegree := functionAlgebraicDegree_le_sub_of_isCorrelationImmune
    f (n - 1) hf.1 (by omega)
  omega

/-- Every `(n - 1)`-resilient Boolean function in positive dimension is
affine. -/
theorem exists_affineFunction_of_isResilient_natPred
    (f : BooleanFunction n) (hn : 0 < n)
    (hf : IsResilient (n - 1) f) :
    ∃ b a, f = FABL.affineFunction b a :=
  FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one f
    (functionAlgebraicDegree_le_one_of_isResilient_natPred f hn hf)

end CryptBoolean
