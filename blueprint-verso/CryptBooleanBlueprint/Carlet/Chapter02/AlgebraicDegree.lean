/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.Affine

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic degree, distance, and affine functions" =>

:::definition "carlet-2-function-degree-distance" (lean := "CryptBoolean.functionAlgebraicDegree, CryptBoolean.functionAlgebraicDegree_le_dimension, CryptBoolean.algebraicDegree_le_iff, CryptBoolean.anfCoeff_add, CryptBoolean.anfCoeff_zero, CryptBoolean.algebraicDegree_zero, CryptBoolean.functionAlgebraicDegree_zero, CryptBoolean.algebraicDegree_add_le_max, CryptBoolean.functionAlgebraicDegree_add_le_max, CryptBoolean.hammingDistance, CryptBoolean.hammingDistance_eq_hammingWeight_add, CryptBoolean.hammingDistance_eq_two_pow_mul_relativeHammingDist") (uses := "carlet-2-anf-existence-uniqueness, carlet-2-def-support-weight") (tags := "carlet, chapter-2, algebraic-degree, hamming-distance, mathlib-reuse")
Function-level algebraic degree is the degree of the unique ANF and remains distinct
from real Fourier degree.  It is submaximal under addition.  Raw Hamming distance is
[Mathlib](https://github.com/leanprover-community/mathlib4)'s `hammingDist`, equals the weight of the Boolean sum, and scales [FABL](https://github.com/Polarnova/FABL)'s
relative distance by $`2^n`.
:::

:::theorem "carlet-2-affine-functions" (lean := "CryptBoolean.affineFunction, CryptBoolean.affineCoefficients, CryptBoolean.anfEval_affineCoefficients, CryptBoolean.anfCoeff_affineFunction, CryptBoolean.functionAlgebraicDegree_affineFunction_le_one, CryptBoolean.exists_affineFunction_of_functionAlgebraicDegree_le_one, CryptBoolean.realSignView_affineFunction, CryptBoolean.isBalanced_affineFunction_of_ne_zero, CryptBoolean.hammingWeight_affineFunction_of_ne_zero") (uses := "carlet-2-function-degree-distance, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-2, affine, reed-muller-prerequisite")
Degree-at-most-one Boolean functions are exactly the affine functions
$`x\mapsto b+a\cdot x`.  A nonconstant affine function is balanced and has
weight $`2^{n-1}`.
:::
