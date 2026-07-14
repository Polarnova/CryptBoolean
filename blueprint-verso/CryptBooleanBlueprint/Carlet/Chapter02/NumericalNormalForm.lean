/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.NumericalNormalForm

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Numerical normal form" =>

:::theorem "carlet-2-nnf-existence-uniqueness" (lean := "CryptBoolean.PseudoBooleanFunction, CryptBoolean.NumericalCoefficients, CryptBoolean.numericalMonomial, CryptBoolean.numericalEval, CryptBoolean.numericalEvalLinear, CryptBoolean.numericalEval_injective, CryptBoolean.existsUnique_numericalEval, CryptBoolean.numericalCoeff, CryptBoolean.numericalEval_numericalCoeff, CryptBoolean.numericalCoeff_eq_value_sub_lower") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, section-2-1, nnf")
Every real-valued function on the binary cube has a unique multilinear numerical
normal form.  The canonical coefficient at $`S` is its value at $`\mathbf 1_S`
minus the lower-subset contribution.
:::

:::proposition "carlet-2-prop-4-nnf-mobius" (lean := "CryptBoolean.sum_Icc_neg_one_pow_card_sub, CryptBoolean.numericalMobiusCoeff, CryptBoolean.numericalEval_numericalMobiusCoeff_f₂CubeOfFinset, CryptBoolean.numericalMobiusCoeff_eq_numericalCoeff, CryptBoolean.numericalCoeff_eq_mobius_sum") (uses := "carlet-2-nnf-existence-uniqueness") (tags := "carlet, chapter-2, proposition-4, mobius")
The numerical coefficient is the real Möbius inverse
$`\lambda_S=\sum_{T\subseteq S}(-1)^{|S|-|T|}\varphi(\mathbf 1_T)`.
:::
