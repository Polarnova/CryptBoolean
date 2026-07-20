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

:::theorem "carlet-2-nnf-existence-uniqueness" (parent := "carlet-chapter-2") (lean := "CryptBoolean.PseudoBooleanFunction, CryptBoolean.NumericalCoefficients, CryptBoolean.numericalMonomial, CryptBoolean.numericalEval, CryptBoolean.numericalEvalLinear, CryptBoolean.numericalEval_injective, CryptBoolean.existsUnique_numericalEval, CryptBoolean.numericalCoeff, CryptBoolean.numericalEval_numericalCoeff, CryptBoolean.numericalCoeff_eq_value_sub_lower") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, numerical-normal-form, pages-18-19, fidelity-exact")
*Numerical normal form (Carlet, pp. 18--19).* Every pseudo-Boolean function
$`\varphi:V_n\to\mathbb R` admits a unique family
$`(\lambda_S)_{S\subseteq[n]}` such that
$$`
\varphi(x)=\sum_{S\subseteq[n]}\lambda_S\prod_{i\in S}x_i
\qquad(x\in V_n).
`
Equivalently,
$$`
\varphi(x)=\sum_{S\subseteq\operatorname{supp}(x)}\lambda_S.
`
For every $`S\subseteq[n]`, the coefficients therefore satisfy
$$`
\lambda_S
=\varphi(\mathbf 1_S)-\sum_{T\subsetneq S}\lambda_T.
`
:::

:::proposition "carlet-2-prop-4-nnf-mobius" (parent := "carlet-chapter-2") (lean := "CryptBoolean.sum_Icc_neg_one_pow_card_sub, CryptBoolean.numericalMobiusCoeff, CryptBoolean.numericalEval_numericalMobiusCoeff_f₂CubeOfFinset, CryptBoolean.numericalMobiusCoeff_eq_numericalCoeff, CryptBoolean.numericalCoeff_eq_mobius_sum") (uses := "carlet-2-nnf-existence-uniqueness") (tags := "carlet, chapter-2, proposition-4, relation-8, page-19, fidelity-exact")
*Proposition 4 (Carlet, Relation (8), p. 19).* If
$`\varphi(x)=\sum_{S\subseteq[n]}\lambda_Sx^S`, then for every
$`S\subseteq[n]`,
$$`
\lambda_S
=(-1)^{|S|}
  \sum_{\substack{x\in V_n\\\operatorname{supp}(x)\subseteq S}}
    (-1)^{w_H(x)}\varphi(x)
=\sum_{T\subseteq S}(-1)^{|S|-|T|}\varphi(\mathbf 1_T).
`
:::

:::proposition "carlet-2-prop-5-nnf-integrality" (parent := "carlet-chapter-2") (lean := "CryptBoolean.IsIntegerValued, CryptBoolean.IsBooleanValued, CryptBoolean.numericalEval_integerValued_iff, CryptBoolean.numericalEval_booleanValued_iff_sum_sq_eq_sum") (uses := "carlet-2-prop-4-nnf-mobius") (tags := "carlet, chapter-2, proposition-5, page-21, fidelity-exact")
*Proposition 5 (Carlet, p. 21).* Let
$$`
P(x)=\sum_{S\subseteq[n]}\lambda_Sx^S
\in\mathbb R[x_1,\ldots,x_n]/(x_1^2-x_1,\ldots,x_n^2-x_n).
`
The function represented by $`P` is integer-valued on $`V_n` if and only if
$`\lambda_S\in\mathbb Z` for every $`S\subseteq[n]`. Under this integrality
hypothesis, $`P` is Boolean-valued if and only if
$$`
\sum_{x\in V_n}P(x)^2=\sum_{x\in V_n}P(x).
`
:::
