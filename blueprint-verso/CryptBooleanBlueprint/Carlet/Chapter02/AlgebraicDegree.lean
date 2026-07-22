/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.Restrictions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic degree, distance, and affine functions" =>

:::definition "carlet-2-def-algebraic-degree" (parent := "carlet-chapter-2") (lean := "FABL.functionAlgebraicDegree, FABL.functionAlgebraicDegree_le_dimension, FABL.algebraicDegree_le_iff, FABL.anfCoeff_zero, FABL.algebraicDegree_zero, FABL.functionAlgebraicDegree_zero") (uses := "carlet-2-anf-existence-uniqueness") (tags := "carlet, chapter-2, algebraic-degree, page-12, fidelity-exact-with-zero-convention")
*Algebraic degree (Carlet, p. 12).* Let
$$`
f(x)=\bigoplus_{S\subseteq[n]}c_{f,S}x^S
`
be the unique ANF of $`f:V_n\to\mathbb F_2`. Define
$$`
\deg_{\mathrm{alg}}(f)
=\max\{|S|:c_{f,S}\ne0\},
`
with $`\deg_{\mathrm{alg}}(0)=0`. Then
$$`
\deg_{\mathrm{alg}}(f)\le n,
`
and, for every $`r\ge0`,
$$`
\deg_{\mathrm{alg}}(f)\le r
\quad\Longleftrightarrow\quad
c_{f,S}\ne0\Longrightarrow |S|\le r
\quad\text{for every }S\subseteq[n].
`
:::

:::lemma_ "carlet-2-support-degree-addition" (parent := "carlet-chapter-2") (lean := "FABL.anfCoeff_add, FABL.algebraicDegree_add_le_max, FABL.functionAlgebraicDegree_add_le_max") (uses := "carlet-2-def-algebraic-degree") (tags := "carlet, chapter-2, support, reed-muller-prerequisite, fidelity-derived")
*Degree under addition.* For all Boolean functions $`f,g:V_n\to\mathbb F_2`,
their ANF coefficients satisfy
$$`
c_{f+g,S}=c_{f,S}+c_{g,S}
\qquad(S\subseteq[n]),
`
and therefore
$$`
\deg_{\mathrm{alg}}(f+g)
\le\max\{\deg_{\mathrm{alg}}(f),\deg_{\mathrm{alg}}(g)\}.
`
:::

:::definition "carlet-2-def-hamming-distance" (parent := "carlet-chapter-2") (lean := "CryptBoolean.hammingDistance, CryptBoolean.hammingDistance_eq_hammingWeight_add") (uses := "carlet-2-def-support-weight") (tags := "carlet, chapter-2, hamming-distance, page-8, fidelity-exact")
*Hamming distance (Carlet, p. 8).* For Boolean functions
$`f,g:V_n\to\mathbb F_2`, define
$$`
d_H(f,g)
=\bigl|\{x\in V_n:f(x)\ne g(x)\}\bigr|.
`
Then
$$`
d_H(f,g)=w_H(f+g),
`
where addition is pointwise in $`\mathbb F_2`.
:::

:::theorem "carlet-2-bridge-relative-hamming-distance" (parent := "carlet-chapter-2") (lean := "CryptBoolean.hammingDistance_eq_two_pow_mul_relativeHammingDist") (uses := "carlet-2-def-hamming-distance") (tags := "carlet, chapter-2, hamming-distance, normalization-bridge, fidelity-explicit-bridge")
*Relative-distance normalization bridge.* Define
$$`
d_{\mathrm{rel}}(f,g)
=2^{-n}\bigl|\{x\in V_n:f(x)\ne g(x)\}\bigr|.
`
Then, for all $`f,g:V_n\to\mathbb F_2`,
$$`
d_H(f,g)=2^n d_{\mathrm{rel}}(f,g).
`
:::

*Formalization note.* The raw distance is implemented by
[Mathlib](https://github.com/leanprover-community/mathlib4)'s `hammingDist`, while
$`d_{\mathrm{rel}}` is [FABL](https://github.com/Polarnova/FABL)'s
`relativeHammingDist`. Neither implementation choice is part of Carlet's definition.

:::definition "carlet-2-def-affine-functions" (parent := "carlet-chapter-2") (lean := "FABL.affineFunction, FABL.affineCoefficients, FABL.anfEval_affineCoefficients, FABL.anfCoeff_affineFunction, FABL.functionAlgebraicDegree_affineFunction_le_one, FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one") (uses := "carlet-2-def-algebraic-degree") (tags := "carlet, chapter-2, affine-functions, page-14, fidelity-exact")
*Affine Boolean functions (Carlet, p. 14).* For $`a\in V_n` and
$`b\in\mathbb F_2`, set
$$`
A_{a,b}(x)=b+a\mathbin\cdot x.
`
Its ANF coefficients are
$$`
c_{A_{a,b},\varnothing}=b,
\qquad
c_{A_{a,b},\{i\}}=a_i,
\qquad
c_{A_{a,b},S}=0\quad(|S|>1).
`
For every $`f:V_n\to\mathbb F_2`,
$$`
\deg_{\mathrm{alg}}(f)\le1
\quad\Longleftrightarrow\quad
\exists a\in V_n\;\exists b\in\mathbb F_2\;
\forall x\in V_n,\ f(x)=A_{a,b}(x).
`
:::

:::theorem "carlet-2-affine-invariance" (parent := "carlet-chapter-2") (lean := "FABL.anfMonomial_mul, FABL.anfMul, FABL.anfEval_anfMul, FABL.algebraicDegree_anfMul_le_add, FABL.anfCoeff_mul, FABL.functionAlgebraicDegree_mul_le_add, FABL.functionAlgebraicDegree_one, FABL.functionAlgebraicDegree_finset_prod_le, FABL.functionAlgebraicDegree_finset_sum_le, FABL.functionAlgebraicDegree_affineMap_coordinate_le_one, FABL.functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card, FABL.functionAlgebraicDegree_comp_affineMap_le, FABL.functionAlgebraicDegree_comp_affineEquiv") (uses := "carlet-2-def-algebraic-degree, carlet-2-def-affine-functions") (tags := "carlet, chapter-2, affine-invariance, page-12, fidelity-exact")
*Affine invariance of algebraic degree (Carlet, p. 12).* Let
$`L:V_n\to V_n` be an affine isomorphism, so that
$`L(x)=Mx+t` for some $`M\in\operatorname{GL}_n(\mathbb F_2)` and $`t\in V_n`.
Then every Boolean function $`f:V_n\to\mathbb F_2` satisfies
$$`
\deg_{\mathrm{alg}}(f\circ L)=\deg_{\mathrm{alg}}(f).
`
:::

*Formalization note.* The proof first establishes nonincrease under an arbitrary affine map by
substituting affine coordinate functions into the unique square-free ANF, then applies the same
bound to $`L^{-1}`.

:::theorem "carlet-2-restriction-recovery" (parent := "carlet-chapter-2") (lean := "CryptBoolean.supportPrecedes, CryptBoolean.supportPrecedesDecidable, CryptBoolean.lowWeightInputs, CryptBoolean.restrictionRecoveryCoefficient, CryptBoolean.card_powerset_filter_card_le, CryptBoolean.card_intermediate_subsets_le, CryptBoolean.restrictionRecoveryFormula_f₂CubeOfFinset, CryptBoolean.restrictionRecoveryFormula, CryptBoolean.eq_of_eq_on_lowWeightInputs, CryptBoolean.eq_of_eq_on_affineImage_lowWeightInputs") (uses := "carlet-2-anf-existence-uniqueness, carlet-2-affine-invariance") (tags := "carlet, chapter-2, restriction-recovery, pages-13-14, fidelity-exact")
*Recovery from low-weight restrictions (Carlet, pp. 13--14).* Write
$`y\preceq x` when $`\operatorname{supp}(y)\subseteq\operatorname{supp}(x)`, and
let $`E_d=\{y\in V_n:w_H(y)\le d\}`. If
$`f:V_n\to\mathbb F_2` satisfies $`\deg_{\mathrm{alg}}(f)\le d<n`, then for
every $`x\in V_n`,
$$`
f(x)
=\bigoplus_{\substack{y\preceq x\\y\in E_d}}
f(y)
\left[
\sum_{i=0}^{d-w_H(y)}
\binom{w_H(x)-w_H(y)}{i}
\bmod 2
\right].
`
Consequently, $`f` is uniquely determined by its restriction to $`E_d`. More generally, for every
affine automorphism $`L\in\operatorname{AGL}(V_n)`, it is uniquely determined by its restriction
to $`L(E_d)`.
:::
