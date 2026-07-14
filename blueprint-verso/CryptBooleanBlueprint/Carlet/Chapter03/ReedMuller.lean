/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter03.ReedMullerDuality

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Reed--Muller codes" =>

:::theorem "carlet-3-affine-weight" (lean := "CryptBoolean.realSignView_affineFunction, CryptBoolean.isBalanced_affineFunction_of_ne_zero, CryptBoolean.hammingWeight_affineFunction_of_ne_zero") (uses := "carlet-2-def-affine-functions, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-3, affine-weight, page-38, fidelity-exact")
*Weight of a nonconstant affine function (Carlet, p. 38).* For
$`a\in V_n`, $`b\in\mathbb F_2`, and $`x\in V_n`,
$$`
(A_{a,b})_\chi(x)=(-1)^b(-1)^{a\mathbin\cdot x}.
`
If $`a\ne0`, then $`A_{a,b}` is balanced and
$$`
w_H(A_{a,b})=2^{n-1}.
`
:::

:::definition "carlet-3-reed-muller-code" (lean := "CryptBoolean.reedMuller, CryptBoolean.mem_reedMuller_iff, CryptBoolean.reedMuller_mono, CryptBoolean.affineFunction_mem_reedMuller_one, CryptBoolean.reedMuller_distance_pos") (uses := "carlet-2-def-algebraic-degree, carlet-2-support-degree-addition, carlet-2-def-hamming-distance, carlet-2-def-affine-functions") (tags := "carlet, chapter-3, reed-muller-code, pages-37-38, fidelity-exact-with-derived-laws")
*Reed--Muller code (Carlet, pp. 37--38).* The Reed--Muller code of order
$`r` in $`n` variables is
$$`
R(r,n)
=\{f:V_n\to\mathbb F_2:\deg_{\mathrm{alg}}(f)\le r\}.
`
It is an $`\mathbb F_2`-linear subspace of the space of Boolean functions. If
$`r\le s`, then
$$`
R(r,n)\subseteq R(s,n),
`
and every affine function belongs to $`R(1,n)`. Moreover, if
$`f,g\in R(r,n)` and $`f\ne g`, then
$$`
d_H(f,g)>0.
`
:::

:::theorem "carlet-3-theorem-1-order-one" (lean := "CryptBoolean.hammingWeight_affineFunction_one_zero, CryptBoolean.two_pow_sub_one_le_hammingWeight_of_degree_le_one, CryptBoolean.reedMuller_one_distance_lower_bound") (uses := "carlet-3-reed-muller-code, carlet-2-def-affine-functions, carlet-3-affine-weight, carlet-2-support-degree-addition, carlet-2-def-hamming-distance") (tags := "carlet, chapter-3, theorem-1, order-one, fidelity-derived-specialization")
*Derived order-one specialization of Carlet's Theorem 1.* Let $`n\ge1`. If
$`f:V_n\to\mathbb F_2` is nonzero and
$`\deg_{\mathrm{alg}}(f)\le1`, then
$$`
w_H(f)\ge2^{n-1}.
`
Equivalently, for all distinct $`f,g\in R(1,n)`,
$$`
d_H(f,g)\ge2^{n-1}.
`
:::

:::theorem "carlet-3-theorem-1" (lean := "CryptBoolean.two_pow_sub_le_hammingWeight_of_degree_le, CryptBoolean.reedMuller_distance_lower_bound") (uses := "carlet-3-reed-muller-code, carlet-2-def-hamming-distance, carlet-2-anf-existence-uniqueness") (tags := "carlet, chapter-3, theorem-1, page-36, fidelity-exact")
*Theorem 1 (Carlet, p. 36).* Let $`0\le r\le n`. If
$`f,g:V_n\to\mathbb F_2` are distinct and
$$`
\deg_{\mathrm{alg}}(f)\le r,
\qquad
\deg_{\mathrm{alg}}(g)\le r,
`
then
$$`
d_H(f,g)\ge2^{n-r}.
`
Equivalently, every nonzero Boolean function $`h` of algebraic degree at most
$`r` satisfies $`w_H(h)\ge2^{n-r}`.
:::

:::proposition "carlet-3-prop-12" (uses := "carlet-3-theorem-1") (tags := "carlet, chapter-3, proposition-12, pages-36-37, source-open")
*Proposition 12 (Carlet, pp. 36--37).* Let $`0\le r\le n`. A Boolean
function $`f:V_n\to\mathbb F_2` satisfies
$$`
\deg_{\mathrm{alg}}(f)=r
\qquad\text{and}\qquad
w_H(f)=2^{n-r}
`
if and only if $`f` is the indicator of an $`(n-r)`-dimensional affine
subspace of $`V_n`.
:::

:::theorem "carlet-3-reed-muller-dimension" (lean := "CryptBoolean.reedMuller_card, CryptBoolean.reedMuller_finrank") (uses := "carlet-3-reed-muller-code, carlet-2-anf-existence-uniqueness") (tags := "carlet, chapter-3, reed-muller-dimension, page-38, fidelity-exact")
*Dimension of the Reed--Muller code (Carlet, p. 38).* For $`0\le r\le n`,
$$`
\dim_{\mathbb F_2}R(r,n)=\sum_{i=0}^{r}\binom ni.
`
Consequently,
$$`
|R(r,n)|=2^{\sum_{i=0}^{r}\binom ni}.
`
:::

:::theorem "carlet-3-theorem-2" (lean := "CryptBoolean.booleanFunctionPairing, CryptBoolean.booleanFunctionPairing_apply, CryptBoolean.booleanFunctionPairing_nondegenerate, CryptBoolean.reedMullerDual, CryptBoolean.reedMuller_complement_le_dual, CryptBoolean.reedMullerDual_eq") (uses := "carlet-3-reed-muller-dimension, carlet-3-reed-muller-code") (tags := "carlet, chapter-3, theorem-2, pages-38-39, fidelity-exact")
*Theorem 2 (Carlet, pp. 38--39).* Let $`0\le r<n`. Equip Boolean functions
with the $`\mathbb F_2`-valued inner product
$$`
\langle f,g\rangle
=\bigoplus_{x\in V_n}f(x)g(x).
`
Then
$$`
R(r,n)^\perp=R(n-r-1,n).
`
:::
