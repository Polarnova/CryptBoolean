/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.SupportCode
import CryptBoolean.Carlet.Chapter06.WalshCongruence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bentness" =>

:::definition "carlet-6-def-7-bent" (parent := "carlet-chapter-6") (lean := "CryptBoolean.natAbs_walshTransform_eq_two_pow_half_of_isBent, CryptBoolean.maxWalshMagnitude_eq_two_pow_half_of_isBent, CryptBoolean.nonlinearity_eq_two_pow_sub_two_pow_half_of_isBent, CryptBoolean.isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half, CryptBoolean.isBent_add_affineFunction_iff, CryptBoolean.isBent_comp_affineEquiv_iff, CryptBoolean.abs_hammingDistance_affine_sub_half_of_isBent") (uses := "carlet-4-rel-36-covering-radius-bent, carlet-4-nonlinearity-affine-invariance, carlet-2-def-walsh-transform, carlet-2-def-hamming-distance") (tags := "carlet, chapter-6, definition-7, pages-77-78, fidelity-exact")
*Definition 7 (Carlet, pp. 77--78).* Let $`n` be even. A Boolean function
$`f:V_n\to\mathbb F_2` is bent when
$$`
\operatorname{nl}(f)=2^{n-1}-2^{n/2-1}.
`
Equivalently, $`|W_f(a)|=2^{n/2}` for every $`a\in V_n`, or the distance
from $`f` to every affine function is $`2^{n-1}\pm2^{n/2-1}`. Bentness is
preserved by affine changes of variables and by addition of affine functions.
:::

:::lemma_ "carlet-6-lemma-2-walsh-congruence" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_iff_forall_walshTransform_modeq") (uses := "carlet-6-def-7-bent, carlet-2-parseval") (tags := "carlet, chapter-6, lemma-2, page-77, fidelity-exact")
*Lemma 2 (Carlet, p. 77).* Let $`n\ge2` be even. A Boolean function
$`f:V_n\to\mathbb F_2` is bent if and only if
$$`
W_f(a)\equiv 2^{n/2}\pmod {2^{n/2+1}}
\qquad(a\in V_n).
`
:::

:::theorem "carlet-6-theorem-8-perfect-nonlinearity" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_iff_forall_nonzero_derivative_isBalanced, CryptBoolean.isBent_iff_satisfiesPropagationCriterion_dimension") (uses := "carlet-6-def-7-bent, carlet-2-rel-25-wiener-khinchin, carlet-4-def-propagation-criteria") (tags := "carlet, chapter-6, theorem-8, page-78, fidelity-exact")
*Theorem 8 (Carlet, p. 78).* A Boolean function $`f:V_n\to\mathbb F_2`
is bent if and only if every derivative in a nonzero direction is balanced:
$$`
\forall a\in V_n\setminus\{0\},\qquad D_af\text{ is balanced}.
`
Equivalently, $`f` satisfies the propagation criterion of degree $`n`.
:::

:::proposition "carlet-6-prop-16-support-code" (parent := "carlet-chapter-6") (lean := "CryptBoolean.supportCodeMap, CryptBoolean.supportCode, CryptBoolean.supportCodewordWeight, CryptBoolean.supportCodewordWeight_zero, CryptBoolean.supportCodewordWeight_eq_card_filter, CryptBoolean.codeCharacterSum_support_eq_card_sub_two_weight, CryptBoolean.four_mul_supportCodewordWeight_eq, CryptBoolean.SupportCodeHasExactlyTwoNonzeroWeights, CryptBoolean.isBent_iff_supportCode_finrank_and_two_nonzero_weights") (uses := "carlet-6-def-7-bent, carlet-4-resiliency-support-dual-distance, carlet-2-balanced-zero-walsh, carlet-2-parseval") (tags := "carlet, chapter-6, proposition-16, pages-78-79, fidelity-corrected-dimension-range")
*Proposition 16 (Carlet, pp. 78--79; corrected dimension range).* Let
$`n\ge4` be even, let $`S_f=\{u_1,\ldots,u_w\}` be the support of
$`f:V_n\to\mathbb F_2`, and let
$$`
C_f=\{(v\mathbin\cdot u_1,\ldots,v\mathbin\cdot u_w):v\in V_n\}.
`
Then $`f` is bent if and only if $`\dim C_f=n` and the nonzero words of
$`C_f` have exactly the two weights
$$`
2^{n-2}\quad\text{and}\quad w_H(f)-2^{n-2},
`
with both weights occurring.
:::

For $`n=2`, every bent function has odd support size, so the second displayed
quantity can coincide with zero; the printed positive-even formulation is
therefore false in that dimension.
