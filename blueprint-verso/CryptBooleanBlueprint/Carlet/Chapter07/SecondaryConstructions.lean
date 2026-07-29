/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.DisjointTruthSupport
import CryptBoolean.Carlet.Chapter07.IndirectSumDegree
import CryptBoolean.Carlet.Chapter07.Tarannikov
import CryptBoolean.Carlet.Chapter07.ThreeFunctionConstruction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Secondary constructions" =>

:::theorem "carlet-7-tarannikov-elementary-construction" (parent := "carlet-chapter-7") (lean := "CryptBoolean.tarannikovPenultimateIndex, CryptBoolean.tarannikovLastIndex, CryptBoolean.tarannikovShearLinearMap, CryptBoolean.tarannikovShearLinearMap_involutive, CryptBoolean.tarannikovShearLinearEquiv, CryptBoolean.tarannikovCoordinates, CryptBoolean.tarannikovCoordinates_eq_append, CryptBoolean.tarannikovElementaryConstruction, CryptBoolean.walshTransform_oneVariableParity_singletonF₂Cube, CryptBoolean.f₂DotProduct_tarannikovCoordinates, CryptBoolean.exists_eq_tarannikovCoordinates, CryptBoolean.f₂DotProduct_tarannikovShear, CryptBoolean.walshTransform_tarannikovElementaryConstruction, CryptBoolean.nonlinearity_tarannikovElementaryConstruction, CryptBoolean.card_f₂Support_tarannikovCoordinates, CryptBoolean.card_f₂Support_singletonF₂Cube, CryptBoolean.isResilient_tarannikovElementaryConstruction, CryptBoolean.isResilient_succ_tarannikovElementaryConstruction, CryptBoolean.functionAlgebraicDegree_tarannikovElementaryConstruction, CryptBoolean.tarannikovLinearStructureDirection, CryptBoolean.tarannikovLinearStructureDirection_ne_zero, CryptBoolean.tarannikovShearLinearEquiv_direction, CryptBoolean.tarannikovLinearStructureDirection_isNonzeroLinearStructure") (uses := "carlet-7-adding-variable, carlet-2-affine-invariance, carlet-4-theorem-3, carlet-4-rel-35-nonlinearity-walsh, carlet-4-def-linear-kernel") (tags := "carlet, chapter-7, tarannikov, resilient-construction, page-125, fidelity-exact")
*Tarannikov's elementary construction (Carlet, p. 125).* Let
$`g:V_r\to\mathbb F_2` and define
$$`
h(x_1,\ldots,x_r,z)
=z\oplus g(x_1,\ldots,x_{r-1},x_r\oplus z).
`
Its Walsh transform is zero when the last two frequency coordinates are
equal and otherwise is twice the corresponding Walsh coefficient of $`g`.
Consequently,
$$`
\operatorname{nl}(h)=2\operatorname{nl}(g).
`
If $`g` is $`m`-resilient, then $`h` is $`m`-resilient. If additionally
$`W_g(a,1)=0` for every $`a` of weight at most $`m`, then $`h` is
$`(m+1)`-resilient. If $`\deg_{\mathrm{alg}}g\ge1`, then
$`\deg_{\mathrm{alg}}h=\deg_{\mathrm{alg}}g`. The direction supported on
the last two coordinates is a nonzero linear structure of $`h`.
:::

:::theorem "carlet-7-theorem-14-indirect-sum" (parent := "carlet-chapter-7") (lean := "CryptBoolean.two_mul_walshTransform_indirectSum, CryptBoolean.walshTransform_indirectSum_cast_eq_relation_66, CryptBoolean.isResilient_indirectSum, CryptBoolean.two_mul_maxWalshMagnitude_indirectSum_of_disjointWalshSupport, CryptBoolean.nonlinearity_indirectSum_cast_eq_relation_67_spectral, CryptBoolean.nonlinearity_indirectSum_cast_eq_relation_67") (uses := "carlet-6-indirect-sum, carlet-7-direct-sum-resilient, carlet-4-theorem-3, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, theorem-14, indirect-sum, relations-66-67, pages-126-127, fidelity-exact")
*Theorem 14 (Carlet, Relations (66)--(67), pp. 126--127).* Let $`r,s>0`,
$`t<r`, and $`m<s`. Let $`f_1,f_2:V_r\to\mathbb F_2` be $`t`-resilient
and $`g_1,g_2:V_s\to\mathbb F_2` be $`m`-resilient. Define
$$`
h(x,y)=f_1(x)\oplus g_1(y)
  \oplus(f_1\oplus f_2)(x)(g_1\oplus g_2)(y).
`
Then $`h` is $`(t+m+1)`-resilient and
$$`
W_h(a,b)=\frac12W_{f_1}(a)(W_{g_1}(b)+W_{g_2}(b))
        +\frac12W_{f_2}(a)(W_{g_1}(b)-W_{g_2}(b)).
`
If the Walsh supports of $`f_1,f_2` are disjoint and likewise those of
$`g_1,g_2`, then
$$`
\operatorname{nl}(h)
=\min_{i,j\in\{1,2\}}
  \left(
    2^{r+s-2}
    +2^{r-1}\operatorname{nl}(g_j)
    +2^{s-1}\operatorname{nl}(f_i)
    -\operatorname{nl}(f_i)\operatorname{nl}(g_j)
  \right).
`
:::

:::theorem "carlet-7-theorem-14-indirect-sum-degree" (parent := "carlet-chapter-7") (lean := "CryptBoolean.booleanBlockProduct, CryptBoolean.booleanBlockProduct_append, CryptBoolean.functionAlgebraicDegree_booleanBlockProduct, CryptBoolean.functionAlgebraicDegree_indirectSum, CryptBoolean.functionAlgebraicDegree_indirectSum_of_leftDifference_eq_zero, CryptBoolean.functionAlgebraicDegree_indirectSum_of_leftDifference_eq_one, CryptBoolean.functionAlgebraicDegree_indirectSum_of_rightDifference_eq_zero, CryptBoolean.functionAlgebraicDegree_indirectSum_of_rightDifference_eq_one") (uses := "carlet-7-theorem-14-indirect-sum, carlet-7-direct-sum-degree, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, theorem-14, indirect-sum, algebraic-degree, pages-126-127, fidelity-corrected-nonconstant-hypotheses")
*Degree clause of Theorem 14 (Carlet, pp. 126--127).* If
$`f_1\oplus f_2` and $`g_1\oplus g_2` are both nonconstant, then
$$`
\deg_{\mathrm{alg}}h=\max\bigl(
  \deg_{\mathrm{alg}}f_1,\deg_{\mathrm{alg}}g_1,
  \deg_{\mathrm{alg}}(f_1\oplus f_2)
    +\deg_{\mathrm{alg}}(g_1\oplus g_2)
\bigr).
`
If either difference is constant, the corresponding branch reduces to a
direct sum and has the degree supplied by that specialization.
:::

:::proposition "carlet-7-prop-34-three-function-construction" (parent := "carlet-chapter-7") (lean := "CryptBoolean.isCorrelationImmune_threeFunctionSum_iff_pairwiseProductSum, CryptBoolean.isResilient_threeFunctionSum_iff_pairwiseProductSum, CryptBoolean.two_mul_maxWalshMagnitude_pairwiseProductSum_le, CryptBoolean.relation_68_threeFunctionConstruction, CryptBoolean.nonlinearity_pairwiseProductSum_cast_lower_bound") (uses := "carlet-6-prop-22-three-function-identity, carlet-4-theorem-3, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, proposition-34, three-function-construction, relations-68-69, pages-127-128, fidelity-exact")
*Proposition 34 (Carlet, Relations (68)--(69), pp. 127--128).* Let
$`n>0` and $`k<n`. Let $`f_1,f_2,f_3:V_n\to\mathbb F_2` each be
correlation immune of order $`k`, respectively $`k`-resilient. Put
$$`
s_1=f_1\oplus f_2\oplus f_3,\qquad
s_2=f_1f_2\oplus f_1f_3\oplus f_2f_3.
`
Then $`s_1` is correlation immune of order $`k`, respectively
$`k`-resilient, if and only if $`s_2` has the same property. Moreover,
$$`
\operatorname{nl}(s_2)\ge
\frac12\left(
  \operatorname{nl}(s_1)+
  \sum_{i=1}^3\operatorname{nl}(f_i)-2^{n-1}
\right).
`
:::

:::theorem "carlet-7-rel-69-three-function-disjoint-spectra" (parent := "carlet-chapter-7") (lean := "CryptBoolean.two_mul_maxWalshMagnitude_pairwiseProductSum_le_of_pairwiseDisjoint, CryptBoolean.relation_69_threeFunctionConstruction, CryptBoolean.nonlinearity_pairwiseProductSum_cast_lower_bound_of_pairwiseDisjoint") (uses := "carlet-7-prop-34-three-function-construction, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, relation-69, three-function-construction, disjoint-walsh-support, page-128, fidelity-exact")
*Relation (69) (Carlet, p. 128).* Under the hypotheses of Proposition 34,
suppose the Walsh supports of $`f_1,f_2,f_3` are pairwise disjoint. Then
$$`
\operatorname{nl}(s_2)\ge
\frac12\left(
  \operatorname{nl}(s_1)+
  \min_{1\le i\le3}\operatorname{nl}(f_i)
\right).
`
:::

:::theorem "carlet-7-disjoint-truth-support-sum" (parent := "carlet-chapter-7") (lean := "CryptBoolean.hammingWeight_add_eq_of_disjoint_truthSupport, CryptBoolean.isBalanced_add_iff_hammingWeight_add_eq_two_pow_pred, CryptBoolean.walshTransform_add_of_disjoint_truthSupport, CryptBoolean.isResilient_add_of_disjoint_truthSupport, CryptBoolean.maxWalshMagnitude_add_le_of_disjoint_truthSupport, CryptBoolean.nonlinearity_add_le_two_pow_pred_add_of_disjoint_truthSupport, CryptBoolean.nonlinearity_add_sub_two_pow_pred_le_of_disjoint_truthSupport, CryptBoolean.functionAlgebraicDegree_add_le_max_of_disjoint_truthSupport, CryptBoolean.exists_disjoint_truthSupport_functionAlgebraicDegree_add_eq_max") (uses := "carlet-2-def-support-weight, carlet-4-theorem-3, carlet-4-rel-35-nonlinearity-walsh, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, disjoint-support, resiliency, nonlinearity, algebraic-degree, page-128, fidelity-exact")
*Sums with disjoint truth supports (Carlet, p. 128).* Let
$`g,h:V_n\to\mathbb F_2` have disjoint truth supports and put
$`f=g\oplus h`. Then $`f` is balanced exactly when
$$`
w_H(g)+w_H(h)=2^{n-1}.
`
If $`g` and $`h` are correlation immune of order $`m` and $`f` is
balanced, then $`f` is $`m`-resilient and
$$`
\operatorname{nl}(f)
\ge\operatorname{nl}(g)+\operatorname{nl}(h)-2^{n-1}.
`
Also
$$`
\deg_{\mathrm{alg}}f
\le\max(\deg_{\mathrm{alg}}g,\deg_{\mathrm{alg}}h),
`
and equality can occur.
:::
