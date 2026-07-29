/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.Dobbertin
import CryptBoolean.Carlet.Chapter07.LinearPullback
import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandDegree
import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandOptimal
import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandUpper
import CryptBoolean.Carlet.Chapter07.PartialSpreadResilient

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Primary constructions" =>

:::definition "carlet-7-rel-59-maiorana-mcfarland-general" (parent := "carlet-chapter-7") (lean := "CryptBoolean.booleanMaioranaMcFarlandGeneral, CryptBoolean.booleanMaioranaMcFarlandGeneral_append") (uses := "carlet-5-def-maiorana-mcfarland") (tags := "carlet, chapter-7, relation-59, maiorana-mcfarland, page-117, fidelity-exact")
*Relation (59) (Carlet, p. 117).* Let $`r>0`, let $`r<n`, put
$`s=n-r`, let $`\varphi:V_s\to V_r`, and let
$`g:V_s\to\mathbb F_2`. Define
$$`
f_{\varphi,g}(x,y)
=x\mathbin\cdot\varphi(y)\oplus g(y)
=\bigoplus_{i=1}^r x_i\varphi_i(y)\oplus g(y).
`
:::

:::theorem "carlet-7-rel-60-maiorana-mcfarland-walsh" (parent := "carlet-chapter-7") (lean := "CryptBoolean.walshTransform_booleanMaioranaMcFarlandGeneral") (uses := "carlet-7-rel-59-maiorana-mcfarland-general, carlet-6-prop-20-general-maiorana-mcfarland, carlet-2-def-walsh-transform") (tags := "carlet, chapter-7, relation-60, maiorana-mcfarland, walsh-transform, page-117, fidelity-exact")
*Relation (60) (Carlet, p. 117).* For every $`a\in V_r` and $`b\in V_s`,
$$`
W_{f_{\varphi,g}}(a,b)
=2^r\sum_{y\in\varphi^{-1}(a)}
  (-1)^{g(y)\oplus b\cdot y}.
`
:::

:::theorem "carlet-7-maiorana-mcfarland-resiliency" (parent := "carlet-chapter-7") (lean := "CryptBoolean.isResilient_booleanMaioranaMcFarlandGeneral, CryptBoolean.isBalanced_booleanMaioranaMcFarlandGeneral, CryptBoolean.isResilient_succ_booleanMaioranaMcFarlandGeneral") (uses := "carlet-7-rel-60-maiorana-mcfarland-walsh, carlet-4-theorem-3") (tags := "carlet, chapter-7, maiorana-mcfarland, resiliency, pages-117-118, fidelity-exact")
*Resiliency of the general Maiorana--McFarland construction (Carlet, pp. 117--118).*
If $`w_H(\varphi(y))>k` for every $`y\in V_s`, then
$`f_{\varphi,g}` is $`k`-resilient. In particular, it is balanced when
$`0\notin\operatorname{im}(\varphi)`. If additionally the restriction of
$`g` to every fiber $`\varphi^{-1}(a)` is balanced, then
$`f_{\varphi,g}` is $`(k+1)`-resilient. An empty fiber satisfies the latter
condition vacuously.
:::

:::theorem "carlet-7-maiorana-mcfarland-degree" (parent := "carlet-chapter-7") (lean := "CryptBoolean.maioranaMcFarlandCoordinate, CryptBoolean.maioranaMcFarlandMapAlgebraicDegree, CryptBoolean.functionAlgebraicDegree_maioranaMcFarlandCoordinate_le, CryptBoolean.maioranaMcFarlandMapAlgebraicDegree_le_dimension, CryptBoolean.maioranaMcFarlandMapAlgebraicDegree_eq_dimension_iff, CryptBoolean.functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_le, CryptBoolean.functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff, CryptBoolean.functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_iff_mapDegree, CryptBoolean.functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_constant_one, CryptBoolean.le_r_sub_two_of_weight_gt_of_maioranaMcFarland_degree_eq, CryptBoolean.functionAlgebraicDegree_booleanMaioranaMcFarlandGeneral_eq_siegenthalerBound_iff, CryptBoolean.isResilient_and_functionAlgebraicDegree_eq_siegenthalerBound_iff") (uses := "carlet-7-rel-59-maiorana-mcfarland-general, carlet-7-siegenthaler-degree-bounds, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, maiorana-mcfarland, algebraic-degree, page-118, fidelity-corrected-unary-endpoint")
*Degree of the general Maiorana--McFarland construction (Carlet, p. 118).*
For $`f_{\varphi,g}` on $`V_r\times V_s`,
$$`
\deg_{\mathrm{alg}}(f_{\varphi,g})\le s+1,
`
with equality exactly when some coordinate of $`\varphi` has degree $`s`.
If every value of $`\varphi` has weight greater than $`k`, equality can
hold only when $`k\le r-2`.

Suppose the resiliency order is $`k`. The function reaches Siegenthaler's
bound $`n-k-1` exactly in one of the following cases:

* $`k=r-2` and $`\deg_{\mathrm{alg}}(\varphi)=s=n-k-2`;
* $`k=r-1`, $`\varphi` is the constant all-one map, and either $`s=1` or
  $`\deg_{\mathrm{alg}}(g)=s=n-k-1`.
:::

:::theorem "carlet-7-rel-61-maiorana-nonlinearity-lower" (parent := "carlet-chapter-7") (lean := "CryptBoolean.maioranaMcFarlandFiberCardinality, CryptBoolean.maxMaioranaMcFarlandFiberCardinality, CryptBoolean.maioranaMcFarlandFiberCardinality_le_max, CryptBoolean.maioranaMcFarlandFiberCharacterSum_natAbs_le_cardinality, CryptBoolean.maxWalshMagnitude_booleanMaioranaMcFarlandGeneral_le, CryptBoolean.relation_61_booleanMaioranaMcFarlandGeneral, CryptBoolean.nonlinearity_booleanMaioranaMcFarlandGeneral_lower_bound") (uses := "carlet-7-rel-60-maiorana-mcfarland-walsh, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, relation-61, maiorana-mcfarland, nonlinearity, page-118, fidelity-exact")
*Relation (61) (Carlet, p. 118).* Let
$$`
M=\max_{a\in V_r}|\varphi^{-1}(a)|.
`
Then
$$`
\operatorname{nl}(f_{\varphi,g})
\ge 2^{n-1}-2^{r-1}M.
`
:::

:::theorem "carlet-7-rel-62-maiorana-nonlinearity-upper" (parent := "carlet-chapter-7") (lean := "CryptBoolean.sum_sq_maioranaMcFarlandFiberCharacterSum, CryptBoolean.two_pow_mul_ceil_sqrt_maxFiber_le_maxWalshMagnitude, CryptBoolean.nonlinearity_booleanMaioranaMcFarlandGeneral_upper_bound") (uses := "carlet-7-rel-60-maiorana-mcfarland-walsh, carlet-2-parseval, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, relation-62, maiorana-mcfarland, nonlinearity, pages-118-119, fidelity-exact-ceiling")
*Relation (62) (Carlet, pp. 118--119).* With
$`M=\max_a|\varphi^{-1}(a)|`,
$$`
\operatorname{nl}(f_{\varphi,g})
\le 2^{n-1}-2^{r-1}\lceil\sqrt M\rceil.
`
More precisely, for every $`a\in V_r`,
$$`
\sum_{b\in V_s}
  \left(
    \sum_{y\in\varphi^{-1}(a)}(-1)^{g(y)\oplus b\cdot y}
  \right)^2
=2^s|\varphi^{-1}(a)|.
`
:::

:::theorem "carlet-7-maiorana-optimal-classification" (parent := "carlet-chapter-7") (lean := "CryptBoolean.maxWalshMagnitude_eq_two_pow_m_add_two_of_nonlinearity_eq, CryptBoolean.map_eq_one_of_weight_gt_natPred, CryptBoolean.booleanMaioranaMcFarlandGeneral_constant_one_eq_directSum, CryptBoolean.twoVariableProduct, CryptBoolean.twoVariableProduct_apply, CryptBoolean.twoVariableProductAt, CryptBoolean.maxWalshMagnitude_eq_of_maioranaMcFarland_optimal, CryptBoolean.leftDimension_eq_succ_or_add_two_of_maioranaMcFarland_optimal, CryptBoolean.maxMaioranaMcFarlandFiberCardinality_const, CryptBoolean.exists_eq_twoVariableProduct_add_affine_of_maxWalshMagnitude_eq_two, CryptBoolean.exists_eq_twoVariableProductAt_add_affine_of_maxWalshMagnitude_eq_two, CryptBoolean.maioranaMcFarland_optimal_constant_branch, CryptBoolean.injective_of_maioranaMcFarland_optimal_add_two_branch, CryptBoolean.card_highWeightCube, CryptBoolean.two_pow_rightDimension_le_k_add_three_of_add_two_branch, CryptBoolean.rightDimension_cast_le_logb_two_k_add_three, CryptBoolean.maioranaMcFarland_optimal_injective_branch, CryptBoolean.maioranaMcFarland_optimal_classification") (uses := "carlet-7-rel-62-maiorana-nonlinearity-upper, carlet-7-maiorana-mcfarland-degree") (tags := "carlet, chapter-7, maiorana-mcfarland, classification, page-119, fidelity-explicit-unary-endpoint")
*Optimal Maiorana--McFarland parameters (Carlet, p. 119).* Suppose
$`w_H(\varphi(y))>k` for every $`y` and
$$`
\operatorname{nl}(f_{\varphi,g})=2^{n-1}-2^{k+1}.
`
Then $`r=k+1` or $`r=k+2`.

If $`r=k+1`, then $`\varphi` is the constant all-one map,
$`n\le k+3`, and either $`s=1` with arbitrary unary $`g`, or $`s=2` with
$$`
g(y_1,y_2)=y_1y_2\oplus\ell(y)
`
for an affine $`\ell`.

If $`r=k+2`, then $`\varphi` is injective,
$$`
n\le k+2+\log_2(k+3),
`
$`g` is arbitrary, and
$$`
\deg_{\mathrm{alg}}(f_{\varphi,g})\le1+\log_2(k+3).
`
:::

:::theorem "carlet-7-linear-pullback-construction" (parent := "carlet-chapter-7") (lean := "CryptBoolean.vectorFourierCoeff_comp_linearMap_eq_zero_of_not_mem_perpendicular_ker, CryptBoolean.binaryCosetMinimumWeight, CryptBoolean.binaryCosetMinimumWeight_le, CryptBoolean.binaryCosetMinimumWeight_le_dimension, CryptBoolean.linearPullbackWithFrequency, CryptBoolean.walshTransform_linearPullbackWithFrequency, CryptBoolean.isResilient_linearPullbackWithFrequency") (uses := "carlet-4-theorem-3, carlet-2-prop-6-fourier-shifts, carlet-4-resiliency-support-dual-distance") (tags := "carlet, chapter-7, linear-map, resilient-construction, page-120, fidelity-generalized-with-positive-distance")
*Linear-map construction (Carlet, p. 120).* Let $`k<n`, let
$`g:V_k\to\mathbb F_2`, let $`L:V_n\to V_k` be a surjective linear map,
and let $`s\in V_n`. If $`C` is the row space of a matrix for $`L` and
$$`
d=\operatorname{dist}(s,C)>0,
`
then
$$`
f(x)=g(Lx)\oplus s\cdot x
`
is $`(d-1)`-resilient.
:::

The same conclusion holds without surjectivity when $`C` is represented
intrinsically as $`(\ker L)^\perp`.

:::theorem "carlet-7-rel-63-partial-spread-resilient" (parent := "carlet-chapter-7") (lean := "CryptBoolean.partialSpreadResilientFunction, CryptBoolean.partialSpreadResilientFunction_append, CryptBoolean.walshTransform_partialSpreadResilientFunction_append, CryptBoolean.isResilient_partialSpreadResilientFunction") (uses := "carlet-6-partial-spread-construction, carlet-2-trace-pairing-coordinates, carlet-4-theorem-3") (tags := "carlet, chapter-7, relation-63, partial-spread, resilient-construction, pages-120-121, fidelity-generalized-natural-parameters")
*Relation (63) (Carlet, pp. 120--121).* Put $`s=n-r` and identify $`V_r`
with $`\mathbb F_{2^r}`. Let $`g:\mathbb F_{2^r}\to\mathbb F_2`, let
$`\varphi:V_s\to\mathbb F_{2^r}` be linear, and let
$`\varphi^*:\mathbb F_{2^r}\to V_s` be its adjoint for the trace pairing.
Choose $`a\in\mathbb F_{2^r}` and $`b\in V_s` such that
$$`
a+\varphi(y)\ne0\quad(y\in V_s)
`
and
$$`
w_H(\varphi^*(z)+b)>k\quad(z\in\mathbb F_{2^r}).
`
Then
$$`
f(x,y)=g\!\left(\frac{x}{a+\varphi(y)}\right)\oplus b\cdot y
`
is $`k`-resilient.
:::

:::proposition "carlet-7-prop-33-dobbertin-walsh" (parent := "carlet-chapter-7") (lean := "CryptBoolean.dobbertinConstruction, CryptBoolean.dobbertinConstruction_append, CryptBoolean.walshTransform_dobbertinConstruction_general, CryptBoolean.walshTransform_dobbertinConstruction, CryptBoolean.walshTransform_zeroFirstBlock_eq_two_pow_of_isBent, CryptBoolean.walshTransform_dobbertinConstruction_of_isBent_of_isBalanced, CryptBoolean.walshTransform_dobbertinConstruction_zeroFirstBlock, CryptBoolean.walshTransform_dobbertinConstruction_ne_zeroFirstBlock, CryptBoolean.isBalanced_dobbertinConstruction") (uses := "carlet-6-def-7-bent, carlet-5-def-4-normality, carlet-5-flat-indicator-walsh-nonlinearity, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-7, proposition-33, dobbertin, walsh-transform, page-121, fidelity-exact")
*Proposition 33 (Carlet, Relation (64), p. 121).* Let $`n>0` be even.
Let $`f:V_{n/2}\times V_{n/2}\to\mathbb F_2` be bent and satisfy
$`f(x,0)=0` for every $`x`. Let $`g:V_{n/2}\to\mathbb F_2` be balanced and
define
$$`
h(x,y)=f(x,y)\oplus\delta_0(y)g(x).
`
Then
$$`
W_h(u,v)=
\begin{cases}
0,&u=0,\\
W_f(u,v)+W_g(u),&u\ne0.
\end{cases}
`
In particular, $`h` is balanced.
:::

:::theorem "carlet-7-dobbertin-nonlinearity" (parent := "carlet-chapter-7") (lean := "CryptBoolean.maxWalshMagnitude_dobbertinConstruction_le, CryptBoolean.nonlinearity_dobbertinConstruction_add_le, CryptBoolean.nonlinearity_dobbertinConstruction_lowerBound, CryptBoolean.nonlinearity_dobbertinConstruction_boundTerm_eq, CryptBoolean.nonlinearity_dobbertinConstruction_lowerBound_source, CryptBoolean.not_isResilient_dobbertinConstruction_of_pos") (uses := "carlet-7-prop-33-dobbertin-walsh, carlet-4-rel-35-nonlinearity-walsh, carlet-6-def-7-bent") (tags := "carlet, chapter-7, dobbertin, nonlinearity, pages-121-122, fidelity-corrected-dimension-range")
*Dobbertin's nonlinearity bound (Carlet, pp. 121--122).* Under the
hypotheses of Proposition 33,
$$`
\operatorname{nl}(h)
\ge \operatorname{nl}(f)+\operatorname{nl}(g)-2^{n/2-1}
=2^{n-1}-2^{n/2}+\operatorname{nl}(g).
`
If $`n\ge4`, this construction cannot produce a positively resilient
function.
:::
