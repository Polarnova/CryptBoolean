/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter05

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Restricted-weight and restricted-spectrum classes" =>

# 4.1 Affine functions

:::theorem "carlet-5-affine-walsh-spectrum" (parent := "carlet-chapter-5") (lean := "CryptBoolean.walshTransform_affineFunction") (uses := "carlet-2-def-walsh-transform, carlet-3-affine-weight") (tags := "carlet, chapter-5, affine-functions, walsh-spectrum, page-68, fidelity-exact")
*Affine Walsh spectrum (Carlet, Section 5.1, p. 68).* Let $`n\ge0`, let
$`a,u\in V_n`, and let $`\epsilon\in\mathbb F_2`. For
$$`
\ell(x)=a\mathbin\cdot x+\epsilon,
`
the unnormalized Walsh transform satisfies
$$`
W_\ell(u)=
\begin{cases}
2^n(-1)^\epsilon,&u=a,\\
0,&u\ne a.
\end{cases}
`
:::

:::definition "carlet-5-def-maiorana-mcfarland" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsMaioranaMcFarland") (uses := "carlet-2-def-affine-functions") (tags := "carlet, chapter-5, maiorana-mcfarland, affine-restrictions, page-68, fidelity-exact")
*Maiorana--McFarland functions (Carlet, Section 5.1, p. 68).*
Fix a decomposition $`V_{r+s}=V_r\times V_s`. A Boolean function
$`f:V_r\times V_s\to\mathbb F_2` is a Maiorana--McFarland function when,
for every $`y\in V_s`, the function
$`x\mapsto f(x,y)` is affine. Equivalently, the truth table of $`f` is the
concatenation, indexed by $`y`, of affine truth tables on $`V_r`.
:::

Carlet uses this Chapter 5 name for concatenations of affine restrictions. Section 6.4 later
specializes the construction to a class of bent functions.

# 4.2 Quadratic functions

:::definition "carlet-5-def-quadratic-symplectic-form" (parent := "carlet-chapter-5") (lean := "CryptBoolean.quadraticPolarKernel, CryptBoolean.quadraticPolarKernel_eq, CryptBoolean.quadraticPolarKernel_comm, CryptBoolean.quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine, CryptBoolean.quadraticPolarKernel_add_right, CryptBoolean.quadraticPolarKernel_smul_right, CryptBoolean.quadraticPolarKernel_add_left, CryptBoolean.quadraticPolarKernel_smul_left, CryptBoolean.quadraticPolar, CryptBoolean.quadraticPolar_apply, CryptBoolean.quadraticPolar_isSymm, CryptBoolean.quadraticPolar_isAlt, CryptBoolean.quadraticRadical, CryptBoolean.mem_quadraticRadical_iff, CryptBoolean.booleanDerivative_eq_const_of_mem_quadraticRadical, CryptBoolean.quadraticRadicalSignCharacter, CryptBoolean.quadraticRadical_eq_linearKernel") (uses := "carlet-3-reed-muller-code, carlet-2-def-2-derivative, carlet-4-def-linear-kernel") (tags := "carlet, chapter-5, quadratic-functions, symplectic-form, pages-68-69, fidelity-exact-with-derived-identities")
*Quadratic symplectic form (Carlet, Section 5.2, pp. 68--69).* A quadratic
Boolean function is an element $`f\in R(2,n)`, equivalently a function of
algebraic degree at most two. Define
$$`
\varphi_f(x,y)=f(0)+f(x)+f(y)+f(x+y).
`
Then $`\varphi_f` is bilinear, symmetric, and alternating. Its radical is
exactly the linear kernel
$$`
E_f=\{b\in V_n:D_bf\text{ is constant}\},
`
and the map $`b\mapsto D_bf(0)=f(b)+f(0)` is linear on $`E_f`.
:::

:::theorem "carlet-5-rel-41-quadratic-kernel-sum" (parent := "carlet-chapter-5") (lean := "CryptBoolean.walshTransform_zero_sq_eq_two_pow_mul_sum_quadraticRadical, CryptBoolean.walshTransform_zero_sq_eq_two_pow_mul_sum_linearKernel, CryptBoolean.quadraticRadicalSignCharacter_eq_zero_iff, CryptBoolean.walshTransform_zero_sq_eq_if_constant_on_quadraticRadical, CryptBoolean.walshTransform_zero_sq_eq_if_constant_on_linearKernel") (uses := "carlet-5-def-quadratic-symplectic-form, carlet-2-rel-26-total-autocorrelation, carlet-3-affine-weight") (tags := "carlet, chapter-5, quadratic-functions, relation-41, page-69, fidelity-exact")
*Quadratic kernel-sum identity (Carlet, Relation (41), p. 69).* For every
quadratic $`f:V_n\to\mathbb F_2` with linear kernel $`E_f`, one has
$$`
W_f(0)^2=2^n\sum_{b\in E_f}(-1)^{D_bf(0)}.
`
Consequently, this square equals $`2^n|E_f|` when $`f` is constant on
$`E_f`, and it equals $`0` otherwise.
:::

:::theorem "carlet-5-theorem-4" (parent := "carlet-chapter-5") (lean := "CryptBoolean.isBalanced_iff_not_constant_on_linearKernel_of_degree_le_two, CryptBoolean.even_exponent_of_int_sq_eq_two_pow, CryptBoolean.walshTransform_zero_sq_eq_two_pow_add_finrank_of_not_balanced, CryptBoolean.even_dimension_add_finrank_linearKernel_of_not_balanced, CryptBoolean.quadratic_weight_eq_two_pow_sub_or_add, CryptBoolean.theorem_4_quadratic_weight") (uses := "carlet-5-rel-41-quadratic-kernel-sum, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-5, quadratic-functions, theorem-4, page-69, fidelity-explicit-positive-dimension-domain")
*Quadratic weight theorem (Carlet, Theorem 4, p. 69).* Let $`n>0`, let
$`f:V_n\to\mathbb F_2` be quadratic, and let $`k=\dim(E_f)`. Then $`f` is
balanced if and only if its restriction to $`E_f` is not constant. If $`f`
is not balanced, then $`n+k` is even and
$$`
w_H(f)=2^{n-1}+2^{(n+k)/2-1}
\quad\text{or}\quad
w_H(f)=2^{n-1}-2^{(n+k)/2-1}.
`
:::

The condition $`n>0` ensures that the exponent $`(n+k)/2-1` is a natural number.

:::corollary "carlet-5-quadratic-balanced-iff-derivative-one" (parent := "carlet-chapter-5") (lean := "CryptBoolean.isBalanced_iff_quadraticRadicalSignCharacter_ne_zero, CryptBoolean.quadraticRadicalSignCharacter_ne_zero_iff_exists_derivative_one, CryptBoolean.isBalanced_iff_exists_booleanDerivative_eq_one_of_degree_le_two, CryptBoolean.mem_linearKernel_and_ne_zero_value_of_booleanDerivative_eq_one") (uses := "carlet-5-theorem-4, carlet-5-def-quadratic-symplectic-form") (tags := "carlet, chapter-5, quadratic-functions, derivatives, page-69, fidelity-exact-independent-proof")
*Balanced quadratic derivative criterion (Carlet, consequence after Theorem 4, p. 69).*
A quadratic Boolean function $`f` is balanced if and only if there exists
$`b\in V_n` such that
$$`
D_bf=1.
`
Every such direction belongs to $`E_f` and satisfies $`f(b)\ne f(0)`.
:::

:::corollary "carlet-5-quadratic-symplectic-rank-even" (parent := "carlet-chapter-5") (lean := "CryptBoolean.booleanDerivative_add_affineFunction, CryptBoolean.linearKernel_add_affineFunction, CryptBoolean.walshTransform_add_linearFunction_zero, CryptBoolean.even_dimension_add_finrank_linearKernel_of_degree_le_two, CryptBoolean.even_codimension_linearKernel_of_degree_le_two") (uses := "carlet-5-theorem-4, carlet-5-affine-walsh-spectrum, carlet-2-parseval") (tags := "carlet, chapter-5, quadratic-functions, symplectic-rank, page-69, fidelity-exact-independent-proof")
*Even symplectic rank (Carlet, consequence after Theorem 4, p. 69).* For
every quadratic Boolean function $`f`, the codimension of its linear kernel
$`E_f` is even. Equivalently, the alternating bilinear form $`\varphi_f` has
even rank.
:::

:::theorem "carlet-5-quadratic-weight-nonlinearity-values" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsQuadraticOffsetExponent, CryptBoolean.isQuadraticOffsetExponent_iff_ceilingHalf, CryptBoolean.isQuadraticOffsetExponent_iff_ceilDiv, CryptBoolean.isQuadraticOffsetExponent_iff_exists_parameters, CryptBoolean.hammingWeight_eq_two_pow_pred_of_isBalanced, CryptBoolean.isBalanced_iff_hammingWeight_eq_two_pow_pred, CryptBoolean.nonlinearity_affineFunction, CryptBoolean.maxWalshMagnitude_affineFunction, CryptBoolean.nonlinearity_add_affineFunction, CryptBoolean.hammingWeight_add_constant_one, CryptBoolean.quadraticOffsetWitness, CryptBoolean.functionAlgebraicDegree_quadraticOffsetWitness_le_two, CryptBoolean.walshTransform_innerProductModTwoBit_zero, CryptBoolean.walshTransform_quadraticOffsetWitness_zero, CryptBoolean.hammingWeight_quadraticOffsetWitness, CryptBoolean.quadraticOffsetWitnessComplement, CryptBoolean.functionAlgebraicDegree_quadraticOffsetWitnessComplement_le_two, CryptBoolean.hammingWeight_quadraticOffsetWitnessComplement, CryptBoolean.maxWalshMagnitude_quadraticOffsetWitness, CryptBoolean.nonlinearity_quadraticOffsetWitness, CryptBoolean.exists_quadratic_hammingWeight_eq_two_pow_pred, CryptBoolean.exists_quadratic_hammingWeight_eq_sub, CryptBoolean.exists_quadratic_hammingWeight_eq_add, CryptBoolean.exists_quadratic_nonlinearity_eq_sub, CryptBoolean.quadratic_hammingWeight_value_restriction, CryptBoolean.not_isBalanced_of_hammingWeight_eq_quadraticOffset, CryptBoolean.quadratic_affine_shift_hammingWeight_trichotomy, CryptBoolean.maxWalshMagnitude_eq_natAbs_walshTransform_zero_of_quadratic_notBalanced, CryptBoolean.natAbs_walshTransform_zero_eq_two_pow_succ_of_quadratic_weight, CryptBoolean.maxWalshMagnitude_eq_two_pow_succ_of_quadratic_weight, CryptBoolean.quadratic_nonlinearity_eq_sub_of_hammingWeight_offset, CryptBoolean.quadratic_nonlinearity_value_restriction, CryptBoolean.exists_quadratic_hammingWeight_eq_iff, CryptBoolean.exists_quadratic_nonlinearity_eq_iff") (uses := "carlet-5-theorem-4, carlet-5-quadratic-symplectic-rank-even, carlet-5-affine-walsh-spectrum, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-5, quadratic-functions, weight-spectrum, nonlinearity, page-69, fidelity-exact")
*Quadratic weight and nonlinearity values (Carlet, p. 69).* Let $`n\ge1` and
$$`
I_n=\{i\in\mathbb N:\lceil n/2\rceil-1\le i\le n-1\}.
`
The set of weights of quadratic $`n`-variable Boolean functions is exactly
$$`
\{2^{n-1}\}\cup
\{2^{n-1}-2^i,\ 2^{n-1}+2^i:i\in I_n\},
`
and the set of their nonlinearities is exactly
$$`
\{2^{n-1}-2^i:i\in I_n\}.
`
Moreover, if $`w_H(f)=2^{n-1}\pm2^i`, then for every affine $`\ell`,
$$`
w_H(f+\ell)\in\{2^{n-1}-2^i,\ 2^{n-1},\ 2^{n-1}+2^i\}.
`
:::

Complete inner-product blocks, extended by unused coordinates, realize every displayed value.

:::theorem "carlet-5-theorem-5" (parent := "carlet-chapter-5") (lean := "CryptBoolean.exists_affineFunction_of_quadraticPolarKernel_eq_zero, CryptBoolean.quadraticNormalFormSplitLinearEquiv, CryptBoolean.quadraticNormalFormDimension, CryptBoolean.quadraticNormalFormDimension_eq, CryptBoolean.quadraticNormalForm, CryptBoolean.quadraticNormalFormFirstFreeCoordinate, CryptBoolean.quadratic_affine_normal_form") (uses := "carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-4, carlet-2-affine-invariance") (tags := "carlet, chapter-5, quadratic-functions, normal-form, theorem-5, page-70, fidelity-exact")
*Quadratic affine normal form (Carlet, Theorem 5, p. 70).* Put
$$`
Q_\ell=x_1x_2+x_3x_4+\cdots+x_{2\ell-1}x_{2\ell}.
`
Every non-affine quadratic $`f:V_n\to\mathbb F_2` is affinely equivalent to
$`Q_\ell+x_{2\ell+1}` for some $`1\le\ell\le(n-1)/2` when $`f` is
balanced; to $`Q_\ell` for some $`1\le\ell\le n/2` when
$`w_H(f)<2^{n-1}`; and to $`Q_\ell+1` for some
$`1\le\ell\le n/2` when $`w_H(f)>2^{n-1}`.
:::

:::lemma_ "carlet-5-quadraticization-step" (parent := "carlet-chapter-5") (lean := "CryptBoolean.quadraticizationLift, CryptBoolean.quadraticizationLift_append, CryptBoolean.walshTransform_quadraticizationLift_zero") (uses := "carlet-2-def-walsh-transform") (tags := "carlet, chapter-5, quadraticization, walsh-lift, page-70, fidelity-exact")
*Quadraticization step (Carlet, Remark after Theorem 5, p. 70).* Let
$`f_1,f_2,f_3:V_n\to\mathbb F_2`, set
$`g(x)=f_1(x)f_2(x)+f_3(x)`, and define
$$`
F(x,y_1,y_2)=y_1y_2+y_1f_1(x)+y_2f_2(x)+f_3(x).
`
Then
$$`
W_F(0)=2W_g(0).
`
Thus one product $`f_1f_2` may be replaced by a quadratic term in two fresh
variables together with terms linear in those variables, while doubling the
zero-frequency Walsh value.
:::

:::corollary "carlet-5-degree-three-walsh-lift" (parent := "carlet-chapter-5") (lean := "CryptBoolean.exists_degree_le_three_walshTransform_zero_lift") (uses := "carlet-5-quadraticization-step, carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-5, quadraticization, degree-three, reference-51, page-70, fidelity-exact")
*Degree-three Walsh lift (Carlet, iterated consequence of the Remark, p. 70).*
For every Boolean function $`g:V_n\to\mathbb F_2`, there exist
$`m\in\mathbb N` and a Boolean function $`F:V_{n+2m}\to\mathbb F_2` of
algebraic degree at most three such that
$$`
W_F(0)=2^mW_g(0).
`
:::

Iterating the one-product construction over the ANF support proves the result: each step adds two
variables, doubles the zero-frequency Walsh coefficient, and decreases the total excess of
monomial degrees above three.

:::theorem "carlet-5-quadratic-trace-representation" (parent := "carlet-chapter-5") (lean := "CryptBoolean.quadraticTraceMiddleNorm, CryptBoolean.quadraticTraceMiddleNorm_map_eq_pow, CryptBoolean.functionAlgebraicDegree_le_two_iff_exists_odd_quadraticTraceRepresentation, CryptBoolean.functionAlgebraicDegree_le_two_iff_exists_even_quadraticTraceRepresentation") (uses := "carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-5, carlet-2-absolute-trace, carlet-2-trace-monomial-degree, carlet-2-trace-pairing-coordinates") (tags := "carlet, chapter-5, quadratic-functions, trace-representation, pages-70-71, fidelity-explicit-coordinate-and-subfield-maps")
*Quadratic trace representation (Carlet, pp. 70--71).* Put
$`K_j=\operatorname{GF}(2^j)`. If
$`\theta:V_{2m+1}\simeq_{\mathbb F_2}K_{2m+1}`, then a Boolean function
$`f:V_{2m+1}\to\mathbb F_2` is quadratic if and only if there exist
$`\beta_\varnothing,\beta_i\in K_{2m+1}` such that
$$`
f(x)=\operatorname{Tr}_{2m+1}\!\left(
\beta_\varnothing+
\sum_{i=0}^{m}\beta_i\theta(x)^{2^i+1}
\right).
`
If $`m>0` and $`\theta:V_{2m}\simeq_{\mathbb F_2}K_{2m}`, then a Boolean
function $`f:V_{2m}\to\mathbb F_2` is quadratic if and only if there exist an
$`\mathbb F_2`-algebra embedding $`\iota:K_m\hookrightarrow K_{2m}`,
$`\beta_\varnothing,\beta_i\in K_{2m}`, and $`\gamma\in K_m` such that
$$`
f(x)=\operatorname{Tr}_{2m}\!\left(
\beta_\varnothing+
\sum_{i=0}^{m-1}\beta_i\theta(x)^{2^i+1}
\right)
+\operatorname{Tr}_m\!\left(\gamma N_\iota(\theta(x))\right),
`
where $`N_\iota:K_{2m}\to K_m` is the relative norm and
$`\iota(N_\iota(z))=z^{2^m+1}`.
:::

The coordinate map is stated explicitly. In even dimension, the chosen embedding identifies the
half-degree subfield inside $`K_{2m}`, and the relative norm satisfies the printed power formula.

:::definition "carlet-5-def-quadratic-semi-bent" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsQuadraticSemiBent") (uses := "carlet-5-quadratic-weight-nonlinearity-values, carlet-5-quadratic-trace-representation") (tags := "carlet, chapter-5, quadratic-functions, semi-bent, trace-form, page-71, fidelity-exact-predicate")
*Quadratic semi-bent functions (Carlet, Section 5.2, p. 71).* For odd $`n`,
a quadratic Boolean function is called semi-bent in this section when
$$`
\operatorname{nl}(f)=2^{n-1}-2^{(n-1)/2}.
`
The cited trace-form studies concern functions
$$`
\operatorname{Tr}_n\!\left(
\sum_{i=1}^{(n-1)/2}c_i x^{2^i+1}
\right)
`
that satisfy this condition.
:::

The displayed nonlinearity is part of the definition. The trace expression describes the family
under study, whose coefficients must satisfy that condition.

# 4.3 Indicators of flats

:::theorem "carlet-5-flat-indicator-walsh-nonlinearity" (parent := "carlet-chapter-5") (lean := "CryptBoolean.rawFourierTransform_setIndicator_binaryAffineSubspace, CryptBoolean.realSignView_affineFlatIndicator, CryptBoolean.walshTransform_affineFlatIndicator, CryptBoolean.maxWalshMagnitude_affineFlatIndicator_of_two_le_codimension, CryptBoolean.nonlinearity_affineFlatIndicator_of_two_le_codimension, CryptBoolean.nonlinearity_affineFlatIndicator_of_codimension_le_one, CryptBoolean.nonlinearity_affineFlatIndicator, CryptBoolean.nonlinearity_affineFlatIndicator_of_codimension_one, CryptBoolean.nonlinearity_affineFlatIndicator_of_finrank_eq") (uses := "carlet-3-prop-12, carlet-2-def-walsh-transform, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-5, affine-flat-indicator, walsh-spectrum, nonlinearity, page-71, fidelity-corrected-codimension-one")
*Affine-flat indicator spectrum (Carlet, Section 5.3, p. 71).* Let
$`1\le r\le n`, let $`a_1,\ldots,a_r\in V_n` be linearly independent, and
let $`\epsilon_1,\ldots,\epsilon_r\in\mathbb F_2`. For the codimension-$`r`
affine flat
$$`
A=\{x\in V_n:a_i\mathbin\cdot x=\epsilon_i+1\text{ for every }i\},
`
its indicator is
$$`
f(x)=\prod_{i=1}^r(a_i\mathbin\cdot x+\epsilon_i),
\qquad w_H(f)=2^{n-r}.
`
If $`u\notin\operatorname{span}\{a_1,\ldots,a_r\}`, then $`W_f(u)=0`. If
$`0\ne u=\sum_i\eta_i a_i`, then
$$`
W_f(u)=-2^{n-r+1}(-1)^{\sum_i\eta_i(\epsilon_i+1)},
`
while $`W_f(0)=2^n-2^{n-r+1}`. Consequently,
$$`
\operatorname{nl}(f)=
\begin{cases}
0,&r=1,\\
2^{n-r},&r\ge2.
\end{cases}
`
:::

For $`r=1` the indicator is affine and has nonlinearity zero. Thus the printed value
$`\operatorname{nl}(f)=2^{n-r}` follows from the stated Walsh formula precisely when $`r\ge2`.

# 4.4 Normal functions

:::theorem "carlet-5-rel-42-restriction-nonlinearity" (parent := "carlet-chapter-5") (lean := "CryptBoolean.coordinateAffineSubspaceRestriction, CryptBoolean.coordinateAffineSubspaceDimension_le, CryptBoolean.exists_ambientFrequency_restricts_to_subspace, CryptBoolean.sum_walshTransform_perpendicularCoset_eq_restriction, CryptBoolean.abs_walshTransform_coordinateAffineSubspaceRestriction_le, CryptBoolean.maxWalshMagnitude_coordinateAffineSubspaceRestriction_le, CryptBoolean.two_mul_nonlinearity_add_two_pow_le_restriction, CryptBoolean.nonlinearity_cast_le_restriction_relation_42, CryptBoolean.nonlinearity_le_restriction_relation_42, CryptBoolean.nonlinearity_le_restriction_relation_42_of_isCompl") (uses := "carlet-2-cor-1-poisson-summation, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-5, restrictions, nonlinearity, relation-42, pages-71-72, fidelity-exact-with-division-free-total-form")
*Restriction nonlinearity bound (Carlet, Relation (42), pp. 71--72).* Let
$`E,E'` be complementary subspaces of $`V_n`, let $`\dim(E)=k`, and, for
each $`a\in E'`, let $`h_a` be the Boolean function on $`E` obtained by
restricting $`f` to $`a+E`. Then, for every $`a\in E'`,
$$`
\operatorname{nl}(f)
\le 2^{n-1}-2^{k-1}+\operatorname{nl}(h_a).
`
:::

Carlet's alternative proof from the Poisson formula yields the displayed inequality. Its
division-free form remains valid for $`k=0`; the natural-exponent form assumes $`1\le k`.

:::corollary "carlet-5-affine-flat-restriction-bound" (parent := "carlet-chapter-5") (lean := "CryptBoolean.walshTransform_add_affineFunction, CryptBoolean.walshTransform_add_affineFunction_natAbs, CryptBoolean.maxWalshMagnitude_add_affineFunction, CryptBoolean.sum_vectorWalshCharacter_perpendicular_eq_zero_of_not_mem, CryptBoolean.exists_affineFunction_eq_coordinateAffineSubspaceRestriction_of_isAffineOnAffineFlat, CryptBoolean.nonlinearity_coordinateAffineSubspaceRestriction_eq_zero_of_isAffineOnAffineFlat, CryptBoolean.nonlinearity_le_of_isAffineOnAffineFlat, CryptBoolean.isBalanced_coordinateAffineSubspaceRestriction_add_affineFunction_of_eq_bound") (uses := "carlet-5-rel-42-restriction-nonlinearity, carlet-2-def-affine-functions, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-5, affine-flat, restrictions, nonlinearity, page-72, fidelity-exact-positive-dimension")
*Affine-flat restriction bound (Carlet, consequence of Relation (42), p. 72).*
If the restriction of $`f:V_n\to\mathbb F_2` to a $`k`-dimensional affine
flat $`A` is affine, then
$$`
\operatorname{nl}(f)\le2^{n-1}-2^{k-1}.
`
If equality holds and $`\ell` is any ambient affine extension of that
restriction, then $`f+\ell` is balanced on every other coset of the direction
space of $`A`.
:::

The natural-exponent bound assumes $`1\le k`. In the equality case,
$`z+a\notin E` says exactly that $`z+E` is a coset other than $`a+E`.

:::definition "carlet-5-def-4-normality" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsKNormal, CryptBoolean.IsKWeaklyNormal, CryptBoolean.IsKNormal.isKWeaklyNormal, CryptBoolean.IsKNormal.le_normality, CryptBoolean.IsKWeaklyNormal.le_weakNormality") (uses := "carlet-4-other-complexity-definitions") (tags := "carlet, chapter-5, definition-4, normality, weak-normality, page-72, fidelity-exact-fixed-dimension")
*Normal and weakly normal functions (Carlet, Definition 4, p. 72).* A Boolean
function is $`k`-weakly normal when its restriction to some
$`k`-dimensional affine flat is affine, and it is $`k`-normal when its
restriction to some $`k`-dimensional affine flat is constant. For even $`n`,
the unqualified term normal means $`(n/2)`-normal.
:::

:::theorem "carlet-5-random-nonnormality" (parent := "carlet-chapter-5") (lean := "CryptBoolean.weakNormalityProbability, CryptBoolean.weakNormalityProbability_le_of_le, CryptBoolean.weakNormalityProbability_le, CryptBoolean.normalityProbability, CryptBoolean.normalityProbability_le_weakNormalityProbability, CryptBoolean.tendsto_weakNormalityProbability_zero_of_ratio, CryptBoolean.nonWeakNormalityProbability, CryptBoolean.tendsto_nonWeakNormalityProbability_one_of_ratio, CryptBoolean.nonnormalityProbability, CryptBoolean.tendsto_nonnormalityProbability_one_of_ratio, CryptBoolean.carletNonnormalityDimension, CryptBoolean.tendsto_carletNonnormalityProbability") (uses := "carlet-5-def-4-normality, carlet-4-degree-count") (tags := "carlet, chapter-5, normality, random-functions, asymptotic, reference-65, page-72, fidelity-exact")
*Random nonnormality (Carlet, p. 72).* For every real $`\alpha>1`, as
$`n\to\infty` the uniform probability that an $`n`-variable Boolean
function is not $`\lfloor\alpha\log_2 n\rfloor`-normal tends to one.
:::

The proof first establishes the general criterion $`2^{k_n}/(nk_n)\to\infty`, then verifies it for
the displayed floored logarithmic dimension.

# 4.5 Functions admitting partial covering sequences

:::definition "carlet-5-def-5-covering-sequence" (parent := "carlet-chapter-5") (lean := "CryptBoolean.bitValueInt, CryptBoolean.integerWalshTransform, CryptBoolean.weightedDerivativeSum, CryptBoolean.IsCoveringSequence") (uses := "carlet-2-def-2-derivative") (tags := "carlet, chapter-5, definition-5, covering-sequence, page-73, fidelity-exact-integer-valued")
*Covering sequences (Carlet, Definition 5, p. 73).* Let
$`f:V_n\to\mathbb F_2` and let $`\lambda=(\lambda_a)_{a\in V_n}` be
integer-valued. It is a covering sequence of $`f` with level $`\rho\in
\mathbb Z` when the integer-valued function
$$`
x\longmapsto\sum_{a\in V_n}\lambda_a D_af(x)
`
is constantly $`\rho`, where each derivative bit is viewed in $`\mathbb Z`.
The sequence is nontrivial when $`\rho\ne0`.
:::

Carlet's printed definition uses integer coefficients; footnote 31 also permits real or complex
coefficients.

:::theorem "carlet-5-covering-sequence-balancedness" (parent := "carlet-chapter-5") (lean := "CryptBoolean.integerWalshTransform_one, CryptBoolean.isBalanced_of_isCoveringSequence_of_ne_zero, CryptBoolean.isCoveringSequence_one_of_isBalanced, CryptBoolean.isBalanced_iff_exists_nontrivialCoveringSequence") (uses := "carlet-5-def-5-covering-sequence, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-5, covering-sequence, balancedness, reference-94, page-73, fidelity-exact")
*Covering sequences and balancedness (Carlet, p. 73).* Every Boolean
function admitting a nontrivial covering sequence is balanced. Conversely,
every balanced $`n`-variable Boolean function admits the constant sequence
$`\lambda_a=1` as a covering sequence of level $`2^{n-1}`.
:::

:::theorem "carlet-5-covering-sequence-walsh-characterization" (parent := "carlet-chapter-5") (lean := "CryptBoolean.weightedTranslatedSignSum, CryptBoolean.bitSignInt_eq_one_sub_two_mul_bitValueInt, CryptBoolean.bitSignInt_booleanDerivative_mul_left, CryptBoolean.weightedTranslatedSignSum_eq, CryptBoolean.integerWalshTransform_mul_bitSignInt, CryptBoolean.integerWalshTransform_weightedTranslatedSignSum, CryptBoolean.integerWalshTransform_const_mul_bitSignInt, CryptBoolean.integerWalshTransform_cast_eq_rawFourierTransform, CryptBoolean.integerWalshTransform_involution, CryptBoolean.integerWalshTransform_injective, CryptBoolean.isCoveringSequence_iff_integerWalshTransform, CryptBoolean.isCoveringSequence_iff_transform_eq_on_walshSupport") (uses := "carlet-5-def-5-covering-sequence, carlet-2-pseudoboolean-fourier, carlet-2-def-walsh-transform") (tags := "carlet, chapter-5, covering-sequence, walsh-characterization, reference-94, pages-73-74, fidelity-exact-with-transform-identities")
*Walsh characterization of covering sequences (Carlet, pp. 73--74).* For an
integer sequence $`\lambda` on $`V_n`, define
$$`
\widehat\lambda(b)=\sum_{a\in V_n}\lambda_a(-1)^{a\mathbin\cdot b}.
`
Then $`\lambda` is a covering sequence of $`f` with level $`\rho` if and
only if
$$`
\widehat\lambda(b)=\widehat\lambda(0)-2\rho
`
for every $`b` with $`W_f(b)\ne0`; equivalently, $`\widehat\lambda` is
constant with that value on the Walsh support of $`f`.
:::

:::theorem "carlet-5-covering-sequence-resiliency" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsMinimumNonzeroTransformFiberWeight, CryptBoolean.isCorrelationImmune_of_coveringSequence_of_minimumTransformFiberWeight, CryptBoolean.isResilient_of_coveringSequence_of_minimumTransformFiberWeight, CryptBoolean.walshZeroIndicator, CryptBoolean.walshZeroCoveringSequence, CryptBoolean.walshZeroCoveringLevel, CryptBoolean.integerWalshTransform_walshZeroCoveringSequence, CryptBoolean.integerWalshTransform_walshZeroCoveringSequence_eq_zero_iff, CryptBoolean.walshZeroCoveringSequence_transformTarget_eq_zero, CryptBoolean.isCoveringSequence_walshZeroCoveringSequence, CryptBoolean.exists_coveringSequence_of_correlationImmune_not_succ, CryptBoolean.exists_nontrivialCoveringSequence_of_resilient_not_succ") (uses := "carlet-5-covering-sequence-walsh-characterization, carlet-5-covering-sequence-balancedness, carlet-4-theorem-3") (tags := "carlet, chapter-5, covering-sequence, resiliency, reference-94, page-74, fidelity-exact-on-feasible-orders")
*Covering sequences and resiliency (Carlet, p. 74).* Suppose $`\lambda` is
a covering sequence of $`f` with level $`\rho`, put
$`\mu=\widehat\lambda(0)-2\rho`, and suppose $`k+1` is the minimum Hamming
weight of a nonzero $`b` satisfying $`\widehat\lambda(b)=\mu`. Then $`f` is
$`k`th-order correlation immune, and if $`\rho\ne0` it is $`k`-resilient.
Conversely, if $`f` is $`k`th-order correlation immune but not
$`(k+1)`th-order correlation immune, there is a covering sequence with this
minimum equal to $`k+1`; if $`f` is $`k`-resilient but not
$`(k+1)`-resilient, such a sequence can be chosen nontrivial.
:::

:::definition "carlet-5-def-regular-function" (parent := "carlet-chapter-5") (lean := "CryptBoolean.weightOneDirectionIndicator, CryptBoolean.IsRegularAtLevel, CryptBoolean.IsRegular, CryptBoolean.integerWalshTransform_weightOneDirectionIndicator, CryptBoolean.isResilient_natPred_of_isRegularAtLevel, CryptBoolean.directionFamilyIndicator, CryptBoolean.HasPairwiseDisjointSupports, CryptBoolean.integerWalshTransform_directionFamilyIndicator, CryptBoolean.integerWalshTransform_directionFamilyIndicator_zero, CryptBoolean.isResilient_natPred_of_pairwiseDisjointSupportCoveringSequence") (uses := "carlet-5-def-5-covering-sequence, carlet-5-covering-sequence-resiliency") (tags := "carlet, chapter-5, regular-functions, covering-sequence, resiliency, reference-94, page-74, fidelity-exact-on-positive-natural-levels")
*Regular functions (Carlet, p. 74).* A Boolean function is regular when the
indicator of the set of weight-one directions is a covering sequence. If its
level is $`\rho\ge1`, then it is $`(\rho-1)`-resilient. More generally, the
same conclusion holds when the covering sequence is the indicator of a set
of directions with pairwise disjoint supports.
:::

:::definition "carlet-5-def-6-partial-covering-sequence" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsPartialCoveringSequence, CryptBoolean.partialCoveringExceptionalSet") (uses := "carlet-5-def-5-covering-sequence") (tags := "carlet, chapter-5, definition-6, partial-covering-sequence, reference-68, page-74, fidelity-exact-integer-valued")
*Partial covering sequences (Carlet, Definition 6, p. 74).* An integer
sequence $`\lambda=(\lambda_a)_{a\in V_n}` is a partial covering sequence of
$`f` with levels $`\rho,\rho'\in\mathbb Z` when, for every $`x\in V_n`,
$$`
\sum_{a\in V_n}\lambda_aD_af(x)\in\{\rho,\rho'\}.
`
The levels may coincide. The sequence is nontrivial when at least one level
is nonzero.
:::

:::theorem "carlet-5-derivative-space-partial-covering-sequence" (parent := "carlet-chapter-5") (lean := "CryptBoolean.IsDerivativeSpace, CryptBoolean.sum_bitValueInt_submodule_eq_zero_or_half, CryptBoolean.derivativeDirectionRepresentative, CryptBoolean.booleanDerivative_derivativeDirectionRepresentative, CryptBoolean.derivativeDirectionRepresentative_injective, CryptBoolean.derivativeRepresentativeDirections, CryptBoolean.card_derivativeRepresentativeDirections, CryptBoolean.bijOn_booleanDerivative_derivativeRepresentativeDirections, CryptBoolean.sum_derivativeRepresentativeDirections, CryptBoolean.isPartialCoveringSequence_derivativeRepresentativeDirections") (uses := "carlet-5-def-6-partial-covering-sequence, carlet-2-def-2-derivative") (tags := "carlet, chapter-5, partial-covering-sequence, derivative-space, page-74, fidelity-exact")
*Derivative-space partial covering sequence (Carlet, example after Definition 6, p. 74).*
Let $`D` be a nonzero finite $`\mathbb F_2`-vector space of Boolean functions,
every element of which is a derivative $`D_af`. Then
$$`
\sum_{g\in D}g(x)\in\{0,|D|/2\}
`
for every $`x`. If $`E` is a set of directions chosen minimally so that
$`a\mapsto D_af` is a bijection from $`E` to $`D`, then the indicator of
$`E` is a nontrivial partial covering sequence of $`f` with levels $`0` and
$`|D|/2`.
:::

Choosing one direction for each element of the finite binary derivative space gives a bijection
onto $`D` and hence a minimal representative set. Since $`D` is nonzero, the second level is
nonzero.

:::theorem "carlet-5-theorem-6" (parent := "carlet-chapter-5") (lean := "CryptBoolean.theorem_6_partialCoveringSequence") (uses := "carlet-5-def-6-partial-covering-sequence, carlet-2-prop-6-fourier-shifts, carlet-2-def-walsh-transform") (tags := "carlet, chapter-5, partial-covering-sequence, theorem-6, relation-43, reference-68, pages-75-76, fidelity-exact")
*Partial-covering Walsh identity (Carlet, Theorem 6 and Relation (43), pp. 75--76).*
Let $`\lambda` be a partial covering sequence of $`f` with levels
$`\rho,\rho'`. If $`\rho'\ne\rho`, set
$$`
A=\left\{x\in V_n:\sum_a\lambda_aD_af(x)=\rho'\right\};
`
if $`\rho'=\rho`, set $`A=\varnothing`. Then, for every $`b\in V_n`,
$$`
\bigl(\widehat\lambda(b)-\widehat\lambda(0)+2\rho\bigr)W_f(b)
=2(\rho-\rho')\sum_{x\in A}(-1)^{f(x)+b\mathbin\cdot x}.
`
:::

:::corollary "carlet-5-theorem-6-weight-corollary" (parent := "carlet-chapter-5") (lean := "CryptBoolean.theorem_6_weight_identity") (uses := "carlet-5-theorem-6, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-5, partial-covering-sequence, theorem-6, weight, reference-68, page-76, fidelity-strengthened-division-free")
*Partial-covering weight identity (Carlet, consequence of Theorem 6, p. 76).*
Under the hypotheses and notation of Theorem 6, if $`\rho\ne0`, then
$$`
2^n-2w_H(f)=W_f(0)
=\left(1-\frac{\rho'}{\rho}\right)
\sum_{x\in A}(-1)^{f(x)}.
`
:::

Multiplying by $`\rho` gives the equivalent identity
$`\rho W_f(0)=(\rho-\rho')\sum_{x\in A}(-1)^{f(x)}` without assuming
$`\rho\ne0`.

# 4.6 Functions with low univariate degree

:::theorem "carlet-5-theorem-7-weil-bound" (parent := "carlet-chapter-5") (tags := "carlet, chapter-5, additive-character-sums, weil-bound, theorem-7, reference-245, page-76, source-open")
*Weil bound (Carlet, Theorem 7, p. 76).* Let $`q` be a prime power, let
$`P\in\mathbb F_q[X]` have degree $`d\ge1` with $`\gcd(d,q)=1`, and let
$`\chi` be a nontrivial additive character of $`\mathbb F_q`. Then
$$`
\left|\sum_{x\in\mathbb F_q}\chi(P(x))\right|
\le(d-1)\sqrt q.
`
:::

The binary trace specialization fixes $`\chi` as an additive character.

:::theorem "carlet-5-trace-character-sum-walsh" (parent := "carlet-chapter-5") (lean := "CryptBoolean.tracePolynomialBooleanFunction, CryptBoolean.tracePolynomialCharacterSum, CryptBoolean.exists_tracePolynomialCharacterSum_eq_walshTransform, CryptBoolean.maxWalshMagnitude_tracePolynomialBooleanFunction_le, CryptBoolean.two_pow_le_two_mul_nonlinearity_add_of_tracePolynomialCharacterSum_le, CryptBoolean.tracePolynomialCharacterSum_nonlinearity_lower_bound") (uses := "carlet-2-def-walsh-transform, carlet-2-trace-pairing-coordinates, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-5, trace-pairing, character-sums, walsh-transform, nonlinearity, page-76, fidelity-explicit-character-identification")
*Walsh coefficients as trace-character sums.* Let
$`\theta:V_n\simeq_{\mathbb F_2}\operatorname{GF}(2^n)`, let
$`a\in\operatorname{GF}(2^n)^\times`, and let
$`P\in\operatorname{GF}(2^n)[X]`. For $`u\in V_n`, let
$`b\in\operatorname{GF}(2^n)` be the unique trace-pairing coefficient such that
$$`
u\mathbin\cdot x=\operatorname{Tr}_n(b\theta(x))\qquad(x\in V_n),
`
and
$$`
W_{\operatorname{Tr}_n(aP\circ\theta)}(u)
=\sum_{y\in\operatorname{GF}(2^n)}
(-1)^{\operatorname{Tr}_n(a(P(y)+(b/a)y))}.
`
Therefore, if the absolute value of the sum on the right is at most $`B` for every
linear perturbation $`P+cX`, then
$$`
\max_u|W_{\operatorname{Tr}_n(aP\circ\theta)}(u)|\le B
\quad\text{and}\quad
\operatorname{nl}(\operatorname{Tr}_n(aP\circ\theta))
\ge \frac{2^n-B}{2}.
`
:::

The trace-pairing coefficient identifies every cube character with a unique finite-field trace
character. The character-sum estimate is a hypothesis in this reduction; Theorem 7 supplies it
for the stated polynomial degrees.

:::corollary "carlet-5-weil-nonlinearity-bound" (parent := "carlet-chapter-5") (uses := "carlet-5-theorem-7-weil-bound, carlet-5-trace-character-sum-walsh") (tags := "carlet, chapter-5, weil-bound, nonlinearity, trace, page-76, source-open")
*Binary Weil nonlinearity bound (Carlet, consequence of Theorem 7, p. 76).*
Let $`n>0`, let $`P\in\operatorname{GF}(2^n)[X]` have odd degree $`d>1`,
and let $`a\in\operatorname{GF}(2^n)` be nonzero. For every
$`\mathbb F_2`-linear equivalence $`\theta:V_n\simeq\operatorname{GF}(2^n)`,
define
$$`
h_\theta(x)=\operatorname{Tr}_n\bigl(aP(\theta(x))\bigr).
`
Then every Walsh coefficient of $`h_\theta` has magnitude at most
$`(d-1)\sqrt{2^n}`, and
$$`
\operatorname{nl}(h_\theta)
\ge2^{n-1}-\frac{d-1}{2}\sqrt{2^n}.
`
:::

:::theorem "carlet-5-reciprocal-character-sum-bound" (parent := "carlet-chapter-5") (uses := "carlet-2-absolute-trace") (tags := "carlet, chapter-5, reciprocal-polynomials, character-sums, kloosterman-sums, references-96-325, page-76, source-open, fidelity-source-correction")
*Reciprocal-polynomial character-sum bound (Carlet, p. 76).* Let $`n>0`
and let $`P,Q\in\operatorname{GF}(2^n)[X]` have odd degrees. Then
$$`
\left|
\sum_{x\in\operatorname{GF}(2^n)^\times}
(-1)^{\operatorname{Tr}_n(P(x^{-1})+Q(x))}
\right|
\le(\deg P+\deg Q)\sqrt{2^n}.
`
If $`\operatorname{inv}(0)=0` and $`\operatorname{inv}(x)=x^{-1}` for
$`x\ne0`, then the whole-field convention satisfies
$$`
\left|
\sum_{x\in\operatorname{GF}(2^n)}
(-1)^{\operatorname{Tr}_n(P(\operatorname{inv}(x))+Q(x))}
\right|
\le1+(\deg P+\deg Q)\sqrt{2^n}.
`
For $`P(X)=X` and $`Q(X)=aX`, the punctured sums are the Kloosterman sums.
:::

Carlet prints a one-sided inequality over the whole field after assigning
$`\operatorname{inv}(0)=0`. Theorem 1 of reference 325 states the sharp absolute-value bound over
the nonzero Teichmuller units, which specialize here to
$`\operatorname{GF}(2^n)^\times`. The omitted summand has modulus one, so the displayed
whole-field consequence requires the added $`1`.
