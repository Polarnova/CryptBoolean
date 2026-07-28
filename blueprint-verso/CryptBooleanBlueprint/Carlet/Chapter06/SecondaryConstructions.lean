/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.DirectSum
import CryptBoolean.Carlet.Chapter06.FlatSwitching
import CryptBoolean.Carlet.Chapter06.IndirectSum
import CryptBoolean.Carlet.Chapter06.PermutationReindex
import CryptBoolean.Carlet.Chapter06.Rothaus

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Secondary constructions of bent functions" =>

:::theorem "carlet-6-direct-sum" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsDecomposable, CryptBoolean.isDecomposable_booleanDirectSum, CryptBoolean.walshTransform_directSum, CryptBoolean.isBent_booleanDirectSum, CryptBoolean.bentDual_booleanDirectSum_append") (uses := "carlet-6-def-7-bent, carlet-6-dual") (tags := "carlet, chapter-6, direct-sum, pages-88-89, fidelity-exact")
*Direct sum (Carlet, pp. 88--89).* If $`f:V_n\to\mathbb F_2` and
$`g:V_m\to\mathbb F_2` are bent, then
$$`
h(x,y)=f(x)+g(y)
`
is bent on $`V_{n+m}`. Its spectrum and dual factor as
$`W_h(a,b)=W_f(a)W_g(b)` and
$`\widetilde h(a,b)=\widetilde f(a)+\widetilde g(b)`.
:::

:::theorem "carlet-6-rothaus-construction" (parent := "carlet-chapter-6") (lean := "CryptBoolean.rothausConstruction, CryptBoolean.rothausConstruction_append, CryptBoolean.isBent_rothausConstruction") (uses := "carlet-6-theorem-10-slice-construction, carlet-6-cor-4-three-function-construction") (tags := "carlet, chapter-6, rothaus, page-89, fidelity-exact")
*Dillon--Rothaus construction (Carlet, p. 89).* Let $`g,h,k`, and
$`g+h+k` be bent functions on $`V_n`. Then the function on
$`\mathbb F_2^2\times V_n` given by
$$`
gh+gk+hk+(g+h)x_1+(g+k)x_2+x_1x_2
`
is bent.
:::

:::theorem "carlet-6-theorem-9-flat-switching" (parent := "carlet-chapter-6") (lean := "CryptBoolean.flatSwitch, CryptBoolean.IsBalancedOnAffineFlat, CryptBoolean.IsConstantOrBalancedOnAffineFlat, CryptBoolean.affineFlatWalshSum, CryptBoolean.walshTransform_sub_flatSwitch, CryptBoolean.affineFlatWalshSum_eq_bitSignInt_mul_walshTransform_restriction, CryptBoolean.affineSubspaceRestrictionImbalance_bentDual_add_linear, CryptBoolean.abs_affineSubspaceRestrictionImbalance_bentDual_add_linear, CryptBoolean.autocorrelation_flatSwitch, CryptBoolean.isBent_flatSwitch_iff_derivative_balanced_on_affineFlat, CryptBoolean.isBent_flatSwitch_iff_bentDual_add_linear_constant_or_balanced, CryptBoolean.derivative_balanced_on_affineFlat_iff_bentDual_add_linear_constant_or_balanced, CryptBoolean.two_pow_half_dvd_walshTransform_affineFlatRestriction, CryptBoolean.half_dimension_le_finrank_of_isBent_flatSwitch, CryptBoolean.functionAlgebraicDegree_affineFlatRestriction_le_of_isBent_flatSwitch, CryptBoolean.isBent_flatSwitch_of_half_dimension_of_restriction_degree_le_one") (uses := "carlet-6-theorem-8-perfect-nonlinearity, carlet-6-rel-46-dual-poisson, carlet-2-prop-11-walsh-divisibility, carlet-3-prop-12") (tags := "carlet, chapter-6, theorem-9, pages-90-91, fidelity-exact")
*Theorem 9 (Carlet, pp. 90--91).* Let $`f` be bent on $`V_n`, let
$`b+E` be an affine flat, and put $`f^*=f+\mathbf1_{b+E}`. Then $`f^*` is
bent if and only if either of the following equivalent conditions holds:

1. for every $`a\notin E`, the derivative $`D_af` is balanced on $`b+E`;
2. on every coset of $`E^\perp`, the restriction of
   $`\widetilde f(x)+b\mathbin\cdot x` is constant or balanced.

If both $`f` and $`f^*` are bent, then $`\dim E\ge n/2` and the restriction
of $`f` to $`b+E` has algebraic degree at most
$`\dim E-n/2+1`. Conversely, if $`\dim E=n/2` and that restriction is
affine, then $`f^*` is bent.
:::

:::theorem "carlet-6-theorem-10-slice-construction" (parent := "carlet-chapter-6") (lean := "CryptBoolean.firstBlockSlice, CryptBoolean.dualSliceFunction, CryptBoolean.walshTransform_eq_two_pow_half_mul_walshTransform_dualSliceFunction, CryptBoolean.isBent_iff_forall_isBent_dualSliceFunction, CryptBoolean.bentDual_append_eq_bentDual_dualSliceFunction") (uses := "carlet-6-def-7-bent, carlet-6-dual") (tags := "carlet, chapter-6, theorem-10, pages-91-92, fidelity-exact")
*Theorem 10 (Carlet, pp. 91--92).* Let $`n,m` be even and let
$`f:V_n\times V_m\to\mathbb F_2`. Suppose every slice
$`f_y(x)=f(x,y)` is bent, and define $`\varphi_s(y)=\widetilde{f_y}(s)`.
Then $`f` is bent if and only if every $`\varphi_s` is bent. In that case
$$`
\widetilde f(s,t)=\widetilde{\varphi_s}(t).
`
:::

:::theorem "carlet-6-indirect-sum" (parent := "carlet-chapter-6") (lean := "CryptBoolean.indirectSum, CryptBoolean.indirectSum_append, CryptBoolean.isBent_indirectSum, CryptBoolean.bentDual_indirectSum_append") (uses := "carlet-6-theorem-10-slice-construction") (tags := "carlet, chapter-6, indirect-sum, page-92, fidelity-exact")
*Indirect sum (Carlet, p. 92).* If $`f_1,f_2` are bent on $`V_n` and
$`g_1,g_2` are bent on $`V_m`, then
$$`
h(x,y)=f_1(x)+g_1(y)+(f_1+f_2)(x)(g_1+g_2)(y)
`
is bent. Its dual is obtained by applying the same formula to the four
duals.
:::

:::proposition "carlet-6-prop-21-permutation-reindexing" (parent := "carlet-chapter-6") (lean := "CryptBoolean.hammingDistance_comp_perm, CryptBoolean.hammingDistance_comp_perm_symm_linearFunction, CryptBoolean.walshTransform_comp_perm_symm_eq_two_pow_sub_two_hammingDistance, CryptBoolean.isBent_comp_perm_symm_of_hammingDistance") (uses := "carlet-6-def-7-bent, carlet-2-def-hamming-distance") (tags := "carlet, chapter-6, proposition-21, pages-93-94, fidelity-exact")
*Proposition 21 (Carlet, pp. 93--94).* Let $`\sigma` be a permutation of
$`V_n`, with coordinate functions $`\sigma_1,\ldots,\sigma_n`. If
$$`
d_H\!\left(f,\sum_{i=1}^n a_i\sigma_i\right)
=2^{n-1}\pm2^{n/2-1}
\qquad(a\in V_n),
`
then $`f\circ\sigma^{-1}` is bent.
:::

:::proposition "carlet-6-prop-22-three-function-identity" (parent := "carlet-chapter-6") (lean := "CryptBoolean.threeFunctionSum, CryptBoolean.threeFunctionPairwiseProductSum, CryptBoolean.bitValueInt_threeFunctionIdentity, CryptBoolean.rawFourierTransform_threeFunctionIdentity, CryptBoolean.walshTransform_cast_eq_rawFourierTransform_sub_two_mul, CryptBoolean.walshTransform_threeFunctionIdentity") (uses := "carlet-2-pseudoboolean-fourier, carlet-2-def-walsh-transform") (tags := "carlet, chapter-6, proposition-22, relation-50, pages-94-95, fidelity-exact")
*Proposition 22 (Carlet, Relation (50), pp. 94--95).* For Boolean functions
$`f_1,f_2,f_3`, put
$$`
s_1=f_1+f_2+f_3,
\qquad
s_2=f_1f_2+f_1f_3+f_2f_3.
`
As integer-valued functions, $`f_1+f_2+f_3=s_1+2s_2`; consequently
$$`
W_{f_1}+W_{f_2}+W_{f_3}=W_{s_1}+2W_{s_2}.
`
:::

:::corollary "carlet-6-cor-4-three-function-construction" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_threeFunctionPairwiseProductSum_and_bentDual_eq, CryptBoolean.isBent_threeFunctionSum_of_two_pow_half_dvd_walshTransform") (uses := "carlet-6-prop-22-three-function-identity, carlet-6-lemma-2-walsh-congruence, carlet-6-dual") (tags := "carlet, chapter-6, corollary-4, page-95, fidelity-exact")
*Corollary 4 (Carlet, p. 95).* Suppose $`f_1,f_2,f_3` are bent. If
$`s_1=f_1+f_2+f_3` is bent and
$`\widetilde{s_1}=\widetilde f_1+\widetilde f_2+\widetilde f_3`, then
$`s_2=f_1f_2+f_1f_3+f_2f_3` is bent and
$$`
\widetilde{s_2}
=\widetilde f_1\widetilde f_2+
 \widetilde f_1\widetilde f_3+
 \widetilde f_2\widetilde f_3.
`
Conversely, if $`2^{n/2}` divides every Walsh coefficient of $`s_2`, then
$`s_1` is bent.
:::
