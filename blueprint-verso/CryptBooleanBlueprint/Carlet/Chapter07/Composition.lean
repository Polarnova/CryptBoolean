/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.AddingVariable
import CryptBoolean.Carlet.Chapter07.ConcatenationStructure
import CryptBoolean.Carlet.Chapter07.DirectSumDegree
import CryptBoolean.Carlet.Chapter07.GeneralConcatenation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Composition on coordinate blocks" =>

:::theorem "carlet-7-adding-variable" (parent := "carlet-chapter-7") (lean := "CryptBoolean.oneVariableParity, CryptBoolean.oneVariableParity_apply, CryptBoolean.oneVariableParity_eq_booleanFunctionF₂Encoding, CryptBoolean.oneVariableParity_eq_affineFunction, CryptBoolean.oneVariableParity_isResilient, CryptBoolean.nonlinearity_oneVariableParity, CryptBoolean.functionAlgebraicDegree_oneVariableParity, CryptBoolean.addingVariable, CryptBoolean.addingVariable_append, CryptBoolean.isResilient_addingVariable, CryptBoolean.nonlinearity_addingVariable, CryptBoolean.addedVariableDirection, CryptBoolean.addedVariableDirection_ne_zero, CryptBoolean.addedVariableDirection_isNonzeroLinearStructure, CryptBoolean.functionAlgebraicDegree_addingVariable_eq, CryptBoolean.functionAlgebraicDegree_addingVariable_eq_source, CryptBoolean.nonlinearity_addingVariable_ge_source") (uses := "carlet-7-sarkar-maitra-nonlinearity-bound, carlet-7-siegenthaler-degree-bounds, carlet-4-def-linear-kernel") (tags := "carlet, chapter-7, adding-variable, resilient-construction, page-122, fidelity-exact")
*Adding a variable (Carlet, p. 122).* If
$`f:V_r\to\mathbb F_2` is $`t`-resilient, then
$$`
h(x,z)=f(x)\oplus z
`
is $`(t+1)`-resilient. If $`f` has parameters
$$`
(r,t,r-t-1,\,2^{r-1}-2^{t+1}),
`
then $`h` has parameters
$$`
(r+1,t+1,r-t-1,\,2^r-2^{t+2}).
`
The last coordinate direction is a nonzero linear structure of $`h`.
:::

:::theorem "carlet-7-direct-sum-resilient" (parent := "carlet-chapter-7") (lean := "CryptBoolean.card_f₂Support_append, CryptBoolean.walshTransform_natAbs_le_maxWalshMagnitude, CryptBoolean.maxWalshMagnitude_booleanDirectSum, CryptBoolean.isResilient_booleanDirectSum, CryptBoolean.two_mul_nonlinearity_booleanDirectSum_add_product, CryptBoolean.nonlinearity_booleanDirectSum_cast_eq_half_product, CryptBoolean.nonlinearity_booleanDirectSum_cast_eq_source, CryptBoolean.nonlinearity_booleanDirectSum, CryptBoolean.booleanDerivative_booleanDirectSum_append, CryptBoolean.isLinearStructure_booleanDirectSum_append, CryptBoolean.noNonzeroLinearStructure_booleanDirectSum") (uses := "carlet-6-direct-sum, carlet-4-theorem-3, carlet-4-rel-35-nonlinearity-walsh, carlet-4-def-linear-kernel") (tags := "carlet, chapter-7, direct-sum, resilient-construction, pages-122-123, fidelity-exact")
*Direct sum (Carlet, pp. 122--123).* Let $`f:V_r\to\mathbb F_2` be
$`t`-resilient and $`g:V_s\to\mathbb F_2` be $`m`-resilient, where
$`t<r` and $`m<s`. Then
$$`
h(x,y)=f(x)\oplus g(y)
`
is $`(t+m+1)`-resilient and
$$`
W_h(a,b)=W_f(a)W_g(b).
`
Moreover,
$$`
\begin{aligned}
\operatorname{nl}(h)
&=2^{r+s-1}
 -\frac12(2^r-2\operatorname{nl}(f))
              (2^s-2\operatorname{nl}(g))\\
&=2^r\operatorname{nl}(g)+2^s\operatorname{nl}(f)
 -2\operatorname{nl}(f)\operatorname{nl}(g).
\end{aligned}
`
Finally, $`h` has no nonzero linear structure if and only if neither
$`f` nor $`g` has a nonzero linear structure.
:::

:::theorem "carlet-7-direct-sum-degree" (parent := "carlet-chapter-7") (lean := "CryptBoolean.functionAlgebraicDegree_add_constant_eq, CryptBoolean.functionAlgebraicDegree_eq_zero_iff_exists_constant, CryptBoolean.functionAlgebraicDegree_add_eq_right_of_lt, CryptBoolean.functionAlgebraicDegree_booleanDirectSum") (uses := "carlet-7-direct-sum-resilient, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, direct-sum, algebraic-degree, page-123, fidelity-exact")
*Degree of a direct sum (Carlet, p. 123).* For Boolean functions
$`f:V_r\to\mathbb F_2` and $`g:V_s\to\mathbb F_2` on disjoint coordinate
blocks,
$$`
\deg_{\mathrm{alg}}(f\oplus g)
=\max(\deg_{\mathrm{alg}}f,\deg_{\mathrm{alg}}g).
`
:::

:::theorem "carlet-7-rel-65-siegenthaler-concatenation" (parent := "carlet-chapter-7") (lean := "CryptBoolean.walshTransform_hyperplaneExtension_append, CryptBoolean.isResilient_hyperplaneExtension, CryptBoolean.isResilient_succ_hyperplaneExtension_of_walshCancellation") (uses := "carlet-4-theorem-3, carlet-2-def-walsh-transform") (tags := "carlet, chapter-7, relation-65, concatenation, page-123, fidelity-exact")
*Relation (65) (Carlet, p. 123).* For
$`f,g:V_r\to\mathbb F_2`, define
$$`
h(x,z)=(z\oplus1)f(x)\oplus zg(x).
`
Then
$$`
W_h(a,c)=W_f(a)+(-1)^cW_g(a).
`
If $`f` and $`g` are both $`m`-resilient, then $`h` is
$`m`-resilient. If additionally
$$`
W_f(a)+W_g(a)=0
`
for every frequency $`a` of weight $`m+1`, then $`h` is
$`(m+1)`-resilient.
:::

:::theorem "carlet-7-siegenthaler-concatenation-nonlinearity" (parent := "carlet-chapter-7") (lean := "CryptBoolean.nonlinearity_add_le_hyperplaneExtension, CryptBoolean.maxWalshMagnitude_hyperplaneExtension_of_disjointWalshSupport, CryptBoolean.nonlinearity_hyperplaneExtension_of_disjointWalshSupport") (uses := "carlet-7-rel-65-siegenthaler-concatenation, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, concatenation, nonlinearity, pages-123-124, fidelity-exact")
*Nonlinearity of concatenation (Carlet, pp. 123--124).* For the preceding
function $`h`,
$$`
\operatorname{nl}(h)
\ge\operatorname{nl}(f)+\operatorname{nl}(g).
`
If the Walsh supports of $`f` and $`g` are disjoint, then
$$`
\operatorname{nl}(h)
=2^{r-1}+\min(\operatorname{nl}(f),\operatorname{nl}(g)).
`
:::

:::theorem "carlet-7-siegenthaler-concatenation-degree" (parent := "carlet-chapter-7") (lean := "CryptBoolean.hyperplaneExtension_append_eq_add_mul_difference, CryptBoolean.hyperplaneExtension_eq_booleanDirectSum_add_booleanBlockProduct, CryptBoolean.booleanDerivative_hyperplaneExtension_append, CryptBoolean.HaveEqualConstantDerivative, CryptBoolean.isLinearStructure_hyperplaneExtension_append_zero_iff, CryptBoolean.functionAlgebraicDegree_hyperplaneExtension_eq_succ_max, CryptBoolean.not_isLinearStructure_hyperplaneExtension_append_one, CryptBoolean.no_nonzero_linearStructure_hyperplaneExtension") (uses := "carlet-7-rel-65-siegenthaler-concatenation, carlet-4-def-linear-kernel, carlet-2-def-2-derivative, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, concatenation, algebraic-degree, linear-structures, page-124, fidelity-corrected-degenerate-cases")
*Degree and linear structures of concatenation (Carlet, p. 124).* Put
$`q=f\oplus g`. Then
$$`
h(x,z)=f(x)\oplus zq(x)
`
and
$$`
D_{(a,c)}h(x,z)
=D_af(x)\oplus cq(x)\oplus zD_aq(x)\oplus cD_aq(x).
`
If $`q\ne0` and
$`\deg_{\mathrm{alg}}q=\max(\deg_{\mathrm{alg}}f,\deg_{\mathrm{alg}}g)`,
then
$$`
\deg_{\mathrm{alg}}h
=1+\max(\deg_{\mathrm{alg}}f,\deg_{\mathrm{alg}}g).
`
If $`0<\deg_{\mathrm{alg}}q` and
$`\deg_{\mathrm{alg}}q\ge\deg_{\mathrm{alg}}f`, no direction $`(a,1)` is
a linear structure. A direction $`(a,0)` is a linear structure exactly
when $`a` is a common linear structure of $`f` and $`g` with the same
derivative constant. Thus, under these hypotheses, absence of such a
nonzero $`a` implies that $`h` has no nonzero linear structure.
:::

:::theorem "carlet-7-concatenation-family" (parent := "carlet-chapter-7") (lean := "CryptBoolean.familyConcatenation, CryptBoolean.familyConcatenation_append, CryptBoolean.firstBlockSlice_familyConcatenation, CryptBoolean.walshTransform_familyConcatenation_append, CryptBoolean.isResilient_familyConcatenation") (uses := "carlet-7-rel-65-siegenthaler-concatenation, carlet-4-theorem-3") (tags := "carlet, chapter-7, generalized-concatenation, resiliency, page-124, fidelity-exact")
*Generalized concatenation (Carlet, p. 124).* Let
$`(f_y)_{y\in V_s}` be a family of $`r`-variable $`m`-resilient functions
and define $`F(x,y)=f_y(x)`. Then $`F` is $`m`-resilient, and for every
$`a\in V_r` and $`b\in V_s`,
$$`
W_F(a,b)=\sum_{y\in V_s}(-1)^{b\cdot y}W_{f_y}(a).
`
:::
