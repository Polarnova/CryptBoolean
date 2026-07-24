/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter04

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Resiliency and propagation" =>

:::definition "carlet-4-def-resiliency-correlation-immunity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.signCubeView, CryptBoolean.signCubeView_toReal, CryptBoolean.IsCorrelationImmune, CryptBoolean.IsResilient, CryptBoolean.isCorrelationImmune_iff_fabl, CryptBoolean.isBalanced_iff_fabl, CryptBoolean.isResilient_iff_fabl, CryptBoolean.isResilient_iff_forall_coordinateRestriction_balanced, CryptBoolean.isCorrelationImmune_iff_fixing_exactly, CryptBoolean.isResilient_iff_fixing_exactly") (uses := "carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, definition-3, resiliency, correlation-immunity, pages-55-56, fidelity-exact")
*Definition 3 (Carlet, pp. 55--56).* Let $`n>0` and $`0\le m<n`. A
function $`f:V_n\to\mathbb F_2` is $`m`-resilient if every restriction
obtained by fixing at most $`m` input coordinates is balanced. It is
correlation immune of order $`m` if fixing any such inputs leaves the output
distribution unchanged. Fixing exactly $`m` coordinates is equivalent in
both definitions.
:::

:::theorem "carlet-4-theorem-3" (parent := "carlet-chapter-4") (lean := "CryptBoolean.walshTransform_eq_zero_iff_vectorFourierCoeff_eq_zero, CryptBoolean.theorem_3_correlationImmune_iff_walshTransform_eq_zero, CryptBoolean.theorem_3_resilient_iff_walshTransform_eq_zero") (uses := "carlet-4-def-resiliency-correlation-immunity, carlet-2-cor-1-poisson-summation, carlet-2-def-walsh-transform, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, theorem-3, resiliency, page-57, fidelity-exact")
*Theorem 3 (Carlet, p. 57).* A Boolean function $`f` is $`m`-resilient if
and only if
$$`
W_f(u)=0\qquad\text{for every }u\in V_n\text{ with }w_H(u)\le m.
`
It is correlation immune of order $`m` if and only if the same vanishing
holds for every $`u` with $`0<w_H(u)\le m`.
:::

:::corollary "carlet-4-resiliency-support-dual-distance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.codeCharacterSum, CryptBoolean.HasDualDistanceAtLeast, CryptBoolean.sum_vectorWalshCharacter_eq_zero, CryptBoolean.walshTransform_cast_eq_neg_two_mul_codeCharacterSum_support, CryptBoolean.isCorrelationImmune_iff_support_hasDualDistanceAtLeast, CryptBoolean.isBalanced_iff_support_card_eq_two_pow_pred, CryptBoolean.isResilient_iff_support_card_and_hasDualDistanceAtLeast") (uses := "carlet-4-theorem-3, carlet-2-def-support-weight") (tags := "carlet, chapter-4, resiliency, dual-distance, page-57, fidelity-exact")
*Support dual-distance characterization (Carlet, p. 57).* The function
$`f` is $`m`-resilient if and only if
$$`
|\operatorname{supp}(f)|=2^{n-1}
`
and $`\operatorname{supp}(f)` has dual distance at least $`m+1`. It is
correlation immune of order $`m` if and only if the dual-distance condition
alone holds.
:::

Formalization note. `HasDualDistanceAtLeast` uses Carlet's character-sum
definition for an arbitrary finite binary code, so the result is not encoded as
a restatement of Walsh-transform vanishing.

:::theorem "carlet-4-code-generator-resilient" (parent := "carlet-chapter-4") (lean := "CryptBoolean.binaryGeneratorCodeword, CryptBoolean.IsBinaryCodeGenerator, CryptBoolean.binaryGeneratorPullback, CryptBoolean.isBalanced_binaryGeneratorPullback, CryptBoolean.binaryGeneratorPullback_isResilient") (uses := "carlet-4-def-resiliency-correlation-immunity") (tags := "carlet, chapter-4, resilient-construction, pages-57-58, fidelity-exact-generator-matrix")
*Code-generator construction (Carlet, pp. 57--58).* Let $`G` generate a
binary $`[n,k,d]` linear code, and let $`g:V_k\to\mathbb F_2` be balanced.
Then
$$`
f(x)=g(xG^{\mathsf T})
`
is $`(d-1)`-resilient.
:::

:::theorem "carlet-4-resiliency-translation-invariance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.walshTransform_domainTranslate_cast, CryptBoolean.isResilient_domainTranslate") (uses := "carlet-4-theorem-3, carlet-2-prop-6-fourier-shifts") (tags := "carlet, chapter-4, resiliency, translation, page-58, fidelity-exact")
*Translation invariance of resiliency (Carlet, p. 58).* If $`f` is
$`m`-resilient, then for every $`b\in V_n` the function
$$`
x\longmapsto f(x+b)
`
is $`m`-resilient.
:::

:::definition "carlet-4-def-propagation-criteria" (parent := "carlet-chapter-4") (lean := "CryptBoolean.lowWeightNonzeroDirections, CryptBoolean.SatisfiesPropagationCriterionOn, CryptBoolean.SatisfiesPropagationCriterion, CryptBoolean.satisfiesPropagationCriterion_iff_on_lowWeightNonzeroDirections, CryptBoolean.isBalanced_booleanDerivative_iff_autocorrelation_eq_zero, CryptBoolean.satisfiesPropagationCriterion_iff_autocorrelation_eq_zero, CryptBoolean.SatisfiesStrictAvalancheCriterion, CryptBoolean.satisfiesStrictAvalancheCriterion_iff_pc_one, CryptBoolean.SatisfiesPropagationCriterion.mono, CryptBoolean.coordinateRestriction, CryptBoolean.SatisfiesPropagationCriterionOfOrder, CryptBoolean.SatisfiesPropagationCriterionOfOrder.mono_order, CryptBoolean.SatisfiesPropagationCriterionOfOrder.mono_level, CryptBoolean.SatisfiesStrictAvalancheCriterionOfOrder, CryptBoolean.satisfiesStrictAvalancheCriterionOfOrder_iff_pc_one, CryptBoolean.SatisfiesExtendedPropagationCriterion, CryptBoolean.SatisfiesExtendedPropagationCriterion.toPropagationCriterionOfOrder") (uses := "carlet-2-def-2-derivative, carlet-2-def-autocorrelation, carlet-2-balanced-zero-walsh, carlet-4-def-resiliency-correlation-immunity") (tags := "carlet, chapter-4, propagation-criterion, sac, epc, pages-58-59, fidelity-exact")
*Propagation criteria (Carlet, pp. 58--59).* A function $`f` satisfies the
propagation criterion with respect to $`E\subseteq V_n` if $`D_af` is
balanced for every $`a\in E`. It satisfies $`\mathrm{PC}(\ell)` if
$$`
\Delta_f(a)=0
\quad\text{whenever}\quad 0<w_H(a)\le\ell;
`
$`\mathrm{SAC}` is $`\mathrm{PC}(1)`. The order-$`k` form requires every
restriction obtained by fixing $`k` coordinates to satisfy the criterion.
Finally, $`\mathrm{EPC}(\ell)` of order $`k` requires every such nonzero
$`D_af` to be $`k`-resilient; it implies the corresponding propagation
criterion.
:::
