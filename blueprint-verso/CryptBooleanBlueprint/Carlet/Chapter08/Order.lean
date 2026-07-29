/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter08.OrderAlgebraicDegree
import CryptBoolean.Carlet.Chapter08.OrderCharacterization
import CryptBoolean.Carlet.Chapter08.RestrictionWalshCharacterization
import CryptBoolean.Carlet.Chapter08.ExtremalOrderNecessity
import CryptBoolean.Carlet.Chapter08.ExtremalOrderPeriod

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Propagation criteria of order" =>

:::theorem "carlet-8-prop-36-order-characterization" (parent := "carlet-chapter-8") (lean := "CryptBoolean.all_coordinateRestrictions_balanced_iff_walshTransform_eq_zero, CryptBoolean.satisfiesPropagationCriterionOfOrder_iff_derivativeRestrictions_balanced, CryptBoolean.walshTransform_booleanDerivative_eq_sum_bitSignInt, CryptBoolean.walshTransform_booleanDerivative_zero_direction, CryptBoolean.satisfiesExtendedPropagationCriterion_iff_walshTransform_booleanDerivative_eq_zero, CryptBoolean.satisfiesPropagationCriterionOfOrder_iff_walshTransform_booleanDerivative_eq_zero") (uses := "carlet-4-def-propagation-criteria, carlet-4-theorem-3, carlet-2-def-2-derivative") (tags := "carlet, chapter-8, proposition-36, propagation-criterion, order, walsh-transform, page-132, fidelity-exact")
*Proposition 36 (Carlet, p. 132).* Let $`\ell+k\le n` and
$`f:V_n\to\mathbb F_2`. Then $`f` satisfies $`\mathrm{EPC}(\ell)` of order
$`k` if and only if, for every $`a,b\in V_n` with $`w_H(a)\le\ell`,
$`w_H(b)\le k`, and $`(a,b)\ne(0,0)`,
$$`
\sum_{x\in V_n}(-1)^{f(x)\oplus f(x\oplus a)\oplus b\cdot x}=0.
`
It satisfies $`\mathrm{PC}(\ell)` of order $`k` if and only if the same
identity holds whenever, in addition,
$`\operatorname{supp}(a)\cap\operatorname{supp}(b)=\varnothing`.
:::

:::theorem "carlet-8-prop-37-restriction-walsh-characterization" (parent := "carlet-chapter-8") (lean := "CryptBoolean.predecessorSubspace, CryptBoolean.mem_predecessorSubspace_iff, CryptBoolean.card_predecessorSubspace, CryptBoolean.perpendicular_predecessorSubspace, CryptBoolean.mem_perpendicular_predecessorSubspace_iff, CryptBoolean.coordinateRestrictedWalshTransform, CryptBoolean.predecessorWalshRestrictionProductSum, CryptBoolean.derivativeWalshRectangleSum, CryptBoolean.predecessorWalshRestrictionProductSum_eq_derivativeWalshRectangleSum, CryptBoolean.satisfiesExtendedPropagationCriterion_iff_predecessorWalshRestrictionProductSum, CryptBoolean.satisfiesPropagationCriterionOfOrder_iff_predecessorWalshRestrictionProductSum") (uses := "carlet-8-prop-36-order-characterization, carlet-2-cor-1-poisson-summation") (tags := "carlet, chapter-8, proposition-37, propagation-criterion, order, walsh-transform, restriction, page-133, fidelity-exact")
*Proposition 37 (Carlet, p. 133).* Let $`\ell+k\le n` and
$`f:V_n\to\mathbb F_2`. For $`v\in V_n`, define
$$`
W_f^v(w)=\sum_{x\preceq v}(-1)^{f(x)\oplus w\cdot x}.
`
Then $`f` satisfies $`\mathrm{EPC}(\ell)` of order $`k` if and only if, for
all $`u,v\in V_n` with $`w_H(u)\ge n-\ell` and $`w_H(v)\ge n-k`,
$$`
\sum_{w\preceq u}W_f(w)W_f^v(w)=2^{w_H(u)+w_H(v)}.
`
It satisfies $`\mathrm{PC}(\ell)` of order $`k` if and only if the same
identity holds whenever
$`\operatorname{supp}(\bar u)\cap\operatorname{supp}(\bar v)=\varnothing`.
:::

:::theorem "carlet-8-sac-order-algebraic-degree" (parent := "carlet-chapter-8") (lean := "CryptBoolean.coordinateRestriction_zeroFixed_apply, CryptBoolean.anfCoeff_coordinateRestriction_zeroFixed_univ, CryptBoolean.coordinateRestriction_degree_le_of_satisfiesStrictAvalancheCriterionOfOrder, CryptBoolean.functionAlgebraicDegree_le_of_satisfiesStrictAvalancheCriterionOfOrder") (uses := "carlet-8-pc-algebraic-degree-bound, carlet-4-def-propagation-criteria, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-8, strict-avalanche-criterion, order, algebraic-degree, page-133, fidelity-explicit-valid-dimension-range")
*Algebraic degree under SAC of order $`k` (Carlet, p. 133).* Let
$`k+3\le n`, and let $`f:V_n\to\mathbb F_2` satisfy the strict avalanche
criterion of order $`k`. Every restriction obtained by fixing $`k` input
coordinates has algebraic degree at most $`n-k-1`; in particular,
$$`
\deg(f)\le n-k-1.
`
:::

:::theorem "carlet-8-extremal-order-complete-quadratic-classification" (parent := "carlet-chapter-8") (lean := "CryptBoolean.isBalanced_add_constant_iff, CryptBoolean.eq_constant_of_coordinateDerivatives_eq_zero, CryptBoolean.completeQuadraticPolarFrequency_apply_eq_sum_add, CryptBoolean.booleanDerivative_completeQuadraticBit_eq_affineFunction, CryptBoolean.ne_completeQuadraticPolarFrequency_of_disjoint_of_support_card_add_lt, CryptBoolean.booleanDerivative_domainTranslate, CryptBoolean.satisfiesPropagationCriterionOfOrder_domainTranslate_iff, CryptBoolean.satisfiesPropagationCriterionOfOrder_add_affineFunction_iff, CryptBoolean.satisfiesPropagationCriterionOfOrder_completeQuadraticBit, CryptBoolean.satisfiesPropagationCriterionOfOrder_completeQuadraticBit_add_affineFunction, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_completeQuadraticBit_add_affineFunction, CryptBoolean.completeQuadraticBit_finAppend, CryptBoolean.secondBooleanDerivative_same_direction, CryptBoolean.secondBooleanDerivative_add, CryptBoolean.secondBooleanDerivative_completeQuadraticBit_coordinateDirections_eq_one, CryptBoolean.exists_completeQuadraticBit_add_affineFunction_of_coordinateSecondDerivatives_eq_one, CryptBoolean.exists_firstBlockSlice_completeQuadraticBit_add_affineFunction, CryptBoolean.isBent_firstBlockSlice_completeQuadraticBit_add_affineFunction, CryptBoolean.cubeReindexLinearEquiv, CryptBoolean.hammingWeight_comp_cubeReindexLinearEquiv, CryptBoolean.isBalanced_comp_cubeReindexLinearEquiv_iff, CryptBoolean.card_f₂Support_cubeReindexLinearEquiv, CryptBoolean.f₂Support_cubeReindexLinearEquiv, CryptBoolean.booleanDerivative_comp_cubeReindexLinearEquiv, CryptBoolean.satisfiesPropagationCriterion_comp_cubeReindexLinearEquiv_iff, CryptBoolean.satisfiesPropagationCriterionOfOrder_comp_cubeReindexLinearEquiv_iff, CryptBoolean.embeddingFinsetEquiv, CryptBoolean.canonicalEmbeddingReindexEquiv, CryptBoolean.freeCoordinateEmbedding_canonicalEmbeddingReindexEquiv, CryptBoolean.embeddedCoordinateRestriction, CryptBoolean.satisfiesPropagationCriterion_embeddedCoordinateRestriction_of_order, CryptBoolean.satisfiesPropagationCriterionOfOrder_embeddedCoordinateRestriction, CryptBoolean.isBent_comp_cubeReindexLinearEquiv_iff, CryptBoolean.isBent_embeddedCoordinateRestriction_iff, CryptBoolean.isBent_embeddedCoordinateRestriction_of_order_dimension, CryptBoolean.isBent_embeddedCoordinateRestriction_of_order_pred_two, CryptBoolean.standardPredThreeDirection, CryptBoolean.false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_linearStructure, CryptBoolean.satisfiesPropagationCriterion_firstBlockSlice_of_order_one, CryptBoolean.isLinearStructure_or_isBalanced_of_satisfiesPropagationCriterion_pred_two_odd, CryptBoolean.hammingWeight_eq_add_firstBlockSlices, CryptBoolean.isBalanced_of_firstBlockSlices, CryptBoolean.firstBlockSlice_eq_complement_of_isBalanced, CryptBoolean.satisfiesPropagationCriterionOfOrder_comp_coordinateSwapLinearEquiv_iff, CryptBoolean.lastTwoCoordinateProduct, CryptBoolean.standardDirectionInsertion, CryptBoolean.false_of_satisfiesPropagationCriterionOfOrder_pred_three_of_standardDirection_product, CryptBoolean.isBent_of_satisfiesPropagationCriterionOfOrder_pred_three_of_even, CryptBoolean.satisfiesPropagationCriterionOfOrder_dimension_completeQuadraticBit_add_affineFunction, CryptBoolean.exists_completeQuadraticBit_add_affineFunction_of_order_dimension, CryptBoolean.satisfiesPropagationCriterionOfOrder_dimension_iff_completeQuadratic_add_affine, CryptBoolean.satisfiesPropagationCriterionOfOrder_add_two_of_even, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_add_two_of_even, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_even, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_add_three_of_odd, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic_of_odd, CryptBoolean.satisfiesPropagationCriterionOfOrder_extremal_iff_completeQuadratic") (uses := "carlet-4-def-propagation-criteria, carlet-6-rel-56-complete-quadratic, carlet-2-def-affine-functions, carlet-8-even-pc-pred-two-bent, carlet-8-odd-pc-pred-two-classification, carlet-6-codimension-two-restrictions") (tags := "carlet, chapter-8, propagation-criterion, order, complete-quadratic, classification, page-133, fidelity-reviewed-inclusive-ranges")
*Extremal propagation criteria of order (Carlet, p. 133).* Let
$`f:V_n\to\mathbb F_2` and suppose either

* $`n\ge6`, $`\ell` is positive and even, and $`\ell\le n-4`; or
* $`n\ge10`, $`\ell` is odd, and $`5\le\ell\le n-5`.

Then $`f` satisfies $`\mathrm{PC}(\ell)` of order $`n-\ell-2` if and only
if there exists an affine function $`h:V_n\to\mathbb F_2` such that
$$`
f(x_1,\ldots,x_n)=
\bigoplus_{1\le i<j\le n}x_ix_j\oplus h(x_1,\ldots,x_n).
`
:::
