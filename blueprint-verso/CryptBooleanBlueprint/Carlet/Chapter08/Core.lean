/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter08.AffineFlatWalshCharacterization
import CryptBoolean.Carlet.Chapter08.AlgebraicDegree
import CryptBoolean.Carlet.Chapter08.ExtremalPropagation
import CryptBoolean.Carlet.Chapter08.PropagationNonlinearity
import CryptBoolean.Carlet.Chapter08.WalshCharacterization

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Propagation criteria and Walsh analysis" =>

:::theorem "carlet-8-even-pc-pred-two-bent" (parent := "carlet-chapter-8") (lean := "CryptBoolean.isBent_of_satisfiesPropagationCriterion_pred_two_of_even, CryptBoolean.satisfiesPropagationCriterion_pred_two_iff_isBent_of_even, CryptBoolean.satisfiesPropagationCriterion_dimension_of_pred_two_of_even, CryptBoolean.not_satisfiesPropagationCriterion_pred_two_of_even_of_isBalanced") (uses := "carlet-4-def-propagation-criteria, carlet-6-theorem-8-perfect-nonlinearity") (tags := "carlet, chapter-8, propagation-criterion, bent-functions, even-dimension, page-131, fidelity-explicit-valid-dimension-range")
*Extremal propagation in even dimension (Carlet, p. 131).* Let $`n\ge4`
be even and let $`f:V_n\to\mathbb F_2`. Then
$$`
f\text{ satisfies }\mathrm{PC}(n-2)
\quad\Longleftrightarrow\quad
f\text{ is bent}.
`
Equivalently, $`\mathrm{PC}(n-2)` already implies $`\mathrm{PC}(n)`.
Consequently, no balanced $`n`-variable function satisfies
$`\mathrm{PC}(n-2)`.
:::

:::theorem "carlet-8-odd-pc-pred-one-classification" (parent := "carlet-chapter-8") (lean := "CryptBoolean.oddDiagonalProjection, CryptBoolean.oddDiagonalBentLift, CryptBoolean.HasOddDiagonalBentNormalForm, CryptBoolean.satisfiesPropagationCriterion_pred_one_iff_hasOddDiagonalBentNormalForm") (uses := "carlet-4-def-propagation-criteria, carlet-6-def-7-bent, carlet-2-def-affine-functions") (tags := "carlet, chapter-8, propagation-criterion, classification, odd-dimension, page-131, fidelity-reviewed-endpoint")
*Extremal propagation in odd dimension (Carlet, p. 131).* Let $`n\ge3` be
odd and let $`f:V_n\to\mathbb F_2`. Then $`f` satisfies
$`\mathrm{PC}(n-1)` if and only if there exist a bent function
$`g:V_{n-1}\to\mathbb F_2` and an affine function
$`h:V_n\to\mathbb F_2` such that
$$`
f(x_1,\ldots,x_n)=
g(x_1\oplus x_n,\ldots,x_{n-1}\oplus x_n)\oplus h(x_1,\ldots,x_n).
`
:::

:::theorem "carlet-8-odd-pc-pred-two-classification" (parent := "carlet-chapter-8") (lean := "CryptBoolean.coordinateDirection, CryptBoolean.HasUniqueHighWeightLinearStructure, CryptBoolean.satisfiesPropagationCriterion_pred_two_iff_hasUniqueHighWeightLinearStructure, CryptBoolean.puncturedDiagonalShearLinearMap, CryptBoolean.puncturedDiagonalShearLinearMap_involutive, CryptBoolean.puncturedDiagonalShearLinearEquiv, CryptBoolean.oddPuncturedDiagonalProjection, CryptBoolean.oddPuncturedDiagonalProjection_apply_same, CryptBoolean.oddPuncturedDiagonalProjection_apply_of_ne, CryptBoolean.coordinateSwapLinearEquiv, CryptBoolean.coordinateSwapLinearEquiv_apply, CryptBoolean.oddTerminalDiagonalProjectionAt, CryptBoolean.oddTerminalDiagonalProjectionAt_apply_same, CryptBoolean.oddTerminalDiagonalProjectionAt_apply_of_ne, CryptBoolean.oddTerminalDiagonalProjection, CryptBoolean.oddTerminalDiagonalProjection_apply_castSucc, CryptBoolean.oddTerminalDiagonalProjection_apply_last, CryptBoolean.oddPuncturedDiagonalBentLift, CryptBoolean.oddTerminalDiagonalBentLiftAt, CryptBoolean.oddPenultimateIndex, CryptBoolean.HasOddPredTwoBentNormalForm, CryptBoolean.hasOddPredTwoBentNormalForm_of_satisfiesPropagationCriterion, CryptBoolean.satisfiesPropagationCriterion_of_hasOddPredTwoBentNormalForm, CryptBoolean.satisfiesPropagationCriterion_pred_two_iff_hasOddPredTwoBentNormalForm") (uses := "carlet-8-odd-pc-pred-one-classification, carlet-4-def-linear-kernel, carlet-6-def-7-bent") (tags := "carlet, chapter-8, propagation-criterion, classification, linear-structures, odd-dimension, page-131, fidelity-primary-coordinate-forms-restored")
*The $`\mathrm{PC}(n-2)` classification in odd dimension (Carlet, p. 131).*
Let $`n\ge3` be odd. A function $`f:V_n\to\mathbb F_2` satisfies
$`\mathrm{PC}(n-2)` if and only if it is an affine function plus a bent
function on one of the following three quotient-coordinate systems:

* $`y_j=x_j\oplus x_n` for every $`1\le j\le n-1`;
* for one $`i`, $`y_i=x_i` and $`y_j=x_j\oplus x_n` for $`j\ne i`;
* $`y_j=x_j\oplus x_{n-1}` for $`1\le j\le n-2`, and $`y_{n-1}=x_n`.

Equivalently, there exists a nonzero $`a\in V_n` with $`w_H(a)\ge n-1`
such that $`D_af` is constant, while $`D_bf` is balanced for every nonzero
$`b\ne a`. Thus $`f` has exactly one nonzero linear structure, of weight
$`n-1` or $`n`.
:::

:::theorem "carlet-8-pc-algebraic-degree-bound" (parent := "carlet-chapter-8") (lean := "CryptBoolean.differenceMultiplicity_even, CryptBoolean.functionAlgebraicDegree_le_pred_of_satisfiesPropagationCriterion") (uses := "carlet-4-def-propagation-criteria, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-8, propagation-criterion, algebraic-degree, page-131, fidelity-explicit-valid-dimension-range")
*Algebraic degree under a propagation criterion (Carlet, p. 131).* Let
$`n\ge3`, $`1\le \ell<n`, and $`f:V_n\to\mathbb F_2`. If $`f` satisfies
$`\mathrm{PC}(\ell)`, then
$$`
\deg(f)\le n-1.
`
:::

:::theorem "carlet-8-propagating-subspace-nonlinearity-bound" (parent := "carlet-chapter-8") (lean := "CryptBoolean.walshTransform_sq_le_of_balanced_derivatives_on_subspace, CryptBoolean.nonlinearity_lowerBound_of_balanced_derivatives_on_subspace, CryptBoolean.walshTransform_sq_le_of_satisfiesPropagationCriterion, CryptBoolean.nonlinearity_lowerBound_of_satisfiesPropagationCriterion") (uses := "carlet-4-def-propagation-criteria, carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-8, propagation-criterion, nonlinearity, walsh-transform, page-131, fidelity-exact")
*Nonlinearity from a propagating subspace (Carlet, p. 131).* Let
$`F\le V_n` have dimension $`\ell`, and assume that $`D_af` is balanced for
every nonzero $`a\in F`. Then, for every $`u\in V_n`,
$$`
W_f(u)^2\le 2^{2n-\ell}
`
and
$$`
\operatorname{nl}(f)\ge
2^{n-1}-2^{n-\ell/2-1}.
`
Consequently, the same bounds hold whenever $`0\le\ell\le n` and $`f`
satisfies $`\mathrm{PC}(\ell)`.
:::

:::theorem "carlet-8-propagation-bound-equality-parameters" (parent := "carlet-chapter-8") (lean := "CryptBoolean.propagationCriterion_nonlinearity_equality_parameters") (uses := "carlet-8-propagating-subspace-nonlinearity-bound, carlet-2-parseval, carlet-6-theorem-8-perfect-nonlinearity") (tags := "carlet, chapter-8, propagation-criterion, nonlinearity, equality, page-131, fidelity-exact")
*Parameters for equality in the propagation bound (Carlet, p. 131).* Let
$`1\le\ell\le n`, and let $`f:V_n\to\mathbb F_2` satisfy
$`\mathrm{PC}(\ell)`. If
$$`
\operatorname{nl}(f)=2^{n-1}-2^{n-\ell/2-1},
`
then either $`n` is odd and $`\ell=n-1`, or $`n` is even and $`\ell=n`.
:::

:::theorem "carlet-8-walsh-square-pc-characterization" (parent := "carlet-chapter-8") (lean := "CryptBoolean.sum_vectorWalshCharacter_mul_walshTransform_sq, CryptBoolean.satisfiesPropagationCriterion_iff_sum_vectorWalshCharacter_mul_walshTransform_sq_eq_zero") (uses := "carlet-4-def-propagation-criteria, carlet-2-rel-25-wiener-khinchin, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-8, propagation-criterion, walsh-transform, characterization, page-131, fidelity-exact")
*Wiener--Khintchine characterization (Carlet, p. 131).* Let
$`0\le\ell\le n` and $`f:V_n\to\mathbb F_2`. Then $`f` satisfies
$`\mathrm{PC}(\ell)` if and only if, for every nonzero $`a\in V_n` with
$`w_H(a)\le\ell`,
$$`
\sum_{u\in V_n}(-1)^{a\cdot u}W_f(u)^2=0.
`
:::

:::theorem "carlet-8-prop-35-affine-flat-walsh-square-characterization" (parent := "carlet-chapter-8") (lean := "CryptBoolean.predecessorWalshSquareSum, CryptBoolean.predecessorWalshSquareSum_eq_autocorrelationSum, CryptBoolean.satisfiesPropagationCriterion_iff_predecessorWalshSquareSum") (uses := "carlet-4-def-propagation-criteria, carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin") (tags := "carlet, chapter-8, proposition-35, propagation-criterion, walsh-transform, affine-flat, page-131, page-132, fidelity-exact")
*Proposition 35 (Carlet, pp. 131--132).* Let $`0\le\ell\le n` and
$`f:V_n\to\mathbb F_2`. Write $`w\preceq u` when
$`\operatorname{supp}(w)\subseteq\operatorname{supp}(u)`. Then $`f`
satisfies $`\mathrm{PC}(\ell)` if and only if, for every $`u,v\in V_n` with
$`w_H(u)\ge n-\ell`,
$$`
\sum_{w\preceq u}W_f(w\oplus v)^2=2^{n+w_H(u)}.
`
:::
