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

#doc (Manual) "Maximum correlation" =>

:::definition "carlet-4-def-maximum-correlation" (parent := "carlet-chapter-4") (lean := "CryptBoolean.CoordinateSignChoice, CryptBoolean.coordinateBooleanFunction, CryptBoolean.coordinateBooleanFunction_dependsOn, CryptBoolean.exists_coordinateSignChoice_iff_dependsOn, CryptBoolean.normalizedCorrelation, CryptBoolean.normalizedCorrelation_eq_one_sub_two_mul_hammingDistance, CryptBoolean.distanceToCoordinateFunctions, CryptBoolean.maximumCorrelation, CryptBoolean.distanceToCoordinateFunctions_cast_eq, CryptBoolean.higherOrderNonlinearity_le_distanceToCoordinateFunctions, CryptBoolean.restrictionMaximumCorrelation, CryptBoolean.maximumCorrelation_eq_restrictionMaximumCorrelation, CryptBoolean.restrictionRawImbalance, CryptBoolean.maximumCorrelation_eq_sum_abs_restrictionRawImbalance_div_two_pow, CryptBoolean.maximumCorrelation_eq_zero_iff_restrictions_balanced") (uses := "carlet-4-def-higher-order-nonlinearity, carlet-4-def-resiliency-correlation-immunity, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, maximum-correlation, pages-66-67, fidelity-exact-with-zero-dimensional-form")
*Maximum correlation on a coordinate set (Carlet, pp. 66--67).* Let
$`\mathrm{BF}_{I,n}` be the functions depending only on coordinates in $`I`
and define
$$`
C_f(I)=2^{-n}\max_{g\in\mathrm{BF}_{I,n}}\mathcal F(f+g).
`
Then
$$`
d_H(f,\mathrm{BF}_{I,n})=2^{n-1}(1-C_f(I)).
`
If $`|I|=r`, this distance is at least $`\operatorname{nl}_r(f)`. Moreover,
$`C_f(I)` is $`2^{-n}` times the sum of the absolute imbalances of the
restrictions obtained by fixing $`I`; hence it vanishes exactly when all
those restrictions are balanced.
:::

:::theorem "carlet-4-rel-40-maximum-correlation-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.restrictedWalshSquareSum, CryptBoolean.restrictedWalshSquareSum_eq_sum_filter, CryptBoolean.two_pow_sq_mul_expect_restrictionMean_sq_eq_restrictedWalshSquareSum, CryptBoolean.maximumCorrelation_le_sqrt_restrictedWalshSquareSum_div, CryptBoolean.restrictedWalshSquareSum_le_card_mul_maxWalshMagnitude_sq, CryptBoolean.sqrt_restrictedWalshSquareSum_le, CryptBoolean.relation_40_maximumCorrelation_bound, CryptBoolean.distanceToCoordinateFunctions_cast_ge_walshSquare, CryptBoolean.distanceToCoordinateFunctions_cast_ge_maxWalshMagnitude") (uses := "carlet-4-def-maximum-correlation, carlet-4-def-nonlinearity, carlet-2-def-walsh-transform, carlet-2-cor-1-poisson-summation") (tags := "carlet, chapter-4, relation-40, maximum-correlation, page-66, fidelity-exact-with-real-rpow-source-form")
*Relation (40) (Carlet, p. 66).* For $`I\subseteq\{1,\ldots,n\}`,
$$`
C_f(I)
\le2^{-n}\left(\sum_{\operatorname{supp}(u)\subseteq I}W_f(u)^2\right)^{1/2}
\le2^{-n+|I|/2}\bigl(2^n-2\operatorname{nl}(f)\bigr).
`
Equivalently,
$$`
d_H(f,\mathrm{BF}_{I,n})
\ge2^{n-1}-\frac12
\left(\sum_{\operatorname{supp}(u)\subseteq I}W_f(u)^2\right)^{1/2}
\ge2^{n-1}-2^{|I|/2-1}\max_u|W_f(u)|.
`
:::

:::definition "carlet-4-generalized-linear-structure-distance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.IsZeroDerivativeDirection, CryptBoolean.zeroDerivativeKernel, CryptBoolean.mem_zeroDerivativeKernel, CryptBoolean.zeroDerivativeKernel_le_linearKernel, CryptBoolean.zeroDerivativeKernelAffineEquiv, CryptBoolean.finrank_zeroDerivativeKernel_comp_affineEquiv, CryptBoolean.zeroDerivativeKernel_zero, CryptBoolean.finrank_zeroDerivativeKernel_zero, CryptBoolean.largeZeroDerivativeFunctions, CryptBoolean.largeZeroDerivativeFunctions_nonempty, CryptBoolean.generalizedLinearStructureDistance, CryptBoolean.mem_largeZeroDerivativeFunctions_comp_affineEquiv_iff, CryptBoolean.generalizedLinearStructureDistance_comp_affineEquiv_le, CryptBoolean.generalizedLinearStructureDistance_comp_affineEquiv") (uses := "carlet-4-def-linear-kernel, carlet-2-def-hamming-distance") (tags := "carlet, chapter-4, generalized-linear-structure, page-67, fidelity-exact-on-feasible-range")
*Generalized distance to a large zero-derivative space (Carlet, p. 67).* For
$`0\le k\le n`, define the distance from $`f` to the functions $`g` satisfying
$$`
\dim\{e\in V_n:D_eg=0\}\ge k.
`
This distance is invariant under affine equivalence.
:::
