/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter09.CarletFeng
import CryptBoolean.Carlet.Chapter09.CarletFengNonlinearity
import CryptBoolean.Carlet.Chapter09.Majority

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Functions with optimal algebraic immunity" =>

:::theorem "carlet-9-majority-parameters" (parent := "carlet-chapter-9") (lean := "CryptBoolean.carletMajority, CryptBoolean.carletMajority_apply_eq_one_iff, CryptBoolean.carletMajority_apply_eq_one_iff_ceiling_half, CryptBoolean.carletMajority_eq_of_support_card_eq, CryptBoolean.carletMajority_symmetric, CryptBoolean.carletMajority_isKNormal, CryptBoolean.algebraicImmunity_carletMajority, CryptBoolean.fourierInfinityNorm_majority_even, CryptBoolean.fourierInfinityNorm_majority_odd, CryptBoolean.maxWalshMagnitude_carletStrictMajority_even, CryptBoolean.maxWalshMagnitude_carletStrictMajority_odd, CryptBoolean.nonlinearity_carletStrictMajority_odd, CryptBoolean.nonlinearity_carletStrictMajority_even, CryptBoolean.nonlinearity_carletStrictMajority, CryptBoolean.nonlinearity_add_constant_one, CryptBoolean.nonlinearity_carletMajority_eq_strictMajority, CryptBoolean.nonlinearity_carletMajority, CryptBoolean.nonlinearity_carletMajority_of_even, CryptBoolean.nonlinearity_carletMajority_of_odd") (uses := "carlet-5-def-4-normality, carlet-9-normality-ai-bound, carlet-9-lobanov-bound, carlet-4-def-nonlinearity, carlet-2-def-support-weight") (tags := "carlet, chapter-9, majority, algebraic-immunity, normality, nonlinearity, page-135, page-137, fidelity-exact")
*Parameters of the majority function (Carlet, pp. 135, 137).* Let $`n>0`
and define $`\operatorname{Maj}_n:V_n\to\mathbb F_2` by
$$`
\operatorname{Maj}_n(x)=1
\quad\Longleftrightarrow\quad
2w_H(x)\ge n.
`
It is symmetric, $`\lfloor n/2\rfloor`-normal, and
$`\operatorname{AI}(\operatorname{Maj}_n)=\lceil n/2\rceil`. Its exact
nonlinearity is
$$`
\operatorname{nl}(\operatorname{Maj}_n)=
\begin{cases}
2^{n-1}-\binom{n-1}{n/2},& n\text{ even},\\
2^{n-1}-\binom{n-1}{(n-1)/2},& n\text{ odd}.
\end{cases}
`
:::

:::theorem "carlet-9-majority-threshold-variants" (parent := "carlet-chapter-9") (lean := "CryptBoolean.binaryComplementAffineEquiv, CryptBoolean.binaryComplementAffineEquiv_apply, CryptBoolean.carletStrictMajority, CryptBoolean.carletStrictMinority, CryptBoolean.carletWeakMinority, CryptBoolean.f₂Support_binaryCubeComplement, CryptBoolean.card_f₂Support_binaryCubeComplement, CryptBoolean.carletStrictMajority_apply_eq_one_iff, CryptBoolean.carletStrictMinority_apply_eq_one_iff, CryptBoolean.carletWeakMinority_apply_eq_one_iff, CryptBoolean.carletStrictMinority_eq_affineReindexing, CryptBoolean.carletWeakMinority_eq_outputComplement, CryptBoolean.carletMajority_eq_affineReindexing_add_one, CryptBoolean.algebraicImmunity_carletStrictMajority, CryptBoolean.algebraicImmunity_carletStrictMinority, CryptBoolean.algebraicImmunity_carletWeakMinority, CryptBoolean.nonlinearity_carletWeakMinority, CryptBoolean.nonlinearity_carletStrictMinority") (uses := "carlet-9-majority-parameters, carlet-9-ai-weight-bounds, carlet-4-def-annihilator-algebraic-immunity") (tags := "carlet, chapter-9, majority, affine-equivalence, algebraic-immunity, page-137, fidelity-exact")
*Majority threshold variants (Carlet, p. 137).* Replacing the condition
$`w_H(x)\ge n/2` by any of
$$`
w_H(x)>n/2,
\qquad w_H(x)\le n/2,
\qquad w_H(x)<n/2
`
gives a function affinely equivalent to $`\operatorname{Maj}_n`, possibly
after adding the constant one. All four functions therefore have algebraic
immunity $`\lceil n/2\rceil`.
:::

:::theorem "carlet-9-theorem-15" (parent := "carlet-chapter-9") (lean := "CryptBoolean.carletFengSupport, CryptBoolean.carletFengFieldFunction, CryptBoolean.carletFengBooleanFunction, CryptBoolean.mem_carletFengSupport_iff, CryptBoolean.carletFengSupport_card, CryptBoolean.support_carletFengBooleanFunction, CryptBoolean.isBalanced_carletFengBooleanFunction, CryptBoolean.algebraicImmunity_carletFengBooleanFunction, CryptBoolean.carletFeng_balanced_and_algebraicImmunity") (uses := "carlet-2-univariate-representation, carlet-2-univariate-binary-degree, carlet-4-def-annihilator-algebraic-immunity, carlet-4-ai-upper-bound, carlet-2-def-support-weight") (tags := "carlet, chapter-9, theorem-15, carlet-feng, algebraic-immunity, balancedness, page-138, page-139, fidelity-primary-domain-restored")
*Theorem 15 (Carlet, pp. 138--139).* Let $`n\ge2`, let
$`K=\operatorname{GF}(2^n)`, and let $`\alpha` be a primitive element of
$`K`. Let $`f:K\to\mathbb F_2` have support
$$`
\{0\}\cup\{\alpha^i\mid 0\le i\le2^{n-1}-2\}.
`
Then $`f` is balanced and
$$`
\operatorname{AI}(f)=\left\lceil\frac n2\right\rceil.
`
:::

:::theorem "carlet-9-rel-70" (parent := "carlet-chapter-9") (lean := "CryptBoolean.carletFengUnivariateRepresentation, CryptBoolean.coeff_carletFengUnivariateRepresentation, CryptBoolean.coeff_top_carletFengUnivariateRepresentation, CryptBoolean.carletFengClosedPolynomial, CryptBoolean.carletFengUnivariateRepresentation_eq_closedPolynomial, CryptBoolean.carletFeng_relation_70") (uses := "carlet-9-theorem-15, carlet-2-univariate-representation") (tags := "carlet, chapter-9, relation-70, carlet-feng, univariate-representation, page-139, page-140, fidelity-exact")
*Relation (70) (Carlet, pp. 139--140).* Under the hypotheses of Theorem 15,
the bounded univariate representation of $`f` is
$$`
f(x)=1+\sum_{i=1}^{2^n-2}
\frac{\alpha^i}{(1+\alpha^i)^{1/2}}x^i,
`
where $`u^{1/2}=u^{2^{n-1}}` in $`\operatorname{GF}(2^n)`.
:::

:::theorem "carlet-9-carlet-feng-degree" (parent := "carlet-chapter-9") (lean := "CryptBoolean.coeff_two_pow_sub_two_carletFengUnivariateRepresentation_ne_zero, CryptBoolean.functionAlgebraicDegree_carletFengBooleanFunction") (uses := "carlet-9-rel-70, carlet-2-univariate-binary-degree") (tags := "carlet, chapter-9, carlet-feng, algebraic-degree, page-140, fidelity-exact")
*Algebraic degree of the Carlet--Feng function (Carlet, p. 140).* Under the
hypotheses of Theorem 15,
$$`
\deg(f)=n-1.
`
:::

:::theorem "carlet-9-carlet-feng-nonlinearity" (parent := "carlet-chapter-9") (lean := "CryptBoolean.maxWalshMagnitude_carletFengBooleanFunction_cast_le, CryptBoolean.nonlinearity_carletFengBooleanFunction_lower_bound") (uses := "carlet-9-theorem-15, carlet-4-rel-35-nonlinearity-walsh, carlet-2-trace-pairing-coordinates") (tags := "carlet, chapter-9, carlet-feng, nonlinearity, character-sums, page-140, fidelity-exact")
*Nonlinearity of the Carlet--Feng function (Carlet, p. 140).* Under the
hypotheses of Theorem 15,
$$`
\operatorname{nl}(f)\ge
2^{n-1}-n\ln(2)\,2^{n/2}-1,
`
where the integer nonlinearity is embedded in $`\mathbb R`.
:::
