/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter09.HigherOrderAlgebraicImmunity
import CryptBoolean.Carlet.Chapter09.MesnagerHigherOrder
import CryptBoolean.Carlet.Chapter09.NonlinearityBounds
import CryptBoolean.Carlet.Chapter09.OptimalNonlinearity
import CryptBoolean.Carlet.Chapter09.PrescribedDegreeAnnihilators

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Nonlinearity bounds" =>

:::theorem "carlet-9-basic-nonlinearity-from-ai" (parent := "carlet-chapter-9") (lean := "CryptBoolean.sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity") (uses := "carlet-9-ai-weight-bounds, carlet-9-ai-addition-stability, carlet-4-def-nonlinearity, carlet-3-reed-muller-code") (tags := "carlet, chapter-9, algebraic-immunity, nonlinearity, page-136, fidelity-exact")
*A nonlinearity bound from algebraic immunity (Carlet, p. 136).* Let $`n>0`
and $`f:V_n\to\mathbb F_2`. Then
$$`
\operatorname{nl}(f)\ge
\sum_{i=0}^{\operatorname{AI}(f)-2}\binom ni,
`
where the sum is zero when $`\operatorname{AI}(f)<2`.
:::

:::theorem "carlet-9-basic-higher-order-nonlinearity-from-ai" (parent := "carlet-chapter-9") (lean := "CryptBoolean.sum_choose_below_algebraicImmunity_sub_le_higherOrderNonlinearity") (uses := "carlet-9-ai-weight-bounds, carlet-9-ai-addition-stability, carlet-4-def-higher-order-nonlinearity, carlet-3-reed-muller-code") (tags := "carlet, chapter-9, algebraic-immunity, higher-order-nonlinearity, page-136, fidelity-exact")
*Higher-order nonlinearity from algebraic immunity (Carlet, p. 136).* For
every $`r\in\mathbb N`,
$$`
\operatorname{nl}_r(f)\ge
\sum_{i=0}^{\operatorname{AI}(f)-r-1}\binom ni,
`
where the sum is zero when $`\operatorname{AI}(f)\le r`.
:::

:::theorem "carlet-9-lobanov-bound" (parent := "carlet-chapter-9") (lean := "CryptBoolean.algebraicImmunity_le_firstCoordinateSlice_add_one, CryptBoolean.exists_dotProduct_normalizing_linearEquiv, CryptBoolean.two_mul_sum_choose_below_algebraicImmunity_sub_one_le_nonlinearity") (uses := "carlet-9-ai-weight-bounds, carlet-4-def-nonlinearity, carlet-4-def-annihilator-algebraic-immunity, carlet-3-reed-muller-code") (tags := "carlet, chapter-9, algebraic-immunity, nonlinearity, lobanov, reference-253, page-136, fidelity-exact")
*Lobanov's bound (Carlet, p. 136).* For every $`f:V_n\to\mathbb F_2`,
$$`
\operatorname{nl}(f)\ge
2\sum_{i=0}^{\operatorname{AI}(f)-2}\binom{n-1}{i},
`
where the sum is zero when $`\operatorname{AI}(f)<2`.
:::

:::theorem "carlet-9-carlet-higher-order-bound" (parent := "carlet-chapter-9") (lean := "CryptBoolean.annihilatorSpaceDimension_add_sum_choose_sub_degree_le, CryptBoolean.sum_choose_sub_degree_le_hammingWeight_mul, CryptBoolean.two_mul_sum_choose_sub_le_higherOrderNonlinearity") (uses := "carlet-9-ai-weight-bounds, carlet-9-basic-higher-order-nonlinearity-from-ai, carlet-4-def-higher-order-nonlinearity, carlet-4-annihilator-linear-system") (tags := "carlet, chapter-9, algebraic-immunity, higher-order-nonlinearity, reference-70, page-136, fidelity-exact-positive-order")
*Carlet's higher-order extension (Carlet, p. 136).* Let
$`0<r<\operatorname{AI}(f)`. Then
$$`
\operatorname{nl}_r(f)\ge
2\sum_{i=0}^{\operatorname{AI}(f)-r-1}\binom{n-r}{i}.
`
:::

:::theorem "carlet-9-mesnager-higher-order-bound" (parent := "carlet-chapter-9") (lean := "CryptBoolean.annihilatorSpaceDimension_le_hammingWeight_productMismatch, CryptBoolean.annihilatorSpaceDimensions_add_le_hammingWeight_add, CryptBoolean.sum_choose_add_degreeBand_le_higherOrderNonlinearity") (uses := "carlet-9-ai-weight-bounds, carlet-9-ai-addition-stability, carlet-9-basic-higher-order-nonlinearity-from-ai, carlet-4-def-higher-order-nonlinearity, carlet-3-reed-muller-code") (tags := "carlet, chapter-9, algebraic-immunity, higher-order-nonlinearity, mesnager, reference-277, page-136, fidelity-exact")
*Mesnager's higher-order bound (Carlet, p. 136).* Set
$`k=\operatorname{AI}(f)` and let $`0<r<k`. Then
$$`
\operatorname{nl}_r(f)\ge
\sum_{i=0}^{k-r-1}\binom ni+
\sum_{i=\max(0,k-2r)}^{k-r-1}\binom{n-r}{i}.
`
:::

:::theorem "carlet-9-optimal-ai-lobanov-corollaries" (parent := "carlet-chapter-9") (lean := "CryptBoolean.nonlinearity_lowerBound_of_even_optimalAlgebraicImmunity, CryptBoolean.even_optimalAlgebraicImmunity_lowerBound_eq, CryptBoolean.centralBinomial_le_nonlinearity_of_even_optimalAlgebraicImmunity, CryptBoolean.nonlinearity_lowerBound_of_odd_optimalAlgebraicImmunity") (uses := "carlet-9-lobanov-bound") (tags := "carlet, chapter-9, algebraic-immunity, nonlinearity, optimal-immunity, page-137, fidelity-exact")
*Lobanov bounds at optimal algebraic immunity (Carlet, p. 137).* Let $`n>0`
and let $`f:V_n\to\mathbb F_2` have optimal algebraic immunity. If $`n` is
even, then
$$`
\operatorname{nl}(f)\ge
2^{n-1}-2\binom{n-1}{n/2-1}
=2^{n-1}-\binom n{n/2}.
`
If $`n` is odd, then
$$`
\operatorname{nl}(f)\ge
2^{n-1}-\binom{n-1}{(n-1)/2}.
`
:::
