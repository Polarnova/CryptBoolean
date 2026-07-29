/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.MaximumCorrelation
import CryptBoolean.Carlet.Chapter07.PropagationEquality
import CryptBoolean.Carlet.Chapter07.PropagationTradeoff

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Correlation and propagation criteria" =>

:::theorem "carlet-7-maximum-correlation-support" (parent := "carlet-chapter-7") (lean := "CryptBoolean.card_highWeightFrequenciesSupportedIn_eq_sum_choose, CryptBoolean.card_walshSupport_filter_subset_le_sum_choose_of_isResilient, CryptBoolean.maximumCorrelation_eq_abs_walshTransform_f₂CubeOfFinset_div_of_isResilient") (uses := "carlet-4-def-maximum-correlation, carlet-4-rel-40-maximum-correlation-bound, carlet-4-theorem-3") (tags := "carlet, chapter-7, maximum-correlation, walsh-support, page-115, fidelity-exact")
*Maximum correlation on a coordinate set (Carlet, p. 115).* Let
$`f:V_n\to\mathbb F_2` be $`m`-resilient and let $`I\subseteq[n]`.
Among the Walsh frequencies supported in $`I`, at most
$$`
\sum_{j=m+1}^{|I|}\binom{|I|}{j}
`
have nonzero coefficients. If $`|I|=m+1` and $`u_I` is the unique
frequency with support $`I`, then the maximum correlation of $`f` with
functions depending only on $`I` is
$$`
2^{-n}|W_f(u_I)|.
`
:::

:::theorem "carlet-7-resiliency-propagation-tradeoff" (parent := "carlet-chapter-7") (lean := "CryptBoolean.resilient_propagationCriterion_parameter_tradeoff") (uses := "carlet-4-def-resiliency-correlation-immunity, carlet-4-def-propagation-criteria, carlet-4-theorem-3, carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin") (tags := "carlet, chapter-7, resiliency, propagation-criterion, page-116, fidelity-exact")
*Resiliency--propagation tradeoff (Carlet, p. 116).* If an $`n`-variable
Boolean function is $`m`-resilient and satisfies $`\mathrm{PC}(\ell)`, then
$$`
m+\ell\le n-1.
`
:::

:::theorem "carlet-7-resiliency-propagation-equality" (parent := "carlet-chapter-7") (lean := "CryptBoolean.resilient_propagationCriterion_equality_classification") (uses := "carlet-7-resiliency-propagation-tradeoff") (tags := "carlet, chapter-7, resiliency, propagation-criterion, equality, page-116, fidelity-explicit-positive-propagation-order")
*Equality in the resiliency--propagation tradeoff (Carlet, p. 116).* Let
$`\ell>0`. If an $`n`-variable $`m`-resilient Boolean function satisfies
$`\mathrm{PC}(\ell)` and
$$`
m+\ell=n-1,
`
then $`n` is odd, $`\ell=n-1`, and $`m=0`.
:::
