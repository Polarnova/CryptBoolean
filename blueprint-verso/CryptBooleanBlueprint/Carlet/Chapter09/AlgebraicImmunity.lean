/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter09.GeneralProperties
import CryptBoolean.Carlet.Chapter09.NormalitySeparation
import CryptBoolean.Carlet.Chapter09.TracePowerRunBound

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic immunity" =>

:::theorem "carlet-9-trace-power-run-bound" (parent := "carlet-chapter-9") (lean := "CryptBoolean.binaryWeight_ofBits, CryptBoolean.binaryWeight_two_pow_sub_one, CryptBoolean.ofBits_eq_sum, CryptBoolean.rotateBinaryExponent, CryptBoolean.testBit_rotateBinaryExponent, CryptBoolean.binaryCyclicExponent, CryptBoolean.binaryCyclicExponent_lt, CryptBoolean.binaryCyclicExponent_succ_eq_rotate, CryptBoolean.binaryWeight_binaryCyclicExponent, CryptBoolean.binaryCyclicExponent_pos, CryptBoolean.pow_binaryCyclicExponent, CryptBoolean.functionAlgebraicDegree_traceMonomial_le_binaryWeight, CryptBoolean.tracePowerFunction, CryptBoolean.cyclicOneRunCount, CryptBoolean.cyclicOneRunCount_binaryCyclicExponent, CryptBoolean.cyclicOneRunCount_pos, CryptBoolean.traceRunMultiplierPositions, CryptBoolean.traceRunMultiplierExponent, CryptBoolean.bitIndices_traceRunMultiplierExponent, CryptBoolean.testBit_traceRunMultiplierExponent, CryptBoolean.traceRunMultiplierExponent_lt_two_pow, CryptBoolean.binaryWeight_traceRunMultiplierExponent, CryptBoolean.positiveCyclicSum, CryptBoolean.pow_positiveCyclicSum, CryptBoolean.binaryWeight_positiveCyclicSum_traceRunMultiplier_le, CryptBoolean.binaryWeight_traceRunMultiplier_add_binaryCyclicExponent_le, CryptBoolean.algebraicImmunity_tracePowerFunction_le_runBound") (uses := "carlet-2-trace-monomial-degree, carlet-2-univariate-binary-degree, carlet-4-def-annihilator-algebraic-immunity") (tags := "carlet, chapter-9, algebraic-immunity, trace-monomial, cyclic-runs, reference-282, page-134, fidelity-exact")
*Algebraic immunity of trace monomials (Carlet, p. 134).* Let $`n>0`, let
$`K=\operatorname{GF}(2^n)`, and let $`d` be represented modulo $`2^n-1`
by an $`n`-bit word. Let $`r(d)` be the number of cyclic maximal nonempty
blocks of consecutive ones in this word. For $`a\in K`, define
$$`
f(x)=\operatorname{Tr}_n(ax^d).
`
If $`r(d)<\sqrt n/2`, then
$$`
\operatorname{AI}(f)\le
r(d)\lfloor\sqrt n\rfloor+
\left\lceil\frac{n}{\lfloor\sqrt n\rfloor}\right\rceil-1.
`
:::

:::theorem "carlet-9-prop-38" (parent := "carlet-chapter-9") (lean := "CryptBoolean.algebraicImmunity_eq_ceiling_half_of_odd_balanced_of_no_annihilator") (uses := "carlet-3-reed-muller-code, carlet-3-reed-muller-dimension, carlet-3-theorem-2, carlet-4-annihilator-linear-system, carlet-4-ai-upper-bound") (tags := "carlet, chapter-9, proposition-38, algebraic-immunity, balancedness, page-134, page-135, fidelity-exact")
*Proposition 38 (Carlet, pp. 134--135).* Let $`n` be odd and let
$`f:V_n\to\mathbb F_2` be balanced. If $`f` has no nonzero annihilator of
algebraic degree at most $`(n-1)/2`, then
$$`
\operatorname{AI}(f)=\frac{n+1}{2}.
`
:::

:::theorem "carlet-9-normality-ai-bound" (parent := "carlet-chapter-9") (lean := "CryptBoolean.algebraicImmunity_le_sub_of_isKNormal") (uses := "carlet-5-def-4-normality, carlet-3-prop-12, carlet-4-def-annihilator-algebraic-immunity") (tags := "carlet, chapter-9, algebraic-immunity, normality, page-135, fidelity-exact")
*Normality and algebraic immunity (Carlet, p. 135).* If
$`f:V_n\to\mathbb F_2` is $`k`-normal, then
$$`
\operatorname{AI}(f)\le n-k.
`
More precisely, if $`f` is constantly $`\varepsilon` on a $`k`-dimensional
affine flat $`A`, then the indicator of $`A` is a nonzero annihilator of
$`f+\varepsilon` and has algebraic degree $`n-k`.
:::

:::theorem "carlet-9-ai-does-not-force-normality" (parent := "carlet-chapter-9") (lean := "CryptBoolean.tendsto_carletNonnormalityDimension_div, CryptBoolean.eventually_ceilingHalf_le_sub_carletNonnormalityDimension, CryptBoolean.eventually_exists_algebraicImmunity_le_sub_not_isKNormal") (uses := "carlet-9-normality-ai-bound, carlet-5-random-nonnormality, carlet-4-ai-upper-bound") (tags := "carlet, chapter-9, algebraic-immunity, normality, asymptotic, page-135, fidelity-explicit-eventual-form")
*Algebraic-immunity bounds do not force normality (Carlet, p. 135).* Let
$`a>1`. As $`n` tends to infinity, the uniform probability that an
$`n`-variable Boolean function is not $`\lfloor a\log_2 n\rfloor`-normal
tends to one, while every such function satisfies
$`\operatorname{AI}(f)\le\lceil n/2\rceil`. Consequently, for all
sufficiently large $`n` there exists $`f` such that
$$`
\operatorname{AI}(f)\le n-\lfloor a\log_2 n\rfloor
`
but $`f` is not $`\lfloor a\log_2 n\rfloor`-normal.
:::

:::theorem "carlet-9-ai-weight-bounds" (parent := "carlet-chapter-9") (lean := "CryptBoolean.algebraicImmunity_add_constant_one, CryptBoolean.sum_choose_below_algebraicImmunity_le_hammingWeight, CryptBoolean.hammingWeight_le_sum_choose_to_sub_algebraicImmunity") (uses := "carlet-4-def-annihilator-algebraic-immunity, carlet-4-annihilator-linear-system, carlet-2-def-support-weight, carlet-5-quadratic-weight-nonlinearity-values") (tags := "carlet, chapter-9, algebraic-immunity, hamming-weight, page-135, page-136, fidelity-exact")
*Weight bounds from algebraic immunity (Carlet, pp. 135--136).* Let
$`k=\operatorname{AI}(f)`. Then
$$`
\sum_{i=0}^{k-1}\binom ni
\le w_H(f)\le
\sum_{i=0}^{n-k}\binom ni.
`
The lower sum is zero when $`k=0`.
:::

:::theorem "carlet-9-optimal-odd-ai-balanced" (parent := "carlet-chapter-9") (lean := "CryptBoolean.isBalanced_of_odd_of_algebraicImmunity_eq_ceiling_half") (uses := "carlet-9-ai-weight-bounds, carlet-2-def-support-weight") (tags := "carlet, chapter-9, algebraic-immunity, balancedness, odd-dimension, page-136, fidelity-exact")
*Optimal algebraic immunity in odd dimension (Carlet, p. 136).* Let $`n` be
odd. If
$$`
\operatorname{AI}(f)=\frac{n+1}{2},
`
then $`f` is balanced, equivalently $`w_H(f)=2^{n-1}`.
:::

:::theorem "carlet-9-ai-addition-stability" (parent := "carlet-chapter-9") (lean := "CryptBoolean.algebraicImmunity_add_le_add_functionAlgebraicDegree, CryptBoolean.algebraicImmunity_sub_functionAlgebraicDegree_le_add") (uses := "carlet-4-def-annihilator-algebraic-immunity, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-9, algebraic-immunity, low-degree-perturbation, page-136, fidelity-exact-total-natural-form")
*Stability under low-degree perturbations (Carlet, p. 136).* Let
$`f,h:V_n\to\mathbb F_2` and suppose $`\deg(h)\le r`. Then
$$`
\operatorname{AI}(f)\le\operatorname{AI}(f+h)+r
\quad\text{and}\quad
\operatorname{AI}(f+h)\le\operatorname{AI}(f)+r.
`
:::
