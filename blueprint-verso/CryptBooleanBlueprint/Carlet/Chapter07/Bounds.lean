/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.EntropyNonlinearity
import CryptBoolean.Carlet.Chapter07.NonlinearityBounds
import CryptBoolean.Carlet.Chapter07.SarkarMaitra
import CryptBoolean.Carlet.Chapter07.SiegenthalerWeight

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Degree, divisibility, and nonlinearity" =>

:::theorem "carlet-7-siegenthaler-degree-bounds" (parent := "carlet-chapter-7") (lean := "CryptBoolean.booleanFunctionF₂Encoding_signCubeView, CryptBoolean.functionAlgebraicDegree_le_sub_sub_one_of_isResilient, CryptBoolean.functionAlgebraicDegree_le_sub_of_isCorrelationImmune, CryptBoolean.functionAlgebraicDegree_le_one_of_isResilient_natPred, CryptBoolean.exists_affineFunction_of_isResilient_natPred, CryptBoolean.functionAlgebraicDegree_le_sub_sub_one_of_isCorrelationImmune_of_weight") (uses := "carlet-4-def-resiliency-correlation-immunity, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-7, algebraic-degree, siegenthaler, page-111, fidelity-exact-endpoints")
*Siegenthaler's inequalities (Carlet, p. 111).* Let
$`f:V_n\to\mathbb F_2`. If $`0\le m<n-1` and $`f` is
$`m`-resilient, then
$$`
\deg_{\mathrm{alg}}(f)\le n-m-1.
`
Every $`(n-1)`-resilient function is affine. More generally, if $`f` is
correlation immune of order $`m<n`, then
$$`
\deg_{\mathrm{alg}}(f)\le n-m.
`
If additionally $`2^{m+1}` divides $`w_H(f)`, then the sharper bound
$`\deg_{\mathrm{alg}}(f)\le n-m-1` holds.
:::

:::proposition "carlet-7-prop-32-nnf-characterization" (parent := "carlet-chapter-7") (lean := "CryptBoolean.functionNumericalDegree_booleanRealEmbedding_eq_fourierDegree_signCubeView, CryptBoolean.functionNumericalDegree_booleanRealEmbedding_le_iff_walshTransform, CryptBoolean.proposition_32_resilient_iff_functionNumericalDegree_le") (uses := "carlet-4-theorem-3, carlet-2-rel-30-nnf-fourier, carlet-2-nnf-existence-uniqueness") (tags := "carlet, chapter-7, proposition-32, numerical-normal-form, pages-111-112, fidelity-exact")
*Proposition 32 (Carlet, pp. 111--112).* Let $`n>0`, let $`m<n`, and let
$`f:V_n\to\mathbb F_2`. Define
$$`
g(x)=f(x)\oplus x_1\oplus\cdots\oplus x_n.
`
Then $`f` is $`m`-resilient if and only if the numerical normal form of
$`g` has degree at most $`n-m-1`.
:::

:::theorem "carlet-7-walsh-weight-divisibility" (parent := "carlet-chapter-7") (lean := "CryptBoolean.bitSignInt_cast_eq_realSignView, CryptBoolean.sum_walshTransform_submodule_eq, CryptBoolean.two_pow_m_add_two_dvd_walshTransform_of_isResilient, CryptBoolean.two_pow_m_add_one_dvd_walshTransform_of_isCorrelationImmune, CryptBoolean.two_pow_m_dvd_hammingWeight_of_isCorrelationImmune, CryptBoolean.two_pow_m_add_two_dvd_walshTransform_of_isCorrelationImmune_of_weight") (uses := "carlet-7-prop-32-nnf-characterization, carlet-2-rel-30-nnf-fourier, carlet-2-def-support-weight, carlet-2-def-walsh-transform") (tags := "carlet, chapter-7, walsh-divisibility, weight-divisibility, page-112, fidelity-exact")
*Walsh and weight divisibility (Carlet, p. 112).* Let $`0\le m\le n-2`.
If $`f:V_n\to\mathbb F_2` is $`m`-resilient, then
$$`
2^{m+2}\mid W_f(a)\qquad(a\in V_n).
`
If $`f` is correlation immune of order $`m`, then
$`2^{m+1}\mid W_f(a)` for every $`a` and $`2^m\mid w_H(f)`. If moreover
$`2^{m+1}\mid w_H(f)`, then $`2^{m+2}\mid W_f(a)` for every $`a`.
:::

:::theorem "carlet-7-sarkar-maitra-nonlinearity-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.two_mul_nonlinearity_add_two_pow_m_add_two_le_of_isResilient, CryptBoolean.nonlinearity_add_two_pow_m_add_one_le_two_pow_sub_one_of_isResilient, CryptBoolean.nonlinearity_le_two_pow_sub_two_pow_of_isResilient, CryptBoolean.nonlinearity_eq_sarkarMaitra_bound_iff_hasPlateauedWalshAmplitude, CryptBoolean.walshTransform_eq_zero_or_eq_neg_two_pow_or_eq_two_pow_of_sarkarMaitra_equality, CryptBoolean.isPlateaued_of_sarkarMaitra_equality") (uses := "carlet-7-walsh-weight-divisibility, carlet-2-parseval, carlet-4-rel-35-nonlinearity-walsh, carlet-6-def-plateaued") (tags := "carlet, chapter-7, sarkar-maitra, nonlinearity, plateaued, pages-112-113, fidelity-exact")
*Sarkar--Maitra bound (Carlet, pp. 112--113).* Let
$`f:V_n\to\mathbb F_2` be $`m`-resilient, where $`m\le n-2`. Then
$$`
\operatorname{nl}(f)\le 2^{n-1}-2^{m+1}.
`
Equality holds if and only if $`f` is plateaued with nonzero Walsh
magnitude $`2^{m+2}`; equivalently,
$$`
W_f(a)\in\{0,-2^{m+2},2^{m+2}\}\qquad(a\in V_n).
`
:::

:::theorem "carlet-7-theorem-13-degree-divisibility" (parent := "carlet-chapter-7") (lean := "CryptBoolean.two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isResilient, CryptBoolean.two_pow_m_add_one_add_degree_quotient_dvd_nonlinearity_of_isResilient") (uses := "carlet-7-walsh-weight-divisibility, carlet-2-cor-1-poisson-summation, carlet-6-prop-19, carlet-4-theorem-3") (tags := "carlet, chapter-7, theorem-13, divisibility, algebraic-degree, page-113, fidelity-exact")
*Theorem 13 (Carlet, p. 113).* Let $`f:V_n\to\mathbb F_2` be
$`m`-resilient, let $`m\le n-2`, and put
$`d=\deg_{\mathrm{alg}}(f)>0`. Every Walsh coefficient of $`f` is divisible
by
$$`
2^{\,m+2+\lfloor(n-m-2)/d\rfloor}.
`
Consequently, $`\operatorname{nl}(f)` is divisible by
$$`
2^{\,m+1+\lfloor(n-m-2)/d\rfloor}.
`
:::

:::theorem "carlet-7-correlation-immune-degree-divisibility" (parent := "carlet-chapter-7") (lean := "CryptBoolean.two_pow_m_add_one_add_degree_quotient_dvd_walshTransform_of_isCorrelationImmune, CryptBoolean.two_pow_m_add_two_add_degree_quotient_dvd_walshTransform_of_isCorrelationImmune_of_weight") (uses := "carlet-6-prop-19, carlet-2-cor-1-poisson-summation, carlet-4-theorem-3, carlet-2-def-support-weight") (tags := "carlet, chapter-7, correlation-immunity, divisibility, algebraic-degree, page-113, fidelity-exact-endpoints")
*Correlation-immune divisibility (Carlet, p. 113).* Let $`f` be correlation
immune of order $`m`, where $`m\le n-1`, and put
$`d=\deg_{\mathrm{alg}}(f)>0`. Then
$$`
2^{\,m+1+\lfloor(n-m-1)/d\rfloor}\mid W_f(a)
\qquad(a\in V_n).
`
If $`m\le n-2` and
$$`
2^{\,m+1+\lfloor(n-m-2)/d\rfloor}\mid w_H(f),
`
then every $`W_f(a)` is divisible by
$`2^{\,m+2+\lfloor(n-m-2)/d\rfloor}`.
:::

:::theorem "carlet-7-degree-sensitive-nonlinearity-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.nonlinearity_le_two_pow_sub_two_pow_degree_quotient_of_isResilient, CryptBoolean.functionAlgebraicDegree_eq_sub_sub_one_of_sarkarMaitra_equality") (uses := "carlet-7-theorem-13-degree-divisibility, carlet-7-siegenthaler-degree-bounds, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, nonlinearity, algebraic-degree, page-114, fidelity-exact")
*Degree-sensitive nonlinearity bound (Carlet, p. 114).* Let $`f` be
$`m`-resilient, let $`m\le n-2`, and put
$`d=\deg_{\mathrm{alg}}(f)>0`. Then
$$`
\operatorname{nl}(f)
\le 2^{n-1}-2^{\,m+1+\lfloor(n-m-2)/d\rfloor}.
`
In particular, equality in the Sarkar--Maitra bound is possible only when
$`d=n-m-1`.
:::

:::theorem "carlet-7-even-dimension-nonlinearity-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.nonlinearity_le_even_dimension_resilient_bound") (uses := "carlet-7-walsh-weight-divisibility, carlet-4-rel-36-covering-radius-bent, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-7, nonlinearity, even-dimension, page-114, fidelity-exact")
*Even-dimensional bound (Carlet, p. 114).* Let $`n>0` be even, let
$`m\le n/2-2`, and let $`f:V_n\to\mathbb F_2` be $`m`-resilient. Then
$$`
\operatorname{nl}(f)
\le 2^{n-1}-2^{n/2-1}-2^{m+1}.
`
:::

:::theorem "carlet-7-rel-57-parseval-nonlinearity-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.nonlinearity_le_parseval_resilient_bound") (uses := "carlet-7-walsh-weight-divisibility, carlet-4-theorem-3, carlet-2-parseval, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-7, relation-57, nonlinearity, parseval, pages-114-115, fidelity-exact")
*Relation (57) (Carlet, pp. 114--115).* Let $`f` be $`m`-resilient,
where $`m\le n-2`. Then
$$`
\operatorname{nl}(f)\le
2^{n-1}-2^{m+1}
\left\lceil
\frac{2^{n-m-2}}
{\sqrt{\,2^n-\sum_{i=0}^{m}\binom ni\,}}
\right\rceil.
`
:::

:::theorem "carlet-7-rel-58-entropy-nonlinearity-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.binaryEntropyBaseTwo, CryptBoolean.entropyPower_div_sqrt_le_choose, CryptBoolean.nonlinearity_le_entropy_resilient_bound") (uses := "carlet-7-rel-57-parseval-nonlinearity-bound") (tags := "carlet, chapter-7, relation-58, nonlinearity, entropy, page-115, fidelity-explicit-positive-order-domain")
*Relation (58) (Carlet, p. 115).* Let $`f` be $`m`-resilient, where
$`1\le m\le n/2`, and define
$$`
H_2(x)=-x\log_2x-(1-x)\log_2(1-x).
`
Then
$$`
\operatorname{nl}(f)\le
2^{n-1}-2^{m+1}
\left\lceil
\frac{2^{n-m-2}}
{\sqrt{\,2^n-
  2^{nH_2(m/n)}/\sqrt{8m(1-m/n)}\,}}
\right\rceil.
`
:::
