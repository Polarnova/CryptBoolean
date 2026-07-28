/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.DualAffine
import CryptBoolean.Carlet.Chapter06.DualCoefficientDivisibility
import CryptBoolean.Carlet.Chapter06.DualNNF
import CryptBoolean.Carlet.Chapter06.DualPoisson

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The dual" =>

:::definition "carlet-6-dual" (parent := "carlet-chapter-6") (lean := "CryptBoolean.bentDual, CryptBoolean.walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual, CryptBoolean.realSignView_bentDual, CryptBoolean.isBent_bentDual, CryptBoolean.walshTransform_bentDual, CryptBoolean.bentDual_bentDual") (uses := "carlet-6-def-7-bent, carlet-2-def-walsh-transform, carlet-2-fourier-inversion") (tags := "carlet, chapter-6, duality, section-6-1, page-79, fidelity-exact")
*Bent dual (Carlet, Section 6.1, p. 79).* Let $`n` be even and let
$`f:V_n\to\mathbb F_2` be bent. Its dual is the unique Boolean function
$`\widetilde f:V_n\to\mathbb F_2` satisfying
$$`
W_f(u)=2^{n/2}(-1)^{\widetilde f(u)}
\qquad(u\in V_n).
`
The function $`\widetilde f` is bent and satisfies
$$`
W_{\widetilde f}(a)=2^{n/2}(-1)^{f(a)},
\qquad
\widetilde{\widetilde f}=f.
`
:::

:::theorem "carlet-6-rel-44-dual-isometry" (parent := "carlet-chapter-6") (lean := "CryptBoolean.walshTransform_zero_bentDual_add, CryptBoolean.hammingDistance_bentDual") (uses := "carlet-6-dual, carlet-2-rel-22-plancherel, carlet-2-def-hamming-distance") (tags := "carlet, chapter-6, duality, relation-44, page-79, fidelity-exact")
*Relation (44) (Carlet, p. 79).* If $`f,g:V_n\to\mathbb F_2` are bent,
then
$$`
W_{\widetilde f+\widetilde g}(0)=W_{f+g}(0).
`
Consequently,
$$`
d_H(\widetilde f,\widetilde g)=d_H(f,g),
`
so duality preserves pairwise Hamming distance on bent functions.
:::

:::theorem "carlet-6-rel-45-dual-derivatives" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_domainTranslate, CryptBoolean.isBent_domainTranslate_add_linear, CryptBoolean.bentDual_domainTranslate_add_linear, CryptBoolean.walshTransform_zero_bentDual_derivative_add_linear") (uses := "carlet-6-dual, carlet-6-rel-44-dual-isometry, carlet-2-prop-6-fourier-shifts, carlet-2-def-2-derivative") (tags := "carlet, chapter-6, duality, relation-45, pages-79-80, fidelity-exact")
*Relation (45) (Carlet, pp. 79--80).* Let $`f:V_n\to\mathbb F_2` be bent
and let $`a,b\in V_n`. The function
$$`
g(x)=f(x+b)+a\mathbin\cdot x
`
is bent, and its dual is
$$`
\widetilde g(x)=\widetilde f(x+a)+b\mathbin\cdot(x+a).
`
Writing $`\ell_c(x)=c\mathbin\cdot x`, one has
$$`
W_{D_a\widetilde f+\ell_b}(0)
=W_{D_bf+\ell_a}(0).
`
:::

:::theorem "carlet-6-dual-nnf" (parent := "carlet-chapter-6") (lean := "CryptBoolean.booleanRealEmbedding_bentDual_eq_rawFourierTransform, CryptBoolean.booleanRealEmbedding_bentDual_eq_numericalCoeff_sum") (uses := "carlet-6-dual, carlet-2-nnf-existence-uniqueness, carlet-2-rel-30-nnf-fourier") (tags := "carlet, chapter-6, duality, numerical-normal-form, pages-79-80, fidelity-exact")
*Numerical normal form of the dual (Carlet, pp. 79--80).* Let
$`f:V_n\to\mathbb F_2` be bent, and write its numerical normal form as
$$`
f(x)=\sum_{S\subseteq[n]}\lambda_Sx^S.
`
If $`\delta_0(x)` is one at $`x=0` and zero elsewhere, then
$$`
\widetilde f(x)
=\frac12-\frac{2^{n/2}}2\,\delta_0(x)
+\frac{(-1)^{w_H(x)}}{2^{n/2}}
  \sum_{\operatorname{supp}(x)\subseteq S}
    2^{n-|S|}\lambda_S.
`
This identity determines the numerical normal form of $`\widetilde f`.
:::

:::proposition "carlet-6-prop-17-dual-nnf-divisibility" (parent := "carlet-chapter-6") (lean := "CryptBoolean.bentDual_and_self_nnfCoefficient_divisibility") (uses := "carlet-6-dual-nnf, carlet-6-lemma-2-walsh-congruence, carlet-2-prop-5-nnf-integrality") (tags := "carlet, chapter-6, duality, numerical-normal-form, proposition-17, page-80, fidelity-exact")
*Proposition 17 (Carlet, p. 80).* Let $`f:V_n\to\mathbb F_2` be bent,
where $`n` is even, and let $`\lambda_I` and $`\widetilde\lambda_I` be the
integer numerical-normal-form coefficients of $`f` and $`\widetilde f`.
For every proper subset $`I\subsetneq[n]` with $`|I|>n/2`,
$$`
2^{|I|-n/2}\mid\lambda_I,
\qquad
2^{|I|-n/2}\mid\widetilde\lambda_I.
`
:::

:::corollary "carlet-6-half-degree-anf-complement" (parent := "carlet-chapter-6") (lean := "CryptBoolean.anfCoeff_bentDual_eq_complement_of_card_eq_half, CryptBoolean.anfCoeff_eq_bentDual_complement_of_card_eq_half") (uses := "carlet-6-prop-17-dual-nnf-divisibility, carlet-6-dual-nnf, carlet-2-anf-existence-uniqueness") (tags := "carlet, chapter-6, duality, algebraic-normal-form, page-81, fidelity-exact-with-dual-symmetry")
*Complementary half-degree ANF coefficients (Carlet, p. 81).* Let $`n\ge4`,
let $`f:V_n\to\mathbb F_2` be bent, and let $`c_{f,I}` denote the coefficient
of $`x^I` in the ANF of $`f`. For every $`I\subseteq[n]` with $`|I|=n/2`,
$$`
c_{\widetilde f,I}=c_{f,[n]\setminus I},
\qquad
c_{f,I}=c_{\widetilde f,[n]\setminus I}.
`
:::

:::theorem "carlet-6-rel-46-dual-poisson" (parent := "carlet-chapter-6") (lean := "CryptBoolean.bentDual_poissonSummationFormula") (uses := "carlet-6-dual, carlet-2-cor-1-poisson-summation") (tags := "carlet, chapter-6, duality, poisson-summation, relation-46, page-81, fidelity-exact")
*Relation (46) (Carlet, p. 81).* Let $`f:V_n\to\mathbb F_2` be bent, let
$`E\le V_n`, and let $`a,b\in V_n`. Then
$$`
\sum_{x\in a+E}(-1)^{\widetilde f(x)+b\mathbin\cdot x}
=2^{-n/2}|E|(-1)^{a\mathbin\cdot b}
 \sum_{x\in b+E^\perp}(-1)^{f(x)+a\mathbin\cdot x}.
`
:::
