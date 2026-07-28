/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.PartialBent
import CryptBoolean.Carlet.Chapter06.PartialBentCounterexamples
import CryptBoolean.Carlet.Chapter06.PartialBentDual
import CryptBoolean.Carlet.Chapter06.PartiallyBent
import CryptBoolean.Carlet.Chapter06.PlateauedOrphan
import CryptBoolean.Carlet.Chapter06.PlateauedSecondOrder
import CryptBoolean.Carlet.Chapter06.PlateauedSupport

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Superclasses of bent functions" =>

:::proposition "carlet-6-prop-26-partially-bent" (parent := "carlet-chapter-6") (lean := "CryptBoolean.autocorrelationSupport, CryptBoolean.mem_autocorrelationSupport, CryptBoolean.nonzeroAutocorrelationCount, CryptBoolean.rawFourierSupport_autocorrelation, CryptBoolean.two_pow_le_nonzeroAutocorrelationCount_mul_card_walshSupport, CryptBoolean.IsPartiallyBent, CryptBoolean.isPartiallyBent_of_functionAlgebraicDegree_le_two, CryptBoolean.HasBentAffineComplementDecomposition, CryptBoolean.HasBentAffineComplementDecomposition.isPartiallyBent, CryptBoolean.HasBentAffineComplementDecomposition.linearKernel_eq_affineSubspace, CryptBoolean.HasBentAffineComplementDecomposition.dimensions_add, CryptBoolean.HasBentAffineComplementDecomposition.even_bentDimension, CryptBoolean.exists_hasBentAffineComplementDecomposition_of_isPartiallyBent, CryptBoolean.isPartiallyBent_iff_exists_bentAffineComplementDecomposition, CryptBoolean.isLinearStructure_iff_abs_autocorrelation_eq_two_pow, CryptBoolean.isPartiallyBent_of_nonzeroAutocorrelationCount_mul_card_walshSupport_eq, CryptBoolean.nonzeroAutocorrelationCount_mul_card_walshSupport_eq_of_isPartiallyBent, CryptBoolean.nonzeroAutocorrelationCount_mul_card_walshSupport_eq_two_pow_iff, CryptBoolean.HasBentAffineComplementDecomposition.nonzeroAutocorrelationCount_eq, CryptBoolean.hasPlateauedWalshSpectrum_of_isPartiallyBent, CryptBoolean.IsPartiallyBent.isPlateaued, CryptBoolean.isPlateaued_of_functionAlgebraicDegree_le_two, CryptBoolean.HasBentAffineComplementDecomposition.hasPlateauedWalshAmplitude") (uses := "carlet-2-rel-25-wiener-khinchin, carlet-2-parseval, carlet-4-def-linear-kernel, carlet-6-def-plateaued") (tags := "carlet, chapter-6, proposition-26, relation-53, pages-103-104, fidelity-exact")
*Proposition 26 (Carlet, Relation (53), pp. 103--104).* For a Boolean
function $`f:V_n\to\mathbb F_2`, let
$$`
N_{\Delta_f}=|\{b:\Delta_f(b)\ne0\}|,
\qquad
N_{W_f}=|\{u:W_f(u)\ne0\}|.
`
Then $`N_{\Delta_f}N_{W_f}\ge2^n`. Equality holds if and only if every
derivative $`D_bf` is balanced or constant. Equivalently, there are
complementary subspaces $`E,E'` and functions $`g,h`, with $`g` bent on
$`E` and $`h` affine on $`E'`, such that
$$`
f(x+y)=g(x)+h(y)
\qquad(x\in E,\ y\in E').
`
Such functions are called partially bent. Every quadratic function is
partially bent, and every partially bent function is plateaued.
:::

:::proposition "carlet-6-prop-27-fourier-uncertainty" (parent := "carlet-chapter-6") (lean := "CryptBoolean.pseudoBooleanSupport, CryptBoolean.mem_pseudoBooleanSupport, CryptBoolean.two_pow_le_card_pseudoBooleanSupport_mul_card_rawFourierSupport, CryptBoolean.IsModulatedAffineFlatIndicator, CryptBoolean.IsModulatedAffineFlatIndicator.card_support_mul_card_rawFourierSupport_eq, CryptBoolean.isModulatedAffineFlatIndicator_of_card_support_mul_card_rawFourierSupport_eq, CryptBoolean.card_support_mul_card_rawFourierSupport_eq_two_pow_iff") (uses := "carlet-2-pseudoboolean-fourier, carlet-2-parseval, carlet-2-cor-1-poisson-summation") (tags := "carlet, chapter-6, proposition-27, pages-104-105, fidelity-exact-nonzero-modulation")
*Proposition 27 (Carlet, pp. 104--105).* Let
$`\varphi:V_n\to\mathbb R` be nonzero, and write
$$`
N_\varphi=|\{x:\varphi(x)\ne0\}|,
\qquad
N_{\widehat\varphi}=|\{u:\widehat\varphi(u)\ne0\}|.
`
Then $`N_\varphi N_{\widehat\varphi}\ge2^n`. Equality holds if and only if
there are a nonzero real number $`\lambda`, a frequency $`u`, and an affine
flat $`F` such that
$$`
\varphi(x)=
\begin{cases}
\lambda(-1)^{u\mathbin\cdot x},&x\in F,\\
0,&x\notin F.
\end{cases}
`
:::

:::definition "carlet-6-def-partial-bent" (parent := "carlet-chapter-6") (lean := "CryptBoolean.HasPartialBentFourierLevels, CryptBoolean.IsPartialBent, CryptBoolean.partialBentIntegerFourier, CryptBoolean.partialBentIntegerFourier_cast") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-6, partial-bent, page-105, fidelity-exact")
*Partial bent functions (Carlet, p. 105).* Let $`n` be even. A Boolean
function $`f:V_n\to\mathbb F_2` is partial bent if there is an integer
$`\lambda` such that, on $`V_n\setminus\{0\}`, its raw Fourier transform as
a $`\{0,1\}`-valued function takes exactly the two values $`\lambda` and
$`\lambda+2^{n/2}`.
:::

:::theorem "carlet-6-partial-bent-duality" (parent := "carlet-chapter-6") (lean := "CryptBoolean.partialBentDual, CryptBoolean.partialBentDual_zero, CryptBoolean.exists_partialBentDual_fourierLevels, CryptBoolean.partialBentDual_involution, CryptBoolean.exists_isPartialBent_partialBentDual_and_involution") (uses := "carlet-6-def-partial-bent, carlet-2-cor-2-fourier-involution") (tags := "carlet, chapter-6, partial-bent, duality, page-105, fidelity-formal-zero-frequency-convention")
*Duality for partial bent functions (Carlet, p. 105).* Let $`f` be partial
bent with Fourier levels $`\lambda` and $`\lambda+2^{n/2}`. Define its dual
at zero by $`\widetilde f(0)=f(0)` and, for every nonzero $`u`, by
$$`
\widetilde f(u)=
\begin{cases}
0,&\widehat f(u)=\lambda,\\
1,&\widehat f(u)=\lambda+2^{n/2}.
\end{cases}
`
Then $`\widetilde f` is partial bent and $`\widetilde{\widetilde f}=f`.
:::

:::theorem "carlet-6-partial-bent-degree-bound" (parent := "carlet-chapter-6") (lean := "CryptBoolean.partialBentDegreeCounterexample, CryptBoolean.partialBentDegreeCounterexample_refutes_bound") (uses := "carlet-6-def-partial-bent, carlet-6-prop-18-rothaus-degree-bound") (tags := "carlet, chapter-6, partial-bent, algebraic-degree, rothaus-bound, counterexample, page-105, fidelity-source-error-exact-two-level-counterexample")
*Counterexample to the printed partial-bent degree bound (Carlet, p. 105).*
On $`V_2`, let $`f` be the indicator of the point $`(1,0)`. Then $`f` is
partial bent, but
$$`
\deg_{\mathrm{alg}}(f)=2>2/2.
`
Thus the printed half-dimension bound requires additional regularity
hypotheses beyond the exact punctured two-level definition.
:::

:::theorem "carlet-6-partial-bent-types" (parent := "carlet-chapter-6") (lean := "CryptBoolean.partialBent_fourier_level_types") (uses := "carlet-6-def-partial-bent, carlet-2-parseval") (tags := "carlet, chapter-6, partial-bent, types, parseval, page-105, fidelity-source-correction-type-formula")
*The two types of partial bent functions (Carlet, p. 105; corrected).* Let
$`n>0` be even, put $`q=2^{n/2}` and $`e=f(0)`, and let $`f` be partial
bent with Fourier levels $`\lambda` and $`\lambda+q`. Exactly one of the
two identities
$$`
\widehat f(0)-e=-(\lambda-e)(q-1)
`
and
$$`
\widehat f(0)-e=(q+\lambda-e)(q+1)
`
holds; these alternatives define the two types.
:::

:::theorem "carlet-6-partial-bent-disjoint-support-sum" (parent := "carlet-chapter-6") (lean := "CryptBoolean.partialBentSumCounterexampleCompanion, CryptBoolean.partialBentCounterexamples_refute_disjoint_support_sum") (uses := "carlet-6-def-partial-bent, carlet-6-partial-bent-types, carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-6, partial-bent, sum, supports, counterexample, page-105, fidelity-source-error-exact-two-level-counterexample")
*Counterexample to the printed partial-bent sum assertion (Carlet, p. 105).*
On $`V_2`, let $`f` be the indicator of $`\{(1,0)\}` and let $`g(x)=x_2`,
the indicator of $`\{(0,1),(1,1)\}`. Their punctured Fourier levels are
$`\{-1,1\}` and $`\{-2,0\}`, respectively. Both functions are partial bent
of the corrected first type, and
$$`
\operatorname{supp}(f)\cap\operatorname{supp}(g)\subseteq\{0\}.
`
Nevertheless, $`f+g` is not partial bent. Hence the printed closure assertion
also requires an additional regularity convention.
:::

:::definition "carlet-6-def-plateaued" (parent := "carlet-chapter-6") (lean := "CryptBoolean.HasPlateauedWalshAmplitude, CryptBoolean.IsPlateaued, CryptBoolean.isPlateaued_iff_hasPlateauedWalshSpectrum, CryptBoolean.isBent_iff_isPlateaued_and_forall_walshTransform_ne_zero, CryptBoolean.card_walshSupport_mul_amplitude_sq_eq_two_pow_two_mul, CryptBoolean.exists_plateauedAmplitudeExponent, CryptBoolean.two_pow_add_one_div_two_dvd_walshTransform_of_hasPlateauedWalshAmplitude") (uses := "carlet-2-def-walsh-transform, carlet-2-parseval, carlet-6-def-7-bent") (tags := "carlet, chapter-6, plateaued, pages-105-106, fidelity-exact")
*Plateaued functions (Carlet, pp. 105--106).* A Boolean function is
plateaued with amplitude $`\lambda>0` when every Walsh coefficient belongs
to $`\{0,\lambda,-\lambda\}`. A plateaued function is bent exactly when
its Walsh transform has full support. Parseval's identity forces
$`\lambda=2^r` with $`2r\ge n`; consequently every Walsh coefficient is
divisible by $`2^{\lceil n/2\rceil}`.
:::

:::theorem "carlet-6-plateaued-support-nonlinearity" (parent := "carlet-chapter-6") (lean := "CryptBoolean.maxWalshMagnitude_eq_of_hasPlateauedWalshAmplitude, CryptBoolean.sum_walshTransform_sq_walshSupport, CryptBoolean.two_pow_sq_le_card_walshSupport_mul_maxWalshMagnitude_sq, CryptBoolean.two_pow_sq_eq_card_walshSupport_mul_maxWalshMagnitude_sq_iff_plateaued, CryptBoolean.nonlinearity_cast_le_walshSupport_bound, CryptBoolean.nonlinearity_cast_eq_walshSupport_bound_iff_plateaued") (uses := "carlet-6-def-plateaued, carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval") (tags := "carlet, chapter-6, plateaued, page-106, fidelity-exact")
*Walsh-support bound (Carlet, p. 106).* If $`N_{W_f}` is the cardinality
of the Walsh support of $`f:V_n\to\mathbb F_2`, then
$$`
\operatorname{nl}(f)
\le 2^{n-1}\left(1-\frac1{\sqrt{N_{W_f}}}\right).
`
Equality holds if and only if $`f` is plateaued.
:::

:::proposition "carlet-6-prop-28-second-order-plateaued" (parent := "carlet-chapter-6") (lean := "CryptBoolean.hasPlateauedWalshAmplitude_iff_forall_walshTransform_cube_eq, CryptBoolean.isPlateaued_iff_exists_forall_secondDerivativeDoubleSum_eq_sq") (uses := "carlet-6-def-plateaued, carlet-6-prop-24-second-order-characterization") (tags := "carlet, chapter-6, proposition-28, relation-55, page-106, fidelity-exact")
*Proposition 28 (Carlet, Relation (55), p. 106).* A Boolean function
$`f:V_n\to\mathbb F_2` is plateaued if and only if there is a positive
integer $`\lambda` such that, for every $`x\in V_n`,
$$`
\sum_{a,b\in V_n}(-1)^{D_aD_bf(x)}=\lambda^2.
`
The integer $`\lambda` is the Walsh amplitude.
:::

:::theorem "carlet-6-plateaued-coset-orphan" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsFirstOrderCosetLeader, CryptBoolean.FirstOrderCosetBelow, CryptBoolean.IsFirstOrderOrphan, CryptBoolean.IsPlateaued.add_affineFunction, CryptBoolean.eq_of_plateaued_cosetLeaders_of_support_subset, CryptBoolean.isFirstOrderOrphan_of_isPlateaued") (uses := "carlet-6-def-plateaued, carlet-6-plateaued-support-nonlinearity, carlet-3-reed-muller-code, carlet-4-def-nonlinearity, carlet-2-parseval") (tags := "carlet, chapter-6, plateaued, orphan, page-106, fidelity-source-correction-non-affine-hypothesis")
*Langevin's orphan theorem (Carlet, p. 106).* Order the cosets of
$`R(1,n)` as follows: $`g+R(1,n)` is below $`f+R(1,n)` when there are
minimum-weight representatives $`g_1` and $`f_1` of the respective cosets
such that $`\operatorname{supp}(g_1)\subseteq\operatorname{supp}(f_1)`.
A maximal coset for this order is called an orphan. If $`f` is plateaued and
$`f\notin R(1,n)`, then $`f+R(1,n)` is an orphan. The non-affine hypothesis
is necessary: affine functions are plateaued, while $`R(1,n)` is the least
coset in this order.
:::
