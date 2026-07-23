/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Citations
import CryptBoolean.Carlet.Chapter04.DegreeCount
import CryptBoolean.Carlet.Chapter04.Nonlinearity
import CryptBoolean.Carlet.Chapter04.RandomNonlinearityAsymptotics
import CryptBoolean.Carlet.Chapter04.RodierLowerTail
import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity
import CryptBoolean.Carlet.Chapter04.SevenVariableMaximumNonlinearity
import CryptBoolean.Carlet.Chapter04.FiveVariableMaximumNonlinearity
import CryptBoolean.Carlet.Chapter04.PropagationNonlinearity
import CryptBoolean.Carlet.Chapter04.DegreeRepairNonlinearity
import CryptBoolean.Carlet.Chapter04.ReedMullerCosetDistance
import CryptBoolean.Carlet.Chapter04.DerivativeNonlinearity
import CryptBoolean.Carlet.Chapter04.OddWeightingNonlinearity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Nonlinearity" =>

:::theorem "carlet-4-degree-count" (parent := "carlet-chapter-4") (lean := "CryptBoolean.sum_choose_le_n_sub_two, CryptBoolean.card_booleanFunctions_degree_le_n_sub_two, CryptBoolean.card_booleanFunctions_degree_le_n_sub_two_eq, CryptBoolean.natCard_booleanFunction, CryptBoolean.highAlgebraicDegreeProbability, CryptBoolean.highAlgebraicDegreeProbability_eq_card_ratio, CryptBoolean.tendsto_highAlgebraicDegreeProbability") (uses := "carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-4, algebraic-degree, page-49, fidelity-exact")
*High algebraic degree is typical (Carlet, p. 49).* For $`n\ge2`, the number
of functions $`f:V_n\to\mathbb F_2` with $`\deg_{\mathrm{alg}}(f)\le n-2` is
$$`
2^{\sum_{i=0}^{n-2}\binom ni}=2^{2^n-n-1}.
`
Consequently, the probability that a uniformly chosen $`n`-variable Boolean
function has degree at least $`n-1` tends to one as $`n\to\infty`.
:::

:::definition "carlet-4-def-nonlinearity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.nonlinearity") (uses := "carlet-2-def-hamming-distance, carlet-2-def-affine-functions") (tags := "carlet, chapter-4, nonlinearity, pages-49-51, fidelity-exact")
*Nonlinearity (Carlet, pp. 49--51).* For $`f:V_n\to\mathbb F_2`, define
$$`
\operatorname{nl}(f)
=\min_{a\in V_n,\ b\in\mathbb F_2}
d_H\bigl(f,x\mapsto a\mathbin\cdot x+b\bigr).
`
:::

:::theorem "carlet-4-nonlinearity-affine-invariance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hammingDistance_comp_affineEquiv, CryptBoolean.exists_affineFunction_comp_affineEquiv, CryptBoolean.nonlinearity_comp_affineEquiv_le, CryptBoolean.nonlinearity_comp_affineEquiv") (uses := "carlet-4-def-nonlinearity, carlet-2-affine-invariance") (tags := "carlet, chapter-4, nonlinearity, affine-invariance, page-50, fidelity-exact")
*Affine invariance of nonlinearity (Carlet, p. 50).* If
$`L:V_n\to V_n` is an affine automorphism, then every
$`f:V_n\to\mathbb F_2` satisfies
$$`
\operatorname{nl}(f\circ L)=\operatorname{nl}(f).
`
:::

:::theorem "carlet-4-rel-35-nonlinearity-walsh" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maxWalshMagnitude, CryptBoolean.hammingDistance_cast_affineFunction, CryptBoolean.bitSignInt_cast, CryptBoolean.hammingDistance_cast_affineFunction_eq, CryptBoolean.hammingDistance_cast_linearFunction_eq, CryptBoolean.hammingDistance_cast_complementLinearFunction_eq, CryptBoolean.nonlinearity_cast_eq_distanceToAffineSigns, CryptBoolean.maxWalshMagnitude_cast_eq_spectralInfinityNorm, CryptBoolean.two_mul_nonlinearity_add_maxWalshMagnitude, CryptBoolean.nonlinearity_cast_eq_relation_35") (uses := "carlet-4-def-nonlinearity, carlet-2-def-walsh-transform") (tags := "carlet, chapter-4, relation-35, page-51, fidelity-exact-with-division-free-form")
*Relation (35) (Carlet, p. 51).* For $`a\in V_n`, write
$`\ell_a(x)=a\mathbin\cdot x`. Then
$$`
d_H(f,\ell_a)=2^{n-1}-\frac12W_f(a),
\qquad
d_H(f,\ell_a+1)=2^{n-1}+\frac12W_f(a),
`
and hence
$$`
\operatorname{nl}(f)
=2^{n-1}-\frac12\max_{a\in V_n}|W_f(a)|.
`
:::

:::theorem "carlet-4-rel-36-covering-radius-bent" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_inv_sqrt_card_le_vectorFourierCoeff_abs, CryptBoolean.spectralInfinityNorm_ge_inv_sqrt_card, CryptBoolean.distanceToAffineSigns_le_coveringRadius, CryptBoolean.two_pow_mul_inv_sqrt, CryptBoolean.sqrt_two_pow_eq_rpow, CryptBoolean.coveringRadius_eq_relation_36, CryptBoolean.nonlinearity_cast_le_coveringRadius, CryptBoolean.nonlinearity_cast_le_relation_36, CryptBoolean.vectorFourierCoeff_abs_eq_inv_sqrt_of_spectralInfinityNorm_eq, CryptBoolean.spectralInfinityNorm_eq_inv_sqrt_of_forall_abs, CryptBoolean.distanceToAffineSigns_eq_coveringRadius_iff, CryptBoolean.HasFlatWalshSpectrum, CryptBoolean.hasFlatWalshSpectrum_iff_vectorFourierCoeff, CryptBoolean.nonlinearity_eq_coveringRadius_iff_flatWalshSpectrum, CryptBoolean.nonlinearity_cast_eq_relation_36_iff_flatWalshSpectrum, CryptBoolean.even_of_hasFlatWalshSpectrum, CryptBoolean.IsBent, CryptBoolean.sqrt_two_pow_eq_pow_half, CryptBoolean.even_of_isBent, CryptBoolean.hasFlatWalshSpectrum_iff_isBent, CryptBoolean.even_of_exists_isBent, CryptBoolean.not_isBalanced_of_isBent, CryptBoolean.isBent_iff_nonlinearity_cast_eq_relation_36_of_even, CryptBoolean.nonlinearity_cast_eq_relation_36_iff_isBent") (uses := "carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, relation-36, bent, page-51, fidelity-exact-with-real-rpow-source-form")
*Covering-radius bound and bent equality (Carlet, Relation (36), p. 51).*
Every $`f:V_n\to\mathbb F_2` satisfies
$$`
\operatorname{nl}(f)\le2^{n-1}-2^{n/2-1}.
`
Equality holds exactly when $`|W_f(a)|=2^{n/2}` for every $`a\in V_n`.
Such a function is bent; it can exist only for even $`n` and is not balanced.
:::

:::theorem "carlet-4-random-nonlinearity-lower-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.carletRandomFourierThreshold, CryptBoolean.carletRandomNonlinearityThreshold, CryptBoolean.carletRandomNonlinearityThreshold_eq_displayed, CryptBoolean.carletRandomFourierThreshold_nonneg, CryptBoolean.card_mul_carletRandomFourierThreshold_sq_div_two, CryptBoolean.measure_fourierInfinityNorm_ge_carletThreshold_le, CryptBoolean.carletRandomNonlinearityFailureBound, CryptBoolean.fourier_union_bound_eq_failureBound, CryptBoolean.tendsto_carletRandomNonlinearityFailureBound, CryptBoolean.spectralInfinityNorm_encoding_eq_fourierInfinityNorm, CryptBoolean.nonlinearity_encoding_eq_fourierInfinityNorm, CryptBoolean.carletRandomNonlinearityThreshold_lt_of_fourierInfinityNorm_lt, CryptBoolean.carletRandomNonlinearityProbability, CryptBoolean.one_sub_failureBound_le_carletRandomNonlinearityProbability, CryptBoolean.tendsto_carletRandomNonlinearityProbability") (uses := "carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-4, asymptotic-nonlinearity, olejar-stanek, page-51, fidelity-exact")
*Random-function nonlinearity lower bound (Olejár--Stanek; Carlet, p. 51).* As
$`n\to\infty`, the uniform probability tends to $`1` that
$`f:V_n\to\mathbb F_2` satisfies
$$`
\operatorname{nl}(f)>2^{n-1}-\sqrt n\,2^{(n-1)/2}.
`
:::

Formalization note. The finite proof bounds the failure probability by
$`2(2/e)^n`, using the exact Walsh threshold, a single-frequency Hoeffding bound,
and a union bound over all $`2^n` frequencies. Relation (35) transports the
result to Carlet's raw nonlinearity normalization.

:::theorem "carlet-4-rodier-lower-endpoint" (parent := "carlet-chapter-4") (lean := "CryptBoolean.rodierRandomFourierUpperThreshold, CryptBoolean.rodierRandomNonlinearityLowerThreshold, CryptBoolean.rodierRandomNonlinearityLowerThreshold_eq_displayed, CryptBoolean.rodierRandomFourierUpperThreshold_nonneg, CryptBoolean.card_mul_rodierRandomFourierUpperThreshold_sq_div_two_ge, CryptBoolean.measure_fourierInfinityNorm_ge_rodierUpperThreshold_le, CryptBoolean.rodierRandomNonlinearityLowerFailureBound, CryptBoolean.tendsto_rodierRandomNonlinearityLowerFailureBound, CryptBoolean.rodierRandomNonlinearityLowerThreshold_lt_of_fourierInfinityNorm_lt, CryptBoolean.rodierRandomNonlinearityLowerProbability, CryptBoolean.one_sub_rodierLowerFailureBound_le_probability, CryptBoolean.tendsto_rodierRandomNonlinearityLowerProbability") (uses := "carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-4, asymptotic-nonlinearity, rodier, page-51, fidelity-derived-one-sided")
*Rodier lower endpoint (one-sided consequence of the sharp interval; Carlet, p. 51).* As $`n\to\infty`, the uniform probability tends to $`1` that
$`f:V_n\to\mathbb F_2` satisfies
$$`
\operatorname{nl}(f)>
2^{n-1}-2^{n/2-1}\sqrt n
\left(\sqrt{2\ln2}+\frac{4\ln n}{n}\right).
`
:::

Formalization note. A one-frequency Hoeffding estimate followed by a union
bound over all Walsh frequencies gives failure probability at most $`2/n`.
Relation (35) converts the spectral event to the displayed nonlinearity event.

:::lemma_ "carlet-4-rodier-upper-endpoint-reduction" (parent := "carlet-chapter-4") (lean := "CryptBoolean.rodierRandomFourierLowerThreshold, CryptBoolean.rodierRandomNonlinearityUpperThreshold, CryptBoolean.rodierRandomNonlinearityUpperThreshold_eq_displayed, CryptBoolean.nonlinearity_lt_rodierRandomNonlinearityUpperThreshold, CryptBoolean.rodierRandomFourierLowerProbability, CryptBoolean.rodierRandomNonlinearityUpperProbability, CryptBoolean.rodierRandomFourierLowerProbability_le_nonlinearityUpperProbability, CryptBoolean.tendsto_rodierRandomNonlinearityUpperProbability_of_fourierLower") (uses := "carlet-4-rel-35-nonlinearity-walsh") (tags := "project-bridge, carlet, chapter-4, asymptotic-nonlinearity, rodier, lower-spectral-tail, fidelity-exact-reduction")
*Project bridge: reduction of Rodier's upper endpoint to a spectral lower tail.*
Put
$$`
\tau_n=\sqrt n\left(\sqrt{2\ln2}-\frac{5\ln n}{n}\right)2^{-n/2}.
`
If the uniform probability of
$`\tau_n<\|\widehat{(-1)^f}\|_\infty` tends to $`1`, then the uniform
probability tends to $`1` that
$$`
\operatorname{nl}(f)<
2^{n-1}-2^{n/2-1}\sqrt n
\left(\sqrt{2\ln2}-\frac{5\ln n}{n}\right).
`
:::

Formalization note. Relation (35) proves the deterministic event inclusion;
monotonicity of the uniform measure transports the assumed spectral limit.
Thus only the lower tail of the maximum Walsh coefficient remains analytic.

:::lemma_ "carlet-4-rodier-pair-characteristic-moments" (parent := "carlet-chapter-4") (lean := "CryptBoolean.rodierPairPhase, CryptBoolean.rodierPairCharacteristic, CryptBoolean.rodierPairCharacteristic_eq_prod_cos, CryptBoolean.sum_monomial_mul_eq_zero_of_ne, CryptBoolean.sum_rodierPairPhase_sq, CryptBoolean.sum_rodierPairPhase_fourth") (tags := "project-bridge, carlet, chapter-4, asymptotic-nonlinearity, rodier, characteristic-function, fidelity-exact-finite-core")
*Project bridge: Rodier's two-character characteristic-function moments.*
For distinct Walsh characters $`\chi_S,\chi_T` and real $`t,r`, put
$`u_x=t\chi_S(x)+r\chi_T(x)`. Then the joint characteristic function of
the corresponding raw Walsh coefficients is
$$`
\prod_{x\in\{-1,1\}^n}\cos u_x,
`
and
$$`
\sum_xu_x^2=2^n(t^2+r^2),
\qquad
\sum_xu_x^4=2^n(t^4+6t^2r^2+r^4).
`
:::

Formalization note. Independence gives the cosine product and Walsh-character
orthogonality cancels the mixed odd terms. These are the exact finite
identities used before Rodier's smoothed Fourier estimates.

:::theorem "carlet-4-rodier-sharp-random-nonlinearity-interval" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_rodierAsymptoticOffDiagonalPairError_bound, CryptBoolean.tendsto_rodierRandomFourierLowerProbability, CryptBoolean.rodierSharpRandomNonlinearityIntervalProbability, CryptBoolean.tendsto_rodierSharpRandomNonlinearityIntervalProbability") (uses := "carlet-4-rodier-lower-endpoint, carlet-4-rodier-upper-endpoint-reduction, carlet-4-rodier-pair-characteristic-moments") (tags := "carlet, chapter-4, asymptotic-nonlinearity, rodier, page-51, fidelity-exact")
*Sharp random-function nonlinearity interval (Rodier; Carlet, p. 51).* As
$`n\to\infty`, the uniform probability tends to $`1` that
$`f:V_n\to\mathbb F_2` has nonlinearity between
$$`
2^{n-1}-2^{n/2-1}\sqrt n
\left(\sqrt{2\ln2}+\frac{4\ln n}{n}\right)
`
and
$$`
2^{n-1}-2^{n/2-1}\sqrt n
\left(\sqrt{2\ln2}-\frac{5\ln n}{n}\right).
`
:::

Formalization note. Following {Citations.citet rodier2006}[], the proof uses
correlated Walsh pairs, smoothed cutoff estimates, and a second-moment
argument. A uniform off-diagonal covariance error tends to zero at the
required scale; the resulting spectral lower tail is intersected with the
compiled one-sided upper tail. Relation (35) then gives the simultaneous
nonlinearity interval, including the exact $`+4\ln(n)/n` and
$`-5\ln(n)/n` corrections.

:::theorem "carlet-4-odd-dimension-exact-five" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maximumNonlinearity_five") (uses := "carlet-4-odd-dimension-quadratic-covering-bounds, carlet-3-affine-weight, carlet-3-reed-muller-dimension, carlet-4-def-higher-order-nonlinearity") (tags := "carlet, chapter-4, odd-dimension, exact-five-variables, pages-51-52, fidelity-exact")
*Exact best nonlinearity in dimension five (Carlet, pp. 51--52).* If $`M_n`
denotes the maximum nonlinearity of an $`n`-variable Boolean function, then
$$`
M_5=2^4-2^2=12.
`
:::

Formalization note. The quadratic construction gives the lower bound. For the
upper bound, a hypothetical weight-thirteen first-order Reed--Muller coset
leader yields a self-complementary binary $`[13,6,\ge5]` code. Residuation at
a minimum-weight word produces a binary $`[7,5,\ge3]` or $`[8,5,\ge3]` code,
and the radius-one Hamming bound rules out both cases.

:::lemma_ "carlet-4-six-variable-covering-coset-coordinate" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_minimum_affine_error_one_at_of_nonlinearity_eq_28") (uses := "carlet-4-rel-36-covering-radius-bent") (tags := "project-bridge, carlet, chapter-4, odd-dimension, reed-muller-coset, hou-1996, fidelity-strengthened")
*Project bridge: coordinate-covering leaders of six-variable deep cosets.*
Let $`f:V_6\to\mathbb F_2` have $`\operatorname{nl}(f)=28`. For every
$`x\in V_6`, there is an affine function $`\ell` such that
$$`
d_H(f,\ell)=28
\qquad\text{and}\qquad
(f+\ell)(x)=1.
`
:::

Formalization note. This is the covering-radius orphan fact used in Hou's
dimension-seven argument. The proof derives the flat Walsh spectrum from
Relation (36) and uses Walsh inversion to force a minimum representative
through every prescribed coordinate; it needs no finite truth-table
certificate or degree hypothesis.

:::lemma_ "carlet-4-six-variable-degree-four-coset-coordinate" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_minimum_affine_error_one_at_of_degree_le_four_nonlinearity_eq_26") (uses := "carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval, carlet-3-theorem-2") (tags := "project-bridge, carlet, chapter-4, odd-dimension, reed-muller-coset, hou-1997, fidelity-exact")
*Project bridge: coordinate-covering leaders of degree-four six-variable cosets.*
Let $`f:V_6\to\mathbb F_2` have algebraic degree at most $`4` and
$`\operatorname{nl}(f)=26`. For every $`x\in V_6`, there is an affine
function $`\ell` such that
$$`
d_H(f,\ell)=26
\qquad\text{and}\qquad
(f+\ell)(x)=1.
`
:::

Formalization note. Reed--Muller duality forces all affine-coset weights to
be congruent modulo four. Relation (35) and Parseval then give exactly 24
Walsh coefficients of magnitude 12 and 40 of magnitude 4; Walsh inversion
forces a minimum representative through every prescribed coordinate. This
is Hou's remaining six-variable orphan fact, without a finite certificate.

:::theorem "carlet-4-odd-dimension-best-nonlinearity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.firstCoordinateSliceSeven, CryptBoolean.exists_linearEquiv_firstCoordinateSlices_degree_le_four, CryptBoolean.nonlinearity_le_56_of_degree_le_five_seven, CryptBoolean.exists_minimum_affine_error_one_at_of_degree_le_five_nonlinearity_eq_56_seven, CryptBoolean.nonlinearity_le_fifty_six_of_degree_five_covering, CryptBoolean.maximumNonlinearity_seven") (uses := "carlet-4-odd-dimension-quadratic-covering-bounds, carlet-4-six-variable-covering-coset-coordinate, carlet-4-six-variable-degree-four-coset-coordinate") (tags := "carlet, chapter-4, odd-dimension, exact-seven-variables, pages-51-52, fidelity-exact")
*Exact best nonlinearity in dimension seven (Carlet, pp. 51--52).* If $`M_n`
denotes the maximum nonlinearity of an $`n`-variable Boolean function, then
$$`
M_7=2^6-2^3=56.
`
:::

Formalization note. The proof follows Hou's alternative to Mykkeltveit's
self-complementary-code argument. A point-indicator quotient reduces an
arbitrary seven-variable word to degree at most five. An alternating-form
radical supplies a linear coordinate in which both six-variable slices have
degree at most four; the two coordinate-covering results above close the
nonlinearity-$`24`, $`26`, and $`28` equality cases. The quadratic
construction gives the matching lower bound.

:::theorem "carlet-4-odd-dimension-quadratic-covering-bounds" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maximumNonlinearity, CryptBoolean.nonlinearity_le_maximumNonlinearity, CryptBoolean.exists_nonlinearity_eq_maximumNonlinearity, CryptBoolean.oddQuadraticFunction, CryptBoolean.walshTransform_oddQuadraticFunction, CryptBoolean.maxWalshMagnitude_oddQuadraticFunction, CryptBoolean.nonlinearity_oddQuadraticFunction, CryptBoolean.quadraticBound_le_maximumNonlinearity_of_odd, CryptBoolean.maximumNonlinearity_cast_le_relation_36, CryptBoolean.maximumNonlinearity_odd_bounds") (uses := "carlet-4-rel-35-nonlinearity-walsh, carlet-4-rel-36-covering-radius-bent") (tags := "carlet, chapter-4, odd-dimension, quadratic-bound, covering-radius, pages-51-52, fidelity-exact")
*Quadratic and covering-radius bounds in odd dimension (Carlet, pp. 51--52).*
For every odd $`n`, if $`M_n` is the maximum nonlinearity of an $`n`-variable
Boolean function, then
$$`
2^{n-1}-2^{(n-1)/2}
\le M_n\le
2^{n-1}-2^{n/2-1}.
`
:::

Formalization note. The lower bound is attained by FABL's complete
inner-product bent function on $`n-1` variables extended by one dummy
coordinate. Relation (35) gives its exact nonlinearity. The upper bound is
Relation (36), applied to a function attaining the finite maximum.

:::theorem "carlet-4-odd-dimension-exact-one-three" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maximumNonlinearity_one, CryptBoolean.maximumNonlinearity_three") (uses := "carlet-4-odd-dimension-quadratic-covering-bounds") (tags := "carlet, chapter-4, odd-dimension, exact-small-dimensions, page-52, fidelity-exact")
*Exact best nonlinearities in dimensions one and three (Carlet, p. 52).* If
$`M_n` denotes the maximum nonlinearity of an $`n`-variable Boolean function,
then
$$`
M_1=0\qquad\text{and}\qquad M_3=2.
`
:::

Formalization note. The quadratic construction supplies the matching lower
bounds, while Relation (36) makes the covering-radius upper bounds strict
enough that integrality determines both maxima.

:::theorem "carlet-4-odd-dimension-strict-above-quadratic" (parent := "carlet-chapter-4") (lean := "CryptBoolean.f₂CubeNatIndex, CryptBoolean.f₂CubeOfNat, CryptBoolean.kavutYucelTruthTable, CryptBoolean.kavutYucelFunction9, CryptBoolean.kavutYucelFunction9_walsh_bound, CryptBoolean.kavutYucelFunction9_walsh_witness, CryptBoolean.maxWalshMagnitude_kavutYucelFunction9, CryptBoolean.nonlinearity_kavutYucelFunction9, CryptBoolean.kavutYucelBentExtension, CryptBoolean.realSignView_kavutYucelBentExtension, CryptBoolean.walshTransform_kavutYucelBentExtension_append, CryptBoolean.natAbs_walshTransform_innerProductModTwoBit, CryptBoolean.natAbs_walshTransform_kavutYucelBentExtension_append, CryptBoolean.maxWalshMagnitude_kavutYucelBentExtension, CryptBoolean.nonlinearity_kavutYucelBentExtension, CryptBoolean.quadraticBound_lt_nonlinearity_kavutYucelBentExtension, CryptBoolean.exists_nonlinearity_gt_quadraticBound_of_odd, CryptBoolean.quadraticBound_lt_maximumNonlinearity_of_odd") (uses := "carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-4, odd-dimension, kavut-yucel, pages-51-52, fidelity-exact")
*Strict improvement above the quadratic bound (Carlet, pp. 51--52).* For every
odd $`n>7`, there exists $`f:V_n\to\mathbb F_2` such that
$$`
\operatorname{nl}(f)>2^{n-1}-2^{(n-1)/2}.
`
:::

Formalization note. The base case is the first nine-variable truth table in
Kavut--Yücel, with a kernel-checked fast Walsh certificate proving
$`\max_a|W_f(a)|=28` and hence $`\operatorname{nl}(f)=242`. Direct product
with FABL's complete $`2m`-variable bent block scales all raw Walsh magnitudes
by $`2^m`, yielding every odd dimension above seven.

:::theorem "carlet-4-odd-dimension-balanced-above-quadratic" (parent := "carlet-chapter-4") (lean := "CryptBoolean.flipOn, CryptBoolean.MaitraKavutYucel.seedTruthTable, CryptBoolean.MaitraKavutYucel.seedFunction9, CryptBoolean.MaitraKavutYucel.shiftFrequency9, CryptBoolean.MaitraKavutYucel.shiftedSeedFunction9, CryptBoolean.MaitraKavutYucel.bentTruthTable, CryptBoolean.MaitraKavutYucel.bentFunction4, CryptBoolean.MaitraKavutYucel.initialFunction13, CryptBoolean.MaitraKavutYucel.flipPointList13, CryptBoolean.MaitraKavutYucel.flipPoints13, CryptBoolean.maitraKavutYucelFunction13, CryptBoolean.maitraKavutYucelFunction13_walsh_bound, CryptBoolean.isBalanced_maitraKavutYucelFunction13, CryptBoolean.maitraKavutYucelFunction13_walsh_witness, CryptBoolean.maxWalshMagnitude_maitraKavutYucelFunction13, CryptBoolean.nonlinearity_maitraKavutYucelFunction13, CryptBoolean.maitraKavutYucelBentExtension, CryptBoolean.isBalanced_maitraKavutYucelBentExtension, CryptBoolean.maxWalshMagnitude_maitraKavutYucelBentExtension, CryptBoolean.nonlinearity_maitraKavutYucelBentExtension, CryptBoolean.quadraticBound_lt_nonlinearity_maitraKavutYucelBentExtension, CryptBoolean.exists_isBalanced_nonlinearity_gt_quadraticBound_of_odd") (uses := "carlet-4-rel-35-nonlinearity-walsh, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, odd-dimension, balanced, maitra-kavut-yucel, page-52, fidelity-strengthened-dimension-range")
*Balanced functions above the quadratic bound (Carlet, p. 52, footnote 22).*
For every odd $`n\ge15`, there exists a balanced Boolean function
$`f:V_n\to\mathbb F_2` such that
$$`
\operatorname{nl}(f)>2^{n-1}-2^{(n-1)/2}.
`
:::

Formalization note. Maitra--Kavut--Yücel's published thirteen-variable
function is reconstructed from its nine-variable seed, linear shift,
four-variable bent direct-sum component, and eight toggled positions. A
kernel-checked $`512`-point seed certificate plus the exact flip formula proves
balance, $`\max_a|W_f(a)|=120`, and $`\operatorname{nl}(f)=4036`. Complete
bent direct sums preserve balance and scale the spectrum, proving the stronger
range of every odd $`n\ge13`.

:::theorem "carlet-4-odd-dimension-pc-one-above-quadratic" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maitraKavutYucelZeroAutocorrelationBasis, CryptBoolean.maitraKavutYucelZeroAutocorrelationBasis_independent, CryptBoolean.maitraKavutYucelPCOneReindex, CryptBoolean.maitraKavutYucelPCOneFunction13, CryptBoolean.satisfiesPropagationCriterion_one_maitraKavutYucelPCOneFunction13, CryptBoolean.nonlinearity_maitraKavutYucelPCOneFunction13, CryptBoolean.maitraKavutYucelPCOneBentExtension, CryptBoolean.satisfiesPropagationCriterion_one_maitraKavutYucelPCOneBentExtension, CryptBoolean.maxWalshMagnitude_maitraKavutYucelPCOneBentExtension, CryptBoolean.nonlinearity_maitraKavutYucelPCOneBentExtension, CryptBoolean.quadraticBound_lt_nonlinearity_maitraKavutYucelPCOneBentExtension, CryptBoolean.exists_pc_one_nonlinearity_gt_quadraticBound_of_odd") (uses := "carlet-4-odd-dimension-balanced-above-quadratic, carlet-4-def-propagation-criteria") (tags := "carlet, chapter-4, odd-dimension, propagation-criterion, maitra-sarkar, page-52, fidelity-strengthened-dimension-range")
*PC(1) functions above the quadratic bound (Carlet, p. 52, footnote 22).* For
every odd $`n\ge15`, there exists a Boolean function
$`f:V_n\to\mathbb F_2` satisfying $`\mathrm{PC}(1)` such that
$$`
\operatorname{nl}(f)>2^{n-1}-2^{(n-1)/2}.
`
:::

Formalization note. Carlet cites Maitra--Sarkar, reference 264. The compiled
construction linearly reindexes the thirteen-variable Maitra--Kavut--Yücel
function along a certified basis of zero-autocorrelation directions and then
uses complete bent extensions. This proves the stronger range of every odd
$`n\ge13`.

:::theorem "carlet-4-odd-dimension-degree-pred-above-quadratic" (parent := "carlet-chapter-4") (lean := "CryptBoolean.nonlinearity_le_hammingDistance_add_nonlinearity, CryptBoolean.exists_isBalanced_degree_pred_nonlinearity_ge_sub_two, CryptBoolean.exists_isBalanced_degree_pred_nonlinearity_gt_quadraticBound_of_odd") (uses := "carlet-4-odd-dimension-balanced-above-quadratic, carlet-3-prop-12, carlet-4-def-nonlinearity") (tags := "carlet, chapter-4, odd-dimension, algebraic-degree, page-52, fidelity-strengthened-balancedness")
*Degree-$`n-1` functions above the quadratic bound (Carlet, p. 52, footnote 22).*
For every odd $`n\ge15`, there exists a Boolean function
$`f:V_n\to\mathbb F_2` with $`\deg_{\mathrm{alg}}(f)=n-1` such that
$$`
\operatorname{nl}(f)>2^{n-1}-2^{(n-1)/2}.
`
:::

Formalization note. A balanced function already of degree $`n-1` is left
unchanged. Otherwise, swapping one zero and one one is addition by the
indicator of their affine line. Proposition 12 gives that indicator degree
$`n-1` and weight two; the algebraic-degree sum bound forces exact degree,
while Hamming-triangle Lipschitzness loses at most two units of nonlinearity.
Applied to the balanced family above, the remaining spectral margin is strict
for every odd $`n\ge15`. The compiled witnesses are therefore also balanced.

:::theorem "carlet-4-reed-muller-coset-distance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.minimumHammingDistance, CryptBoolean.firstOrderCosetUnion, CryptBoolean.firstOrderReedMullerCoset, CryptBoolean.HasDistinctFirstOrderCosets, CryptBoolean.minimumPairNonlinearity, CryptBoolean.mem_firstOrderCosetUnion_iff, CryptBoolean.mem_firstOrderReedMullerCoset_iff, CryptBoolean.firstOrderCosetUnion_pair, CryptBoolean.minimumHammingDistance_le, CryptBoolean.le_minimumHammingDistance, CryptBoolean.minimumPairNonlinearity_le, CryptBoolean.le_minimumPairNonlinearity, CryptBoolean.hammingDistance_add_right, CryptBoolean.hammingDistance_eq_cosetDifference, CryptBoolean.nonlinearity_le_hammingDistance_of_mem_cosets, CryptBoolean.nonlinearity_le_two_pow_sub_one, CryptBoolean.exists_pair_nonlinearity_eq_minimumPairNonlinearity, CryptBoolean.firstOrderCosetUnion_offDiag_nonempty, CryptBoolean.dimension_pos_of_hasDistinctFirstOrderCosets, CryptBoolean.two_pow_sub_one_le_hammingDistance_of_mem_same_coset, CryptBoolean.minimumPairNonlinearity_le_two_pow_sub_one, CryptBoolean.minimumHammingDistance_firstOrderCosetUnion, CryptBoolean.hasDistinctFirstOrderCosets_pair_zero, CryptBoolean.minimumPairNonlinearity_pair_zero, CryptBoolean.minimumHammingDistance_two_firstOrderReedMullerCosets") (uses := "carlet-4-def-nonlinearity, carlet-3-reed-muller-code") (tags := "carlet, chapter-4, reed-muller, cosets, page-52, fidelity-corrected-distinct-cosets")
*Corrected distances of unions of first-order Reed--Muller cosets (Carlet, p. 52).* Let
$`\mathcal F` be a finite family with at least two members and
suppose that distinct members represent distinct cosets of $`R(1,n)`. Then
$$`
d_{\min}\!\left(\bigcup_{f\in\mathcal F}(f+R(1,n))\right)
=\min_{\substack{f,g\in\mathcal F\\f\ne g}}
\operatorname{nl}(f+g).
`
In particular, if $`f\notin R(1,n)`, then
$$`
d_{\min}\bigl(R(1,n)\cup(f+R(1,n))\bigr)=\operatorname{nl}(f).
`
:::

Formalization note. The source omits the distinct-coset hypothesis. Without
it the displayed equality is false: for affine $`f`, the two listed cosets
coincide. The formal declaration records the necessary correction explicitly.

:::theorem "carlet-4-derivative-nonlinearity-bounds" (parent := "carlet-chapter-4") (lean := "CryptBoolean.minimumAutocorrelationMagnitude, CryptBoolean.autocorrelation_add_of_isLinearStructure, CryptBoolean.abs_autocorrelation_add_of_isLinearStructure, CryptBoolean.exists_abs_autocorrelation_eq_absoluteIndicator, CryptBoolean.nonlinearity_cast_le_autocorrelation_upper_bound, CryptBoolean.relation_37_nonlinearity_lower_bound") (uses := "carlet-4-def-nonlinearity, carlet-4-hyperplane-walsh-autocorrelation, carlet-2-def-2-derivative, carlet-2-def-autocorrelation") (tags := "carlet, chapter-4, relation-37, derivatives, pages-52-53, fidelity-exact-with-real-rpow-source-form")
*Derivative bounds for nonlinearity (Carlet, Relation (37), pp. 52--53).*
For $`\Delta_f(e)=\sum_x(-1)^{D_ef(x)}`, one has
$$`
\operatorname{nl}(f)
\le2^{n-1}-\frac12
\sqrt{2^n+\max_{e\ne0}|\Delta_f(e)|}
`
and
$$`
\operatorname{nl}(f)
\ge2^{n-2}-\frac14\min_{e\ne0}|\Delta_f(e)|.
`
:::

:::corollary "carlet-4-odd-weighting-nonlinearity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.subspaceCosetWeight, CryptBoolean.IsMaximalOddWeightingSubspace, CryptBoolean.hammingWeight_lower_bound_of_isMaximalOddWeightingSubspace, CryptBoolean.isMaximalOddWeightingSubspace_add_affineFunction, CryptBoolean.hammingWeight_lower_bound_of_maximalOddWeightingSubspace, CryptBoolean.nonlinearity_lower_bound_of_maximalOddWeightingSubspace") (uses := "carlet-4-def-nonlinearity") (tags := "carlet, chapter-4, odd-weighting, page-53, fidelity-exact")
*Odd-weighting subspace bound (Carlet, p. 53).* If $`f` admits a maximal
odd-weighting subspace $`E` of dimension $`d\ge2`, then
$$`
\operatorname{nl}(f)\ge2^{n-d}.
`
:::
