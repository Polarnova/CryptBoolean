/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Citations
import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
import CryptBoolean.Carlet.Chapter04.HigherOrderJuntaDistance
import CryptBoolean.Carlet.Chapter04.HigherOrderGeneralBounds
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwo
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightEight
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightTwelveClassification
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightFourteenClassification
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoLowWeightSpectrum
import CryptBoolean.Carlet.Chapter04.HigherOrderTupleCountDifferences
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoMomentDifference
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoAsymptotics
import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.OrbitAggregation
import CryptBoolean.Carlet.Chapter03.ReedMullerWeightSixteenSelfDual

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Higher-order nonlinearity" =>

:::definition "carlet-4-def-higher-order-nonlinearity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.higherOrderNonlinearity, CryptBoolean.nonlinearity_eq_higherOrderNonlinearity_one, CryptBoolean.higherOrderNonlinearity_le_hammingDistance, CryptBoolean.exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity, CryptBoolean.higherOrderNonlinearity_antitone") (uses := "carlet-3-reed-muller-code, carlet-2-def-hamming-distance") (tags := "carlet, chapter-4, higher-order-nonlinearity, pages-53-54, fidelity-exact-with-derived-laws")
*Higher-order nonlinearity (Carlet, pp. 53--54).* For $`0\le r<n`, define
$$`
\operatorname{nl}_r(f)
=\min_{g\in R(r,n)}d_H(f,g).
`
The sequence $`(\operatorname{nl}_r(f))_{0\le r<n}` is the nonlinearity
profile of $`f`.
:::

:::theorem "carlet-4-higher-order-junta-distance" (parent := "carlet-chapter-4") (lean := "CryptBoolean.anfCoeff_eq_zero_of_coordinate_invariant, CryptBoolean.anfCoeff_eq_zero_of_dependsOn_of_not_subset, CryptBoolean.functionAlgebraicDegree_le_card_of_dependsOn, CryptBoolean.higherOrderNonlinearity_le_hammingDistance_of_dependsOn") (uses := "carlet-4-def-higher-order-nonlinearity, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-4, higher-order-nonlinearity, juntas, page-53, fidelity-exact")
*Distance to functions on a prescribed coordinate set (Carlet, p. 53).* If
$`I\subseteq\{1,\ldots,n\}` and $`|I|=r`, then
$$`
\operatorname{nl}_r(f)
\le \min_{g\text{ depending only on }I}d_H(f,g).
`
:::

:::lemma_ "carlet-4-higher-order-counting-criterion" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hammingBallVolume, CryptBoolean.exists_higherOrderNonlinearity_gt_of_counting, CryptBoolean.exists_higherOrderNonlinearity_gt_of_hammingBallVolume_lt") (uses := "carlet-4-def-higher-order-nonlinearity, carlet-3-reed-muller-dimension") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, sphere-covering, page-54, fidelity-exact-finite-core")
*Project bridge: finite sphere-covering criterion for Carlet's p. 54 lower bound.* Put
$$`
V(N,t)=\sum_{j=0}^{t}\binom Nj,
\qquad
D=\sum_{j=0}^{r}\binom nj.
`
If
$$`
2^D V(2^n,t)<2^{2^n},
`
then some $`f:V_n\to\mathbb F_2` satisfies
$`t<\operatorname{nl}_r(f)`. Equivalently, it suffices that
$`V(2^n,t)<2^{2^n-D}`.
:::

:::theorem "carlet-4-higher-order-asymptotic-lower-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_higherOrderNonlinearity_gt_lower_bound_of_dimension, CryptBoolean.eventually_twice_sum_choose_le_two_pow, CryptBoolean.eventually_exists_higherOrderNonlinearity_gt_carlet_lower_bound") (uses := "carlet-4-higher-order-counting-criterion") (tags := "carlet, chapter-4, higher-order-nonlinearity, asymptotic-lower-bound, pages-53-54, fidelity-exact")
*Asymptotic lower existence bound for higher-order nonlinearity (Carlet, pp. 53--54).*
For each fixed $`r` and all sufficiently large $`n`, there is a function
$`f:V_n\to\mathbb F_2` such that
$$`
\operatorname{nl}_r(f)>
2^{n-1}-\sqrt{2^{n-1}\sum_{i=0}^{r}\binom ni}.
`
:::

:::lemma_ "carlet-4-higher-order-plotkin-induction" (parent := "carlet-chapter-4") (lean := "CryptBoolean.maximumHigherOrderNonlinearity, CryptBoolean.higherOrderNonlinearity_le_maximum, CryptBoolean.exists_higherOrderNonlinearity_eq_maximum, CryptBoolean.maximumHigherOrderNonlinearity_succ_le, CryptBoolean.maximumHigherOrderNonlinearity_self, CryptBoolean.maximumHigherOrderNonlinearity_le_sum_Ico, CryptBoolean.maximumHigherOrderNonlinearity_cast_le_sum_Ico_of_le, CryptBoolean.maximumHigherOrderNonlinearity_cast_le_carlet_step") (uses := "carlet-4-def-higher-order-nonlinearity") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, plotkin-recurrence, reference-91, fidelity-exact-finite-core")
*Project bridge: finite Plotkin induction for the cited upper bound.* Define
$`\rho(r,n)=\max_f\operatorname{nl}_r(f)`. For $`1\le r\le n`,
$$`
\rho(r,n)\le\sum_{j=r}^{n-1}\rho(r-1,j).
`
More generally, if throughout this range
$$`
\rho(r-1,j)\le 2^{j-1}-A(\sqrt2)^j+e(j),
`
then
$$`
\rho(r,n)\le
\frac{2^n-2^r}{2}
-A(1+\sqrt2)\big((\sqrt2)^n-(\sqrt2)^r\big)
+\sum_{j=r}^{n-1}e(j).
`
:::

Formalization note. The proof constructs the Plotkin approximant from the two
coordinate slices and then evaluates the two finite geometric sums exactly.
Thus the cited sharp constant reduces to the order-two covering-radius
theorem.

## Proof architecture of the sharp upper bound

The argument below is organized as a chain of mathematical interfaces rather
than as one monolithic calculation. First, the correlation-moment ratio turns
a lower bound for two consecutive even moments into an upper bound for the
order-two covering radius. Character orthogonality then rewrites those moments
as signed counts of words in the dual Reed--Muller code, and finite Fourier
inversion groups the counts by Hamming weight. The difference of the seventh
and eighth moments is supported only at weights $`0,8,12,14,16`; separate
geometric or classification arguments bound the character sum at each weight.
The resulting moment inequality gives the sharp $`\sqrt{15}/2` order-two
coefficient, and the Plotkin recurrence propagates it to every fixed order
$`r\ge2`, multiplying it by $`1+\sqrt2` at each step.

The weight-sixteen branch is the only exceptional part of this spine. Its
rank-seven words are normalized through an augmented self-dual
$`[16,8,\ge4]` code, classified into the three affine orbits $`2E_8`,
$`D_{16}^{+}`, and $`F_{16}`, and controlled by an orbit-wise sum-of-squares
identity. Words of affine-span rank at most six are handled by a separate
rank-deficient affine-mask cover. Adding these two estimates supplies the
single weight-sixteen character bound consumed by the moment argument; no
later analytic step depends on the details of the finite classification.

More explicitly, the exceptional branch factors through the following
mathematical interfaces.

1. Orthogonality to $`R(2,n)` bounds the affine-span dimension of a
   weight-sixteen support by seven and, in dimension seven, produces an
   augmented self-dual $`[16,8,\ge4]` code.
2. Choosing a support point and seven genuine support differences identifies
   the full-rank support with a systematic sixteen-point subset of $`V_7`;
   its quadratic parity constraints are precisely those inherited from the
   dual Reed--Muller condition.
3. The systematic constraints classify the normalized support into one of
   the three canonical patterns. Affine composition transports that
   classification back to $`V_n`, and pairwise orbit disjointness makes the
   three alternatives unique.
4. For each canonical pattern, a nonnegative complete affine-map sum is split
   into injective and rank-deficient maps. Counting the latter and then
   dividing by the common positive fiber size gives the lower bound for the
   corresponding set of distinct image words.
5. If the affine-span dimension is at most six, a padded basis realizes the
   support as the image of a mask on $`V_7` under a rank-deficient affine map.
   Counting maps and masks bounds both the residual family and its character
   loss.
6. The exact rank-seven/residual partition adds the three orbit estimates and
   the residual estimate. This is the sole weight-sixteen input to the
   seventh/eighth moment inequality.

:::lemma_ "carlet-4-higher-order-order-two-moment-ratio" (parent := "carlet-chapter-4") (lean := "CryptBoolean.orderTwoCorrelation, CryptBoolean.orderTwoCorrelation_eq_two_pow_sub_two_hammingDistance, CryptBoolean.maximumOrderTwoCorrelation, CryptBoolean.maximumOrderTwoCorrelation_eq, CryptBoolean.orderTwoCorrelation_le_maximum, CryptBoolean.exists_orderTwoCorrelation_eq_maximum, CryptBoolean.maximumOrderTwoCorrelation_nonneg, CryptBoolean.abs_orderTwoCorrelation_le_maximum, CryptBoolean.orderTwoCorrelationPowerSum, CryptBoolean.orderTwoCorrelationPowerSum_nonneg, CryptBoolean.orderTwoCorrelationPowerSum_pos, CryptBoolean.orderTwoCorrelationPowerSum_succ_le, CryptBoolean.sqrt_orderTwoCorrelationPowerSum_ratio_le, CryptBoolean.minimumOrderTwoMomentRatio, CryptBoolean.maximumHigherOrderNonlinearity_two_cast_le_momentRatio") (uses := "carlet-4-def-higher-order-nonlinearity, carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, moment-method, reference-91, fidelity-exact-finite-core")
*Project bridge: second-order correlation moment ratio.* For
$`f:V_n\to\mathbb F_2` and $`g\in R(2,n)`, put
$$`
C_f(g)=2^n-2d_H(f,g),
\qquad
S_k(f)=\sum_{g\in R(2,n)} C_f(g)^{2k}.
`
Then $`S_k(f)>0` and
$$`
\sqrt{\frac{S_{k+1}(f)}{S_k(f)}}
\le 2^n-2\operatorname{nl}_2(f).
`
Consequently, if $`\rho(2,n)=\max_f\operatorname{nl}_2(f)` and
$`\mu_{k,n}=\min_f\sqrt{S_{k+1}(f)/S_k(f)}`, then
$$`
\rho(2,n)\le 2^{n-1}-\frac{\mu_{k,n}}2.
`
:::

Formalization note. Relations (9.7)--(9.10) of the cited Carlet--Mesnager
argument reduce the sharp order-two bound to a uniform lower estimate for
consecutive even correlation moments. The low-weight dual Reed--Muller
classification supplies that estimate through the subsequent weight-by-weight
decomposition.

:::lemma_ "carlet-4-higher-order-order-two-dual-moment-decomposition" (parent := "carlet-chapter-4") (lean := "CryptBoolean.tuplePointParity, CryptBoolean.booleanFunctionPairing_tuplePointParity, CryptBoolean.orderTwoAdmissibleTuples, CryptBoolean.reedMullerTwoPairingCharacterSum, CryptBoolean.reedMullerTwoPairingCharacterSum_eq_card_of_mem_dual, CryptBoolean.reedMullerTwoPairingCharacterSum_eq_zero_of_not_mem_dual, CryptBoolean.orderTwoCorrelationPowerSum_eq_admissibleTupleCharacterSum") (uses := "carlet-4-higher-order-order-two-moment-ratio, carlet-3-theorem-2") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, moment-decomposition, reference-91, fidelity-exact-finite-core")
*Project bridge: dual-code decomposition of second-order correlation moments.*
For an ordered $`2k`-tuple $`x=(x_i)` of points of $`V_n`, let $`p_x` be
the Boolean function recording the parity of the multiplicity of each point,
and let
$$`
U_{k,n}=\{x:p_x\in R(n-3,n)\}.
`
If $`n\ge3`, then
$$`
S_k(f)=|R(2,n)|
\sum_{x\in U_{k,n}}(-1)^{\langle f,p_x\rangle}.
`
:::

Formalization note. Expanding the even power gives ordered tuples. Character
orthogonality over $`R(2,n)` leaves exactly its dual, and Chapter 3 duality
identifies that code with $`R(n-3,n)`. This is Carlet--Mesnager Lemma 9.2.2;
the subsequent grouping by low dual weights remains separate.

:::lemma_ "carlet-4-higher-order-order-two-weight-grouping" (parent := "carlet-chapter-4") (lean := "CryptBoolean.orderTwoDualWords, CryptBoolean.tuplePointParityFiber, CryptBoolean.tuplePointParityMultiplicity, CryptBoolean.tuplePointParityMultiplicity_comp_perm, CryptBoolean.tuplePointParityMultiplicity_eq_of_hammingWeight_eq, CryptBoolean.tuplePointParityMultiplicityByWeight, CryptBoolean.tuplePointParityMultiplicity_eq_byWeight, CryptBoolean.tuplePointParityMultiplicityByWeight_eq_fourierSum, CryptBoolean.tuplePointParityKrawtchoukMultiplicity, CryptBoolean.tuplePointParityMultiplicityByWeight_eq_krawtchoukSum, CryptBoolean.orderTwoCorrelationPowerSum_eq_dualWeightGroupedCharacterSum, CryptBoolean.orderTwoCorrelationPowerSum_eq_dualFourierMultiplicityCharacterSum, CryptBoolean.orderTwoCorrelationPowerSum_eq_dualKrawtchoukMultiplicityCharacterSum") (uses := "carlet-4-higher-order-order-two-dual-moment-decomposition") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-grouping, krawtchouk, reference-91, fidelity-exact-finite-core")
*Project bridge: weight grouping and finite inversion of tuple multiplicities.*
Let $`N_k(w)` be the number of ordered $`2k`-tuples whose point-parity word
is a prescribed Boolean function of Hamming weight $`w`. This number depends
only on $`w`, and
$$`
N_k(w)=2^{-2^n}\sum_{j=0}^{2^n}
K_j^{(2^n)}(w)(2^n-2j)^{2k},
`
where $`K_j^{(2^n)}` is the binary Krawtchouk polynomial. Consequently the
dual-code moment decomposition can be grouped by dual words and then by their
Hamming weights using these exact multiplicities.
:::

Formalization note. Permuting the Boolean cube identifies all tuple-parity
fibers of equal weight. Character orthogonality on the full Boolean-function
group gives finite Fourier inversion, and FABL's Krawtchouk API groups the
Fourier sum by Hamming weight. This is the finite form of Carlet--Mesnager
Proposition 9.2.5 and Lemma 9.2.7.

:::lemma_ "carlet-4-higher-order-order-two-low-weight-support" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hasOrderTwoLowWeightSpectrum, CryptBoolean.tuplePointParityMultiplicityByWeight_eq_zero_of_lt, CryptBoolean.tuplePointParityMomentDifference_eq_zero_of_sixteen_lt, CryptBoolean.orderTwoMomentDifferenceCharacterSum_eq_lowWeights") (uses := "carlet-4-higher-order-order-two-weight-grouping, carlet-3-theorem-1") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, low-weight-spectrum, reference-91, fidelity-exact-finite-core")
*Project bridge: support of the seventh/eighth moment difference.* Let
$`h\in R(n-3,n)` and $`n\ge7`. Among even weights at most $`16`, the only
possibilities are
$$`
0,\ 8,\ 12,\ 14,\ 16.
`
Moreover, a point-parity multiplicity for ordered $`2k`-tuples vanishes
when $`w>2k`. Hence the coefficient of $`h` in
$`S_8(f)-15\cdot2^nS_7(f)` vanishes for $`w>16`, so this moment difference
is supported only at the five displayed weights.
:::

Formalization note. The minimum-distance theorem excludes weights below
eight and the codimension-three spectrum excludes weight ten; tuple support
alone removes weights above sixteen. This is the finite support reduction
used before the individual low-weight estimates in
{Citations.citet carletMesnager2007}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-eight-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.orderTwoWeightEightDualWords_eq_affineFlatIndicators, CryptBoolean.orderTwoWeightEightCharacterSum_eq_affineFlatCharacterSum, CryptBoolean.card_binaryAffineFlats_two, CryptBoolean.binaryAffineFlatCharacterSum_three_ge_neg_card, CryptBoolean.binaryAffineFlatCharacterSum_three_ge, CryptBoolean.orderTwoWeightEightCharacterSum_ge") (uses := "carlet-4-higher-order-order-two-low-weight-support, carlet-3-prop-12") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-eight, affine-flats, reference-91, fidelity-exact-finite-core")
*Project bridge: weight-eight dual character bound.* For $`n\ge3`, the
weight-eight words of $`R(n-3,n)` are precisely the indicators of affine
three-flats. If
$$`
M_8(f)=\sum_{\substack{h\in R(n-3,n)\\\operatorname{wt}(h)=8}}
(-1)^{\langle f,h\rangle},
`
then
$$`
M_8(f)\ge
-\frac{2^n(2^n-1)(2^n-2)}{336}.
`
:::

Formalization note. Proposition 12 supplies the affine-flat normal form.
The character sum over parallel affine two-flat pairs is a square; removing
the diagonal leaves the stated lower bound. This is
Carlet--Mesnager Proposition 9.2.10(1)
{Citations.citep carletMesnager2007}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-twelve-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hasWeightTwelveFlatPairClassification, CryptBoolean.weightTwelveRepresentationCharacterSum_ge, CryptBoolean.orderTwoWeightTwelveCharacterSum_eq_representation, CryptBoolean.orderTwoWeightTwelveCharacterSum_ge") (uses := "carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-twelve, affine-flats, reference-91, fidelity-exact-finite-core")
*Project bridge: weight-twelve dual character bound.* For $`n\ge5`, every
weight-twelve word of $`R(n-3,n)` has exactly twenty ordered
representations as the sum of two affine three-flat indicators whose
intersection is an affine line. Consequently, with
$$`
M_{12}(f)=\sum_{\substack{h\in R(n-3,n)\\\operatorname{wt}(h)=12}}
(-1)^{\langle f,h\rangle},
`
one has
$$`
M_{12}(f)\ge-\frac{(2^n)^5}{20}.
`
:::

Formalization note. The exact fiber size converts the word sum into a
normalized affine-flat representation sum. The unrestricted sum is a sum of
squares indexed by affine lines; the excluded nontransverse configurations
inject into five ambient vectors. The low-weight classification follows the
Kasami--Tokura analysis
{Citations.citep kasamiTokura1970, kasamiTokuraAzumi1976}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-fourteen-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hasWeightFourteenFlatPairClassification, CryptBoolean.weightFourteenRepresentationCharacterSum_ge, CryptBoolean.orderTwoWeightFourteenCharacterSum_eq_representation, CryptBoolean.orderTwoWeightFourteenCharacterSum_ge") (uses := "carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-fourteen, affine-flats, reference-91, fidelity-exact-finite-core")
*Project bridge: weight-fourteen dual character bound.* Every
weight-fourteen word of $`R(n-3,n)` is the sum of two affine three-flat
indicators meeting in one point, with exactly the two ordered
representations obtained by exchanging the flats. Therefore
$$`
M_{14}(f)=\sum_{\substack{h\in R(n-3,n)\\\operatorname{wt}(h)=14}}
(-1)^{\langle f,h\rangle}
\ge-\frac{(2^n)^6}{2}.
`
:::

Formalization note. The complete ordered-pair sum at each base point is a
square. Nontransverse pairs inject into five ambient vectors, and the exact
two-element representation fiber transfers the resulting bound to distinct
dual words. The classification is the relevant Kasami--Tokura low-weight
case {Citations.citep kasamiTokura1970, kasamiTokuraAzumi1976}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-sixteen-rank-reduction" (parent := "carlet-chapter-4") (lean := "CryptBoolean.finrank_supportDifferenceSpan_le_seven_of_weight_sixteen, CryptBoolean.exists_supportDifferenceBasis_of_finrank_eq, CryptBoolean.augmentedSupportDifferenceCode_le_perpendicular, CryptBoolean.four_le_binaryVectorWeight_of_mem_augmentedSupportDifferenceCode, CryptBoolean.finrank_augmentedSupportDifferenceCode_eq_eight, CryptBoolean.augmentedSupportDifferenceCode_eq_perpendicular") (uses := "carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-sixteen, self-dual-code, affine-span, reference-91, fidelity-exact-finite-core")
*Project bridge: rank reduction and the augmented self-dual code.* Let
$`h\in R(n-3,n)` have weight $`16`, and choose $`p\in\operatorname{supp}(h)`.
Then the affine span of the support differences has dimension at most seven.
Whenever this dimension is $`r`, one can choose $`r` actual support
differences that form a basis of the span.
If its dimension is seven, adjoining the constant coordinate to affine
evaluation on the sixteen support points produces a binary self-dual code
of length $`16`, dimension $`8`, and minimum distance at least $`4`.
:::

Formalization note. Orthogonality to $`R(2,n)` gives self-orthogonality of
the augmented evaluation code; the full-span rank calculation upgrades this
to self-duality. A basis is then extracted from the genuine support
differences spanning the direction space. Thus the rank-seven branch reduces
to the classification of
projective binary self-dual $`[16,8,\ge4]` codes, whose three types are
described in {Citations.citet pless1972}[] and surveyed by
{Citations.citet rainsSloane1998}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-sixteen-rank-seven-classification" (parent := "carlet-chapter-4") (lean := "CryptBoolean.rankSevenWeightSixteenPatternCertificate, CryptBoolean.hasRankSevenWeightSixteenOrbitClassification") (uses := "carlet-4-higher-order-order-two-weight-sixteen-rank-reduction") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-sixteen, rank-seven, finite-classification, fidelity-exact")
*Project bridge: rank-seven weight-sixteen classification.* A weight-sixteen
word $`h\in R(n-3,n)` whose support has affine-span dimension seven is an
injective affine image of exactly one of the three canonical sixteen-point
patterns $`2E_8`, $`D_{16}^{+}`, and $`F_{16}`. Conversely, every such image
has weight sixteen, belongs to $`R(n-3,n)`, and has support-affine-span
dimension seven; the three affine orbits are pairwise disjoint.
:::

Formalization note. Choosing a support point and a basis of genuine support
differences gives an affine embedding of a normalized sixteen-point set in
$`V_7`. The quadratic dual-code constraints become systematic parity
conditions on that set. Their three solutions, transported back by affine
composition, agree with the complete classification in
{Citations.citet mesnagerOblaukhov2022}[] and with the self-dual code types in
{Citations.citet pless1972, rainsSloane1998}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-sixteen-orbit-sos" (parent := "carlet-chapter-4") (lean := "CryptBoolean.rankSevenWeightSixteenPatternAffineProduct, CryptBoolean.rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum, CryptBoolean.rankSevenWeightSixteenPatternCompleteAffineMapCharacterSum_nonneg, CryptBoolean.rankSevenWeightSixteenInjectiveAffineMapData, CryptBoolean.rankSevenWeightSixteenInjectiveAffineMapCharacterSum_ge, CryptBoolean.rankSevenWeightSixteenPatternOrbitWords, CryptBoolean.rankSevenWeightSixteenPatternOrbitCharacterSum, CryptBoolean.rankSevenWeightSixteenPatternOrbitCharacterSum_ge") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-sixteen, orbit-sum, sum-of-squares, fidelity-exact-finite-core")
*Project bridge: nonnegative affine-map sums for rank-seven patterns.* Let
$`\sigma:V_n\to\{-1,1\}`. For each
$`c\in\{2E_8,D_{16}^{+},F_{16}\}`, the sum over all affine maps
$`A:V_7\to V_n` of
$$`
\prod_{x\in c}\sigma(Ax)
`
is nonnegative. Restricting to injective affine maps and then to distinct
image words gives, for every $`f:V_n\to\mathbb F_2`,
$$`
\sum_{h\in\mathcal O_c}(-1)^{\langle f,h\rangle}
\ge-127(2^n)^7.
`
:::

Formalization note. The $`2E_8` sum is a square, the $`D_{16}^{+}` sum is a
sum of squares after a fourfold convolution, and the $`F_{16}` sum is a
nonnegative four-cycle trace. Splitting the complete sum into injective and
rank-deficient maps loses at most $`127(2^n)^7`, since every character product
is at most one. Postcomposition by affine automorphisms identifies the fibers
over distinct injective images and gives them one common positive cardinality;
division by this cardinality yields the orbit bound. This is the repaired
orbit-level substitute for the overextended disjoint-three-flat step in
{Citations.citet carletMesnager2007}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-sixteen-residual-cover" (parent := "carlet-chapter-4") (lean := "CryptBoolean.sevenVariableAffineMaskWord, CryptBoolean.rankDeficientSevenVariableAffineMaskImageWords, CryptBoolean.card_rankDeficientSevenVariableAffineMaskImageWords_le, CryptBoolean.HasRankAtMostSixWeightSixteenDeficientAffineMaskCover, CryptBoolean.hasRankAtMostSixWeightSixteenDeficientAffineMaskCover, CryptBoolean.orderTwoWeightSixteenRankAtMostSixResidualWords_subset_affineMaskImage_of_cover, CryptBoolean.card_orderTwoWeightSixteenRankAtMostSixResidualWords_le, CryptBoolean.orderTwoWeightSixteenRankAtMostSixResidualCharacterSum, CryptBoolean.orderTwoWeightSixteenRankAtMostSixResidualCharacterSum_ge") (uses := "carlet-4-higher-order-order-two-weight-sixteen-rank-reduction") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-sixteen, low-rank, residual-cover, fidelity-exact-finite-core")
*Project bridge: rank-at-most-six residual cover.* For $`n\ge3`, every
weight-sixteen word of $`R(n-3,n)` whose support-affine-span dimension is at
most six is the image of an arbitrary mask on $`V_7` under a rank-deficient
affine map $`V_7\to V_n`. Hence the residual family has cardinality at most
$$`
127\cdot2^{128}(2^n)^7,
`
and its character sum is at least the negative of this quantity.
:::

Formalization note. A padded basis of the support-difference span supplies
the rank-deficient affine map, while the inverse image of the support supplies
the mask. There are at most $`127(2^n)^7` such affine maps and exactly
$`2^{128}` masks; taking images cannot increase cardinality, and a sum of
$`\{-1,1\}` characters is bounded below by minus the number of words. This
deliberately coarse cover handles the weight-sixteen words missed by the
non-minimal disjoint-flat classification of
{Citations.citet borissovManevNikova2003}[]; the existence of minimal
weight-sixteen words is documented by {Citations.citet borissovManev2004}[].

:::lemma_ "carlet-4-higher-order-order-two-weight-sixteen-character-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.orderTwoWeightSixteenCharacterSum_ge_rankSevenClassification") (uses := "carlet-4-higher-order-order-two-weight-sixteen-rank-seven-classification, carlet-4-higher-order-order-two-weight-sixteen-orbit-sos, carlet-4-higher-order-order-two-weight-sixteen-residual-cover") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, dual-code, weight-sixteen, character-sum, fidelity-exact")
*Project bridge: aggregate weight-sixteen character bound.* For $`n\ge3`
and every $`f:V_n\to\mathbb F_2`,
$$`
M_{16}(f)=
\sum_{\substack{h\in R(n-3,n)\\\operatorname{wt}(h)=16}}
(-1)^{\langle f,h\rangle}
\ge-\bigl(3\cdot127+127\cdot2^{128}\bigr)(2^n)^7.
`
:::

Formalization note. The rank-seven classification and the low-rank cover
partition the weight-sixteen words into the three canonical affine orbits and
the rank-at-most-six residual family. The orbit estimates and the residual
cardinality estimate then add without requiring a universal disjoint-flat
representation.

:::lemma_ "carlet-4-higher-order-order-two-moment-difference" (parent := "carlet-chapter-4") (lean := "CryptBoolean.tuplePointParityMomentDifference_zero_ge, CryptBoolean.tuplePointParityMomentDifference_eight_bounds, CryptBoolean.tuplePointParityMomentDifference_twelve_bounds, CryptBoolean.tuplePointParityMomentDifference_fourteen_bounds, CryptBoolean.tuplePointParityMomentDifference_sixteen_bounds, CryptBoolean.orderTwoCorrelationPowerSum_difference_eq_lowWeights, CryptBoolean.orderTwoCorrelationPowerSum_difference_ge_of_weightSixteenCharacterSum") (uses := "carlet-4-higher-order-order-two-weight-eight-bound, carlet-4-higher-order-order-two-weight-twelve-bound, carlet-4-higher-order-order-two-weight-fourteen-bound, carlet-4-higher-order-order-two-weight-sixteen-character-bound") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, moment-difference, low-weight-spectrum, reference-91, fidelity-exact-conditional-core")
*Project bridge: seventh/eighth moment-difference estimate.* Put $`q=2^n`.
For $`n\ge7`, the exact dual-weight decomposition gives
$$`
S_8(f)-15qS_7(f)
=|R(2,n)|\sum_{w\in\{0,8,12,14,16\}}
\Delta_w(n)M_w(f),
`
where $`\Delta_w(n)=N_8(w)-15qN_7(w)`. If
$`M_{16}(f)\ge-Bq^7` with $`B\ge0`, then
$$`
S_8(f)-15qS_7(f)
\ge-\bigl(133000020000000+21000000000000B\bigr)
|R(2,n)|q^7.
`
:::

Formalization note. Exact tuple-count polynomials provide one-sided bounds
for the five coefficients $`\Delta_w`; the weight-eight, twelve, and fourteen
sum estimates control the corresponding terms, leaving only the parameter
$`B` for weight sixteen. This is the quantitative meeting point of
the finite classification and moment branches.

:::lemma_ "carlet-4-higher-order-order-two-asymptotic-upper" (parent := "carlet-chapter-4") (lean := "CryptBoolean.reedMuller_card_mul_two_pow_seven_le_orderTwoCorrelationPowerSum_seven, CryptBoolean.orderTwoCorrelationPowerSum_eight_div_seven_ge_of_card_scaled, CryptBoolean.sqrt_fifteen_mul_sqrtTwo_pow_sub_sqrt_le_momentRatio, CryptBoolean.maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference, CryptBoolean.eventually_maximumHigherOrderNonlinearity_two_cast_le_of_card_scaled_moment_difference") (uses := "carlet-4-higher-order-order-two-moment-ratio, carlet-4-higher-order-order-two-moment-difference") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, order-two, asymptotic-upper-bound, reference-91, fidelity-exact-conditional-core")
*Project bridge: order-two asymptotic extraction.* If some $`K\ge0`
satisfies, for every $`f:V_n\to\mathbb F_2`,
$$`
15\cdot2^nS_7(f)-K|R(2,n)|(2^n)^7\le S_8(f),
`
then
$$`
\rho(2,n)\le
2^{n-1}-\frac{\sqrt{15}}2(\sqrt2)^n+\frac{\sqrt K}{2}.
`
The same implication holds eventually when the moment hypothesis holds
eventually and uniformly in $`f`.
:::

Formalization note. Jensen's inequality and the exact second moment give
$`S_7(f)\ge|R(2,n)|(2^n)^7`. Division by this denominator, the consecutive
moment-ratio inequality, and one square-root estimate expose the sharp
$`\sqrt{15}/2` coefficient.

:::lemma_ "carlet-4-higher-order-general-r-propagation" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_maximumHigherOrderNonlinearity_cast_le_of_card_scaled_moment_difference") (uses := "carlet-4-higher-order-plotkin-induction, carlet-4-higher-order-order-two-asymptotic-upper") (tags := "project-bridge, carlet, chapter-4, higher-order-nonlinearity, fixed-order, asymptotic-upper-bound, reference-91, fidelity-exact-conditional-core")
*Project bridge: propagation from order two to fixed order.* Suppose there is
$`K\ge0` such that eventually, uniformly in $`f:V_n\to\mathbb F_2`,
$$`
15\cdot2^nS_7(f)-K|R(2,n)|(2^n)^7\le S_8(f).
`
For every fixed $`r\ge2`, there is $`D\ge0` such that, for all $`n\ge r`,
$$`
\rho(r,n)\le
2^{n-1}-\frac{\sqrt{15}}2(1+\sqrt2)^{r-2}(\sqrt2)^n
+D(n+1)^{r-2}.
`
:::

Formalization note. The preceding order-two estimate supplies the base case.
Iterating the Plotkin recurrence multiplies the square-root coefficient by
$`1+\sqrt2` at each order and turns the bounded base remainder into a
polynomial error of degree $`r-2`.

:::theorem "carlet-4-higher-order-general-bounds" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_maximumHigherOrderNonlinearity_cast_le_sharp") (uses := "carlet-4-higher-order-general-r-propagation, carlet-4-higher-order-order-two-weight-sixteen-character-bound") (tags := "carlet, chapter-4, higher-order-nonlinearity, asymptotic-upper-bound, page-53, fidelity-exact")
*Sharp asymptotic upper bound for higher-order nonlinearity (Carlet, p. 53).*
Define
$`\rho(r,n)=\max_f\operatorname{nl}_r(f)`. For fixed $`r\ge2`, the cited
asymptotic upper bound is
$$`
\rho(r,n)\le
2^{n-1}-\frac{\sqrt{15}}2(1+\sqrt2)^{r-2}2^{n/2}
+O(n^{r-2}).
`
:::

Formalization note. The upper constant comes from the Carlet--Mesnager
order-two covering-radius theorem {Citations.citep carletMesnager2007}[]. The
moment ratio reduces the order-two estimate to the seventh/eighth moment
difference; dual-code orthogonality and Krawtchouk inversion reduce that
difference to weights $`0,8,12,14,16`. At weight sixteen, the
disjoint-three-flat description of
{Citations.citet borissovManevNikova2003}[] covers the non-minimal case but
not the minimal words exhibited by {Citations.citet borissovManev2004}[]. The
complete alternative is the rank-seven three-orbit classification of
{Citations.citet mesnagerOblaukhov2022}[] together with the rank-at-most-six
affine-mask cover above. Their character estimates feed the moment inequality,
and Plotkin induction propagates the resulting $`\sqrt{15}/2` coefficient by
the factor $`1+\sqrt2` at every increase of order.

:::proposition "carlet-4-prop-13" (parent := "carlet-chapter-4") (lean := "CryptBoolean.hammingWeight_translate, CryptBoolean.hammingWeight_booleanDerivative_le_two_mul, CryptBoolean.booleanDerivative_add, CryptBoolean.derivative_higherOrderNonlinearity_le_two_mul, CryptBoolean.maxDerivativeHigherOrderNonlinearity, CryptBoolean.maxDerivativeHigherOrderNonlinearity_le_two_mul, CryptBoolean.proposition_13_first_bound, CryptBoolean.two_mul_higherOrderNonlinearity_le_two_pow, CryptBoolean.autocorrelation_eq_walshTransform_booleanDerivative_zero, CryptBoolean.autocorrelation_eq_two_pow_sub_two_derivative_weight, CryptBoolean.autocorrelation_le_two_pow_sub_two_higherOrderNonlinearity, CryptBoolean.derivativeHigherOrderNonlinearitySum, CryptBoolean.higherOrderNonlinearity_gap_sq_le, CryptBoolean.proposition_13_second_bound, CryptBoolean.proposition_13_second_bound_source_form") (uses := "carlet-4-def-higher-order-nonlinearity, carlet-2-def-2-derivative") (tags := "carlet, chapter-4, proposition-13, pages-54-55, fidelity-exact")
*Proposition 13 (Carlet, pp. 54--55).* Let $`1\le r<n`. Then
$$`
\operatorname{nl}_r(f)
\ge\frac12\max_{a\in V_n}\operatorname{nl}_{r-1}(D_af)
`
and
$$`
\operatorname{nl}_r(f)
\ge2^{n-1}-\frac12
\sqrt{2^{2n}-2\sum_{a\in V_n}\operatorname{nl}_{r-1}(D_af)}.
`
:::
