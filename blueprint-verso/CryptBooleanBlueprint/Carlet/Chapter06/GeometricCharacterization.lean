/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.GeometricCharacterization

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Geometric characterization" =>

:::lemma_ "carlet-6-lemma-3-subspace-indicators" (parent := "carlet-chapter-6") (lean := "CryptBoolean.linearSubspaceIndicatorInt, CryptBoolean.halfSubspaceCombination, CryptBoolean.ambientFunctionalKernel, CryptBoolean.mem_ambientFunctionalKernel_iff, CryptBoolean.finrank_ambientFunctionalKernel, CryptBoolean.nonzeroDualFinset, CryptBoolean.mem_nonzeroDualFinset, CryptBoolean.card_nonzeroDualFinset, CryptBoolean.functionalKernelCombination_modeq, CryptBoolean.HasHalfSubspaceRepresentation, CryptBoolean.hasHalfSubspaceRepresentation_indicator_of_finrank_eq, CryptBoolean.hasHalfSubspaceRepresentation_indicator_of_half_le_finrank, CryptBoolean.rankTwoIntermediateSubspace, CryptBoolean.mem_rankTwoIntermediateSubspace_iff, CryptBoolean.finrank_rankTwoIntermediateSubspace, CryptBoolean.rankTwoSubspaceDiamond, CryptBoolean.hasHalfSubspaceRepresentation_scaledIndicator_of_finrank_le_half, CryptBoolean.carletLemma3") (tags := "carlet, chapter-6, lemma-3, subspace-indicators, section-6-6-2, page-99, fidelity-exact")
*Lemma 3 (Carlet, p. 99).* Let $`n` be even and let $`F\le V_n` have
dimension $`d`. There are $`n/2`-dimensional subspaces
$`E_1,\ldots,E_k`, integers $`m_1,\ldots,m_k`, and an integer $`m` such
that, pointwise on $`V_n`,
$$`
2^{n/2-d}1_F\equiv m+\sum_{i=1}^k m_i1_{E_i}
  \pmod {2^{n/2}}
\qquad(d<n/2),
`
and there are $`n/2`-dimensional subspaces $`E_1,\ldots,E_k` and integers
$`m_1,\ldots,m_k` such that
$$`
1_F\equiv\sum_{i=1}^k m_i1_{E_i}
  \pmod {2^{n/2}}
\qquad(d>n/2).
`
:::

:::theorem "carlet-6-theorem-12-geometric-characterization" (parent := "carlet-chapter-6") (lean := "CryptBoolean.originIndicatorInt, CryptBoolean.geometricBentExpression, CryptBoolean.perpendicularGeometricBentExpression, CryptBoolean.integerWalshTransform_linearSubspaceIndicatorInt, CryptBoolean.integerWalshTransform_originIndicatorInt, CryptBoolean.integerWalshTransform_bitValueInt_eq_booleanNNFFourierCoeffInt, CryptBoolean.integerWalshTransform_halfSubspaceCombination, CryptBoolean.integerWalshTransform_geometricBentExpression, CryptBoolean.HasGeometricBentCongruence, CryptBoolean.isBent_of_hasGeometricBentCongruence, CryptBoolean.HasExactGPSRepresentation, CryptBoolean.isBent_and_bitValueInt_bentDual_of_exactGPSRepresentation, CryptBoolean.numericalMonomialInt, CryptBoolean.numericalMonomialInt_cast, CryptBoolean.numericalMonomialInt_eq_sum_coordinateZeroIndicators, CryptBoolean.finrank_coordinateZeroSubspace, CryptBoolean.linearSubspaceIndicatorInt_coordinateZeroSubspace_univ, CryptBoolean.bitValueInt_eq_sum_booleanNumericalCoeffInt_mul_numericalMonomialInt, CryptBoolean.hasGeometricBentCongruence_of_isBent, CryptBoolean.isBent_iff_hasGeometricBentCongruence") (uses := "carlet-6-prop-23-nnf-characterization, carlet-6-lemma-3-subspace-indicators, carlet-6-lemma-2-walsh-congruence, carlet-2-prop-7-subspace-indicator, carlet-6-dual") (tags := "carlet, chapter-6, theorem-12, relation-51, generalized-partial-spread, section-6-6-2, page-99, fidelity-exact")
*Theorem 12 (Carlet, Relation (51), p. 99).* Let $`n\ge2` be even. A
Boolean function $`f:V_n\to\mathbb F_2` is bent if and only if there are
$`n/2`-dimensional subspaces $`E_1,\ldots,E_k\le V_n` and integers
$`m_1,\ldots,m_k` such that, for every $`x\in V_n`,
$$`
f(x)\equiv\sum_{i=1}^k m_i1_{E_i}(x)-2^{n/2-1}\delta_0(x)
  \pmod {2^{n/2}}.
`
If this congruence is an equality over the integers, then $`f` belongs to
the generalized partial-spread class and its dual is
$$`
\widetilde f(x)=
\sum_{i=1}^k m_i1_{E_i^\perp}(x)-2^{n/2-1}\delta_0(x).
`
In particular, the dual also belongs to the generalized partial-spread
class.
:::
