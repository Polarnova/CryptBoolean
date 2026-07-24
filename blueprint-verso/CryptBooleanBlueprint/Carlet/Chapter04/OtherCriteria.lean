/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter04

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Other criteria" =>

:::definition "carlet-4-other-complexity-definitions" (parent := "carlet-chapter-4") (lean := "CryptBoolean.algebraicThickness, CryptBoolean.exists_affineEquiv_anfSupport_card_eq_algebraicThickness, CryptBoolean.IsConstantOnAffineFlat, CryptBoolean.IsAffineOnAffineFlat, CryptBoolean.IsConstantOnAffineFlat.isAffineOnAffineFlat, CryptBoolean.normality, CryptBoolean.weakNormality, CryptBoolean.normality_le_weakNormality, CryptBoolean.spectralComplexity") (uses := "carlet-2-def-algebraic-degree, carlet-2-affine-invariance, carlet-2-spectral-support-bounds") (tags := "carlet, chapter-4, algebraic-thickness, normality, spectral-complexity, page-67, fidelity-exact-with-derived-laws")
*Algebraic thickness, normality, and spectral complexity (Carlet, p. 67).*
The algebraic thickness of $`f` is the least number of nonzero ANF terms
among functions affinely equivalent to $`f`. Its normality parameter is the
largest dimension of a flat on which $`f` is constant; weak normality permits
an affine restriction. Its spectral complexity is
$$`
|\operatorname{supp}(W_f)|.
`
:::

:::theorem "carlet-4-kth-nonhomomorphicity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.booleanTupleSum, CryptBoolean.booleanTupleOutputSum, CryptBoolean.kthNonhomomorphicity, CryptBoolean.two_mul_two_pow_mul_kthNonhomomorphicity, CryptBoolean.kthNonhomomorphicity_cast_eq_walshMoment, CryptBoolean.kthNonhomomorphicity_cast_eq_carlet_formula, CryptBoolean.IsAffineBooleanFunction, CryptBoolean.isAffineBooleanFunction_iff_nonlinearity_eq_zero, CryptBoolean.abs_walshTransform_le_two_pow, CryptBoolean.sum_walshTransform_evenMoment_le, CryptBoolean.kthNonhomomorphicity_affineFunction, CryptBoolean.kthNonhomomorphicity_cast_le_max, CryptBoolean.kthNonhomomorphicity_cast_eq_max_iff_isAffine, CryptBoolean.carlet_kthNonhomomorphicity_cast_eq_max_iff_isAffine, CryptBoolean.two_pow_pow_succ_le_sum_walshTransform_evenMoment, CryptBoolean.sum_walshTransform_evenMoment_eq_min_iff_isBent, CryptBoolean.kthNonhomomorphicity_cast_min_le, CryptBoolean.kthNonhomomorphicity_cast_eq_min_iff_isBent, CryptBoolean.carlet_kthNonhomomorphicity_cast_eq_min_iff_isBent") (uses := "carlet-2-def-walsh-transform, carlet-2-parseval, carlet-4-rel-36-covering-radius-bent") (tags := "carlet, chapter-4, nonhomomorphicity, page-67, fidelity-exact-carlet-naming")
*The $`k`th nonhomomorphicity (Carlet, p. 67).* Let $`k` be even with
$`4\le k\le2^n`. The number $`\mathrm{NH}_k(f)` of tuples
$`(u_1,\ldots,u_k)` satisfying
$$`
\sum_i u_i=0,
\qquad
\sum_i f(u_i)=0
`
obeys
$$`
\mathrm{NH}_k(f)
=2^{(k-1)n-1}+2^{-n-1}\sum_{u\in V_n}W_f(u)^k.
`
Its maximum $`2^{(k-1)n}` is attained exactly by affine functions, and its
minimum $`2^{(k-1)n-1}+2^{nk/2-1}` exactly by bent functions.
:::

Formalization note. Carlet calls the zero-sum/even-output count
$`\mathrm{NH}_k`. Reference 357 calls that same quantity homomorphicity and
reserves nonhomomorphicity for the complementary odd-output count; the Lean
declarations follow Carlet's convention.

:::theorem "carlet-4-affine-reindex-first-resilient" (parent := "carlet-chapter-4") (lean := "CryptBoolean.walshCoordinateLinearMap, CryptBoolean.walshCoordinateLinearMap_injective, CryptBoolean.walshReindexLinearEquiv, CryptBoolean.bentDualFrequency_walshReindexLinearEquiv_single, CryptBoolean.walshTransform_linearReindex_cast, CryptBoolean.bentDualFrequency_zero, CryptBoolean.isBalanced_linearReindex, CryptBoolean.exists_linearEquiv_isResilient_one") (uses := "carlet-4-theorem-3, carlet-4-resiliency-translation-invariance, carlet-2-def-affine-functions") (tags := "carlet, chapter-4, resiliency, affine-reindexing, page-68, fidelity-exact")
*Affine reindexing to first-order resiliency (Carlet, p. 68).* Suppose $`f`
is balanced and its zero-Walsh set contains $`n` linearly independent
vectors. Then there is a linear automorphism $`L:V_n\to V_n` such that
$$`
f\circ L
`
is $`1`-resilient.
:::
