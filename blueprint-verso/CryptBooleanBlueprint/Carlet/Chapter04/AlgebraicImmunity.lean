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

#doc (Manual) "Algebraic immunity" =>

:::definition "carlet-4-def-annihilator-algebraic-immunity" (parent := "carlet-chapter-4") (lean := "CryptBoolean.support_mul, CryptBoolean.booleanFunction_mul_self, CryptBoolean.booleanFunction_mul_complement, CryptBoolean.IsAnnihilator, CryptBoolean.annihilatorIdeal, CryptBoolean.mem_annihilatorIdeal_iff, CryptBoolean.isAnnihilator_iff_mem_annihilatorIdeal, CryptBoolean.IsAlgebraicImmunityWitness, CryptBoolean.algebraicImmunityCandidates, CryptBoolean.mem_algebraicImmunityCandidates, CryptBoolean.algebraicImmunityCandidates_nonempty, CryptBoolean.algebraicImmunity, CryptBoolean.algebraicImmunity_le_functionAlgebraicDegree, CryptBoolean.exists_witness_functionAlgebraicDegree_eq_algebraicImmunity, CryptBoolean.IsAnnihilator.comp_affineEquiv, CryptBoolean.IsAlgebraicImmunityWitness.comp_affineEquiv, CryptBoolean.algebraicImmunity_comp_affineEquiv_le, CryptBoolean.algebraicImmunity_comp_affineEquiv") (uses := "carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree, carlet-2-def-support-weight") (tags := "carlet, chapter-4, annihilator, algebraic-immunity, pages-61-62, fidelity-exact")
*Annihilators and algebraic immunity (Carlet, pp. 61--62).* Pointwise
multiplication satisfies
$$`
\operatorname{supp}(fg)
=\operatorname{supp}(f)\cap\operatorname{supp}(g).
`
A nonzero $`g` with $`fg=0` is an annihilator of $`f`; all such
annihilators together with zero form the ideal of multiples of $`f+1`.
Define
$$`
\operatorname{AI}(f)=
\min\{\deg(g):g\ne0,\ fg=0\text{ or }(f+1)g=0\}.
`
Algebraic immunity is invariant under affine equivalence.
:::

:::theorem "carlet-4-low-degree-relation-equivalence" (parent := "carlet-chapter-4") (lean := "CryptBoolean.exists_lowDegreeRelation_iff_exists_algebraicImmunityWitness") (uses := "carlet-4-def-annihilator-algebraic-immunity") (tags := "carlet, chapter-4, algebraic-immunity, page-62, fidelity-exact")
*Low-degree relation equivalence (Carlet, p. 62).* There exist $`g\ne0`
and $`h` such that
$$`
fg=h,
\qquad \deg(g)\le d,
\qquad \deg(h)\le d
`
if and only if there exists $`q\ne0` of degree at most $`d` such that
$`fq=0` or $`(f+1)q=0`.
:::

:::theorem "carlet-4-annihilator-linear-system" (parent := "carlet-chapter-4") (lean := "CryptBoolean.extendLowDegreeCoefficients, CryptBoolean.reedMullerAnfEquiv, CryptBoolean.annihilatorEvaluationLinearMap, CryptBoolean.mem_ker_annihilatorEvaluationLinearMap_iff, CryptBoolean.annihilatorEvaluationLinearMap_domain_finrank, CryptBoolean.annihilatorEvaluationLinearMap_codomain_finrank") (uses := "carlet-4-def-annihilator-algebraic-immunity, carlet-2-anf-existence-uniqueness, carlet-2-def-support-weight") (tags := "carlet, chapter-4, annihilator, linear-system, page-62, fidelity-exact-explicit-coefficient-space")
*Annihilator evaluation system (Carlet, p. 62).* A function $`g` of degree
at most $`d` annihilates $`f` exactly when its low-degree ANF coefficient
vector belongs to the kernel of evaluation on $`\operatorname{supp}(f)`.
The homogeneous system has
$$`
\sum_{i=0}^{d}\binom ni
`
unknown coefficients and $`w_H(f)` equations.
:::

:::theorem "carlet-4-ai-upper-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.functionAlgebraicDegree_affineMap_coordinate_le_one_general, CryptBoolean.functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card_general, CryptBoolean.functionAlgebraicDegree_comp_affineMap_le_general, CryptBoolean.algebraicImmunity_comp_surjectiveAffineMap_le, CryptBoolean.algebraicImmunity_le_ceiling_half, CryptBoolean.HasSurjectiveAffineFactorization, CryptBoolean.algebraicImmunity_le_ceiling_half_of_hasSurjectiveAffineFactorization, CryptBoolean.hasSurjectiveAffineFactorization_of_hasSeparatedLinearStructureNormalForm, CryptBoolean.algebraicImmunity_le_ceiling_half_add_one_of_hasSeparatedLinearStructureNormalForm, CryptBoolean.algebraicImmunity_le_ceiling_half_add_one_of_linearKernel_finrank_ge") (uses := "carlet-4-low-degree-relation-equivalence, carlet-4-annihilator-linear-system, carlet-4-prop-14") (tags := "carlet, chapter-4, algebraic-immunity, upper-bound, page-62, fidelity-exact-surjective-factorization-generalization")
*Upper bounds on algebraic immunity (Carlet, p. 62).* Every
$`f:V_n\to\mathbb F_2` satisfies
$$`
\operatorname{AI}(f)\le\left\lceil\frac n2\right\rceil.
`
If $`f` is affinely equivalent to a function on only $`k` variables, then
$`\operatorname{AI}(f)\le\lceil k/2\rceil`. If
$`\dim\ker_{\mathrm{lin}}(f)=n-k`, then
$`\operatorname{AI}(f)\le\lceil k/2+1\rceil`.
:::

Formalization note. Depending on at most $`k` affine coordinates is
represented by factorization through a surjective affine map to $`V_k`. The
linear-kernel theorem is slightly stronger in its hypothesis form: a contained
tail subspace of the stated dimension suffices, so equality of kernel dimension
is an immediate specialization.

:::definition "carlet-4-fast-algebraic-optimality" (parent := "carlet-chapter-4") (lean := "CryptBoolean.two_pow_lt_sum_choose_add_sum_choose_of_add_ge, CryptBoolean.sum_choose_add_sum_choose_gt_iff, CryptBoolean.fastAlgebraicRelationLinearMap, CryptBoolean.exists_fastAlgebraicRelation_of_add_ge, CryptBoolean.IsFastAlgebraicallyOptimal, CryptBoolean.isFastAlgebraicallyOptimal_iff_no_lowDegreeRelation, CryptBoolean.algebraicImmunity_le_degree_of_mul_eq_of_ne_zero") (uses := "carlet-4-def-annihilator-algebraic-immunity, carlet-4-annihilator-linear-system") (tags := "carlet, chapter-4, fast-algebraic, page-63, fidelity-exact")
*Optimality against fast algebraic relations (Carlet, p. 63).* If
$$`
\sum_{i=0}^{e}\binom ni+
\sum_{i=0}^{d}\binom ni>2^n,
`
equivalently $`e+d\ge n`, then there exist $`g\ne0` and $`h` with
$`fg=h`, $`\deg(g)\le e`, and $`\deg(h)\le d`. The function $`f` is optimal
against such relations when none exists with
$`\deg(g)+\deg(h)<n`. Whenever $`fg=h\ne0`, one also has
$`\deg(h)\ge\operatorname{AI}(f)`.
:::
