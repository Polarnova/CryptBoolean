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

#doc (Manual) "Linear structures" =>

:::definition "carlet-4-def-linear-kernel" (parent := "carlet-chapter-4") (lean := "CryptBoolean.IsLinearStructure, CryptBoolean.isLinearStructure_zero, CryptBoolean.booleanDerivative_add_direction, CryptBoolean.IsLinearStructure.add, CryptBoolean.IsLinearStructure.smul, CryptBoolean.linearKernel, CryptBoolean.mem_linearKernel") (uses := "carlet-2-def-2-derivative") (tags := "carlet, chapter-4, linear-kernel, page-59, fidelity-exact")
*Linear kernel (Carlet, p. 59).* Define
$$`
\ker_{\mathrm{lin}}(f)
=\{e\in V_n:D_ef\text{ is constant}\}.
`
This is an $`\mathbb F_2`-linear subspace of $`V_n`, and its elements are
the linear structures of $`f`.
:::

:::proposition "carlet-4-prop-14" (parent := "carlet-chapter-4") (lean := "CryptBoolean.HasSeparatedLinearStructureNormalForm, CryptBoolean.finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm, CryptBoolean.exists_nonzero_linearStructure_iff_exists_single_coordinate_normalForm") (uses := "carlet-4-def-linear-kernel, carlet-2-def-affine-functions") (tags := "carlet, chapter-4, proposition-14, linear-structures, page-59, fidelity-exact-dimension-split")
*Proposition 14 (Carlet, p. 59).* A function $`f` has a nonzero linear
structure if and only if it is linearly equivalent to
$$`
g(x_1,\ldots,x_{n-1})+\varepsilon x_n.
`
More generally, $`\dim\ker_{\mathrm{lin}}(f)\ge k` if and only if $`f` is
linearly equivalent to
$$`
g(x_1,\ldots,x_{n-k})
+\sum_{i=n-k+1}^{n}\varepsilon_i x_i.
`
:::

Formalization note. The general theorem writes the ambient dimension as
$`m+k`; this is exactly the feasible range of Carlet's $`n-k` and avoids
truncated natural-number subtraction.

:::corollary "carlet-4-linear-kernel-nonlinearity-bound" (parent := "carlet-chapter-4") (lean := "CryptBoolean.nonlinearity_cast_le_of_finrank_linearKernel_eq, CryptBoolean.nonlinearity_cast_le_of_exists_nonzero_linearStructure") (uses := "carlet-4-prop-14, carlet-4-rel-36-covering-radius-bent") (tags := "carlet, chapter-4, linear-kernel, nonlinearity, page-59, fidelity-exact-real-rpow")
*Nonlinearity bound from the linear kernel (Carlet, p. 59).* If
$`\dim\ker_{\mathrm{lin}}(f)=k`, then
$$`
\operatorname{nl}(f)
\le2^{n-1}-2^{(n+k-2)/2}.
`
In particular, a nonzero linear structure gives
$`\operatorname{nl}(f)\le2^{n-1}-2^{(n-1)/2}`.
:::

:::theorem "carlet-4-hyperplane-walsh-autocorrelation" (parent := "carlet-chapter-4") (lean := "CryptBoolean.walshHyperplane, CryptBoolean.mem_walshHyperplane_iff, CryptBoolean.natCard_walshHyperplane, CryptBoolean.sum_walshTransform_sq_hyperplane_coset") (uses := "carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin") (tags := "carlet, chapter-4, walsh, autocorrelation, pages-59-60, fidelity-exact")
*Hyperplane Walsh--autocorrelation identity (Carlet, pp. 59--60).* Let
$`e\ne0`, $`E=\{0,e\}^{\perp}`, and $`a\in V_n`. Then
$$`
\sum_{u\in a+E}W_f(u)^2
=2^{n-1}\left(2^n+(-1)^{a\mathbin\cdot e}\Delta_f(e)\right).
`
:::

:::proposition "carlet-4-prop-15" (parent := "carlet-chapter-4") (lean := "CryptBoolean.walshSupport, CryptBoolean.mem_walshSupport, CryptBoolean.booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane, CryptBoolean.booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl, CryptBoolean.isBalanced_of_booleanDerivative_eq_one, CryptBoolean.isLinearStructure_iff_booleanDerivative_eq_zero_of_not_balanced, CryptBoolean.walshSupportSpan, CryptBoolean.walshSupportRank, CryptBoolean.no_nonzero_null_derivative_iff_walshSupportSpan_eq_top, CryptBoolean.walshSupportRank_eq_n_iff, CryptBoolean.no_nonzero_linearStructure_iff_walshSupportRank_eq_n_of_not_balanced") (uses := "carlet-4-hyperplane-walsh-autocorrelation, carlet-4-def-linear-kernel, carlet-2-def-walsh-transform") (tags := "carlet, chapter-4, proposition-15, linear-structures, page-60, fidelity-exact")
*Proposition 15 (Carlet, p. 60).* For $`e\ne0`, one has $`D_ef=0` if and
only if
$$`
\operatorname{supp}(W_f)\subseteq\{0,e\}^{\perp},
`
and $`D_ef=1` if and only if the Walsh support is contained in the other
coset of this hyperplane. The latter condition implies that $`f` is balanced.
If $`f` is not balanced, it has no nonzero linear structure exactly when its
Walsh support has rank $`n`.
:::

:::theorem "carlet-4-distance-to-linear-structures" (parent := "carlet-chapter-4") (lean := "CryptBoolean.HasNonzeroLinearStructure, CryptBoolean.distanceToLinearStructures, CryptBoolean.distanceToLinearStructures_le_hammingDistance, CryptBoolean.exists_hammingDistance_eq_distanceToLinearStructures, CryptBoolean.abs_autocorrelation_le_absoluteIndicator, CryptBoolean.distanceToLinearStructures_cast_eq, CryptBoolean.distanceToLinearStructures_le_nonlinearity, CryptBoolean.distanceToLinearStructures_le_two_pow, CryptBoolean.absoluteIndicator_eq_zero_iff_isBent, CryptBoolean.distanceToLinearStructures_eq_two_pow_iff_isBent") (uses := "carlet-4-def-linear-kernel, carlet-2-def-hamming-distance, carlet-2-def-autocorrelation, carlet-4-rel-36-covering-radius-bent") (tags := "carlet, chapter-4, linear-structures, distance, page-60, fidelity-exact-with-zero-dimensional-convention")
*Distance to functions with a nonzero linear structure (Carlet, p. 60).*
For $`n\ge2`, let $`d_{\mathrm{LS}}(f)` be the least Hamming distance from
$`f` to such a function. Then
$$`
d_{\mathrm{LS}}(f)
=2^{n-2}-\frac14\max_{e\ne0}|\Delta_f(e)|.
`
Consequently $`d_{\mathrm{LS}}(f)\le\operatorname{nl}(f)` and
$`d_{\mathrm{LS}}(f)\le2^{n-2}`; equality in the latter bound holds exactly
for bent $`f`.
:::
