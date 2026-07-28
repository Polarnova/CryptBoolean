/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.NormalExtension

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Normal and non-normal bent functions" =>

:::definition "carlet-6-def-8-normal-extension" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsNormalExtension, CryptBoolean.IsNormalExtension.isBent_left, CryptBoolean.IsNormalExtension.isBent_right, CryptBoolean.isNormalExtension_refl") (uses := "carlet-6-def-7-bent") (tags := "carlet, chapter-6, definition-8, normal-extension, pages-107-108, fidelity-exact-coordinate-invariant-form")
*Normal extension (Carlet, Definition 8, pp. 107--108).* Let
$`\beta:V_k\to\mathbb F_2` and $`f:V_n\to\mathbb F_2` be bent. Write
$`\beta\preccurlyeq f` when there are a nonnegative integer $`m` and a
linear isomorphism
$$`
L:V_k\times V_m\times V_m\longrightarrow V_n
`
such that
$$`
f\bigl(L(u,w,0)\bigr)=\beta(u)
\qquad(u\in V_k,\ w\in V_m).
`
Equivalently, $`V_n=U\oplus W_1\oplus W_2` with
$`\dim W_1=\dim W_2`, and the restriction of $`f` to
$`U\oplus W_1` is $`\beta` pulled back from $`U`. Every bent function is
a normal extension of itself.
:::

:::theorem "carlet-6-normal-extension-composition-duality" (parent := "carlet-chapter-6") (lean := "CryptBoolean.walshAdjointLinearEquiv, CryptBoolean.walshTransform_comp_linearEquiv, CryptBoolean.bentDual_comp_linearEquiv, CryptBoolean.bentDual_canonical_normalExtension, CryptBoolean.IsNormalExtension.trans, CryptBoolean.IsNormalExtension.bentDual") (uses := "carlet-6-def-8-normal-extension, carlet-6-dual, carlet-6-rel-46-dual-poisson") (tags := "carlet, chapter-6, normal-extension, duality, transitivity, page-108, fidelity-exact")
*Composition and duality of normal extensions (Carlet, p. 108).* The
relation $`\preccurlyeq` is transitive. Moreover, if
$`\beta\preccurlyeq f`, then
$$`
\widetilde\beta\preccurlyeq\widetilde f.
`
In standard coordinates, duality exchanges the two equal complementary
summands.
:::

:::theorem "carlet-6-normal-zero-dimensional-characterization" (parent := "carlet-chapter-6") (lean := "CryptBoolean.zeroDimensionalBooleanFunction, CryptBoolean.zeroDimensionalBooleanFunction_apply, CryptBoolean.isBent_zeroDimensionalBooleanFunction, CryptBoolean.IsSubspaceNormal, CryptBoolean.IsAffineNormalExtension, CryptBoolean.isKNormal_comp_affineEquiv_iff, CryptBoolean.exists_isNormalExtension_zeroDimensional_iff_isSubspaceNormal, CryptBoolean.exists_isAffineNormalExtension_zeroDimensional_iff_isKNormal, CryptBoolean.exists_isKNormal_not_isNormalExtension_zeroDimensional") (uses := "carlet-6-def-8-normal-extension, carlet-5-def-4-normality, carlet-2-affine-invariance") (tags := "carlet, chapter-6, normality, zero-dimensional-extension, page-108, fidelity-source-correction")
*Zero-dimensional normal extensions (Carlet, p. 108; corrected normality convention).* Let $`f:V_n\to\mathbb F_2` be bent. If normality means that
$`f` is constant on an $`n/2`-dimensional linear subspace, then
$$`
f\text{ is normal}
\quad\Longleftrightarrow\quad
\varepsilon\preccurlyeq f
\text{ for some }\varepsilon\in\mathbb F_2.
`
For the affine-flat convention of Definition 4, the exact statement is
instead
$$`
f\text{ is }(n/2)\text{-normal}
\quad\Longleftrightarrow\quad
\varepsilon\preccurlyeq(f\circ A)
`
for some $`\varepsilon\in\mathbb F_2` and some affine automorphism $`A`
of $`V_n`.

The affine automorphism cannot in general be omitted. The two-variable
function
$$`
f(x_1,x_2)=(x_1+1)(x_2+1)
`
is bent and constant on a one-dimensional affine flat, but it is not
constant on any one-dimensional linear subspace.
:::

:::proposition "carlet-6-prop-29-direct-sum-normality" (parent := "carlet-chapter-6") (lean := "CryptBoolean.AreLinearlyEquivalentOrComplementary, CryptBoolean.isSubspaceNormal_booleanDirectSum_iff") (uses := "carlet-6-direct-sum, carlet-6-def-8-normal-extension, carlet-6-normal-zero-dimensional-characterization, carlet-5-affine-flat-restriction-bound") (tags := "carlet, chapter-6, proposition-29, normality, direct-sum, page-108, fidelity-exact-linear-subspace-convention")
*Proposition 29 (Carlet, p. 108).* Let
$`f_i:V_i\to\mathbb F_2` be bent for $`i=1,2`. The direct sum
$`f_1\oplus f_2` is normal if and only if there are bent functions
$`\beta_i` such that $`\beta_i\preccurlyeq f_i` for $`i=1,2` and either
$`\beta_1` is linearly equivalent to $`\beta_2`, or $`\beta_1` is linearly
equivalent to $`\beta_2+1`.
:::

:::proposition "carlet-6-prop-30-normality-descends" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isSubspaceNormal_comp_linearEquiv_iff, CryptBoolean.IsNormalExtension.isSubspaceNormal_left") (uses := "carlet-6-def-8-normal-extension, carlet-6-normal-zero-dimensional-characterization, carlet-6-prop-31-normal-extension-replacement, carlet-5-affine-flat-restriction-bound") (tags := "carlet, chapter-6, proposition-30, normality, normal-extension, page-108, fidelity-exact-linear-subspace-convention")
*Proposition 30 (Carlet, p. 108).* If $`\beta\preccurlyeq f` and the bent
function $`f` is normal, then the bent function $`\beta` is normal.
:::

:::proposition "carlet-6-prop-31-normal-extension-replacement" (parent := "carlet-chapter-6") (lean := "CryptBoolean.canonicalNormalExtensionReplacement, CryptBoolean.canonicalNormalExtensionReplacement_apply_append, CryptBoolean.isBent_canonicalNormalExtensionReplacement, CryptBoolean.normalExtensionReplacement, CryptBoolean.normalExtensionReplacement_apply, CryptBoolean.normalExtensionReplacement_isNormalExtension") (uses := "carlet-6-def-8-normal-extension, carlet-6-normal-extension-composition-duality, carlet-6-rel-46-dual-poisson") (tags := "carlet, chapter-6, proposition-31, normal-extension, replacement, page-108, fidelity-exact-coordinate-invariant-form")
*Proposition 31 (Carlet, p. 108).* Let $`\beta` be bent on $`U`, let
$`f` be bent on $`U\times W\times W`, and suppose
$`\beta\preccurlyeq f` through
$$`
f(x,y,0)=\beta(x).
`
For any bent $`\beta':U\to\mathbb F_2`, define
$$`
f'(x,y,z)=
\begin{cases}
\beta'(x),&z=0,\\
f(x,y,z),&z\ne0.
\end{cases}
`
Then $`f'` is bent and $`\beta'\preccurlyeq f'`.
:::
