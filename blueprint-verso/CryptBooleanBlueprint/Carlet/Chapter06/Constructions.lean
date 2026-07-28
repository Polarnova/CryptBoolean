/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandBalance
import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandBentSubspace
import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandGeneral
import CryptBoolean.Carlet.Chapter06.PartialSpreads

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Primary constructions of bent functions" =>

:::theorem "carlet-6-maiorana-mcfarland" (parent := "carlet-chapter-6") (lean := "CryptBoolean.booleanMaioranaMcFarlandPermutation, CryptBoolean.booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks, CryptBoolean.isMaioranaMcFarland_of_eq_permutation, CryptBoolean.walshTransform_maioranaMcFarlandPermutation, CryptBoolean.isBent_of_maioranaMcFarlandPermutation, CryptBoolean.isBent_booleanMaioranaMcFarlandPermutation, CryptBoolean.bentDual_maioranaMcFarlandPermutation, CryptBoolean.isBent_iff_bijective_maioranaMcFarland") (uses := "carlet-6-def-7-bent, carlet-5-def-maiorana-mcfarland, carlet-5-affine-walsh-spectrum") (tags := "carlet, chapter-6, maiorana-mcfarland, relation-48, pages-83-84, fidelity-exact")
*Maiorana--McFarland construction (Carlet, Relation (48), pp. 83--84).*
For $`x,y\in V_m`, let
$$`
f(x,y)=x\mathbin\cdot\pi(y)+g(y),
`
where $`g:V_m\to\mathbb F_2` is arbitrary. The function $`f` is bent if
and only if $`\pi:V_m\to V_m` is bijective. In that case
$$`
\widetilde f(a,b)=b\mathbin\cdot\pi^{-1}(a)+g(\pi^{-1}(a)).
`
:::

:::proposition "carlet-6-prop-20-general-maiorana-mcfarland" (parent := "carlet-chapter-6") (lean := "CryptBoolean.maioranaMcFarlandFiberCharacterSum, CryptBoolean.walshTransform_maioranaMcFarlandGeneral, CryptBoolean.isBent_iff_maioranaMcFarlandFiberCharacterSum_natAbs, CryptBoolean.isBent_maioranaMcFarlandGeneral_of_affineFibers") (uses := "carlet-6-maiorana-mcfarland, carlet-5-affine-flat-restriction-bound, carlet-6-def-7-bent") (tags := "carlet, chapter-6, proposition-20, relation-49, pages-84-85, fidelity-exact")
*Proposition 20 (Carlet, Relation (49), pp. 84--85).* Let $`n=r+s` be
even with $`r\le s`, let $`\varphi:V_s\to V_r`, and put
$$`
f_{\varphi,g}(x,y)=x\mathbin\cdot\varphi(y)+g(y).
`
For every $`a\in V_r` and $`b\in V_s`,
$$`
W_{f_{\varphi,g}}(a,b)
=2^r\sum_{y\in\varphi^{-1}(a)}(-1)^{g(y)+b\mathbin\cdot y}.
`
If every fiber $`\varphi^{-1}(a)` is an affine subspace of dimension
$`s-r` and, when $`r<s`, the restriction of $`g` to every fiber is bent,
then $`f_{\varphi,g}` is bent.
:::

:::theorem "carlet-6-maiorana-mcfarland-balanced-map" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsBalancedCubeMap, CryptBoolean.isBalancedCubeMap_of_isBent_maioranaMcFarlandGeneral") (uses := "carlet-6-prop-20-general-maiorana-mcfarland") (tags := "carlet, chapter-6, page-85, fidelity-exact")
*Balance of the Maiorana--McFarland frequency map (Carlet, p. 85).*
Let $`n=r+s` be even.  If
$$`
f_{\varphi,g}(x,y)=x\mathbin\cdot\varphi(y)+g(y)
`
is bent on $`V_r\times V_s`, then $`r\le s` and
$`\varphi:V_s\to V_r` is uniformly distributed.  Explicitly,
$$`
|\varphi^{-1}(a)|=2^{s-r}
\qquad(a\in V_r).
`
:::

:::theorem "carlet-6-half-dimensional-bent-subspace" (parent := "carlet-chapter-6") (lean := "CryptBoolean.binaryGaloisFieldCoordinateEquiv, CryptBoolean.fieldMultiplicationCubeMap, CryptBoolean.fieldMaioranaMcFarlandFunction, CryptBoolean.fieldMaioranaMcFarlandFunction_joinF₂CubeBlocks, CryptBoolean.fieldMaioranaMcFarlandLinearMap, CryptBoolean.fieldMultiplicationCubeMap_bijective, CryptBoolean.isBent_fieldMaioranaMcFarlandFunction, CryptBoolean.fieldMaioranaMcFarlandLinearMap_injective, CryptBoolean.maioranaMcFarlandBentSubspace, CryptBoolean.finrank_maioranaMcFarlandBentSubspace, CryptBoolean.isBent_of_mem_maioranaMcFarlandBentSubspace, CryptBoolean.exists_halfDimensionalBentSubspace") (uses := "carlet-6-maiorana-mcfarland") (tags := "carlet, chapter-6, page-86, fidelity-exact")
*Half-dimensional linear spaces of bent functions (Carlet, p. 86).*
For every $`m>0`, there is an $`m`-dimensional $`\mathbb F_2`-linear
subspace $`B` of the Boolean functions on $`V_{2m}` such that
$$`
f\in B\setminus\{0\}\quad\Longrightarrow\quad f\text{ is bent}.
`
:::

:::theorem "carlet-6-partial-spread-construction" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsHalfDimensionalPartialSpread, CryptBoolean.HasPartialSpreadBentCardinality, CryptBoolean.partialSpreadFunction, CryptBoolean.partialSpreadCoefficients, CryptBoolean.bitValueInt_partialSpreadFunction_of_ne_zero, CryptBoolean.partialSpreadFunction_zero, CryptBoolean.hasExactGPSRepresentation_partialSpreadFunction, CryptBoolean.isBent_partialSpreadFunction") (uses := "carlet-6-theorem-12-geometric-characterization") (tags := "carlet, chapter-6, partial-spread, pages-85-86, fidelity-exact-positive-half-dimension")
*Dillon's partial-spread construction (Carlet, pp. 85--86).* Let $`n` be
even with $`n/2\ge2`, and let $`\mathcal P` be a family of
$`n/2`-dimensional subspaces of $`V_n` such that distinct members meet only
at zero. If
$$`
|\mathcal P|=2^{n/2-1}\quad\text{or}\quad
|\mathcal P|=2^{n/2-1}+1,
`
then the sum over $`\mathbb F_2` of the indicators of the members of
$`\mathcal P` is bent. Its dual is obtained by replacing every member by
its orthogonal complement in the corresponding exact partial-spread
expression.
:::
