/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.DegreeRelation

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bound on algebraic degree" =>

:::proposition "carlet-6-prop-18-rothaus-degree-bound" (parent := "carlet-chapter-6") (lean := "CryptBoolean.functionAlgebraicDegree_le_half_of_isBent, CryptBoolean.functionAlgebraicDegree_eq_two_of_isBent") (uses := "carlet-6-prop-17-dual-nnf-divisibility, carlet-6-dual, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-6, algebraic-degree, proposition-18, rothaus-bound, page-83, fidelity-exact")
*Proposition 18: Rothaus' bound (Carlet, p. 83).* Let $`n\ge4` be even.
Every bent function $`f:V_n\to\mathbb F_2` satisfies
$$`
\deg_{\mathrm{alg}}(f)\le n/2,
\qquad
\deg_{\mathrm{alg}}(\widetilde f)\le n/2.
`
In dimension $`n=2`, every bent function, and hence its dual, has algebraic
degree exactly two.
:::

:::proposition "carlet-6-prop-19" (parent := "carlet-chapter-6") (lean := "CryptBoolean.two_pow_ceilDiv_dvd_booleanCharacterSum_of_degree_le, CryptBoolean.bentDual_functionAlgebraicDegree_relation") (uses := "carlet-6-rel-46-dual-poisson, carlet-6-prop-18-rothaus-degree-bound, carlet-6-dual, carlet-2-anf-existence-uniqueness") (tags := "carlet, chapter-6, algebraic-degree, proposition-19, relation-47, page-83, fidelity-exact-positive-even-dimension")
*Proposition 19 (Carlet, Relation (47), p. 83).* Let $`n\ge2` be even, let
$`f:V_n\to\mathbb F_2` be bent, and put
$$`
d=\deg_{\mathrm{alg}}(f),
\qquad
\widetilde d=\deg_{\mathrm{alg}}(\widetilde f).
`
Then
$$`
\frac n2-d
\ge
\frac{\frac n2-\widetilde d}{\widetilde d-1}.
`
:::

For a degree-$`d` ANF monomial $`x^I` of $`f`, take
$`E=\{u\in V_n:u_i=0\text{ for every }i\in I\}`. Relation (46) gives
$$`
\sum_{u\in E}(-1)^{\widetilde f(u)}
=2^{n/2-d}\sum_{x\in E^\perp}(-1)^{f(x)}.
`
The rightmost sum is divisible by two but not by four. The McEliece--Ax
divisibility theorem supplies the comparison exponent
$`\lceil(n-d)/\widetilde d\rceil`; comparing the two powers of two yields
Relation (47).
