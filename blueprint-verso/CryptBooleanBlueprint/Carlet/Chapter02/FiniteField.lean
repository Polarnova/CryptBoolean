/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.FiniteField

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Finite-field representations" =>

:::definition "carlet-2-absolute-trace" (lean := "CryptBoolean.BinaryGaloisField, CryptBoolean.FieldBooleanFunction, CryptBoolean.absoluteTrace, CryptBoolean.algebraMap_absoluteTrace_eq_sum_frobenius, traceForm_nondegenerate, Algebra.trace_surjective, CryptBoolean.exists_absoluteTrace_eq_one, CryptBoolean.absoluteTrace_surjective, CryptBoolean.traceLift, CryptBoolean.absoluteTrace_traceLift") (tags := "carlet, chapter-2, absolute-trace, page-15, fidelity-exact-direct-mathlib")
*Absolute trace (Carlet, p. 15).* Let $`n>0`, let
$`K_n=\operatorname{GF}(2^n)`, and let
$`\iota:\mathbb F_2\hookrightarrow K_n` be the canonical embedding. The
absolute trace is the $`\mathbb F_2`-linear map
$$`
\operatorname{Tr}_n:K_n\longrightarrow\mathbb F_2,
\qquad
\iota(\operatorname{Tr}_n(x))
=\sum_{i=0}^{n-1}x^{2^i}.
`
The pairing $`(x,y)\mapsto\operatorname{Tr}_n(xy)` is nondegenerate; hence
$`\operatorname{Tr}_n` is surjective. In particular, choose
$`\tau\in K_n` with $`\operatorname{Tr}_n(\tau)=1`. For every
$`f:K_n\to\mathbb F_2`, define
$$`
F_\tau(x)=
\begin{cases}
0,&f(x)=0,\\
\tau,&f(x)=1.
\end{cases}
`
Then
$$`
\operatorname{Tr}_n(F_\tau(x))=f(x)
\qquad(x\in K_n).
`
:::

*Formalization note.* The field, finite-field trace, trace nondegeneracy, and Frobenius-sum theorem
are provided by [Mathlib](https://github.com/leanprover-community/mathlib4). The Blueprint statement
records the resulting mathematics rather than those implementation choices.

:::theorem "carlet-2-univariate-representation" (lean := "CryptBoolean.univariateRepresentation, CryptBoolean.eval_univariateRepresentation, CryptBoolean.degree_univariateRepresentation_lt_card, CryptBoolean.existsUnique_univariateRepresentation") (tags := "carlet, chapter-2, relation-4, page-15, fidelity-exact")
*Univariate representation (Carlet, Relation (4), p. 15).* Let $`n>0` and
$`K_n=\operatorname{GF}(2^n)`. For every function $`F:K_n\to K_n`, there
exists a unique polynomial $`P_F\in K_n[X]` such that
$$`
\deg P_F<2^n
\qquad\text{and}\qquad
P_F(x)=F(x)\quad\text{for every }x\in K_n.
`
Equivalently,
$$`
P_F(X)=\sum_{i=0}^{2^n-1}\delta_iX^i
`
for uniquely determined coefficients $`\delta_i\in K_n`.
:::

*Formalization note.* The canonical witness is finite Lagrange interpolation. This theorem has no
mathematical dependency on the absolute trace, so no such edge is recorded in the Blueprint graph.

:::proposition "carlet-2-trace-monomial-degree" (uses := "carlet-2-absolute-trace, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-2, proposition-3, pages-17-18, source-open")
*Proposition 3 (Carlet, pp. 17--18).* Let $`n>0`, let $`a\in K_n`, choose an
$`\mathbb F_2`-linear isomorphism $`\theta:V_n\xrightarrow{\sim}K_n`, and let $`k` be represented
by an integer $`0\le k<2^n-1` modulo $`2^n-1`. If the Boolean function
$$`
f_\theta(x)=\operatorname{Tr}_n\!\left(a\,\theta(x)^k\right)
`
is not identically zero, then
$$`
\deg_{\mathrm{alg}}(f_\theta)=w_2(k),
`
where $`w_2(k)` is the number of nonzero digits in the binary expansion of
$`k`.
:::

*Formalization note.* Carlet identifies $`K_n` with $`V_n` after fixing a basis. Making the
coordinate isomorphism explicit is necessary to apply the cube-based definition of algebraic
degree; changing the basis composes $`f_\theta` with a linear automorphism, so affine invariance
makes the displayed degree basis-independent.
