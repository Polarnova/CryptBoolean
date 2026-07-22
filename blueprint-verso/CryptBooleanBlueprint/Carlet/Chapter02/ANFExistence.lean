/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.ANFExistence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic normal form existence and uniqueness" =>

:::theorem "carlet-2-anf-existence-uniqueness" (parent := "carlet-chapter-2") (lean := "FABL.anfMonomial_f₂CubeOfFinset, FABL.anfEval_f₂CubeOfFinset, FABL.anfCoeff, FABL.anfEval_anfCoeff_f₂CubeOfFinset, FABL.anfEval_anfCoeff, FABL.anfCoeff_unique_of_powerset_sum, FABL.anfEval_injective, FABL.existsUnique_anfEval") (uses := "carlet-2-anf-skeleton") (tags := "carlet, chapter-2, proposition-1, pages-10-11, fidelity-exact")
*Existence and uniqueness of the ANF, and Proposition 1 (Carlet, pp. 10--11).*
For every $`f:V_n\to\mathbb F_2`, there exists a unique family
$`(c_S)_{S\subseteq[n]}` such that
$$`
f(x)=\bigoplus_{S\subseteq[n]}c_S\prod_{i\in S}x_i
\qquad(x\in V_n).
`
If $`\mathbf 1_T` denotes the indicator vector of $`T\subseteq[n]`, then the
coefficient of $`x^S` is
$$`
c_S
=\bigoplus_{\substack{x\in V_n\\\operatorname{supp}(x)\subseteq S}}f(x)
=\bigoplus_{T\subseteq S}f(\mathbf 1_T)
\qquad(S\subseteq[n]).
`
:::

*Formalization note.* The Lean proof establishes existence by the characteristic-two subset-lattice
transform and uniqueness by injectivity of its zeta sums. The interval-cardinality calculation is a
proof mechanism, not part of the theorem statement.
