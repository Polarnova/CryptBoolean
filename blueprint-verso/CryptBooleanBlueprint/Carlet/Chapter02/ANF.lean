/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.ANF

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic normal form" =>

:::definition "carlet-2-anf-skeleton" (lean := "CryptBoolean.ANFCoefficients, CryptBoolean.anfMonomial, CryptBoolean.anfEval, CryptBoolean.anfSupport, CryptBoolean.algebraicDegree, CryptBoolean.mem_anfSupport, CryptBoolean.anfMonomial_empty, CryptBoolean.anfEval_zero, CryptBoolean.anfEval_add, CryptBoolean.algebraicDegree_le_dimension") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, relation-1, pages-9-12, fidelity-exact-with-zero-convention")
*Algebraic normal form (Carlet, Relation (1), p. 9).* Let $`[n]=\{1,\ldots,n\}`.
For coefficients $`c=(c_S)_{S\subseteq[n]}` in $`\mathbb F_2`, set
$$`
x^S=\prod_{i\in S}x_i,
\qquad
\operatorname{ANF}_c(x)
=\bigoplus_{S\subseteq[n]}c_Sx^S.
`
The coefficient support and algebraic degree are
$$`
\operatorname{supp}_{\mathrm{ANF}}(c)
=\{S\subseteq[n]:c_S\ne0\},
\qquad
\deg(c)=\max\{|S|:c_S\ne0\},
`
with $`\deg(0)=0`. For all coefficient families $`c,d`,
$$`
\operatorname{ANF}_{c+d}=\operatorname{ANF}_c+\operatorname{ANF}_d,
\qquad
\deg(c)\le n.
`
:::
