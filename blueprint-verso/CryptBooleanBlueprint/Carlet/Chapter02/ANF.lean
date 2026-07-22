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

:::definition "carlet-2-anf-skeleton" (parent := "carlet-chapter-2") (lean := "FABL.ANFCoefficients, FABL.anfMonomial, FABL.anfEval, FABL.anfSupport, FABL.algebraicDegree, FABL.mem_anfSupport, FABL.anfMonomial_empty, FABL.anfEval_zero, FABL.anfEval_add, FABL.algebraicDegree_le_dimension") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, relation-1, pages-9-12, fidelity-exact-with-zero-convention")
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
