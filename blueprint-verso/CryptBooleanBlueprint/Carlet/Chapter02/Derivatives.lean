/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.Derivatives

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Derivatives and autocorrelation" =>

:::definition "carlet-2-def-2-derivative" (parent := "carlet-chapter-2") (lean := "CryptBoolean.booleanDerivative, CryptBoolean.realSignView_booleanDerivative") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, definition-2, page-27, fidelity-exact")
*Definition 2 (Carlet, p. 27).* Let $`f:V_n\to\mathbb F_2` and $`b\in V_n`.
The derivative of $`f` in direction $`b` is the Boolean function
$$`
D_bf(x)=f(x)+f(x+b)
\qquad(x\in V_n),
`
where addition is in $`\mathbb F_2`. Its sign function satisfies
$$`
(D_bf)_\chi(x)=f_\chi(x)f_\chi(x+b).
`
:::

:::definition "carlet-2-def-autocorrelation" (parent := "carlet-chapter-2") (lean := "CryptBoolean.autocorrelation, CryptBoolean.autocorrelation_eq_rawConvolution_realSignView") (uses := "carlet-2-def-2-derivative, carlet-2-def-convolution") (tags := "carlet, chapter-2, relation-24, page-27, fidelity-exact")
*Autocorrelation (Carlet, Relations (24)--(25), p. 27).* For
$`f:V_n\to\mathbb F_2`, define
$$`
\Delta_f(b)
=\sum_{x\in V_n}(-1)^{D_bf(x)}
=\sum_{x\in V_n}f_\chi(x)f_\chi(x+b)
=(f_\chi\otimes f_\chi)(b).
`
:::

:::theorem "carlet-2-rel-25-wiener-khinchin" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawFourierTransform_autocorrelation") (uses := "carlet-2-def-autocorrelation, carlet-2-prop-8-convolution, carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, relation-25, page-27, fidelity-exact")
*Wiener--Khinchin identity (Carlet, Relation (25), p. 27).* For every
$`f:V_n\to\mathbb F_2` and $`u\in V_n`,
$$`
\widehat{\Delta_f}(u)
=\sum_{b\in V_n}\Delta_f(b)(-1)^{u\mathbin\cdot b}
=W_f(u)^2.
`
:::

:::corollary "carlet-2-rel-26-total-autocorrelation" (parent := "carlet-chapter-2") (lean := "CryptBoolean.sum_autocorrelation_eq_walshTransform_zero_sq") (uses := "carlet-2-rel-25-wiener-khinchin") (tags := "carlet, chapter-2, relation-26, page-28, fidelity-exact")
*Relation (26) (Carlet, p. 28).* For every $`f:V_n\to\mathbb F_2`,
$$`
\sum_{b\in V_n}\Delta_f(b)=W_f(0)^2.
`
:::
