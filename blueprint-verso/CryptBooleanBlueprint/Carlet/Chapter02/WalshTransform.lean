/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.Foundations

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Walsh transform" =>

:::definition "carlet-2-def-walsh-transform" (parent := "carlet-chapter-2") (lean := "CryptBoolean.bitSignInt, CryptBoolean.bitSignInt_add, CryptBoolean.walshTerm, CryptBoolean.walshTransform") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, pages-22-23, fidelity-exact")
*Walsh transform (Carlet, pp. 22--23).* Let
$`f:V_n\to\mathbb F_2`. The Walsh transform of $`f` is the unnormalized
Fourier transform of its sign function:
$$`
W_f(a)=\sum_{x\in V_n}(-1)^{f(x)+a\mathbin\cdot x}
      =\sum_{x\in V_n}f_\chi(x)(-1)^{a\mathbin\cdot x}
\qquad(a\in V_n).
`
:::

:::theorem "carlet-2-walsh-normalization" (parent := "carlet-chapter-2") (lean := "CryptBoolean.card_f₂Cube, CryptBoolean.walshTerm_cast_eq_realSignView_mul_character, CryptBoolean.walshTransform_cast_eq_sum_realSignView_mul_character, CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff") (uses := "carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, walsh-normalization, fidelity-explicit-scaling-identity")
*Normalization of the Walsh transform.* For $`f:V_n\to\mathbb F_2` and
$`a\in V_n`, let
$$`
\widetilde{f_\chi}(a)
=2^{-n}\sum_{x\in V_n}f_\chi(x)(-1)^{a\mathbin\cdot x}.
`
Then, after embedding the integer $`W_f(a)` in $`\mathbb R`,
$$`
W_f(a)=2^n\widetilde{f_\chi}(a).
`
:::

:::theorem "carlet-2-balanced-zero-walsh" (parent := "carlet-chapter-2") (lean := "CryptBoolean.IsBalanced, CryptBoolean.bitSignInt_eq_if_one, CryptBoolean.walshTerm_zero, CryptBoolean.walshTransform_zero_eq_card_sub_two_weight, CryptBoolean.walshTransform_zero_eq_two_pow_sub_two_weight, CryptBoolean.isBalanced_iff_walshTransform_zero_eq_zero") (uses := "carlet-2-def-support-weight, carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, relation-13, page-23, fidelity-exact")
*Zero-frequency identity (Carlet, Relation (13), p. 23).* For every
$`f:V_n\to\mathbb F_2`,
$$`
W_f(0)=2^n-2w_H(f).
`
Consequently,
$$`
f\text{ is balanced}
\quad\Longleftrightarrow\quad
W_f(0)=0.
`
When $`n>0`, these conditions are also equivalent to $`w_H(f)=2^{n-1}`.
:::
