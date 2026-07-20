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

#doc (Manual) "Boolean functions, support, and Walsh transform" =>

:::definition "carlet-2-def-boolean-function" (parent := "carlet-chapter-2") (lean := "CryptBoolean.BooleanFunction, CryptBoolean.realSignView") (tags := "carlet, chapter-2, pages-8-22, fidelity-exact")
*Boolean and sign functions (Carlet, pp. 8 and 22).* Fix $`n\ge 0` and write
$`V_n=\mathbb F_2^n`. An $`n`-variable Boolean function is a map
$`f:V_n\to\mathbb F_2`. Its sign function is
$$`
f_\chi:V_n\longrightarrow\{-1,1\}\subset\mathbb R,
\qquad f_\chi(x)=(-1)^{f(x)}.
`
:::

:::definition "carlet-2-def-support-weight" (parent := "carlet-chapter-2") (lean := "CryptBoolean.support, CryptBoolean.hammingWeight, CryptBoolean.mem_support, CryptBoolean.hammingWeight_eq_card_support") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, page-8, fidelity-exact-with-mathlib-hamming-norm")
*Support and Hamming weight (Carlet, p. 8).* For
$`f:V_n\to\mathbb F_2`, define
$$`
\operatorname{supp}(f)=\{x\in V_n:f(x)=1\},
\qquad
w_H(f)=|\operatorname{supp}(f)|.
`
:::

*Formalization note.* The source-facing weight name is a reducible alias of Mathlib's
`hammingNorm`; the associated bridge proves that it is exactly the cardinality displayed above.

:::definition "carlet-2-def-walsh-transform" (parent := "carlet-chapter-2") (lean := "CryptBoolean.bitSignInt, CryptBoolean.walshTerm, CryptBoolean.walshTransform") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, pages-22-23, fidelity-exact")
*Walsh transform (Carlet, pp. 22--23).* Let
$`f:V_n\to\mathbb F_2`. The Walsh transform of $`f` is the unnormalized
Fourier transform of its sign function:
$$`
W_f(a)=\sum_{x\in V_n}(-1)^{f(x)+a\mathbin\cdot x}
      =\sum_{x\in V_n}f_\chi(x)(-1)^{a\mathbin\cdot x}
\qquad(a\in V_n).
`
:::

:::theorem "carlet-2-bridge-walsh-normalization" (parent := "carlet-chapter-2") (lean := "CryptBoolean.card_f₂Cube, CryptBoolean.walshTerm_cast_eq_realSignView_mul_character, CryptBoolean.walshTransform_cast_eq_sum_realSignView_mul_character, CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff") (uses := "carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, normalization-bridge, fidelity-explicit-bridge")
*Walsh normalization bridge.* For $`f:V_n\to\mathbb F_2` and $`a\in V_n`,
let
$$`
\widetilde{f_\chi}(a)
=2^{-n}\sum_{x\in V_n}f_\chi(x)(-1)^{a\mathbin\cdot x}.
`
Then, after embedding the integer $`W_f(a)` in $`\mathbb R`,
$$`
W_f(a)=2^n\widetilde{f_\chi}(a).
`
:::

*Formalization note.* The normalized coefficient $`\widetilde{f_\chi}(a)` is
[FABL](https://github.com/Polarnova/FABL)'s `vectorFourierCoeff`. The explicit equation above is
the only identification made between Carlet's raw transform and FABL's normalized transform.

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
