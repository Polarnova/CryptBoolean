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

#doc (Manual) "Boolean functions and support" =>

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
