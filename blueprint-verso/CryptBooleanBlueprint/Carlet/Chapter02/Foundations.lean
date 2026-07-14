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

#doc (Manual) "Representation and Walsh foundations" =>

:::definition "carlet-2-def-boolean-function" (lean := "CryptBoolean.BooleanFunction, CryptBoolean.realSignView") (tags := "carlet, chapter-2, section-2-1")
A scalar cryptographic Boolean function is a map $`\mathbb F_2^n\to\mathbb F_2`.
Its real sign view is $`x\mapsto (-1)^{f(x)}`.
:::

:::definition "carlet-2-def-support-weight" (lean := "CryptBoolean.support, CryptBoolean.hammingWeight, CryptBoolean.mem_support") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, section-2-1")
The support of $`f` is $`\{x:f(x)=1\}`. The Hamming weight of $`f` is the cardinality of this support.
:::

:::definition "carlet-2-def-walsh-transform" (lean := "CryptBoolean.bitSignInt, CryptBoolean.walshTerm, CryptBoolean.walshTransform") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, section-2-2")
For $`a\in\mathbb F_2^n`, Carlet's raw Walsh transform is the integer sum
$`\sum_x (-1)^{f(x)+a\cdot x}`.
:::

:::theorem "carlet-2-bridge-walsh-normalization" (lean := "CryptBoolean.card_f₂Cube, CryptBoolean.walshTerm_cast_eq_realSignView_mul_character, CryptBoolean.walshTransform_cast_eq_sum_realSignView_mul_character, CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff") (uses := "carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, section-2-2, bridge")
With the [FABL](https://github.com/Polarnova/FABL) sign convention, Carlet's unnormalized Walsh transform satisfies
$`W_f(a)=2^n\widehat{(-1)^f}(a)`, where the coefficient on the right is FABL's normalized vector Fourier coefficient.
:::


:::theorem "carlet-2-balanced-zero-walsh" (lean := "CryptBoolean.IsBalanced, CryptBoolean.bitSignInt_eq_if_one, CryptBoolean.walshTerm_zero, CryptBoolean.walshTransform_zero_eq_card_sub_two_weight, CryptBoolean.walshTransform_zero_eq_two_pow_sub_two_weight, CryptBoolean.isBalanced_iff_walshTransform_zero_eq_zero") (uses := "carlet-2-def-support-weight, carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, section-2-2, bridge")
A Boolean function is balanced exactly when its zero-frequency Walsh transform vanishes.
Equivalently, $`W_f(0)=2^n-2\operatorname{wt}(f)`.
:::
