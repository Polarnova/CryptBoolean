/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.Fourier

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Walsh inversion and Parseval" =>

:::theorem "carlet-2-fourier-inversion" (lean := "CryptBoolean.two_pow_mul_realSignView_eq_sum_walshTransform_mul_character, CryptBoolean.realSignView_eq_inv_two_pow_mul_sum_walshTransform_mul_character") (uses := "carlet-2-bridge-walsh-normalization") (tags := "carlet, chapter-2, section-2-2")
The sign view is recovered from its Walsh spectrum:
$`(-1)^{f(x)} = 2^{-n}\sum_{a\in\mathbb F_2^n} W_f(a)\,\chi_a(x)`.
Equivalently, $`2^n(-1)^{f(x)} = \sum_a W_f(a)\,\chi_a(x)`.
:::

:::theorem "carlet-2-parseval" (lean := "CryptBoolean.realSignView_mul_self, CryptBoolean.sum_vectorFourierCoeff_realSignView_sq, CryptBoolean.sum_walshTransform_sq_eq_two_pow_sq") (uses := "carlet-2-bridge-walsh-normalization") (tags := "carlet, chapter-2, section-2-2")
Parseval for Carlet's raw Walsh transform:
$`\sum_{a\in\mathbb F_2^n} W_f(a)^2 = (2^n)^2`,
equivalently the normalized sign-view spectrum satisfies
$`\sum_a \widehat{(-1)^f}(a)^2 = 1`.
:::
