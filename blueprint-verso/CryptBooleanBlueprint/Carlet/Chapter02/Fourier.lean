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

:::theorem "carlet-2-fourier-inversion" (lean := "CryptBoolean.two_pow_mul_realSignView_eq_sum_walshTransform_mul_character, CryptBoolean.realSignView_eq_inv_two_pow_mul_sum_walshTransform_mul_character") (uses := "carlet-2-bridge-walsh-normalization") (tags := "carlet, chapter-2, corollary-2, page-25, fidelity-exact-sign-specialization")
*Walsh inversion (Carlet, Corollary 2, Relation (19), p. 25).* For every
$`f:V_n\to\mathbb F_2` and $`x\in V_n`,
$$`
f_\chi(x)
=2^{-n}\sum_{a\in V_n}W_f(a)(-1)^{a\mathbin\cdot x}.
`
Equivalently,
$$`
2^n f_\chi(x)=\sum_{a\in V_n}W_f(a)(-1)^{a\mathbin\cdot x}.
`
:::

:::theorem "carlet-2-parseval" (lean := "CryptBoolean.realSignView_mul_self, CryptBoolean.sum_vectorFourierCoeff_realSignView_sq, CryptBoolean.sum_walshTransform_sq_eq_two_pow_sq") (uses := "carlet-2-bridge-walsh-normalization") (tags := "carlet, chapter-2, corollary-3, relation-23, page-27, fidelity-exact")
*Parseval for Boolean sign functions (Carlet, Corollary 3, Relation (23), p. 27).*
For every $`f:V_n\to\mathbb F_2`,
$$`
\sum_{a\in V_n}W_f(a)^2=2^{2n}.
`
:::

*Formalization note.* Through the explicit normalization bridge, the same theorem is represented
internally by $`\sum_a\widetilde{f_\chi}(a)^2=1` before rescaling to Carlet's raw integer spectrum.
