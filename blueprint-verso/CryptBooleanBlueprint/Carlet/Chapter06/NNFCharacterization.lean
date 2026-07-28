/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.NNFCharacterization

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Characterization through the NNF" =>

:::proposition "carlet-6-prop-23-nnf-characterization" (parent := "carlet-chapter-6") (lean := "CryptBoolean.booleanNNFFourierCoeffInt, CryptBoolean.booleanNNFFourierCoeffInt_cast, CryptBoolean.walshTransform_eq_indicator_sub_two_mul_booleanNNFFourierCoeffInt, CryptBoolean.isBent_iff_forall_booleanNNFFourierCoeffInt_modeq, CryptBoolean.SatisfiesBentNNFCoefficientConditions, CryptBoolean.isBent_iff_nnfCoefficientConditions") (uses := "carlet-6-lemma-2-walsh-congruence, carlet-2-rel-30-nnf-fourier, carlet-2-prop-4-nnf-mobius, carlet-2-prop-5-nnf-integrality") (tags := "carlet, chapter-6, proposition-23, numerical-normal-form, section-6-6-1, page-98, fidelity-exact")
*Proposition 23 (Carlet, p. 98).* Let $`n\ge2` be even, and let
$`f:V_n\to\mathbb F_2` have numerical normal form
$$`
f(x)=\sum_{I\subseteq[n]}\lambda_Ix^I.
`
Then $`f` is bent if and only if both of the following conditions hold:

1. for every $`I\subseteq[n]` with $`n/2<|I|<n`,
   $$`
   2^{|I|-n/2}\mid\lambda_I;
   `
2. for $`N=[n]`,
   $$`
   \lambda_N\equiv2^{n/2-1}\pmod {2^{n/2}}.
   `
:::
