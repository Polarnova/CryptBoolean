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

:::definition "carlet-2-derivative-autocorrelation" (lean := "CryptBoolean.booleanDerivative, CryptBoolean.realSignView_booleanDerivative, CryptBoolean.autocorrelation, CryptBoolean.autocorrelation_eq_rawConvolution_realSignView, CryptBoolean.rawFourierTransform_autocorrelation, CryptBoolean.sum_autocorrelation_eq_walshTransform_zero_sq") (uses := "carlet-2-prop-8-convolution-plancherel, carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, definition-2, relation-24, wiener-khinchin")
The derivative is $`D_bf(x)=f(x)+f(x+b)`.  Its sign sum is the autocorrelation
$`\Delta_f(b)`, whose raw Fourier transform is the pointwise square of the Walsh
spectrum; summing autocorrelation values yields $`W_f(0)^2`.
:::
