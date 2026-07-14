/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.FourierOperations
import CryptBoolean.Carlet.Chapter02.Subspaces

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier operations and subspaces" =>

:::definition "carlet-2-pseudoboolean-fourier" (lean := "CryptBoolean.rawFourierTransform, CryptBoolean.rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, section-2-2, bridge")
For a real-valued function $`\varphi` on $`\mathbb F_2^n`, the raw Fourier transform is
$`\widehat\varphi(a)=\sum_x\varphi(x)(-1)^{a\cdot x}`.  It is exactly $`2^n`
times [FABL](https://github.com/Polarnova/FABL)'s normalized vector Fourier coefficient.
:::

:::proposition "carlet-2-prop-6-fourier-shifts" (lean := "CryptBoolean.vectorFourierCoeff_mul_vectorWalshCharacter, CryptBoolean.rawFourierTransform_modulate_translate") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-6")
Modulation by $`(-1)^{a\cdot x}` and translation by $`b` shift the raw spectrum by $`a`
and multiply it by the corresponding character value.
:::

:::theorem "carlet-2-cor-2-fourier-involution" (lean := "CryptBoolean.rawFourierTransform_involution") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, corollary-2")
Applying the unnormalized Fourier transform twice gives $`\widehat{\widehat\varphi}=2^n\varphi`.
:::

:::proposition "carlet-2-prop-7-subspace-indicator" (lean := "CryptBoolean.two_pow_mul_inversePerpendicularCard_eq_card, CryptBoolean.rawFourierTransform_setIndicator_submodule, CryptBoolean.poissonSummationFormula") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-7, corollary-1, fabl-reuse")
For a binary subspace $`E`, the raw transform of its indicator equals $`|E|` on
$`E^\perp` and zero elsewhere.  The corresponding Poisson summation formula is
delegated to [FABL](https://github.com/Polarnova/FABL)'s finite-subspace theorem.
:::

:::proposition "carlet-2-prop-8-convolution-plancherel" (lean := "CryptBoolean.rawConvolution, CryptBoolean.rawConvolution_eq_two_pow_mul_convolution, CryptBoolean.rawFourierTransform_rawConvolution, CryptBoolean.sum_rawFourierTransform_mul") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-8, corollary-3, fabl-reuse")
Raw convolution transforms to pointwise multiplication.  Consequently,
$`\sum_a\widehat\varphi(a)\widehat\psi(a)=2^n\sum_x\varphi(x)\psi(x)`.
:::
