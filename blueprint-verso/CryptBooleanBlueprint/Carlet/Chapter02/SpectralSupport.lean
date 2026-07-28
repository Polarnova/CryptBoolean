/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.SpectralSupport
import CryptBoolean.Carlet.Chapter02.WalshDivisibility

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier support" =>

:::theorem "carlet-2-spectral-support-bounds" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawFourierSupport, CryptBoolean.mem_rawFourierSupport, CryptBoolean.mem_rawFourierSupport_iff_vectorFourierCoeff_ne_zero, CryptBoolean.indexedRawFourierTransform, CryptBoolean.indexedRawFourierSupport, CryptBoolean.mem_indexedRawFourierSupport, CryptBoolean.indexedRawFourierTransform_eq_card_mul_indexedFourierCoeff, CryptBoolean.mem_indexedRawFourierSupport_iff_indexedFourierCoeff_ne_zero, CryptBoolean.card_indexedRawFourierSupport_signRestriction_le, CryptBoolean.card_indexedRawFourierSupport_binaryFunctionOnSignCube, CryptBoolean.card_rawFourierSupport_coordinateRestriction_le, FABL.booleanRealEmbedding, CryptBoolean.two_pow_functionAlgebraicDegree_le_card_rawFourierSupport_booleanRealEmbedding, FABL.numericalSupport, FABL.mem_numericalSupport, FABL.numericalDegree, FABL.numericalDegree_le_iff, FABL.functionNumericalDegree, CryptBoolean.numericalMonomial_eq_setIndicator_coordinateSubcube, CryptBoolean.f₂Support_subset_of_vectorFourierCoeff_numericalMonomial_ne_zero, CryptBoolean.vectorFourierCoeff_numericalEval, CryptBoolean.f₂Support_card_le_functionNumericalDegree_of_mem_rawFourierSupport, CryptBoolean.card_lowWeightInputs, CryptBoolean.card_rawFourierSupport_le_sum_choose_functionNumericalDegree") (uses := "carlet-2-cor-1-poisson-summation, carlet-2-restriction-recovery, carlet-2-nnf-existence-uniqueness") (tags := "carlet, chapter-2, section-2-2-2, page-32, fidelity-exact-with-explicit-zero-conventions")
*Fourier-support bounds (Carlet, Section 2.2.2, p. 32).* For
$`\varphi:V_n\to\mathbb R`, let
$$`
N_{\widehat\varphi}
=\bigl|\{u\in V_n:\widehat\varphi(u)\ne0\}\bigr|.
`
If $`J\subseteq[n]`, $`b\in\mathbb F_2^{[n]\setminus J}`, and
$`\psi:\mathbb F_2^J\to\mathbb R` is the coordinate restriction
$`\psi(y)=\varphi(y,b)`, then
$$`
N_{\widehat\psi}\le N_{\widehat\varphi}.
`
For a Boolean function $`f:V_n\to\mathbb F_2`, let
$`\varphi_f:V_n\to\mathbb R` be its $`\{0,1\}`-valued real embedding. If
$`f\ne0` and $`\deg_{\mathrm{alg}}(f)=d`, then
$$`
N_{\widehat{\varphi_f}}\ge 2^d.
`
Finally, if $`\varphi\ne0`, $`\varphi(x)=\sum_{S\subseteq[n]}\lambda_Sx^S` is its unique NNF, and
$$`
D=\max\{|S|:\lambda_S\ne0\}
`
is its numerical degree, then
$$`
N_{\widehat\varphi}\le\sum_{i=0}^{D}\binom ni.
`
:::

The lower bound assumes $`f\ne0`, since the zero function has empty Fourier support. The condition
$`\varphi\ne0` likewise makes the displayed numerical degree a maximum over a nonempty set; with
the zero-degree convention, the resulting upper bound also holds for $`\varphi=0`.

:::proposition "carlet-2-prop-11-walsh-divisibility" (parent := "carlet-chapter-2") (lean := "CryptBoolean.vectorFourierCoeff_booleanRealEmbedding_eq, CryptBoolean.functionAlgebraicDegree_le_of_two_pow_dvd_walshTransform") (uses := "carlet-2-def-algebraic-degree, carlet-2-def-walsh-transform") (tags := "carlet, chapter-2, proposition-11, page-34, fidelity-exact")
*Proposition 11 (Carlet, p. 34).* Let $`n\ge2` and $`1\le k\le n`. If
$`2^k` divides $`W_f(a)` for every $`a\in V_n`, then
$$`
\deg_{\mathrm{alg}}(f)\le n-k+1.
`
:::
