/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.FourierOperations
import CryptBoolean.Carlet.Chapter02.SpectralSupport
import CryptBoolean.Carlet.Chapter02.Subspaces

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier operations and subspaces" =>

:::definition "carlet-2-pseudoboolean-fourier" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawFourierTransform, CryptBoolean.rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, relation-11, page-21, fidelity-exact-with-normalization")
*Discrete Fourier transform (Carlet, Relation (11), p. 21).* For a pseudo-Boolean
function $`\varphi:V_n\to\mathbb R`, define
$$`
\mathcal F\varphi(a)
=\widehat\varphi(a)
=\sum_{x\in V_n}\varphi(x)(-1)^{a\mathbin\cdot x}
\qquad(a\in V_n).
`
If $`\widetilde\varphi(a)=2^{-n}\widehat\varphi(a)` denotes the normalized
coefficient, then
$$`
\widehat\varphi(a)=2^n\widetilde\varphi(a).
`
:::

:::proposition "carlet-2-prop-6-fourier-shifts" (parent := "carlet-chapter-2") (lean := "CryptBoolean.vectorFourierCoeff_mul_vectorWalshCharacter, CryptBoolean.rawFourierTransform_modulate_translate") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-6, page-24, fidelity-exact")
*Proposition 6 (Carlet, p. 24).* Let $`\varphi:V_n\to\mathbb R` and
$`a,b,u\in V_n`. If
$$`
\psi(x)=(-1)^{a\mathbin\cdot x}\varphi(x+b),
`
then
$$`
\widehat\psi(u)
=(-1)^{b\mathbin\cdot(a+u)}\widehat\varphi(a+u).
`
:::

:::theorem "carlet-2-cor-2-fourier-involution" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawFourierTransform_involution") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, corollary-2, relation-19, page-25, fidelity-exact")
*Corollary 2 (Carlet, Relation (19), p. 25).* For every
$`\varphi:V_n\to\mathbb R` and $`x\in V_n`,
$$`
\widehat{\widehat\varphi}(x)=2^n\varphi(x).
`
:::

:::proposition "carlet-2-prop-7-subspace-indicator" (parent := "carlet-chapter-2") (lean := "CryptBoolean.two_pow_mul_inversePerpendicularCard_eq_card, CryptBoolean.rawFourierTransform_setIndicator_submodule") (uses := "carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-7, relation-16, pages-24-25, fidelity-exact")
*Proposition 7 (Carlet, Relation (16), pp. 24--25).* Let $`E\le V_n`, let
$`E^\perp=\{u\in V_n:u\mathbin\cdot x=0\text{ for every }x\in E\}`, and let
$`\mathbf 1_E` be the real-valued indicator of $`E`. Then, for every $`u\in V_n`,
$$`
\widehat{\mathbf 1_E}(u)
=
\begin{cases}
|E|,&u\in E^\perp,\\
0,&u\notin E^\perp.
\end{cases}
`
Equivalently, $`\widehat{\mathbf 1_E}=|E|\mathbf 1_{E^\perp}`.
:::

:::corollary "carlet-2-poisson-normalized-specialization" (parent := "carlet-chapter-2") (lean := "FABL.poissonSummationFormula") (uses := "carlet-2-prop-7-subspace-indicator, carlet-2-prop-6-fourier-shifts") (tags := "carlet, chapter-2, corollary-1, page-25, fidelity-normalized-specialization-direct-fabl")
*Normalized Poisson summation specialization.* Let $`E\le V_n`, let
$`\varphi:V_n\to\mathbb R`, and let $`z\in V_n`. Then
$$`
\frac{1}{|E|}\sum_{h\in E}\varphi(h+z)
=\sum_{u\in E^\perp}(-1)^{u\mathbin\cdot z}\widetilde\varphi(u).
`
Here $`\widetilde\varphi(u)=2^{-n}\widehat\varphi(u)`.
:::

This normalized coset-average identity is the specialization $`a=0` of the full Poisson formula
below.

:::corollary "carlet-2-cor-1-poisson-summation" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawPoissonSummationFormula") (uses := "carlet-2-prop-6-fourier-shifts, carlet-2-prop-7-subspace-indicator") (tags := "carlet, chapter-2, corollary-1, relation-17, page-25, fidelity-exact")
*Corollary 1 (Poisson summation; Carlet, Relation (17), p. 25).* For every
$`\varphi:V_n\to\mathbb R`, every subspace $`E\le V_n`, and all $`a,b\in V_n`,
$$`
\sum_{u\in a+E}(-1)^{b\mathbin\cdot u}\widehat\varphi(u)
=|E|(-1)^{a\mathbin\cdot b}
  \sum_{x\in b+E^\perp}(-1)^{a\mathbin\cdot x}\varphi(x).
`
:::

:::definition "carlet-2-def-convolution" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawConvolution, CryptBoolean.rawConvolution_eq_two_pow_mul_convolution") (tags := "carlet, chapter-2, page-26, fidelity-exact")
*Convolution (Carlet, p. 26).* For $`\varphi,\psi:V_n\to\mathbb R`, define
their unnormalized convolution by
$$`
(\varphi\otimes\psi)(x)
=\sum_{y\in V_n}\varphi(y)\psi(x+y)
\qquad(x\in V_n).
`
:::

:::proposition "carlet-2-prop-8-convolution" (parent := "carlet-chapter-2") (lean := "CryptBoolean.rawFourierTransform_rawConvolution") (uses := "carlet-2-def-convolution, carlet-2-pseudoboolean-fourier") (tags := "carlet, chapter-2, proposition-8, relation-20, page-26, fidelity-exact")
*Proposition 8 (Carlet, Relation (20), p. 26).* For all
$`\varphi,\psi:V_n\to\mathbb R` and $`u\in V_n`,
$$`
\widehat{\varphi\otimes\psi}(u)
=\widehat\varphi(u)\widehat\psi(u).
`
:::

:::theorem "carlet-2-rel-22-plancherel" (parent := "carlet-chapter-2") (lean := "CryptBoolean.sum_rawFourierTransform_mul") (uses := "carlet-2-prop-8-convolution, carlet-2-cor-2-fourier-involution") (tags := "carlet, chapter-2, relation-22, corollary-3, page-27, fidelity-exact-bilinear-form")
*Relation (22) and Parseval's relation (Carlet, p. 27).* For all
$`\varphi,\psi:V_n\to\mathbb R`,
$$`
\sum_{u\in V_n}\widehat\varphi(u)\widehat\psi(u)
=2^n\sum_{x\in V_n}\varphi(x)\psi(x).
`
In particular, taking $`\psi=\varphi` gives Corollary 3:
$$`
\sum_{u\in V_n}\widehat\varphi(u)^2
=2^n\sum_{x\in V_n}\varphi(x)^2.
`
:::
