/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.SecondOrderCharacterization

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Characterization by second-order covering sequences" =>

:::proposition "carlet-6-prop-24-second-order-characterization" (parent := "carlet-chapter-6") (lean := "CryptBoolean.secondDerivativeDoubleSum, CryptBoolean.rawTripleConvolution, CryptBoolean.secondDerivativeDoubleSum_eq_mul_rawTripleConvolution, CryptBoolean.rawFourierTransform_rawTripleConvolution, CryptBoolean.rawFourierTransform_const_mul_realSignView, CryptBoolean.eq_of_rawFourierTransform_eq, CryptBoolean.isBent_iff_forall_secondDerivativeDoubleSum_eq_two_pow, CryptBoolean.secondDerivativeDoubleSum_eq_two_pow_iff_rawTripleConvolution_eq, CryptBoolean.isBent_iff_rawTripleConvolution_realSignView_eq, CryptBoolean.isBent_iff_forall_walshTransform_cube_eq") (uses := "carlet-6-theorem-8-perfect-nonlinearity, carlet-4-autocorrelation-indicator-bounds, carlet-4-second-derivative-sum, carlet-2-def-convolution, carlet-2-prop-8-convolution, carlet-2-fourier-inversion") (tags := "carlet, chapter-6, proposition-24, relation-52, second-order-covering-sequence, section-6-6-3, page-100, fidelity-exact")
*Proposition 24 (Carlet, Relation (52), p. 100).* A Boolean function
$`f:V_n\to\mathbb F_2` is bent if and only if, for every $`x\in V_n`,
$$`
\sum_{a,b\in V_n}(-1)^{D_aD_bf(x)}=2^n.
`
Equivalently, for the sign function $`f_\chi=(-1)^f`,
$$`
f_\chi\otimes f_\chi\otimes f_\chi=2^nf_\chi,
`
or, at every $`u\in V_n`,
$$`
W_f(u)^3=2^nW_f(u).
`
:::
