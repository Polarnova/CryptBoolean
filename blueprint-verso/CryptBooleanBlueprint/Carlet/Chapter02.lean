/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter02.Foundations
import CryptBooleanBlueprint.Carlet.Chapter02.WalshTransform
import CryptBooleanBlueprint.Carlet.Chapter02.Fourier
import CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations
import CryptBooleanBlueprint.Carlet.Chapter02.Derivatives
import CryptBooleanBlueprint.Carlet.Chapter02.ANF
import CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence
import CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm
import CryptBooleanBlueprint.Carlet.Chapter02.FiniteField
import CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree
import CryptBooleanBlueprint.Carlet.Chapter02.SpectralSupport

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Generalities on Boolean functions" =>

Chapter 2 develops scalar Boolean-function representations and the relation between Fourier and
Walsh transforms. All page and result references in this chapter point to Claude Carlet's *Boolean
Functions for Cryptography and Error Correcting Codes*. Write $`V_n=\mathbb F_2^n`,
$`f_\chi(x)=(-1)^{f(x)}`, and $`\chi_a(x)=(-1)^{a\mathbin\cdot x}` throughout.

Carlet's raw Walsh transform and the normalized Fourier coefficient satisfy
$`W_f(a)=2^n\widetilde{f_\chi}(a)`.

The chapter includes Proposition 5's numerical-normal-form integrality criterion,
Carlet's full raw Poisson summation formula, affine invariance, recovery from restrictions, and the
spectral-support bounds. It also includes the coordinate formula relating univariate binary
exponent weight to ANF degree, Proposition 3 on trace-monomial degree, and the representation of
binary coordinates by the trace pairing.

# Representation of Boolean functions

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Foundations}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.ANF}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.FiniteField}

# The discrete Fourier transform on pseudo-Boolean and on Boolean functions

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.WalshTransform}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Fourier}

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.Derivatives}

# Fourier support and Cayley graphs

{include 2 CryptBooleanBlueprint.Carlet.Chapter02.SpectralSupport}
