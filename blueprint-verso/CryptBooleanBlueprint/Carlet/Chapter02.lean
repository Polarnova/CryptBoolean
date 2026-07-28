/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter02.Foundations
import CryptBooleanBlueprint.Carlet.Chapter02.Fourier
import CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations
import CryptBooleanBlueprint.Carlet.Chapter02.Derivatives
import CryptBooleanBlueprint.Carlet.Chapter02.ANF
import CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence
import CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm
import CryptBooleanBlueprint.Carlet.Chapter02.FiniteField
import CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Generalities on Boolean functions" =>

Chapter 2 develops scalar Boolean-function representations and the Fourier--Walsh interface. All
page and result references in this chapter point to Claude Carlet's *Boolean Functions for
Cryptography and Error Correcting Codes*. Write $`V_n=\mathbb F_2^n`,
$`f_\chi(x)=(-1)^{f(x)}`, and $`\chi_a(x)=(-1)^{a\mathbin\cdot x}` throughout.

The chapter contains 38 source-facing nodes, all formalized by 166 proved Lean declarations.
Fourier-analytic proofs reuse
[FABL](https://github.com/Polarnova/FABL) only through explicit normalization bridges.

The formalized surface includes Proposition 5's numerical-normal-form integrality criterion,
Carlet's full raw Poisson summation formula, affine invariance, recovery from restrictions, and the
spectral-support bounds. It also includes the exact coordinate/univariate binary-degree bridge,
Proposition 3 on trace-monomial degree through cyclotomic-orbit noncancellation, and the
trace-pairing representation bridge. Chapter 2 has no open node.

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Foundations}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Fourier}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Derivatives}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.ANF}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.FiniteField}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree}
