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

Chapter 2 develops scalar Boolean-function representations and the Fourier--Walsh interface. The
verified surface covers algebraic and numerical normal forms, raw Walsh and pseudo-Boolean Fourier
transforms, subspace identities, derivatives, finite-field representations, Hamming distance, and
affine functions. Fourier-analytic results reuse
[FABL](https://github.com/Polarnova/FABL) through explicit normalization bridges.

The Blueprint also records the remaining source-facing families: the complete affine-change and
restriction laws, Proposition 5's integrality criterion, the full trace-monomial degree formula,
and the spectral-support bounds. Their open status remains visible in the dependency graph.

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Foundations}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Fourier}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.FourierOperations}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.Derivatives}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.ANF}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.ANFExistence}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.NumericalNormalForm}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.FiniteField}

{include 0 CryptBooleanBlueprint.Carlet.Chapter02.AlgebraicDegree}
