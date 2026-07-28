/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import CryptBooleanBlueprint.Citations
import CryptBooleanBlueprint.Carlet.Chapter02
import CryptBooleanBlueprint.Carlet.Chapter03
import CryptBooleanBlueprint.Carlet.Chapter04
import CryptBooleanBlueprint.Carlet.Chapter05
import CryptBooleanBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open CryptBooleanBlueprint.Sources

#doc (Manual) "Cryptographic Boolean Functions in Lean" =>

[CryptBoolean](https://github.com/Polarnova/CryptBoolean) is a formalization of cryptographic
Boolean-function theory in [Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4). Its primary mathematical source is
Claude Carlet's *Boolean Functions for Cryptography and Error-Correcting Codes*
{Citations.citep carlet2010}[].

The library develops algebraic representations, Walsh analysis, finite-field representations,
Reed--Muller coding, and cryptographic criteria for scalar Boolean functions. Carlet's raw Walsh
transform and the normalized Fourier coefficient are related throughout by the identity
$`W_f(a)=2^n\widetilde{f_\chi}(a)`.

The four chapters develop, in order, representations and the Fourier--Walsh relation,
Reed--Muller coding, scalar cryptographic criteria, and classes with constrained weights, Walsh
spectra, and nonlinearities.

The exposition begins with Carlet's Chapter 2. Thus Chapters 1--4 below correspond respectively
to Carlet Chapters 2--5; source references retain Carlet's numbering.

Each entry states the mathematics with explicit domains, hypotheses, quantifiers, and conclusions.
The graph below records the mathematical dependencies among these results.

:::group "carlet-chapter-2"
Chapter 1: Generalities on Boolean functions
:::

:::group "carlet-chapter-3"
Chapter 2: Boolean functions and coding
:::

:::group "carlet-chapter-4"
Chapter 3: Boolean functions and cryptography
:::

:::group "carlet-chapter-5"
Chapter 4: Classes of functions for which restrictions on the possible values of the weights, Walsh spectra and nonlinearities can be proved
:::

{include 0 CryptBooleanBlueprint.Carlet.Chapter02}

{include 0 CryptBooleanBlueprint.Carlet.Chapter03}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04}

{include 0 CryptBooleanBlueprint.Carlet.Chapter05}

{references}

{blueprint_graph (direction := LR)}
