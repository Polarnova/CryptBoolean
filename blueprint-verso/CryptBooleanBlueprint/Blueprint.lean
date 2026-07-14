/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import CryptBooleanBlueprint.Carlet.Chapter02
import CryptBooleanBlueprint.Carlet.Chapter03

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cryptographic Boolean Functions in Lean" =>

[CryptBoolean](https://github.com/Polarnova/CryptBoolean) is a formalization of cryptographic
Boolean-function theory in [Lean 4](https://github.com/leanprover/lean4) and
[Mathlib](https://github.com/leanprover-community/mathlib4). Its primary mathematical source is
Claude Carlet's *Boolean Functions for Cryptography and Error Correcting Codes*.

The library develops algebraic representations, Walsh analysis, finite-field representations, and
Reed--Muller coding for scalar Boolean functions. It uses
[FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis and records explicit bridges
between FABL's normalized Fourier coefficients and Carlet's raw Walsh transform.

This volume contains 23 verified statements associated with 114 compiled Lean declarations and 26
reviewed dependency edges. Chapter 2 develops representations and the Fourier--Walsh interface;
Chapter 3 begins the coding-theoretic development with first-order Reed--Muller codes.

Each entry presents a source-facing mathematical statement beside its Lean declarations. The graph
below records the reviewed mathematical dependencies among these results. The site is generated
with [Verso Blueprint](https://github.com/leanprover/verso-blueprint).

{include 0 CryptBooleanBlueprint.Carlet.Chapter02}

{include 0 CryptBooleanBlueprint.Carlet.Chapter03}

{blueprint_graph}
