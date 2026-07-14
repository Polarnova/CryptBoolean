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

This volume contains 43 source-facing mathematical statements: 41 are associated with 180 proved
Lean declarations, while 2 remain visibly open. The dependency graph records 64 reviewed
mathematical edges. Chapter 2 develops representations and the Fourier--Walsh interface; Chapter 3
develops the distance, dimension, and duality theory of Reed--Muller codes.

Each entry states the mathematics with explicit domains, hypotheses, quantifiers, and conclusions.
Implementation and normalization notes sit outside statement blocks. A source theorem without an
associated declaration is intentionally open rather than hidden or attached to a placeholder. The
graph below records the reviewed mathematical dependencies among these results. The site is
generated with [Verso Blueprint](https://github.com/leanprover/verso-blueprint), and the checked
artifact from `main` is published automatically through GitHub Pages.

{include 0 CryptBooleanBlueprint.Carlet.Chapter02}

{include 0 CryptBooleanBlueprint.Carlet.Chapter03}

{blueprint_graph}
