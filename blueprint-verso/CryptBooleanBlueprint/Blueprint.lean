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

CryptBoolean formalizes scalar cryptographic Boolean functions in Lean 4 and Mathlib.
Carlet's chapters are the primary statement spine; FABL supplies Boolean-cube Fourier analysis.

{include 0 CryptBooleanBlueprint.Carlet.Chapter02}

{include 0 CryptBooleanBlueprint.Carlet.Chapter03}

{blueprint_graph}
