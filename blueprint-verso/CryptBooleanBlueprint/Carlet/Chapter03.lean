/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter03.ReedMuller

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Boolean functions and coding" =>

Chapter 3 develops the coding-theoretic structure of Boolean functions. The verified surface defines
first-order Reed--Muller codes through algebraic degree and establishes their distance lower bound.
The general-order distance theorem, equality classification, dimension formula, and duality remain
visible as subsequent source-facing objectives.

{include 0 CryptBooleanBlueprint.Carlet.Chapter03.ReedMuller}
