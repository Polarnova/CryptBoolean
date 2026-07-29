/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter08.Constructions
import CryptBooleanBlueprint.Carlet.Chapter08.Core
import CryptBooleanBlueprint.Carlet.Chapter08.Order

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strict avalanche and propagation criteria" =>

Carlet's Chapter 8 develops propagation criteria through derivative
balancedness, Walsh-square identities, nonlinearity bounds, constructions,
coordinate restrictions, and criteria of order. Throughout,
$`V_n=\mathbb F_2^n` and $`W_f` denotes the unnormalized Walsh transform.

{include 0 CryptBooleanBlueprint.Carlet.Chapter08.Core}

{include 0 CryptBooleanBlueprint.Carlet.Chapter08.Constructions}

{include 0 CryptBooleanBlueprint.Carlet.Chapter08.Order}
