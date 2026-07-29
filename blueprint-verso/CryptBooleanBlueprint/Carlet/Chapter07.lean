/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter07.Bounds
import CryptBooleanBlueprint.Carlet.Chapter07.Composition
import CryptBooleanBlueprint.Carlet.Chapter07.Counting
import CryptBooleanBlueprint.Carlet.Chapter07.OtherCriteria
import CryptBooleanBlueprint.Carlet.Chapter07.PrimaryConstructions
import CryptBooleanBlueprint.Carlet.Chapter07.SecondaryConstructions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Resilient functions" =>

Carlet's Chapter 7 develops resilient Boolean functions through their
Walsh zeros, divisibility, algebraic degree, nonlinearity, interactions
with other cryptographic criteria, and recursive constructions. Throughout,
$`V_n=\mathbb F_2^n` and $`W_f` denotes the unnormalized Walsh transform.

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.Bounds}

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.OtherCriteria}

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.PrimaryConstructions}

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.Composition}

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.SecondaryConstructions}

{include 0 CryptBooleanBlueprint.Carlet.Chapter07.Counting}
