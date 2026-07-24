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

Chapter 3 develops the coding-theoretic structure of Boolean functions. Its seven source-facing
nodes are all formalized and associated with 32 proved Lean declarations. The verified surface
defines Reed--Muller codes and proves the order-one specialization and full general-order form of
Carlet's Theorem 1, Proposition 12's complete minimum-weight equality classification, the dimension
and cardinality formulas, and Theorem 2 on duality.

{include 0 CryptBooleanBlueprint.Carlet.Chapter03.ReedMuller}
