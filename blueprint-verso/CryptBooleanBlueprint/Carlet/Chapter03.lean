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
nodes contain six formalized results associated with 21 proved Lean declarations and one exact open
statement. The verified surface defines Reed--Muller codes and proves the order-one specialization
and full general-order form of Carlet's Theorem 1, the dimension and cardinality formulas, and
Theorem 2 on duality. Proposition 12's minimum-weight equality classification remains open: it
requires an arbitrary affine-flat normal form, the codimension--degree theorem for affine-flat
indicators, and equality-case slice infrastructure.

{include 0 CryptBooleanBlueprint.Carlet.Chapter03.ReedMuller}
