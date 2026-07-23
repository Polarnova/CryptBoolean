/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity
import CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity
import CryptBooleanBlueprint.Carlet.Chapter04.Resiliency
import CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures
import CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity
import CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation
import CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation
import CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Boolean functions and cryptography" =>

Chapter 4 contains 73 source-facing nodes. All 73 nodes are associated with 568 proved
declarations. They cover nonlinearity and its Walsh formula, Rodier's sharp random-nonlinearity
interval, general odd-dimensional bounds and exact values in dimensions one, three, five, and
seven, balanced, `PC(1)`, and degree-`n-1` constructions above the quadratic bound, higher-order
lower bounds, the rank-seven weight-sixteen classification, and the sharp fixed-order
higher-order upper bound,
Reed--Muller coset distances, resiliency, propagation criteria, linear structures, algebraic
immunity, autocorrelation indicators, maximum correlation, and scalar complexity criteria. The
chapter has no remaining open statement nodes.

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.Resiliency}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation}

{include 0 CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria}
