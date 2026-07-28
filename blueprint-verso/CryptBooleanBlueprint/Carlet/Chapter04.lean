/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicDegree
import CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity
import CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity
import CryptBooleanBlueprint.Carlet.Chapter04.Resiliency
import CryptBooleanBlueprint.Carlet.Chapter04.Propagation
import CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures
import CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity
import CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation
import CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation
import CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Boolean functions and cryptography" =>

Chapter 4 develops nonlinearity and its Walsh formula, Rodier's sharp random-nonlinearity
interval, general odd-dimensional bounds and exact values in dimensions one, three, five, and
seven, balanced, `PC(1)`, and degree-`n-1` constructions above the quadratic bound, higher-order
lower bounds, the rank-seven weight-sixteen classification, and the sharp fixed-order
higher-order upper bound,
Reed--Muller coset distances, resiliency, propagation criteria, linear structures, algebraic
immunity, autocorrelation indicators, maximum correlation, and scalar complexity criteria.

# Algebraic degree

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicDegree}

# Nonlinearity

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity}

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity}

# Balancedness and resiliency

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Resiliency}

# Strict avalanche and propagation criteria

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Propagation}

# Linear structures

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures}

# Algebraic immunity

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity}

# Autocorrelation

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation}

# Maximum correlation

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation}

# Other criteria

{include 2 CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria}
