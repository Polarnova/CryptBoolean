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

#doc (Manual) "Cryptographic criteria" =>

Chapter 4 develops nonlinearity and its Walsh formula, Rodier's sharp random-nonlinearity
interval, general odd-dimensional bounds and exact values in dimensions one, three, five, and
seven, balanced, `PC(1)`, and degree-`n-1` constructions above the quadratic bound, higher-order
lower bounds, the rank-seven weight-sixteen classification, and the sharp fixed-order
higher-order upper bound,
Reed--Muller coset distances, resiliency, propagation criteria, linear structures, algebraic
immunity, autocorrelation indicators, maximum correlation, and scalar complexity criteria.

# 3.1 Cryptographic criteria for Boolean functions

## 3.1.1 The algebraic degree

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicDegree}

## 3.1.2 The nonlinearity

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.Nonlinearity}

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.HigherOrderNonlinearity}

## 3.1.3 Balancedness and resiliency

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.Resiliency}

## 3.1.4 Strict avalanche criterion and propagation criterion

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.Propagation}

## 3.1.5 Non-existence of nonzero linear structure

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.LinearStructures}

## 3.1.6 Algebraic immunity

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.AlgebraicImmunity}

## 3.1.7 Other criteria

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.Autocorrelation}

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.MaximumCorrelation}

{include 3 CryptBooleanBlueprint.Carlet.Chapter04.OtherCriteria}
