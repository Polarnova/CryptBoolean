/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.FiniteField

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Finite-field representations" =>

:::definition "carlet-2-absolute-trace" (lean := "CryptBoolean.BinaryGaloisField, CryptBoolean.FieldBooleanFunction, CryptBoolean.absoluteTrace, CryptBoolean.algebraMap_absoluteTrace_eq_sum_frobenius, CryptBoolean.exists_absoluteTrace_eq_one, CryptBoolean.traceLift, CryptBoolean.absoluteTrace_traceLift") (tags := "carlet, chapter-2, finite-field, mathlib-reuse")
The binary extension field is Mathlib's $`\mathrm{GF}(2^n)`.  Its absolute trace is
the finite-field trace to $`\mathbb F_2`, agrees with the Frobenius sum for $`n>0`,
and is surjective.
:::

:::theorem "carlet-2-univariate-representation" (lean := "CryptBoolean.univariateRepresentation, CryptBoolean.eval_univariateRepresentation, CryptBoolean.degree_univariateRepresentation_lt_card, CryptBoolean.existsUnique_univariateRepresentation") (uses := "carlet-2-absolute-trace") (tags := "carlet, chapter-2, relation-9, lagrange, mathlib-reuse")
Every field-valued function on $`\mathrm{GF}(2^n)` has a unique representing
polynomial of degree strictly below $`2^n`, obtained through Mathlib's finite
Lagrange interpolation.
:::
