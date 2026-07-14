/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.ANF

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic normal form skeleton" =>

:::definition "carlet-2-anf-skeleton" (lean := "CryptBoolean.ANFCoefficients, CryptBoolean.anfMonomial, CryptBoolean.anfEval, CryptBoolean.anfSupport, CryptBoolean.algebraicDegree, CryptBoolean.mem_anfSupport, CryptBoolean.anfMonomial_empty, CryptBoolean.anfEval_zero, CryptBoolean.anfEval_add, CryptBoolean.algebraicDegree_le_dimension") (uses := "carlet-2-def-boolean-function") (tags := "carlet, chapter-2, section-2-1")
An algebraic normal form over $`\mathbb F_2` is represented by a square-free
coefficient family indexed by coordinate subsets. Evaluation is the finite sum
of coefficients times square-free monomials. Its support is the finite family
of nonzero coefficients, and its algebraic degree is the maximum support size,
with the zero coefficient family assigned degree zero.
:::
