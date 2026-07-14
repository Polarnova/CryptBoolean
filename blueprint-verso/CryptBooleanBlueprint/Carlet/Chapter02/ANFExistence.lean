/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter02.ANFExistence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic normal form existence and uniqueness" =>

:::theorem "carlet-2-anf-existence-uniqueness" (lean := "CryptBoolean.anfMonomial_f₂CubeOfFinset, CryptBoolean.anfEval_f₂CubeOfFinset, CryptBoolean.anfCoeff, CryptBoolean.anfEval_anfCoeff_f₂CubeOfFinset, CryptBoolean.anfEval_anfCoeff, CryptBoolean.anfCoeff_unique_of_powerset_sum, CryptBoolean.anfEval_injective, CryptBoolean.existsUnique_anfEval") (uses := "carlet-2-anf-skeleton") (tags := "carlet, chapter-2, section-2-1")
Every Boolean function $`f:\mathbb F_2^n\to\mathbb F_2` has a unique algebraic normal form:
there is exactly one square-free coefficient family $`c` with
$`f(x)=\sum_{S\subseteq[n]} c(S)\prod_{i\in S} x_i`.
The canonical coefficients are the characteristic-two Möbius inverse
$`c(S)=\sum_{T\subseteq S} f(\mathbf 1_T)`, and the interval-parity count
$`\#[T,U]=2^{|U|-|T|}` collapses every off-diagonal contribution modulo two.
:::
