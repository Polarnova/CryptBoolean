/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter04.DegreeCount

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Distribution of algebraic degree" =>

:::theorem "carlet-4-degree-count" (parent := "carlet-chapter-4") (lean := "CryptBoolean.sum_choose_le_n_sub_two, CryptBoolean.card_booleanFunctions_degree_le_n_sub_two, CryptBoolean.card_booleanFunctions_degree_le_n_sub_two_eq, CryptBoolean.natCard_booleanFunction, CryptBoolean.highAlgebraicDegreeProbability, CryptBoolean.highAlgebraicDegreeProbability_eq_card_ratio, CryptBoolean.tendsto_highAlgebraicDegreeProbability") (uses := "carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree") (tags := "carlet, chapter-4, algebraic-degree, page-49, fidelity-exact")
*High algebraic degree is typical (Carlet, p. 49).* For $`n\ge2`, the number
of functions $`f:V_n\to\mathbb F_2` with $`\deg_{\mathrm{alg}}(f)\le n-2` is
$$`
2^{\sum_{i=0}^{n-2}\binom ni}=2^{2^n-n-1}.
`
Consequently, the probability that a uniformly chosen $`n`-variable Boolean
function has degree at least $`n-1` tends to one as $`n\to\infty`.
:::
