/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.MaioranaMcFarlandCounting

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "On the number of bent functions" =>

:::theorem "carlet-6-maiorana-mcfarland-count" (parent := "carlet-chapter-6") (lean := "CryptBoolean.MaioranaMcFarlandParameters, CryptBoolean.booleanMaioranaMcFarlandPermutation, CryptBoolean.booleanMaioranaMcFarlandPermutation_joinF₂CubeBlocks, CryptBoolean.booleanMaioranaMcFarlandOfParameters, CryptBoolean.booleanMaioranaMcFarlandOfParameters_injective, CryptBoolean.card_maioranaMcFarlandParameters, CryptBoolean.originalMaioranaMcFarlandClass, CryptBoolean.card_originalMaioranaMcFarlandClass, CryptBoolean.isBent_booleanMaioranaMcFarlandPermutation, CryptBoolean.originalMaioranaMcFarlandClass_subset_bentFunctionFamily") (uses := "carlet-6-maiorana-mcfarland") (tags := "carlet, chapter-6, counting, page-97, fidelity-exact")
*Number of Maiorana--McFarland functions (Carlet, p. 97).* In dimension
$`n=2m`, the original Maiorana--McFarland class contains exactly
$$`
(2^m)!\,2^{2^m}
`
distinct bent functions.
:::

:::theorem "carlet-6-naive-bent-count-bound" (parent := "carlet-chapter-6") (lean := "CryptBoolean.bentFunctionFamily, CryptBoolean.mem_bentFunctionFamily_iff, CryptBoolean.card_bentFunctionFamily_le_naiveBound") (uses := "carlet-6-prop-18-rothaus-degree-bound, carlet-3-reed-muller-dimension") (tags := "carlet, chapter-6, counting, naive-bound, page-97, fidelity-exact")
*Naive upper bound for the number of bent functions (Carlet, p. 97).* If
$`n\ge4` is even, then the number $`B_n` of bent functions on $`V_n`
satisfies
$$`
B_n\le 2^{\sum_{i=0}^{n/2}\binom ni}.
`
:::
