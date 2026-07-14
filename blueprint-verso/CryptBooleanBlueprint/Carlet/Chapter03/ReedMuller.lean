/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter03.ReedMuller

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Reed--Muller codes" =>

:::definition "carlet-3-reed-muller-code" (lean := "CryptBoolean.reedMuller, CryptBoolean.mem_reedMuller_iff, CryptBoolean.reedMuller_mono, CryptBoolean.affineFunction_mem_reedMuller_one, CryptBoolean.reedMuller_distance_pos") (uses := "carlet-2-function-degree-distance") (tags := "carlet, chapter-3, section-3-1, reed-muller")
The Reed--Muller code $`R(r,n)` is the $`\mathbb F_2`-subspace of Boolean
functions of algebraic degree at most $`r`.  The codes are nested in $`r`, and
the first-order code contains every affine function.
:::

:::theorem "carlet-3-theorem-1-order-one" (lean := "CryptBoolean.hammingWeight_affineFunction_one_zero, CryptBoolean.two_pow_sub_one_le_hammingWeight_of_degree_le_one, CryptBoolean.reedMuller_one_distance_lower_bound") (uses := "carlet-3-reed-muller-code, carlet-2-affine-functions") (tags := "carlet, chapter-3, theorem-1, order-one-closed")
For $`f\ne0` of degree at most one, $`\mathrm{wt}(f)\ge2^{n-1}`.  Equivalently,
any two distinct codewords of $`R(1,n)` have Hamming distance at least
$`2^{n-1}`.
:::

The general-order form of Theorem 1, the equality characterization by flat
indicators (Proposition 12), the dimension formula, and Reed--Muller duality
(Theorem 2) remain open Chapter 3 nodes; no placeholder declarations are
associated with them.
