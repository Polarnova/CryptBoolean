/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.CompleteQuadratic
import CryptBoolean.Carlet.Chapter06.Kerdock
import CryptBoolean.Carlet.Chapter06.KerdockCoordinateIdentity
import CryptBoolean.Carlet.Chapter06.KerdockFieldConstruction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Kerdock codes" =>

:::theorem "carlet-6-rel-56-complete-quadratic" (parent := "carlet-chapter-6") (lean := "FABL.completeQuadraticBit, CryptBoolean.functionAlgebraicDegree_completeQuadraticBit_le_two, CryptBoolean.completeQuadraticBit_eq_choose_support_card, CryptBoolean.completeQuadraticPolarFrequency, CryptBoolean.quadraticPolarKernel_completeQuadraticBit_eq_crossSum, CryptBoolean.quadraticPolarKernel_completeQuadraticBit_eq_dotProduct, CryptBoolean.completeQuadraticPolarFrequency_eq_zero_of_even, CryptBoolean.quadraticRadical_completeQuadraticBit_eq_bot, CryptBoolean.isBent_completeQuadraticBit, CryptBoolean.completeQuadraticBit_zero_dimension, CryptBoolean.isBent_completeQuadraticBit_zero_dimension, CryptBoolean.completeQuadraticBit_two_dimension, CryptBoolean.isBent_completeQuadraticBit_two_dimension") (uses := "carlet-6-quadratic-bent-characterization, carlet-2-def-support-weight") (tags := "carlet, chapter-6, relation-56, pages-109-110, fidelity-exact")
*Relation (56) (Carlet, pp. 109--110).* Define the complete quadratic
function on $`V_n` by
$$`
q_n(x)=\sum_{1\le i<j\le n}x_ix_j.
`
For every $`x\in V_n`, its value is the parity of
$`\binom{w_H(x)}2`. If $`n` is even, the polar form of $`q_n` has trivial
radical and $`q_n` is bent.
:::

:::theorem "carlet-6-kerdock-parameters" (parent := "carlet-chapter-6") (lean := "CryptBoolean.IsKerdockRepresentativeFamily, CryptBoolean.kerdockCodeOfRepresentatives, CryptBoolean.functionAlgebraicDegree_le_two_of_mem_kerdockRepresentatives, CryptBoolean.reedMuller_one_subset_kerdockCodeOfRepresentatives, CryptBoolean.kerdockCodeOfRepresentatives_subset_reedMuller_two, CryptBoolean.nonlinearity_add_eq_kerdockDistance_of_mem, CryptBoolean.hasDistinctFirstOrderCosets_of_isKerdockRepresentativeFamily, CryptBoolean.kerdockRepresentativeFamily_offDiag_nonempty, CryptBoolean.card_kerdockCodeOfRepresentatives, CryptBoolean.minimumPairNonlinearity_eq_kerdockDistance, CryptBoolean.minimumHammingDistance_kerdockCodeOfRepresentatives, CryptBoolean.kerdockCodeOfRepresentatives_parameters") (uses := "carlet-6-def-7-bent, carlet-3-reed-muller-code, carlet-4-reed-muller-coset-distance") (tags := "carlet, chapter-6, kerdock, pages-109-110, fidelity-exact-conditional-reduction")
*Kerdock parameters (Carlet, pp. 109--110).* Let $`n\ge2` be even and
let $`F` be a family of $`2^{n-1}` Boolean functions on $`V_n` containing
zero. Suppose that every nonzero member of $`F` has algebraic degree two
and that $`f+g` is bent whenever $`f,g\in F` are distinct. Then
$$`
K(F)=\bigcup_{f\in F}\bigl(f+R(1,n)\bigr)
`
contains $`R(1,n)`, is contained in $`R(2,n)`, has $`2^{2n}` words, and
has minimum distance
$`2^{n-1}-2^{n/2-1}`. The first-order Reed--Muller cosets in this union
are pairwise distinct.
:::

:::theorem "carlet-6-kerdock-field-trace-identity" (parent := "carlet-chapter-6") (lean := "CryptBoolean.completeQuadraticBit_eq_kerdockFieldRepresentative_one_of_selfDualNormalCoordinates") (uses := "carlet-6-rel-56-complete-quadratic, carlet-2-absolute-trace, carlet-6-kerdock-field-construction") (tags := "carlet, chapter-6, kerdock, relation-56, pages-109-110, fidelity-exact-explicit-coordinate-hypotheses")
*Self-dual normal-basis trace identity (Carlet, pp. 109--110).* Let
$`m=2t+1` and identify $`V_m` with $`\mathbb F_{2^m}` through a self-dual
normal basis. Explicitly, assume that the coordinate equivalence intertwines
Frobenius squaring with cyclic rotation, identifies the absolute trace with
the coordinate sum, and identifies the trace pairing with the standard
binary dot product. Under the induced identification
$`V_{m+1}\simeq\mathbb F_{2^m}\times\mathbb F_2`, the complete quadratic
function of Relation (56) is
$$`
q(x,z)=\operatorname{Tr}_m\!\left(\sum_{j=1}^{t}x^{2^j+1}\right)
      +z\operatorname{Tr}_m(x).
`
:::

:::theorem "carlet-6-kerdock-field-construction" (parent := "carlet-chapter-6") (lean := "CryptBoolean.kerdockTraceQuadratic, CryptBoolean.kerdockFieldQuadratic, CryptBoolean.absoluteTrace_algebraMap_odd, CryptBoolean.kerdockTraceCube, CryptBoolean.kerdockTraceLinearCube, CryptBoolean.functionAlgebraicDegree_kerdockTraceCube_le_two, CryptBoolean.functionAlgebraicDegree_kerdockTraceLinearCube_le_one, CryptBoolean.kerdockFieldCoordinateEquiv, CryptBoolean.kerdockFieldRepresentative, CryptBoolean.kerdockFieldRepresentative_coordinate, CryptBoolean.kerdockFieldRepresentative_zero, CryptBoolean.functionAlgebraicDegree_kerdockFieldRepresentative_le_two, CryptBoolean.quadraticPolarKernel_kerdockFieldRepresentative, CryptBoolean.quadraticPolarKernel_kerdockFieldRepresentative_add, CryptBoolean.eq_zero_of_forall_quadraticPolarKernel_kerdockFieldRepresentative_add, CryptBoolean.isBent_kerdockFieldRepresentative_add, CryptBoolean.functionAlgebraicDegree_kerdockFieldRepresentative_eq_two, CryptBoolean.kerdockFieldRepresentative_injective, CryptBoolean.kerdockFieldRepresentativeFamily, CryptBoolean.card_kerdockFieldRepresentativeFamily, CryptBoolean.isKerdockRepresentativeFamily_kerdockField, CryptBoolean.kerdockFieldConstruction_parameters") (uses := "carlet-5-quadratic-trace-representation, carlet-6-quadratic-bent-characterization, carlet-6-kerdock-parameters, carlet-2-absolute-trace, carlet-2-trace-pairing-coordinates") (tags := "carlet, chapter-6, kerdock, pages-109-110, fidelity-source-footnote-44-coordinate-invariant")
*Finite-field construction of the Kerdock code (Carlet, pp. 109--110).*
Let $`m=2t+1`, set $`n=m+1`, and define
$$`
q(x,z)=\operatorname{Tr}_m\!\left(\sum_{j=1}^{t}x^{2^j+1}\right)
      +z\operatorname{Tr}_m(x)
`
on $`\mathbb F_{2^m}\times\mathbb F_2`. For
$`u\in\mathbb F_{2^m}`, set $`q_u(x,z)=q(ux,z)` and transport these
functions to $`V_n` along an $`\mathbb F_2`-linear coordinate
identification. The representative $`q_0` is zero, every $`q_u` with
$`u\ne0` has algebraic degree two, and $`q_u+q_v` is bent whenever
$`u\ne v`. Thus the $`2^m` representatives form a Kerdock representative
family. Consequently the union of the cosets $`q_u+R(1,n)` is a Kerdock
code with $`2^{2n}` words and minimum distance
$`2^{n-1}-2^{n/2-1}`.
:::
