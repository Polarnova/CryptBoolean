/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.AdditionalDecompositions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Decompositions of bent functions" =>

:::theorem "carlet-6-theorem-11-hyperplane-restrictions" (parent := "carlet-chapter-6") (lean := "CryptBoolean.singletonF₂Cube, CryptBoolean.singletonF₂Cube_apply, CryptBoolean.singletonF₂CubeLinearEquiv, CryptBoolean.sum_singletonF₂Cube, CryptBoolean.walshTransform_append_singletonF₂Cube, CryptBoolean.linearHyperplaneRestriction, CryptBoolean.HasComplementaryHyperplaneRestrictionSpectra, CryptBoolean.isBent_iff_hasComplementaryHyperplaneRestrictionSpectra, CryptBoolean.hyperplaneExtension, CryptBoolean.hyperplaneExtension_append_singletonF₂Cube, CryptBoolean.linearHyperplaneRestriction_hyperplaneExtension_refl, CryptBoolean.isBent_hyperplaneExtension_of_complementaryWalshSpectra, CryptBoolean.isBent_iff_forall_hasComplementaryHyperplaneRestrictionSpectra, CryptBoolean.isBent_iff_exists_hasComplementaryHyperplaneRestrictionSpectra") (uses := "carlet-2-prop-9-restriction-square, carlet-6-def-7-bent") (tags := "carlet, chapter-6, theorem-11, pages-95-96, fidelity-exact")
*Theorem 11 (Carlet, pp. 95--96).* Let $`n\ge4` be even and let
$`f:V_n\to\mathbb F_2`. For a linear hyperplane $`E`, identify $`E` and
its complementary coset with $`V_{n-1}` and denote the two restrictions by
$`h_0,h_1`. The following are equivalent:

1. $`f` is bent;
2. for every linear hyperplane, and equivalently for at least one linear
   hyperplane, the transforms $`W_{h_0}` and $`W_{h_1}` take values in
   $`\{0,\pm2^{n/2}\}`, and at every frequency exactly one is nonzero.
:::

:::corollary "carlet-6-hyperplane-restriction-plateaued" (parent := "carlet-chapter-6") (lean := "CryptBoolean.hasPlateauedWalshAmplitude_linearHyperplaneRestriction_of_isBent, CryptBoolean.isPlateaued_linearHyperplaneRestriction_of_isBent, CryptBoolean.nonlinearity_linearHyperplaneRestriction_of_isBent") (uses := "carlet-6-theorem-11-hyperplane-restrictions, carlet-6-def-plateaued, carlet-4-rel-35-nonlinearity-walsh") (tags := "carlet, chapter-6, hyperplane-restriction, page-96, fidelity-exact")
*Hyperplane-restriction consequence (Carlet, p. 96).* Every restriction of
an $`n`-variable bent function to an affine hyperplane, with $`n\ge4` even,
is plateaued on $`V_{n-1}` with amplitude $`2^{n/2}` and has the optimal
odd-dimensional nonlinearity
$$`
2^{n-2}-2^{(n-2)/2}.
`
:::

:::theorem "carlet-6-balanced-hyperplane-derivative-restrictions" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_linearHyperplaneRestriction_of_balanced_derivatives") (uses := "carlet-6-theorem-11-hyperplane-restrictions, carlet-6-theorem-8-perfect-nonlinearity") (tags := "carlet, chapter-6, decomposition, page-97, fidelity-exact-coordinate-identification")
*Balanced derivatives along a hyperplane (Carlet, p. 97).* Let
$`f:V_{2k+1}\to\mathbb F_2`, and let $`E` be a linear hyperplane. If
$`D_u f` is balanced for every nonzero $`u\in E`, then the restrictions of
$`f` to $`E` and to its complementary coset are bent.
:::

:::theorem "carlet-6-codimension-two-restrictions" (parent := "carlet-chapter-6") (lean := "CryptBoolean.four_mul_walshTransform_firstBlockSlice_eq, CryptBoolean.walshMagnitudeSet, CryptBoolean.walshMagnitudeSet_firstBlockSlice_eq, CryptBoolean.isBent_firstBlockSlices_iff_bentDual_secondDerivative_eq_one") (uses := "carlet-6-theorem-10-slice-construction, carlet-6-dual, carlet-6-quadratic-bent-characterization, carlet-6-prop-24-second-order-characterization") (tags := "carlet, chapter-6, decomposition, page-97, fidelity-exact-coordinate-identification")
*Restrictions to four codimension-two cosets (Carlet, p. 97).* Let $`f` be
bent on $`V_N`, with $`N` even, and let $`E\le V_N` have codimension two.
The four restrictions of $`f` to the cosets of $`E`, viewed in any fixed
linear coordinate identification with $`V_{N-2}`, have the same set of
Walsh magnitudes. If $`E^\perp=\langle a,b\rangle`, then all four
restrictions are bent if and only if
$$`
D_aD_b\widetilde f=1.
`
:::
