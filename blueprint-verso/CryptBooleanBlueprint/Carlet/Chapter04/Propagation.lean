/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter04

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Propagation criteria" =>

:::definition "carlet-4-def-propagation-criteria" (parent := "carlet-chapter-4") (lean := "CryptBoolean.lowWeightNonzeroDirections, CryptBoolean.SatisfiesPropagationCriterionOn, CryptBoolean.SatisfiesPropagationCriterion, CryptBoolean.satisfiesPropagationCriterion_iff_on_lowWeightNonzeroDirections, CryptBoolean.isBalanced_booleanDerivative_iff_autocorrelation_eq_zero, CryptBoolean.satisfiesPropagationCriterion_iff_autocorrelation_eq_zero, CryptBoolean.SatisfiesStrictAvalancheCriterion, CryptBoolean.satisfiesStrictAvalancheCriterion_iff_pc_one, CryptBoolean.SatisfiesPropagationCriterion.mono, CryptBoolean.coordinateRestriction, CryptBoolean.SatisfiesPropagationCriterionOfOrder, CryptBoolean.SatisfiesPropagationCriterionOfOrder.mono_order, CryptBoolean.SatisfiesPropagationCriterionOfOrder.mono_level, CryptBoolean.SatisfiesStrictAvalancheCriterionOfOrder, CryptBoolean.satisfiesStrictAvalancheCriterionOfOrder_iff_pc_one, CryptBoolean.SatisfiesExtendedPropagationCriterion, CryptBoolean.SatisfiesExtendedPropagationCriterion.toPropagationCriterionOfOrder") (uses := "carlet-2-def-2-derivative, carlet-2-def-autocorrelation, carlet-2-balanced-zero-walsh, carlet-4-def-resiliency-correlation-immunity") (tags := "carlet, chapter-4, propagation-criterion, sac, epc, pages-58-59, fidelity-exact")
*Propagation criteria (Carlet, pp. 58--59).* A function $`f` satisfies the
propagation criterion with respect to $`E\subseteq V_n` if $`D_af` is
balanced for every $`a\in E`. It satisfies $`\mathrm{PC}(\ell)` if
$$`
\Delta_f(a)=0
\quad\text{whenever}\quad 0<w_H(a)\le\ell;
`
$`\mathrm{SAC}` is $`\mathrm{PC}(1)`. The order-$`k` form requires every
restriction obtained by fixing $`k` coordinates to satisfy the criterion.
Finally, $`\mathrm{EPC}(\ell)` of order $`k` requires every such nonzero
$`D_af` to be $`k`-resilient; it implies the corresponding propagation
criterion.
:::
