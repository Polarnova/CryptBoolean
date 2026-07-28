/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.HyperBentPartialSpread

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Hyper-bent functions" =>

:::definition "carlet-6-def-hyper-bent" (parent := "carlet-chapter-6") (lean := "CryptBoolean.fieldWalshTransform, CryptBoolean.IsFieldBent, CryptBoolean.fieldPowerReindex, CryptBoolean.fieldPowerMap_bijective, CryptBoolean.fieldPowerEquiv, CryptBoolean.fieldPowerEquiv_apply, CryptBoolean.fieldPowerReindex_eq_comp_fieldPowerEquiv, CryptBoolean.IsHyperBent, CryptBoolean.exists_fieldWalshTransform_eq_walshTransform, CryptBoolean.exists_walshTransform_eq_fieldWalshTransform, CryptBoolean.isFieldBent_iff_isBent_comp_linearEquiv, CryptBoolean.IsHyperBent.isFieldBent, CryptBoolean.isHyperBent_iff_forall_isBent_powerReindex_comp_linearEquiv") (uses := "carlet-2-absolute-trace, carlet-2-trace-pairing-coordinates, carlet-6-def-7-bent") (tags := "carlet, chapter-6, hyper-bent, pages-100-101, fidelity-exact")
*Hyper-bent functions (Carlet, pp. 100--101).* Let $`n` be even and
$`f:\operatorname{GF}(2^n)\to\mathbb F_2`. The function $`f` is hyper-bent
when, for every integer $`i` coprime to $`2^n-1`, every $`a` in the field,
and both $`\varepsilon\in\mathbb F_2`, its distance to
$`x\mapsto\operatorname{Tr}_n(ax^i)+\varepsilon` is
$`2^{n-1}\pm2^{n/2-1}`. Equivalently, every function $`x\mapsto f(x^i)`
is bent. In particular, every hyper-bent function is bent.
:::

:::lemma_ "carlet-6-lemma-4-subfield-intersection" (parent := "carlet-chapter-6") (lean := "CryptBoolean.quadraticSubfieldBasisMap_bijective, CryptBoolean.quadraticSubfieldBasisEquiv, CryptBoolean.quadraticSubfieldBasisEquiv_apply, CryptBoolean.existsUnique_subfield_power_intersection") (uses := "carlet-6-def-hyper-bent, carlet-2-absolute-trace") (tags := "carlet, chapter-6, lemma-4, page-102, fidelity-corrected-even-dimension")
*Lemma 4 (Carlet, p. 102; corrected dimension convention).* Let $`m>0`,
let $`K=\operatorname{GF}(2^m)` be the quadratic subfield of
$`L=\operatorname{GF}(2^{2m})`, and let $`a,\omega\in L\setminus K`. If
$`i` is coprime to $`2^{2m}-1`, then there is a unique $`z\in K` such that
$$`
a(z+\omega)^i\in K.
`
:::

:::proposition "carlet-6-prop-25-psap-hyper-bent" (parent := "carlet-chapter-6") (lean := "CryptBoolean.quadraticSubfield_powerMap_bijective, CryptBoolean.pow_mem_quadraticSubfield_iff, CryptBoolean.relativeTrace_eq_zero_iff_mem_quadraticSubfield, CryptBoolean.absoluteTrace_mul_quadraticSubfield, CryptBoolean.sum_bitSignInt_absoluteTrace_mul_eq_zero, CryptBoolean.sum_quadraticSubfieldTraceCharacter_of_mem, CryptBoolean.sum_quadraticSubfieldTraceCharacter_of_not_mem, CryptBoolean.psapFunction, CryptBoolean.psapFunction_coordinate, CryptBoolean.sum_bitSignInt_field_eq_zero_of_balanced, CryptBoolean.fieldPowerTraceTransform, CryptBoolean.fieldPowerTraceTransform_psap_eq, CryptBoolean.fieldPowerTraceTransform_psap_natAbs, CryptBoolean.isHyperBent_of_forall_fieldPowerTraceTransform, CryptBoolean.isHyperBent_psapFunction") (uses := "carlet-6-def-hyper-bent, carlet-6-lemma-4-subfield-intersection, carlet-6-partial-spread-construction, carlet-5-quadratic-trace-representation") (tags := "carlet, chapter-6, proposition-25, pages-101-102, fidelity-corrected-positive-half-dimension")
*Proposition 25 (Carlet, pp. 101--102).* Let $`m\ge2`, put
$`K=\operatorname{GF}(2^m)` and $`L=\operatorname{GF}(2^{2m})`, choose
$`\omega\in L\setminus K`, and write every $`x\in L` uniquely as
$`x=y'+\omega y` with $`y',y\in K`. If $`g:K\to\mathbb F_2` is balanced
and $`g(0)=0`, define
$$`
f(y'+\omega y)=g(y'/y),
`
with $`y'/y=0` when $`y=0`. Then $`f` is hyper-bent. Equivalently, every
function in Dillon's class $`PS_{ap}` is hyper-bent.
:::
