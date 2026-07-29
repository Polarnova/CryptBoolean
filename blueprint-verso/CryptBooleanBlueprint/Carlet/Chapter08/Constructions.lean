/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter08.DobbertinObstruction
import CryptBoolean.Carlet.Chapter08.MaioranaMcFarland

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Constructions and obstructions" =>

:::theorem "carlet-8-maiorana-mcfarland-pc-construction" (parent := "carlet-chapter-8") (lean := "CryptBoolean.binaryMapDerivative, CryptBoolean.binaryMapDerivative_zero, CryptBoolean.MaioranaMcFarlandFibersHaveMinimumDistanceGreaterThan, CryptBoolean.booleanDerivative_booleanMaioranaMcFarlandGeneral_append, CryptBoolean.booleanDerivative_booleanMaioranaMcFarlandGeneral_append_apply, CryptBoolean.binaryMapDerivative_ne_zero_iff_fibersHaveMinimumDistanceGreaterThan, CryptBoolean.satisfiesPropagationCriterion_booleanMaioranaMcFarlandGeneral, CryptBoolean.satisfiesPropagationCriterion_booleanMaioranaMcFarlandGeneral_of_fibers") (uses := "carlet-7-rel-59-maiorana-mcfarland-general, carlet-2-def-2-derivative, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-8, maiorana-mcfarland, propagation-criterion, construction, page-132, fidelity-exact")
*Maiorana--McFarland propagation construction (Carlet, p. 132).* Let
$`\phi:V_s\to V_r`, $`g:V_s\to\mathbb F_2`, and
$$`
f(x,y)=x\cdot\phi(y)\oplus g(y).
`
For $`a\in V_r` and $`b\in V_s`, its derivative is
$$`
D_{(a,b)}f(x,y)=x\cdot D_b\phi(y)\oplus
a\cdot\phi(y\oplus b)\oplus D_bg(y).
`
Suppose that $`D_b\phi(y)\ne0` for every $`y` and every nonzero $`b` with
$`w_H(b)\le\ell`, and that $`y\mapsto a\cdot\phi(y)` is balanced for every
nonzero $`a` with $`w_H(a)\le\ell`. Then $`f` satisfies
$`\mathrm{PC}(\ell)`. The first hypothesis is equivalent to every fiber of
$`\phi` being empty, a singleton, or a code of minimum distance greater than
$`\ell`.
:::

:::theorem "carlet-8-dobbertin-pc-obstruction" (parent := "carlet-chapter-8") (lean := "CryptBoolean.not_satisfiesPropagationCriterion_dobbertinConstruction") (uses := "carlet-8-prop-35-affine-flat-walsh-square-characterization, carlet-7-prop-33-dobbertin-walsh") (tags := "carlet, chapter-8, dobbertin, propagation-criterion, obstruction, page-132, fidelity-exact")
*Obstruction for Dobbertin's construction (Carlet, p. 132).* Let $`n>0` be
even. Let $`f:V_{n/2}\times V_{n/2}\to\mathbb F_2` be bent with
$`f(x,0)=0` for every $`x`, let $`g:V_{n/2}\to\mathbb F_2` be balanced, and
define
$$`
h(x,y)=f(x,y)\oplus\delta_0(y)g(x).
`
If $`n/2\le\ell\le n`, then $`h` does not satisfy $`\mathrm{PC}(\ell)`.
:::
