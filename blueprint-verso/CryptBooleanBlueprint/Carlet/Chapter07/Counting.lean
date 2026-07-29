/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter07.MaioranaMcFarlandCounting
import CryptBoolean.Carlet.Chapter07.NaiveCounting

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Counting resilient functions" =>

:::theorem "carlet-7-maiorana-mcfarland-count" (parent := "carlet-chapter-7") (lean := "CryptBoolean.pointwiseConstrainedGeneralMaioranaMcFarlandParametersEquiv, CryptBoolean.card_pointwiseConstrainedGeneralMaioranaMcFarlandParameters, CryptBoolean.card_nonzero_f₂Cube, CryptBoolean.card_f₂Cube_weight_gt_eq_sum_choose, CryptBoolean.card_nonzeroGeneralMaioranaMcFarlandParameters, CryptBoolean.card_highWeightGeneralMaioranaMcFarlandParameters, CryptBoolean.card_nonzeroGeneralMaioranaMcFarlandParameters_le, CryptBoolean.card_nonzeroGeneralMaioranaMcFarlandParameters_sourceBound_lt_at_two") (uses := "carlet-7-rel-59-maiorana-mcfarland-general, carlet-7-maximum-correlation-support") (tags := "carlet, chapter-7, maiorana-mcfarland, counting, page-129, fidelity-corrected-r-two")
*Maiorana--McFarland counts (Carlet, p. 129).* Let $`r>0` and
$`s=n-r`. The number of pairs $`(\varphi,g)` in Relation (59) satisfying
$`\varphi(y)\ne0` for every $`y` is
$$`
(2^{r+1}-2)^{2^s}.
`
The number satisfying $`w_H(\varphi(y))>m` for every $`y` is
$$`
\left(
  2\sum_{i=m+1}^{r}\binom ri
\right)^{2^{n-r}}.
`
If $`r=1` or $`r\ge3`, the first quantity is at most
$`2^{2^{n-1}}`. At $`r=2` the printed bound is false and the strict
reverse inequality holds.
:::

:::theorem "carlet-7-naive-resilient-count-bound" (parent := "carlet-chapter-7") (lean := "CryptBoolean.exists_eq_affineFunction_fullFrequency_of_isResilient_natPred, CryptBoolean.natCard_isResilient_le_naiveBound") (uses := "carlet-7-siegenthaler-degree-bounds, carlet-4-degree-count") (tags := "carlet, chapter-7, resiliency, counting, page-129, fidelity-exact")
*Naive counting bound (Carlet, p. 129).* The number of $`m`-resilient
$`n`-variable Boolean functions is at most
$$`
2^{\sum_{i=0}^{n-m-1}\binom ni}.
`
The count is extensional and counts Boolean functions, with algebraic normal
forms serving as their unique representation.
:::
