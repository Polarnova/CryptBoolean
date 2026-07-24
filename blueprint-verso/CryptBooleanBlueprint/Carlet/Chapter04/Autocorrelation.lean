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

#doc (Manual) "Autocorrelation indicators" =>

:::definition "carlet-4-def-autocorrelation-indicators" (parent := "carlet-chapter-4") (lean := "CryptBoolean.sumOfSquaresIndicator, CryptBoolean.absoluteIndicator, CryptBoolean.booleanDerivative_comp_affineEquiv, CryptBoolean.autocorrelation_comp_affineEquiv, CryptBoolean.sumOfSquaresIndicator_comp_affineEquiv, CryptBoolean.absoluteIndicator_comp_affineEquiv, CryptBoolean.absoluteIndicator_zero_dimension") (uses := "carlet-2-def-autocorrelation") (tags := "carlet, chapter-4, relation-38, autocorrelation, page-64, fidelity-exact-with-zero-dimensional-convention")
*Relation (38) (Carlet, p. 64).* Define the sum-of-squares indicator and
absolute indicator by
$$`
\mathcal V(f)=\sum_{e\in V_n}\Delta_f(e)^2,
\qquad
\Delta(f)=\max_{e\ne0}|\Delta_f(e)|.
`
Both quantities are invariant under affine equivalence.
:::

:::theorem "carlet-4-autocorrelation-indicator-bounds" (parent := "carlet-chapter-4") (lean := "CryptBoolean.autocorrelation_zero, CryptBoolean.sumOfSquaresIndicator_lower_bound, CryptBoolean.sumOfSquaresIndicator_eq_two_pow_iff, CryptBoolean.absoluteIndicator_sq_lower_bound, CryptBoolean.absoluteIndicator_lower_bound, CryptBoolean.autocorrelation_sq_of_mem_linearKernel, CryptBoolean.sumOfSquaresIndicator_lower_bound_linearKernel, CryptBoolean.sumOfSquaresIndicator_lower_bound_of_finrank_eq") (uses := "carlet-4-def-autocorrelation-indicators, carlet-4-def-linear-kernel, carlet-2-balanced-zero-walsh") (tags := "carlet, chapter-4, autocorrelation, indicators, pages-64-65, fidelity-exact")
*Bounds for autocorrelation indicators (Carlet, pp. 64--65).* One has
$$`
\mathcal V(f)\ge2^{2n},
\qquad
\Delta(f)\ge
\sqrt{\frac{\mathcal V(f)-2^{2n}}{2^n-1}}.
`
The second inequality is asserted for $`n>0`.
Equality $`\mathcal V(f)=2^{2n}` holds exactly when every nonzero derivative
is balanced. If $`\dim\ker_{\mathrm{lin}}(f)=k`, then
$`\mathcal V(f)\ge2^{2n+k}`.
:::

:::theorem "carlet-4-second-derivative-sum" (parent := "carlet-chapter-4") (lean := "CryptBoolean.secondBooleanDerivative, CryptBoolean.secondBooleanDerivative_apply, CryptBoolean.sumOfSquaresIndicator_eq_sum_secondBooleanDerivative") (uses := "carlet-4-def-autocorrelation-indicators, carlet-2-rel-26-total-autocorrelation") (tags := "carlet, chapter-4, second-derivative, page-65, fidelity-exact")
*Second-derivative expression for the indicator (Carlet, p. 65).* With
$$`
D_aD_ef(x)=f(x)+f(x+a)+f(x+e)+f(x+a+e),
`
one has
$$`
\mathcal V(f)=\sum_{a,e\in V_n}\mathcal F(D_aD_ef),
`
where $`\mathcal F(h)=\sum_x(-1)^{h(x)}`.
:::

:::theorem "carlet-4-rel-39-fourth-walsh-moment" (parent := "carlet-chapter-4") (lean := "CryptBoolean.sum_walshTransform_sq_mul_add_sq_eq, CryptBoolean.sum_walshTransform_fourth_eq_two_pow_mul_sumOfSquaresIndicator") (uses := "carlet-4-def-autocorrelation-indicators, carlet-2-rel-25-wiener-khinchin, carlet-2-rel-22-plancherel") (tags := "carlet, chapter-4, relation-39, fourth-moment, pages-65-66, fidelity-exact")
*Relation (39) (Carlet, pp. 65--66).* For every $`a\in V_n`,
$$`
\sum_{e\in V_n}W_f(e)^2W_f(a+e)^2
=2^n\sum_{e\in V_n}\Delta_f(e)^2(-1)^{e\mathbin\cdot a}.
`
In particular,
$$`
\sum_{e\in V_n}W_f(e)^4=2^n\mathcal V(f).
`
:::

:::theorem "carlet-4-indicator-nonlinearity-spectral-support" (parent := "carlet-chapter-4") (lean := "CryptBoolean.HasPlateauedWalshSpectrum, CryptBoolean.abs_walshTransform_le_maxWalshMagnitude, CryptBoolean.sum_walshTransform_fourth_le_sum_sq_mul_maxWalshMagnitude_sq, CryptBoolean.sum_walshTransform_fourth_le_two_pow_mul_maxWalshMagnitude_fourth, CryptBoolean.sumOfSquaresIndicator_div_two_pow_le_maxWalshMagnitude_sq, CryptBoolean.sumOfSquaresIndicator_le_maxWalshMagnitude_fourth, CryptBoolean.inv_sqrt_two_pow_mul_sqrt_sumOfSquaresIndicator_le_maxWalshMagnitude, CryptBoolean.rpow_one_fourth_sumOfSquaresIndicator_le_maxWalshMagnitude, CryptBoolean.nonlinearity_cast_le_sqrt_sumOfSquaresIndicator_bound, CryptBoolean.nonlinearity_cast_le_fourthRoot_sumOfSquaresIndicator_bound, CryptBoolean.sum_walshTransform_fourth_eq_sum_sq_mul_maxWalshMagnitude_sq_iff_plateaued, CryptBoolean.sum_walshTransform_fourth_eq_two_pow_mul_maxWalshMagnitude_fourth_iff_flat, CryptBoolean.nonlinearity_cast_eq_sqrt_sumOfSquaresIndicator_bound_iff_plateaued, CryptBoolean.nonlinearity_cast_eq_fourthRoot_sumOfSquaresIndicator_bound_iff_bent, CryptBoolean.two_pow_three_mul_n_le_sumOfSquaresIndicator_mul_card_walshSupport, CryptBoolean.sumOfSquaresIndicator_mul_card_walshSupport_eq_two_pow_three_mul_n_iff_plateaued") (uses := "carlet-4-def-nonlinearity, carlet-4-rel-39-fourth-walsh-moment, carlet-2-parseval, carlet-2-spectral-support-bounds, carlet-4-rel-36-covering-radius-bent") (tags := "carlet, chapter-4, autocorrelation, nonlinearity, plateaued, pages-65-66, fidelity-exact-equality-cases")
*Indicator, nonlinearity, and Walsh-support bounds (Carlet, pp. 65--66).*
The fourth-moment identities imply
$$`
\operatorname{nl}(f)
\le2^{n-1}-2^{-n/2-1}\sqrt{\mathcal V(f)}
\le2^{n-1}-\frac12\mathcal V(f)^{1/4}.
`
If $`N_W=|\operatorname{supp}(W_f)|`, then
$$`
\mathcal V(f)N_W\ge2^{3n}.
`
Equality in the first nonlinearity bound or in the product bound occurs
exactly when all nonzero Walsh values have one common magnitude; equality in
the fourth-root bound occurs exactly for bent functions.
:::
