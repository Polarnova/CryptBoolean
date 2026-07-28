/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Verso
import VersoManual
import VersoBlueprint
import CryptBoolean.Carlet.Chapter06.QuadraticBent

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bent functions of low algebraic degrees" =>

:::theorem "carlet-6-quadratic-bent-characterization" (parent := "carlet-chapter-6") (lean := "CryptBoolean.isBent_iff_quadraticRadical_eq_bot, CryptBoolean.isBent_iff_linearKernel_eq_bot_of_degree_le_two") (uses := "carlet-6-def-7-bent, carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-5, carlet-5-quadratic-weight-nonlinearity-values") (tags := "carlet, chapter-6, section-6-2, pages-80-81, fidelity-exact")
*Quadratic bent functions (Carlet, Section 6.2, pp. 80--81).* Let $`n\ge2`
be even and let $`f:V_n\to\mathbb F_2` have algebraic degree at most two. The
following conditions are equivalent:

1. $`f` is bent;
2. $`w_H(f)=2^{n-1}\pm2^{n/2-1}`;
3. the alternating polar form
$$`
\phi_f(x,y)=f(0)+f(x)+f(y)+f(x+y)
`
   is nondegenerate, equivalently the linear kernel of $`f` is $`\{0\}`;
4. the symmetric zero-diagonal coefficient matrix of the quadratic part of
   $`f` is nonsingular;
5. after an invertible affine change of variables, $`f` has the form
$$`
x_1x_2+x_3x_4+\cdots+x_{n-1}x_n+\varepsilon
\qquad(\varepsilon\in\mathbb F_2).
`
:::
