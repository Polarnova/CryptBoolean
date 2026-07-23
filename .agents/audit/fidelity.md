# CryptBoolean statement-to-declaration fidelity audit

## Audit contract

Carlet supplies the source-facing mathematics. Production declarations under `CryptBoolean/`
supply the compiled theorem signatures and proofs. Verso nodes under
`blueprint-verso/CryptBooleanBlueprint/` must keep those two layers visibly aligned without turning
implementation provenance into theorem prose.

Each statement block therefore begins with the printed source result or an explicit project-bridge
label and states its domains, hypotheses, quantifiers, and conclusion. Repository links, reuse of
FABL or Mathlib, proof narration, and completion status belong in a separate `Formalization note`.
An open source result has no `lean :=` association and no placeholder declaration.

The generated manifest currently verifies the following baseline:

| Chapter | Statements | Formalized | Open | Associated declarations | Incoming statement edges |
|---|---:|---:|---:|---:|---:|
| Carlet Chapter 2 | 36 | 35 | 1 | 159 | 45 |
| Carlet Chapter 3 | 7 | 7 | 0 | 32 | 19 |
| Carlet Chapter 4 | 73 | 73 | 0 | 568 | 159 |
| **Total** | **116** | **115** | **1** | **759** | **223** |

The manifest count is an association count, not a claim that every printed result in Carlet
Chapters 2--4 is complete. Coverage outside these 116 reviewed nodes remains governed by the
inventories under `.agents/inventory/`.

## Corrected source mappings

| Blueprint item | Reviewed source statement | Fidelity decision |
|---|---|---|
| `carlet-2-def-support-weight` | Carlet p. 8: `w_H(f)` is the cardinality of the support of `f`. | The public weight is Mathlib's `hammingNorm`; `hammingWeight_eq_card_support` proves that this reused definition is exactly Carlet's support cardinality. |
| `carlet-2-univariate-representation` | Carlet Relation (4), p. 15: every map `F : GF(2^n) -> GF(2^n)` has a unique representing polynomial of degree `< 2^n`. | The earlier Relation (9) attribution was incorrect. The theorem is now cited as Relation (4), and it has no mathematical dependency edge from absolute trace. Mathlib interpolation is implementation provenance only. |
| `carlet-2-absolute-trace` | Carlet p. 15: the absolute trace has the Frobenius-sum formula, its trace pairing is nondegenerate, it is surjective, and a trace-one element lifts Boolean functions. | `traceForm_nondegenerate` and `Algebra.trace_surjective` are associated directly because their Mathlib statements are the exact mathematical facts; local declarations supply the binary-field specialization, explicit surjectivity theorem, and trace lift. |
| `carlet-2-prop-5-nnf-integrality` | Carlet Proposition 5, p. 21: the NNF is integer-valued exactly when all coefficients are integral, and under that condition it is Boolean-valued exactly when its square sum equals its sum. | The four associated predicates/theorems preserve both biconditionals and the integer-coefficient hypothesis; no finite test table replaces the quantified statement. |
| `carlet-2-affine-invariance` | Carlet p. 12: algebraic degree is invariant under affine automorphisms of `V_n`. | The proof first establishes nonincrease for arbitrary affine maps through ANF substitution and then applies the result to an affine equivalence and its inverse. The 13 associated declarations expose only helpers used in that composition. |
| `carlet-2-restriction-recovery` | Carlet pp. 13--14: a degree-at-most-`d` function is recovered by the stated binomial-parity formula from inputs of weight at most `d`, and therefore from every affine-automorphism image of that set. | The associated declarations prove the exact coefficient formula and both uniqueness consequences. The final consequence is restricted to affine automorphisms, not arbitrary affine maps. |
| `carlet-2-poisson-normalized-specialization` | The compiled theorem is the normalized coset-average identity `|E|⁻¹ sum_(h in E) phi(h+z) = sum_(u in E^perp) (-1)^(u dot z) phi_tilde(u)`. | This derived specialization is associated directly with `FABL.poissonSummationFormula`; it remains distinct from the raw source corollary. |
| `carlet-2-cor-1-poisson-summation` | Carlet Corollary 1, Relation (17), p. 25, with arbitrary `a,b in V_n` and the modulated sums over `a+E` and `b+E^perp`. | `rawPoissonSummationFormula` proves the complete raw identity. The normalized specialization is not presented as if it alone proved the full corollary. |
| `carlet-2-rel-22-plancherel` | Carlet Relation (22), p. 27: `sum_u phi_hat(u) psi_hat(u) = 2^n sum_x phi(x) psi(x)`. | The associated declaration proves the bilinear identity. Corollary 3 is recorded only as the consequence obtained by setting `psi = phi`; it is not used to relabel a weaker square-sum statement as Relation (22). |
| `carlet-2-spectral-support-bounds` | Carlet Section 2.2.2, p. 32: Fourier-support cardinality does not increase under coordinate restriction, is at least `2^d` for a nonzero Boolean function of algebraic degree `d`, and is at most the low-weight binomial sum for a nonzero function of numerical degree `D`. | The 24 declarations reuse FABL's normalized Fourier support and restriction results through explicit raw-scaling bridges. Nonzero hypotheses are stated because the project assigns degree zero to the zero function; the Lean upper bound is deliberately stronger and also covers zero. |
| `carlet-3-theorem-1-order-one` | The `r = 1` consequence of Carlet Theorem 1: nonzero degree-at-most-one functions have weight at least `2^(n-1)`, equivalently distinct words of `R(1,n)` have that distance lower bound. | This is explicitly tagged as a derived specialization and is formalized independently. |
| `carlet-3-theorem-1` | Carlet Theorem 1, p. 36: for every `0 <= r <= n`, distinct degree-at-most-`r` functions have Hamming distance at least `2^(n-r)`. | The two all-orders declarations prove the equivalent nonzero-weight and code-distance forms. The separately retained `r = 1` node is only a derived specialization. |
| `carlet-3-prop-12` | Carlet Proposition 12, pp. 36--37: a degree-`r` Boolean function has minimum possible nonzero weight `2^(n-r)` exactly when it is the indicator of an `(n-r)`-dimensional affine flat. | Eleven declarations define arbitrary affine-flat indicators, prove their support, weight, and exact codimension degree, and prove the converse by equality-case slicing. The final equivalences retain both the exact degree and weight hypotheses and classify the support itself. |
| `carlet-3-reed-muller-dimension` | Carlet p. 38: `dim R(r,n) = sum_(i=0)^r C(n,i)` and the code cardinality is the corresponding power of two. | The coefficient restriction is implemented as a linear equivalence; `reedMuller_finrank` proves the dimension formula and `reedMuller_card` derives cardinality from it. |
| `carlet-3-theorem-2` | Carlet Theorem 2, pp. 38--39: for `r<n`, `R(r,n)^⊥ = R(n-r-1,n)` under the Boolean-function pairing. | The six declarations define the bilinear pairing and dual, prove nondegeneracy and one containment, and close equality by the verified dimension formula. |
| `carlet-4-rel-35-nonlinearity-walsh` | Carlet Relation (35), p. 51: for every `a in V_n`, the distances from `f` to `x |-> a dot x` and its complement are `2^(n-1)-W_f(a)/2` and `2^(n-1)+W_f(a)/2`, so `nl(f)=2^(n-1)-(1/2) max_a |W_f(a)|`. | The two distance declarations quantify over every dimension, function, and frequency and state the raw formulas over `R`. `maxWalshMagnitude` is the natural-number maximum of the absolute raw integer Walsh values. `two_mul_nonlinearity_add_maxWalshMagnitude` is the exact division-free natural-number identity, including dimension zero, and `nonlinearity_cast_eq_relation_35` recovers the printed half-factor formula over `R`. The bridges to FABL prove separately that raw distance and raw Walsh magnitude are `2^n` times `distanceToAffineSigns` and `spectralInfinityNorm`; no normalized coefficient is presented as Carlet's raw transform. |
| `carlet-4-random-nonlinearity-lower-bound` | Carlet p. 51: a uniformly random Boolean function has nonlinearity greater than `2^(n-1)-sqrt(n) 2^((n-1)/2)` with probability tending to one. | The associated declarations derive an explicit Fourier union-bound failure probability and prove that it tends to zero. This node remains distinct from Rodier's sharper two-sided interval. |
| `carlet-4-rodier-lower-endpoint` | The one-sided `+4 log(n)/n` consequence of Rodier's sharp interval quoted on Carlet p. 51. | Twelve declarations define the exact normalized threshold, prove a `2/n` Hoeffding--union-bound failure estimate, transport it through Relation (35), and prove that the probability of exceeding the displayed nonlinearity endpoint tends to one. The opposite `-5 log(n)/n` endpoint is not associated with this node. |
| `carlet-4-rodier-upper-endpoint-reduction` | Project bridge for the `-5 log(n)/n` side: convergence of the normalized spectral lower-tail event implies convergence of the displayed upper-nonlinearity event. | Eight declarations define both thresholds and probabilities, prove their exact normalization and deterministic inclusion through Relation (35), and transport an assumed spectral limit by measure monotonicity. They do not assume the missing lower-tail estimate. |
| `carlet-4-rodier-pair-characteristic-moments` | Project bridge for Rodier Lemma 6.4: the joint characteristic function of two distinct raw Walsh coefficients factors as a cosine product, with the stated exact quadratic and quartic phase sums. | Six declarations derive the product from independent signs and the two moments from Walsh-character orthogonality. The later smoothed cutoff and covariance estimates remain separate. |
| `carlet-4-odd-dimension-exact-five` | Carlet pp. 51--52: the maximum nonlinearity in dimension five is `12`. | The quadratic construction supplies the lower bound. A hypothetical weight-13 first-order Reed--Muller coset leader yields a self-complementary binary `[13,6,>=5]` code; residuation gives a `[7,5,>=3]` or `[8,5,>=3]` code, and the radius-one Hamming bound excludes both. |
| `carlet-4-six-variable-covering-coset-coordinate` | Project bridge for Hou's proof of the exact dimension-seven covering radius: a six-variable coset at nonlinearity `28` has a minimum affine representative whose error contains any prescribed coordinate. | The associated declaration proves the statement for every Boolean function and coordinate, without Hou's ambient degree-four restriction. Flat Walsh spectrum and inversion replace the cited orphan terminology and avoid a finite table certificate. |
| `carlet-4-six-variable-degree-four-coset-coordinate` | Project bridge for Hou's proof of the exact dimension-seven covering radius: a degree-at-most-four six-variable coset at nonlinearity `26` has a minimum affine representative whose error contains any prescribed coordinate. | Reed--Muller duality gives affine-coset weights modulo four; Relation (35), Parseval, and Walsh inversion force the coordinate-covering leader. The proof avoids both Hou's cited orphan terminology and a finite truth-table certificate. |
| `carlet-4-odd-dimension-quadratic-covering-bounds` | Carlet pp. 51--52: for odd `n`, the maximum nonlinearity lies between `2^(n-1)-2^((n-1)/2)` and `2^(n-1)-2^(n/2-1)`. | Ten declarations define the finite maximum, reuse FABL's complete inner-product bent function on `n-1` variables with one dummy coordinate for the lower witness, and apply Relation (36) to a maximizing function for the upper bound. |
| `carlet-4-odd-dimension-exact-one-three` | Carlet p. 52: the best nonlinearities in dimensions one and three are `0` and `2`. | The quadratic construction gives both lower bounds; the real covering-radius inequalities are strict enough that natural-number integrality forces equality. |
| `carlet-4-odd-dimension-strict-above-quadratic` | Carlet pp. 51--52 and footnote 22: for every odd `n>7`, some `n`-variable Boolean function has nonlinearity strictly above `2^(n-1)-2^((n-1)/2)`. | A kernel-checked exhaustive Walsh certificate proves nonlinearity `242` for the printed Kavut--Yücel nine-variable truth table. FABL's complete bent direct product extends it to every odd dimension above seven, with exact Walsh magnitude and nonlinearity formulas. |
| `carlet-4-odd-dimension-balanced-above-quadratic` | Carlet footnote 22: for every odd `n>=15`, a balanced function lies strictly above the quadratic bound. | Twenty-two declarations reconstruct Maitra--Kavut--Yücel's thirteen-variable function from its published seed, shift, bent component, and eight toggles; prove balance, maximum Walsh magnitude `120`, and nonlinearity `4036`; and extend it by complete bent blocks. The compiled dimension range `n>=13` is stronger than the source claim. |
| `carlet-4-odd-dimension-pc-one-above-quadratic` | Carlet footnote 22 and reference [264]: for every odd `n>=15`, a function satisfying `PC(1)` lies strictly above the quadratic bound. | Twelve declarations certify a basis of zero-autocorrelation directions for the thirteen-variable Maitra--Kavut--Yücel function, linearly reindex it to satisfy `PC(1)`, retain its exact nonlinearity, and extend it by complete bent blocks. The compiled dimension range `n>=13` is stronger than the source claim. |
| `carlet-4-odd-dimension-degree-pred-above-quadratic` | Carlet footnote 22: for every odd `n>=15`, a degree-`n-1` function lies strictly above the quadratic bound. | A generic two-point repair adds the affine-line indicator through a zero and a one. Proposition 12 gives degree `n-1` and weight two, while the Hamming triangle inequality bounds nonlinearity loss by two. Applied to the balanced family, this proves the source range with witnesses that are also balanced. |
| `carlet-4-reed-muller-coset-distance` | Carlet p. 52: the minimum distance of a union of first-order Reed--Muller cosets is the minimum pair nonlinearity. | The printed unrestricted family equality is false when two representatives determine the same coset. The formal theorem adds the necessary pairwise-distinct-coset hypothesis, and the two-coset corollary assumes its representative is non-affine. These corrected hypotheses are explicit rather than silently altering the source statement. |
| `carlet-4-higher-order-counting-criterion` | Project bridge for Carlet p. 54: if the Reed--Muller code cardinality times a radius-`t` Hamming-ball volume is smaller than the Boolean-function space, some function has higher-order nonlinearity greater than `t`. | The three declarations prove the exact finite sphere-counting implication and its dimension-form restatement. They do not claim the cited fixed-order asymptotic upper and lower estimates. |
| `carlet-4-higher-order-asymptotic-lower-bound` | Carlet pp. 53--54: for fixed `r` and all sufficiently large `n`, some function has `nl_r(f) > 2^(n-1)-sqrt(2^(n-1) sum_(i=0)^r C(n,i))`. | The three declarations combine the finite sphere-counting criterion with a one-sided subgaussian estimate and the eventual binomial-sum bound. They prove exactly the displayed lower existence estimate, independently of the sharper upper bound. |
| `carlet-4-higher-order-plotkin-induction` | Project bridge for the Carlet--Mesnager upper bound cited on Carlet p. 53: the Plotkin recurrence iterates the order-`r-1` covering radii and multiplies the leading square-root coefficient by `1+sqrt(2)`. | Eight declarations define the finite covering radius, prove attainment and the slice recurrence, iterate it from the zero self-radius, and evaluate the geometric sums in the exact finite `A -> A(1+sqrt(2))` propagation formula. They do not supply the missing order-two base. |
| `carlet-4-higher-order-order-two-moment-ratio` | Project bridge for Carlet--Mesnager Relations (9.7)--(9.10): consecutive even correlation moments give a lower bound on maximum order-two correlation and hence an upper bound on `rho(2,n)`. | Fifteen declarations prove the correlation--distance identity, attainment and absolute bound, positivity of the moments, the consecutive-moment inequality, and the resulting finite covering-radius bound. The low-weight dual-code estimate remains outside this bridge. |
| `carlet-4-higher-order-order-two-dual-moment-decomposition` | Project bridge for Carlet--Mesnager Lemma 9.2.2: the even correlation moment is a character sum over ordered tuples whose point-parity word lies in `R(n-3,n)`. | Seven declarations expand powers into tuples, prove character orthogonality over `R(2,n)`, and invoke Chapter 3 duality. The subsequent grouping and low-weight classification remain separate. |
| `carlet-4-prop-13` | Carlet Proposition 13, pp. 54--55: for `1 <= r < n`, `nl_r(f)` is at least one half of the maximum `nl_(r-1)(D_a f)` and at least `2^(n-1)-(1/2)sqrt(2^(2n)-2 sum_a nl_(r-1)(D_a f))`. | The source-facing second-bound declaration carries both hypotheses `1 <= r` and `r < n` and uses exactly the printed `2^(n-1)` and `2^(2n)` normalization. The first bound and the squared-gap inequality are proved in stronger assumption-free forms where their statements remain valid; they do not weaken the associated source result. The finite sum and maximum range over every `a in V_n`, including `a=0`, exactly as printed. |
| `carlet-4-kth-nonhomomorphicity` | Carlet p. 67: for even `k`, the displayed Walsh-moment formula counts tuples whose output sum is zero and gives the affine maximum and bent minimum characterizations. | The declarations follow Carlet's name `k`th nonhomomorphicity for this even-output count. Reference [357] calls that same count homomorphicity and reserves nonhomomorphicity for the complementary odd-output count; the inventory and Blueprint record the terminology discrepancy. |

**Formalization note (Proposition 13).** Carlet refers the omitted proof to reference [72]. The
formal proof follows that source's two arguments: differentiating a closest order-`r` Reed--Muller
approximant lowers its degree and costs at most twice the original Hamming distance; then squaring
the zero-frequency correlation of a closest approximant and summing the derivative correlations
gives the second recursive bound. The production declarations expose the derivative, weight,
autocorrelation, and square-root steps used by this composition rather than assuming either bound.

## Reviewed formalized surface

The 115 formalized statement nodes are split by mathematical result rather than by implementation
module summaries. The fidelity column records how the compiled declarations meet the displayed
source mathematics.

| Family | Formalized Blueprint items | Fidelity | Lean declarations |
|---|---|---|---:|
| Boolean foundations and raw Walsh transform | `carlet-2-def-boolean-function`, `carlet-2-def-support-weight`, `carlet-2-def-walsh-transform`, `carlet-2-bridge-walsh-normalization`, `carlet-2-balanced-zero-walsh` | Exact definitions/results plus explicit Walsh and Mathlib-Hamming bridges | 19 |
| Algebraic normal form | `carlet-2-anf-skeleton`, `carlet-2-anf-existence-uniqueness` | Exact, with the explicit zero-degree convention | 18 |
| Numerical normal form | `carlet-2-nnf-existence-uniqueness`, `carlet-2-prop-4-nnf-mobius`, `carlet-2-prop-5-nnf-integrality` | Exact | 19 |
| Algebraic degree, distance, and affine functions | `carlet-2-def-algebraic-degree`, `carlet-2-support-degree-addition`, `carlet-2-def-hamming-distance`, `carlet-2-bridge-relative-hamming-distance`, `carlet-2-def-affine-functions` | Exact source items plus explicit relative-distance bridge and derived addition law | 18 |
| Affine invariance | `carlet-2-affine-invariance` | Exact source theorem with used ANF-substitution proof layer | 13 |
| Restriction recovery | `carlet-2-restriction-recovery` | Exact formula and affine-automorphism consequence | 10 |
| Raw pseudo-Boolean Fourier operations | `carlet-2-pseudoboolean-fourier`, `carlet-2-prop-6-fourier-shifts`, `carlet-2-cor-2-fourier-involution`, `carlet-2-prop-7-subspace-indicator`, `carlet-2-poisson-normalized-specialization`, `carlet-2-cor-1-poisson-summation`, `carlet-2-def-convolution`, `carlet-2-prop-8-convolution`, `carlet-2-rel-22-plancherel` | Exact raw results plus one explicitly labelled direct-FABL normalized specialization | 13 |
| Spectral-support bounds | `carlet-2-spectral-support-bounds` | Exact with explicit zero-function conventions and raw/normalized bridges | 24 |
| Walsh inversion and Parseval for sign views | `carlet-2-fourier-inversion`, `carlet-2-parseval` | Exact sign-function specializations | 5 |
| Derivatives and autocorrelation | `carlet-2-def-2-derivative`, `carlet-2-def-autocorrelation`, `carlet-2-rel-25-wiener-khinchin`, `carlet-2-rel-26-total-autocorrelation` | Exact | 6 |
| Finite-field representation | `carlet-2-absolute-trace`, `carlet-2-univariate-representation` | Exact, with direct Mathlib trace reuse and interpolation provenance | 14 |
| Reed--Muller foundations | `carlet-3-affine-weight`, `carlet-3-reed-muller-code`, `carlet-3-theorem-1-order-one` | Exact source items plus explicitly derived order-one specialization | 11 |
| General Reed--Muller distance | `carlet-3-theorem-1` | Exact all-orders theorem | 2 |
| Minimum-weight Reed--Muller classification | `carlet-3-prop-12` | Exact affine-flat indicator equivalence | 11 |
| Reed--Muller dimension | `carlet-3-reed-muller-dimension` | Exact | 2 |
| Reed--Muller duality | `carlet-3-theorem-2` | Exact | 6 |
| Degree and first-order nonlinearity | 23 formalized Chapter 4 nodes from `carlet-4-degree-count` through `carlet-4-odd-weighting-nonlinearity` | Exact finite results, explicit Walsh normalization, Rodier's two-sided interval, general odd-dimensional bounds and exact maxima through dimension seven, the balanced and propagation families, the degree repair, and the corrected distinct-coset condition | 204 |
| Higher-order nonlinearity | 22 formalized Chapter 4 nodes from `carlet-4-def-higher-order-nonlinearity` through `carlet-4-higher-order-general-bounds`, together with `carlet-4-prop-13` | Exact distance profile, finite and asymptotic existence bounds, moment-ratio and dual-code decompositions, low-weight classifications, the rank-seven weight-`16` classification and character bound, finite Plotkin propagation, the sharp fixed-order upper bound, and both Proposition 13 bounds | 131 |
| Resiliency and propagation | 6 formalized nodes from `carlet-4-def-resiliency-correlation-immunity` through `carlet-4-def-propagation-criteria` | Exact definitions, Walsh characterization, support/code consequences, and affine translation laws | 44 |
| Linear structures | 6 formalized nodes from `carlet-4-def-linear-kernel` through `carlet-4-distance-to-linear-structures` | Exact kernel, normal-form, spectral, nonlinearity, and distance statements | 37 |
| Algebraic immunity | 5 formalized nodes from `carlet-4-def-annihilator-algebraic-immunity` through `carlet-4-fast-algebraic-optimality` | Exact annihilator definitions, linear systems, bounds, and fast-algebraic criterion | 42 |
| Autocorrelation indicators | 5 formalized nodes from `carlet-4-def-autocorrelation-indicators` through `carlet-4-indicator-nonlinearity-spectral-support` | Exact indicators, moment identities, and spectral/nonlinearity consequences | 36 |
| Maximum correlation and generalized distance | 3 formalized nodes from `carlet-4-def-maximum-correlation` through `carlet-4-generalized-linear-structure-distance` | Exact coordinate-restriction and linear-structure distances | 38 |
| Other complexity criteria | `carlet-4-other-complexity-definitions`, `carlet-4-kth-nonhomomorphicity`, `carlet-4-affine-reindex-first-resilient` | Exact criteria with the recorded tuple-count terminology discrepancy | 36 |
| **Total** | **115 items** |  | **759** |

The following distinctions are part of the fidelity boundary:

- Carlet's Walsh and pseudo-Boolean Fourier transforms are unnormalized sums. FABL's Fourier
  coefficients and convolution are normalized. Every reuse crosses an explicit scaling theorem.
- Carlet's algebraic degree is the degree of the unique algebraic normal form over `F_2`; it is not
  FABL's real Fourier degree.
- Hamming distance is a natural-number cardinality. Its relation to FABL relative distance is a
  separate normalization bridge; Mathlib's `hammingNorm` and `hammingDist` are reused only where
  their cardinality statements are proved to coincide with Carlet's definitions.
- The absolute trace, its Frobenius formula, trace-pairing nondegeneracy, and surjectivity are
  mathematical statements. Exact Mathlib theorems may therefore be associated directly, while
  library provenance remains outside the statement block.
- The normalized Poisson specialization is direct FABL reuse. Carlet's raw Corollary 1 is a
  separate local theorem with both modulation parameters.
- Spectral-support lower and upper bounds distinguish the zero-function convention explicitly;
  the formal upper bound strengthens the source statement by also covering zero.
- Carlet's general Reed--Muller distance theorem is associated independently of its derived
  order-one specialization. Dimension and orthogonal duality use linear structure rather than a
  set-cardinality surrogate.
- Proposition 12 retains exact degree and weight, not merely membership in `R(r,n)` and a lower-
  bound equality. Its affine-flat indicator normal form and converse support classification are
  both compiled.
- Carlet's raw nonlinearity and maximum Walsh magnitude remain natural-number quantities. Their
  equality is proved without division before the printed real-valued half-factor form is derived;
  FABL's normalized distance and spectral norm appear only in explicit bridge declarations.
- Higher-order nonlinearity is distance to the full finite Reed--Muller code. Proposition 13 sums
  and maximizes over all directions, and its displayed source-form declaration retains
  `1 <= r < n` even where intermediate lemmas prove stronger statements.
- The finite higher-order sphere-counting bridge, the derived lower existence estimate, and the
  Plotkin induction, moment-ratio, dual-code decomposition, weight grouping, low-weight support,
  weights `8`, `12`, and `14` character bounds, weight-sixteen rank reduction, moment-difference
  estimate, conditional order-two extraction, and conditional general-order propagation are kept
  distinct from Carlet--Mesnager's sharp fixed-order asymptotic upper bound. The weight-sixteen
  branch is itself split into the rank-seven classifier, the three canonical orbit sums, the
  rank-at-most-six residual cover, and their aggregate character bound. The orbit sum-of-squares
  and residual-cover nodes have direct semantic associations; the rank-seven classification and
  aggregate character bound are associated with their final declarations. Mechanical
  finite-classifier cases are never source-facing
  associations.
- The proved Olejar--Stanek lower bound and Rodier's exact `+4 log(n)/n` lower endpoint are not
  relabelled as Rodier's sharper two-sided interval. The opposite event reduction, exact pair
  moments, smoothed cutoff, and covariance analysis remain separate mathematical layers.
- The general odd-dimensional bounds and exact maxima in dimensions one, three, and five are
  separate from the Kavut--Yücel strict-improvement family. The Maitra--Kavut--Yücel balanced
  family, its linear-reindexing `PC(1)` construction, and the Proposition 12 degree repair have
  their own nodes. The six-variable nonlinearity-28 and degree-at-most-four nonlinearity-26
  coordinate-covering bridges record Hou's two orphan subcases and compose with the remaining
  reduction and normal-form lemmas to prove the dimension-seven equality.
- First-order Reed--Muller coset distance uses the necessary distinct-coset hypothesis, and `k`th
  nonhomomorphicity retains Carlet's terminology while recording reference [357]'s convention.
- Definitions, bridge laws, source propositions, and derived consequences have separate Blueprint
  nodes when their quantifiers or conclusions differ.

## Open source statements

One open node states the complete reviewed mathematics and intentionally has no Lean declaration
association. Chapter 2 contributes the sole foundational blocker:

| Blueprint item | Source location | Exact blocker |
|---|---|---|
| `carlet-2-trace-monomial-degree` | Carlet Proposition 3, pp. 17--18 | Missing the bridge between coordinate ANF degree on `V_n` and maximum binary exponent weight in the univariate finite-field representation, together with cyclotomic-orbit noncancellation proving that a surviving nonzero orbit coefficient has weight `w_2(k)`. Pinned FABL and Mathlib expose neither result. |

Chapter 3 has no open node: Proposition 12's affine-flat and equality-case slice layer is
formalized. Chapter 4 has no open node: its three former frontier statements are associated with
complete declarations while their principal mathematical ingredients retain independent nodes.

## Verification perimeter

The statement-style gate runs as part of the site build and rejects implementation prose, links,
missing mathematical notation, or inconsistent open/formalized metadata inside statement blocks.
The strict manifest validator checks the exact statement split, declaration presence and proof
status, graph node set, open-node set, and edge count.

Run from the repository root:

```bash
lake build CryptBoolean
./.github/scripts/forbidden_tokens.sh
./.github/scripts/audit_axioms.sh
./blueprint-verso/scripts/site.sh build
```

Source fidelity still requires human comparison with Carlet; compilation and manifest validation
alone do not establish that a statement has the correct domain, hypotheses, normalization, or
quantifiers.
