# CryptBoolean statement-to-declaration fidelity audit

## Audit contract

Carlet supplies the source-facing mathematics. Production declarations under `CryptBoolean/`
supply the compiled theorem signatures and proofs. Verso nodes under
`blueprint-verso/CryptBooleanBlueprint/` must keep those two layers visibly aligned without turning
implementation provenance into theorem prose.

Each statement block therefore begins with the printed source result or a descriptive mathematical
title and states its domains, hypotheses, quantifiers, and conclusion. Repository links and API
provenance are omitted from reader text; mathematically informative proof outlines and fidelity
distinctions may follow the block as direct prose.
An open source result has no `lean :=` association and no placeholder declaration.

The generated manifest currently verifies the following baseline:

| Chapter | Statements | Formalized | Open | Associated declarations | Incoming statement edges |
|---|---:|---:|---:|---:|---:|
| Carlet Chapter 2 | 38 | 38 | 0 | 166 | 48 |
| Carlet Chapter 3 | 7 | 7 | 0 | 32 | 19 |
| Carlet Chapter 4 | 73 | 73 | 0 | 568 | 159 |
| Carlet Chapter 5 | 31 | 28 | 3 | 195 | 70 |
| **Total** | **149** | **146** | **3** | **961** | **296** |

The manifest count is an association count, not a claim that every printed result in Carlet
Chapters 2--5 is complete. Coverage outside these 149 reviewed nodes remains governed by the
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
| `carlet-2-spectral-support-bounds` | Carlet Section 2.2.2, p. 32: Fourier-support cardinality does not increase under coordinate restriction, is at least `2^d` for a nonzero Boolean function of algebraic degree `d`, and is at most the low-weight binomial sum for a nonzero function of numerical degree `D`. | The 24 declarations reuse FABL's normalized Fourier support and restriction results through an explicit raw-scaling identity. Nonzero hypotheses are stated because the project assigns degree zero to the zero function; the Lean upper bound is deliberately stronger and also covers zero. |
| `carlet-3-theorem-1-order-one` | The `r = 1` consequence of Carlet Theorem 1: nonzero degree-at-most-one functions have weight at least `2^(n-1)`, equivalently distinct words of `R(1,n)` have that distance lower bound. | This is explicitly tagged as a derived specialization and is formalized independently. |
| `carlet-3-theorem-1` | Carlet Theorem 1, p. 36: for every `0 <= r <= n`, distinct degree-at-most-`r` functions have Hamming distance at least `2^(n-r)`. | The two all-orders declarations prove the equivalent nonzero-weight and code-distance forms. The separately retained `r = 1` node is only a derived specialization. |
| `carlet-3-prop-12` | Carlet Proposition 12, pp. 36--37: a degree-`r` Boolean function has minimum possible nonzero weight `2^(n-r)` exactly when it is the indicator of an `(n-r)`-dimensional affine flat. | Eleven declarations define arbitrary affine-flat indicators, prove their support, weight, and exact codimension degree, and prove the converse by equality-case slicing. The final equivalences retain both the exact degree and weight hypotheses and classify the support itself. |
| `carlet-3-reed-muller-dimension` | Carlet p. 38: `dim R(r,n) = sum_(i=0)^r C(n,i)` and the code cardinality is the corresponding power of two. | The coefficient restriction is implemented as a linear equivalence; `reedMuller_finrank` proves the dimension formula and `reedMuller_card` derives cardinality from it. |
| `carlet-3-theorem-2` | Carlet Theorem 2, pp. 38--39: for `r<n`, `R(r,n)^⊥ = R(n-r-1,n)` under the Boolean-function pairing. | The six declarations define the bilinear pairing and dual, prove nondegeneracy and one containment, and close equality by the verified dimension formula. |
| `carlet-4-rel-35-nonlinearity-walsh` | Carlet Relation (35), p. 51: for every `a in V_n`, the distances from `f` to `x |-> a dot x` and its complement are `2^(n-1)-W_f(a)/2` and `2^(n-1)+W_f(a)/2`, so `nl(f)=2^(n-1)-(1/2) max_a |W_f(a)|`. | The two distance declarations quantify over every dimension, function, and frequency and state the raw formulas over `R`. `maxWalshMagnitude` is the natural-number maximum of the absolute raw integer Walsh values. `two_mul_nonlinearity_add_maxWalshMagnitude` is the exact division-free natural-number identity, including dimension zero, and `nonlinearity_cast_eq_relation_35` recovers the printed half-factor formula over `R`. The normalization identities prove separately that raw distance and raw Walsh magnitude are `2^n` times `distanceToAffineSigns` and `spectralInfinityNorm`; no normalized coefficient is presented as Carlet's raw transform. |
| `carlet-4-random-nonlinearity-lower-bound` | Carlet p. 51: a uniformly random Boolean function has nonlinearity greater than `2^(n-1)-sqrt(n) 2^((n-1)/2)` with probability tending to one. | The associated declarations derive an explicit Fourier union-bound failure probability and prove that it tends to zero. This node remains distinct from Rodier's sharper two-sided interval. |
| `carlet-4-rodier-lower-endpoint` | The one-sided `+4 log(n)/n` consequence of Rodier's sharp interval quoted on Carlet p. 51. | Twelve declarations define the exact normalized threshold, prove a `2/n` Hoeffding--union-bound failure estimate, transport it through Relation (35), and prove that the probability of exceeding the displayed nonlinearity endpoint tends to one. The opposite `-5 log(n)/n` endpoint is not associated with this node. |
| `carlet-4-rodier-upper-endpoint-reduction` | Reduction for the `-5 log(n)/n` side: convergence of the normalized spectral lower-tail event implies convergence of the displayed upper-nonlinearity event. | Eight declarations define both thresholds and probabilities, prove their exact normalization and deterministic inclusion through Relation (35), and transport an assumed spectral limit by measure monotonicity. They do not assume the missing lower-tail estimate. |
| `carlet-4-rodier-pair-characteristic-moments` | Rodier Lemma 6.4: the joint characteristic function of two distinct raw Walsh coefficients factors as a cosine product, with the stated exact quadratic and quartic phase sums. | Six declarations derive the product from independent signs and the two moments from Walsh-character orthogonality. The later smoothed cutoff and covariance estimates remain separate. |
| `carlet-4-odd-dimension-exact-five` | Carlet pp. 51--52: the maximum nonlinearity in dimension five is `12`. | The quadratic construction supplies the lower bound. A hypothetical weight-13 first-order Reed--Muller coset leader yields a self-complementary binary `[13,6,>=5]` code; residuation gives a `[7,5,>=3]` or `[8,5,>=3]` code, and the radius-one Hamming bound excludes both. |
| `carlet-4-six-variable-covering-coset-coordinate` | Lemma in Hou's proof of the exact dimension-seven covering radius: a six-variable coset at nonlinearity `28` has a minimum affine representative whose error contains any prescribed coordinate. | The associated declaration proves the statement for every Boolean function and coordinate, without Hou's ambient degree-four restriction. Flat Walsh spectrum and inversion replace the cited orphan terminology and avoid a finite table certificate. |
| `carlet-4-six-variable-degree-four-coset-coordinate` | Lemma in Hou's proof of the exact dimension-seven covering radius: a degree-at-most-four six-variable coset at nonlinearity `26` has a minimum affine representative whose error contains any prescribed coordinate. | Reed--Muller duality gives affine-coset weights modulo four; Relation (35), Parseval, and Walsh inversion force the coordinate-covering leader. The proof avoids both Hou's cited orphan terminology and a finite truth-table certificate. |
| `carlet-4-odd-dimension-quadratic-covering-bounds` | Carlet pp. 51--52: for odd `n`, the maximum nonlinearity lies between `2^(n-1)-2^((n-1)/2)` and `2^(n-1)-2^(n/2-1)`. | Ten declarations define the finite maximum, reuse FABL's complete inner-product bent function on `n-1` variables with one dummy coordinate for the lower witness, and apply Relation (36) to a maximizing function for the upper bound. |
| `carlet-4-odd-dimension-exact-one-three` | Carlet p. 52: the best nonlinearities in dimensions one and three are `0` and `2`. | The quadratic construction gives both lower bounds; the real covering-radius inequalities are strict enough that natural-number integrality forces equality. |
| `carlet-4-odd-dimension-strict-above-quadratic` | Carlet pp. 51--52 and footnote 22: for every odd `n>7`, some `n`-variable Boolean function has nonlinearity strictly above `2^(n-1)-2^((n-1)/2)`. | A kernel-checked exhaustive Walsh certificate proves nonlinearity `242` for the printed Kavut--Yücel nine-variable truth table. FABL's complete bent direct product extends it to every odd dimension above seven, with exact Walsh magnitude and nonlinearity formulas. |
| `carlet-4-odd-dimension-balanced-above-quadratic` | Carlet footnote 22: for every odd `n>=15`, a balanced function lies strictly above the quadratic bound. | Twenty-two declarations reconstruct Maitra--Kavut--Yücel's thirteen-variable function from its published seed, shift, bent component, and eight toggles; prove balance, maximum Walsh magnitude `120`, and nonlinearity `4036`; and extend it by complete bent blocks. The compiled dimension range `n>=13` is stronger than the source claim. |
| `carlet-4-odd-dimension-pc-one-above-quadratic` | Carlet footnote 22 and reference [264]: for every odd `n>=15`, a function satisfying `PC(1)` lies strictly above the quadratic bound. | Twelve declarations certify a basis of zero-autocorrelation directions for the thirteen-variable Maitra--Kavut--Yücel function, linearly reindex it to satisfy `PC(1)`, retain its exact nonlinearity, and extend it by complete bent blocks. The compiled dimension range `n>=13` is stronger than the source claim. |
| `carlet-4-odd-dimension-degree-pred-above-quadratic` | Carlet footnote 22: for every odd `n>=15`, a degree-`n-1` function lies strictly above the quadratic bound. | A generic two-point repair adds the affine-line indicator through a zero and a one. Proposition 12 gives degree `n-1` and weight two, while the Hamming triangle inequality bounds nonlinearity loss by two. Applied to the balanced family, this proves the source range with witnesses that are also balanced. |
| `carlet-4-reed-muller-coset-distance` | Carlet p. 52: the minimum distance of a union of first-order Reed--Muller cosets is the minimum pair nonlinearity. | The printed unrestricted family equality is false when two representatives determine the same coset. The formal theorem adds the necessary pairwise-distinct-coset hypothesis, and the two-coset corollary assumes its representative is non-affine. These corrected hypotheses are explicit as a stated source correction. |
| `carlet-4-higher-order-counting-criterion` | Finite sphere-covering lemma for Carlet p. 54: if the Reed--Muller code cardinality times a radius-`t` Hamming-ball volume is smaller than the Boolean-function space, some function has higher-order nonlinearity greater than `t`. | The three declarations prove the exact finite sphere-counting implication and its dimension-form restatement. They do not claim the cited fixed-order asymptotic upper and lower estimates. |
| `carlet-4-higher-order-asymptotic-lower-bound` | Carlet pp. 53--54: for fixed `r` and all sufficiently large `n`, some function has `nl_r(f) > 2^(n-1)-sqrt(2^(n-1) sum_(i=0)^r C(n,i))`. | The three declarations combine the finite sphere-counting criterion with a one-sided subgaussian estimate and the eventual binomial-sum bound. They prove exactly the displayed lower existence estimate, independently of the sharper upper bound. |
| `carlet-4-higher-order-plotkin-induction` | Plotkin induction lemma for the Carlet--Mesnager upper bound cited on Carlet p. 53: the Plotkin recurrence iterates the order-`r-1` covering radii and multiplies the leading square-root coefficient by `1+sqrt(2)`. | Eight declarations define the finite covering radius, prove attainment and the slice recurrence, iterate it from the zero self-radius, and evaluate the geometric sums in the exact finite `A -> A(1+sqrt(2))` propagation formula. They do not supply the missing order-two base. |
| `carlet-4-higher-order-order-two-moment-ratio` | Carlet--Mesnager Relations (9.7)--(9.10): consecutive even correlation moments give a lower bound on maximum order-two correlation and hence an upper bound on `rho(2,n)`. | Fifteen declarations prove the correlation--distance identity, attainment and absolute bound, positivity of the moments, the consecutive-moment inequality, and the resulting finite covering-radius bound. The low-weight dual-code estimate remains a separate theorem. |
| `carlet-4-higher-order-order-two-dual-moment-decomposition` | Carlet--Mesnager Lemma 9.2.2: the even correlation moment is a character sum over ordered tuples whose point-parity word lies in `R(n-3,n)`. | Seven declarations expand powers into tuples, prove character orthogonality over `R(2,n)`, and invoke Chapter 3 duality. The subsequent grouping and low-weight classification remain separate. |
| `carlet-4-prop-13` | Carlet Proposition 13, pp. 54--55: for `1 <= r < n`, `nl_r(f)` is at least one half of the maximum `nl_(r-1)(D_a f)` and at least `2^(n-1)-(1/2)sqrt(2^(2n)-2 sum_a nl_(r-1)(D_a f))`. | The source-facing second-bound declaration carries both hypotheses `1 <= r` and `r < n` and uses exactly the printed `2^(n-1)` and `2^(2n)` normalization. The first bound and the squared-gap inequality are proved in stronger assumption-free forms where their statements remain valid; they do not weaken the associated source result. The finite sum and maximum range over every `a in V_n`, including `a=0`, exactly as printed. |
| `carlet-4-kth-nonhomomorphicity` | Carlet p. 67: for even `k`, the displayed Walsh-moment formula counts tuples whose output sum is zero and gives the affine maximum and bent minimum characterizations. | The declarations follow Carlet's name `k`th nonhomomorphicity for this even-output count. Reference [357] calls that same count homomorphicity and reserves nonhomomorphicity for the complementary odd-output count; the inventory and Blueprint record the terminology discrepancy. |
| `carlet-5-theorem-4` | Carlet Theorem 4, p. 69: a quadratic function is balanced exactly when its restriction to the linear kernel is nonconstant; otherwise `n+k` is even and its weight is `2^(n-1) plus or minus 2^((n+k)/2-1)`. | The displayed half-power theorem explicitly assumes `n>0`, the implicit domain in which the natural exponent is total. Balancedness and the even-rank consequence are compiled separately without that restriction where their statements remain valid. |
| `carlet-5-flat-indicator-walsh-nonlinearity` | Carlet p. 71 gives the exact Walsh spectrum of a codimension-`r` affine-flat indicator and concludes `nl(f)=2^(n-r)`. | The source's own spectrum makes the unqualified conclusion false for `r=1`, when the indicator is affine. The formal statement records `nl(f)=0` for `r=1` and retains `nl(f)=2^(n-r)` for `r>=2`; its support, weight, and raw spectrum still agree with the printed formulas. |
| `carlet-5-rel-42-restriction-nonlinearity` | Carlet Relation (42), pp. 71--72: for a restriction `h_a` to a `k`-dimensional affine coset, `nl(f) <= 2^(n-1)-2^(k-1)+nl(h_a)`. | The natural-number form makes the implicit hypothesis `1<=k` explicit. Division-free and real-cast inequalities cover every `k`, including zero. A coordinate equivalence onto the direction subspace supplies the reusable theorem, and a complementary-subspace wrapper recovers Carlet's `E,E'` and coset presentation without changing the mathematical bound. |
| `carlet-5-affine-flat-restriction-bound` | Carlet p. 72: an affine restriction gives `nl(f) <= 2^(n-1)-2^(k-1)`, and equality forces every other coset to be balanced after adding any ambient affine extension. | Eight declarations prove the affine-extension theorem, the zero restricted nonlinearity, the bound, affine Walsh modulation, perpendicular-character cancellation, and the full equality case. The positive-dimensional domain of the natural exponent and the condition identifying every coset other than the original one are explicit. |
| `carlet-5-covering-sequence-walsh-characterization` | Carlet pp. 73--74 defines integer covering sequences and characterizes them by the integer Walsh transform of their coefficient sequence on the raw Walsh support of `f`. | The interface stays integer-valued, as in the printed definition, and uses the unnormalized integer transform. Explicit cast and involution identities connect it to the already compiled raw pseudo-Boolean Fourier API; no normalized FABL coefficient is substituted for Carlet's transform. |
| `carlet-5-covering-sequence-resiliency` | Carlet p. 74 derives correlation-immunity and resiliency orders from the minimum nonzero transform-fiber weight and gives converses at the first failed order. | The forward and converse declarations retain the stated minimum and nontrivial-level conditions on every feasible order. The Walsh-zero coefficient sequence is constructed explicitly from its defining formula. |
| `carlet-5-derivative-space-partial-covering-sequence` | Carlet p. 74: a nonzero binary space of derivatives has pointwise integer sum zero or half its cardinality, and a minimal representative direction set gives a nontrivial partial covering sequence. | Ten declarations model the finite Boolean-function subspace, prove the half-cardinality dichotomy, choose one direction per derivative, prove the resulting derivative map is bijective and the representative set has cardinality `|D|`, and establish the two-level partial-covering property with nonzero upper level. |
| `carlet-5-theorem-6-weight-corollary` | Carlet p. 76 divides by a nonzero level `rho` to write `W_f(0)=(1-rho'/rho) sum_(x in A)(-1)^f(x)`. | The associated theorem proves the equivalent integer identity `rho W_f(0)=(rho-rho') sum_(x in A)(-1)^f(x)`, valid even at `rho=0`; the printed quotient follows under its stated nonzero hypothesis. |

**Proof of Proposition 13.** Carlet refers the omitted proof to reference [72]. The
formal proof follows that source's two arguments: differentiating a closest order-`r` Reed--Muller
approximant lowers its degree and costs at most twice the original Hamming distance; then squaring
the zero-frequency correlation of a closest approximant and summing the derivative correlations
gives the second recursive bound. The derivative, weight, autocorrelation, and square-root lemmas
prove both bounds from these ingredients.

### Chapter 5 source-recovery boundary

Four cited Chapter 5 claims remain inventory records outside the Blueprint because the
survey does not supply theorem-complete parameters or because the cited source boundary still
needs an explicit fidelity decision:

- The Kasami--Tokura classification is now recovered with complete parameter inequalities and
  weights from Borissov--Manev--Nikova, ISIT 2001, Theorem 4, and independently cross-checked
  against Carlet--Sole, arXiv:2301.13497v3. The original IEEE paper remains closed with no
  repository full text. Promotion must separate that input-affine classification from the Walsh
  spectra that Carlet says can subsequently be computed from the normal forms; visible source
  material does not attribute a Walsh theorem to Kasami--Tokura.
- The Alon--Goldreich--Hastad--Peralta citation requires recovery of the explicit family, its
  dimension range, and the affine-automorphism passage from coordinate flats.
- Bourgain's abstract states an affine extractor for arbitrary fixed positive entropy ratio,
  stronger than Carlet's preliminary displayed range, but its exact binary-output specialization
  still needs recovery.
- Barak--Kindler--Shaltiel--Sudakov--Wigderson define an affine `delta`-source by dimension at least
  `delta*n`; this is not Carlet's printed `n^delta` claim. That mismatch must be resolved against
  the primary journal theorem or recorded as a source correction before promotion.

## Reviewed formalized surface

The 146 formalized statements are split by mathematical result. Implementation module boundaries
do not determine this split. The fidelity column records how the compiled declarations meet the displayed
source mathematics.

| Family | Formalized Blueprint items | Fidelity | Lean declarations |
|---|---|---|---:|
| Boolean foundations and raw Walsh transform | `carlet-2-def-boolean-function`, `carlet-2-def-support-weight`, `carlet-2-def-walsh-transform`, `carlet-2-walsh-normalization`, `carlet-2-balanced-zero-walsh` | Exact definitions and results, including Walsh normalization and the Hamming-weight identification | 20 |
| Algebraic normal form | `carlet-2-anf-skeleton`, `carlet-2-anf-existence-uniqueness` | Exact, with the explicit zero-degree convention | 18 |
| Numerical normal form | `carlet-2-nnf-existence-uniqueness`, `carlet-2-prop-4-nnf-mobius`, `carlet-2-prop-5-nnf-integrality` | Exact | 19 |
| Algebraic degree, distance, and affine functions | `carlet-2-def-algebraic-degree`, `carlet-2-support-degree-addition`, `carlet-2-def-hamming-distance`, `carlet-2-relative-hamming-normalization`, `carlet-2-def-affine-functions` | Exact source items plus explicit relative-distance normalization and derived addition law | 18 |
| Affine invariance | `carlet-2-affine-invariance` | Exact source theorem with used ANF-substitution proof layer | 13 |
| Restriction recovery | `carlet-2-restriction-recovery` | Exact formula and affine-automorphism consequence | 10 |
| Raw pseudo-Boolean Fourier operations | `carlet-2-pseudoboolean-fourier`, `carlet-2-prop-6-fourier-shifts`, `carlet-2-cor-2-fourier-involution`, `carlet-2-prop-7-subspace-indicator`, `carlet-2-poisson-normalized-specialization`, `carlet-2-cor-1-poisson-summation`, `carlet-2-def-convolution`, `carlet-2-prop-8-convolution`, `carlet-2-rel-22-plancherel` | Exact raw results plus one explicitly labelled direct-FABL normalized specialization | 13 |
| Spectral-support bounds | `carlet-2-spectral-support-bounds` | Exact with explicit zero-function conventions and the raw/normalized support identity | 24 |
| Walsh inversion and Parseval for sign views | `carlet-2-fourier-inversion`, `carlet-2-parseval` | Exact sign-function specializations | 6 |
| Derivatives and autocorrelation | `carlet-2-def-2-derivative`, `carlet-2-def-autocorrelation`, `carlet-2-rel-25-wiener-khinchin`, `carlet-2-rel-26-total-autocorrelation` | Exact | 6 |
| Finite-field representation | 5 formalized nodes from `carlet-2-absolute-trace` through `carlet-2-trace-monomial-degree` | Exact absolute trace and interpolation results, an explicit shared trace-pairing coordinate theorem, the binary-degree formula for canonical univariate representations, and Proposition 3's exact nonzero trace-monomial degree | 19 |
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
| Chapter 5 affine and quadratic classes | 13 formalized nodes from `carlet-5-affine-walsh-spectrum` through `carlet-5-def-quadratic-semi-bent` | Exact affine spectra, quadratic polar/radical structure, Relation (41), Theorems 4 and 5, derivative and even-rank consequences, exact weight and nonlinearity value sets with realizations, the complete affine normal-form trichotomy, the odd/even finite-field quadratic trace representation, the quadraticization step and its degree-three iteration, and an exact semi-bent predicate | 89 |
| Chapter 5 flat restrictions and normality | `carlet-5-flat-indicator-walsh-nonlinearity`, `carlet-5-rel-42-restriction-nonlinearity`, `carlet-5-affine-flat-restriction-bound`, `carlet-5-def-4-normality`, `carlet-5-random-nonnormality` | Corrected codimension-one flat value, total restriction inequalities, the full equality case, exact fixed-dimension normality predicates, the finite certificate bound, and the exact floored logarithmic random-nonnormality limit | 44 |
| Chapter 5 covering sequences | 9 formalized nodes from `carlet-5-def-5-covering-sequence` through `carlet-5-theorem-6-weight-corollary` | Exact integer covering and partial-covering definitions, Walsh characterization, balancedness/resiliency consequences, regular families, the derivative-space representative construction, Theorem 6, and its division-free weight identity | 56 |
| Chapter 5 trace-character reduction | `carlet-5-trace-character-sum-walsh` | Reuse of the shared Chapter 2 trace-pairing coordinate theorem, the exact complete-sum Walsh identity, and the conditional maximum-Walsh/nonlinearity reduction | 6 |
| **Total** | **146 items** |  | **961** |

The following distinctions are part of the fidelity boundary:

- Carlet's Walsh and pseudo-Boolean Fourier transforms are unnormalized sums. FABL's Fourier
  coefficients and convolution are normalized. Every reuse crosses an explicit scaling theorem.
- Carlet's algebraic degree is the degree of the unique algebraic normal form over `F_2`; it is not
  FABL's real Fourier degree.
- Hamming distance is a natural-number cardinality. Its relation to FABL relative distance is a
  separate normalization theorem; Mathlib's `hammingNorm` and `hammingDist` are reused only where
  their cardinality statements are proved to coincide with Carlet's definitions.
- The absolute trace, its Frobenius formula, trace-pairing nondegeneracy, and surjectivity are
  mathematical statements. Exact Mathlib theorems may therefore be associated directly, while
  library provenance remains outside the statement block.
- The normalized Poisson specialization is direct FABL reuse. Carlet's raw Corollary 1 is a
  separate local theorem with both modulation parameters.
- Spectral-support lower and upper bounds distinguish the zero-function convention explicitly;
  the formal upper bound strengthens the source statement by also covering zero.
- Carlet's general Reed--Muller distance theorem is associated independently of its derived
  order-one specialization. Dimension and orthogonal duality use the linear structure directly.
- Proposition 12 retains exact degree and weight, not merely membership in `R(r,n)` and a lower-
  bound equality. Its affine-flat indicator normal form and converse support classification are
  both compiled.
- Carlet's raw nonlinearity and maximum Walsh magnitude remain natural-number quantities. Their
  equality is proved without division before the printed real-valued half-factor form is derived;
  FABL's normalized distance and spectral norm appear only in explicit normalization declarations.
- Higher-order nonlinearity is distance to the full finite Reed--Muller code. Proposition 13 sums
  and maximizes over all directions, and its displayed source-form declaration retains
  `1 <= r < n` even where intermediate lemmas prove stronger statements.
- The finite higher-order sphere-counting lemma, the derived lower existence estimate, and the
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
  coordinate-covering lemmas record Hou's two subcases and compose with the remaining
  reduction and normal-form lemmas to prove the dimension-seven equality.
- First-order Reed--Muller coset distance uses the necessary distinct-coset hypothesis, and `k`th
  nonhomomorphicity retains Carlet's terminology while recording reference [357]'s convention.
- Chapter 5's quadratic weight formula exposes its implicit `n>0` domain; the balancedness,
  derivative-one, and even-symplectic-rank statements remain assumption-free where valid.
- An affine-flat indicator has nonlinearity zero in codimension one. The formal case split corrects
  Carlet's unqualified conclusion while preserving the printed Walsh spectrum and every
  codimension-at-least-two value.
- Relation (42) separates its `1<=k` natural-number display from division-free and real-cast forms
  valid for all `k`. Coordinate-equivalence and complementary-subspace presentations are explicit
  coordinate representations, and the equality corollary quantifies over every ambient affine
  extension and every other coset.
- Covering sequences use integer coefficients and an unnormalized integer Walsh transform. Their
  resiliency consequences are restricted to feasible orders, and Theorem 6's weight consequence
  is compiled first without division.
- The four Chapter 5 citation-recovery records are not weakened into Blueprint statements. In
  particular, the BKSSW primary formulation uses affine dimension at least `delta*n`, whereas
  Carlet prints `n^delta`.
- Definitions, normalization laws, source propositions, and derived consequences have separate Blueprint
  nodes when their quantifiers or conclusions differ.

## Open source statements

Three open nodes state complete reviewed analytic mathematics and intentionally have no Lean
declaration association. All three are in the Chapter 5 character-sum branch.

| Blueprint item | Source location | Exact blocker |
|---|---|---|
| `carlet-5-theorem-7-weil-bound` | Carlet Theorem 7, p. 76 | Pinned Mathlib and FABL stop at additive-character orthogonality and Gauss/Jacobi identities. They have no arbitrary polynomial-phase bound and no Artin--Schreier, genus, Riemann--Roch, or Hasse--Weil point-count layer from which the stated degree-sensitive square-root estimate could be derived. |
| `carlet-5-weil-nonlinearity-bound` | Carlet p. 76 | The shared trace-pairing coordinate identification is compiled in `carlet-2-trace-pairing-coordinates`, and the Walsh/nonlinearity reduction is compiled in `carlet-5-trace-character-sum-walsh`; only the analytic Weil estimate needed to discharge its uniform character-sum hypothesis remains open. |
| `carlet-5-reciprocal-character-sum-bound` | Carlet p. 76; Shanbhag--Kumar--Helleseth [325, Theorem 1] | Carlet's printed whole-field one-sided inequality is corrected to the primary sharp absolute-value bound over the nonzero field elements; the whole-field convention has the resulting bound with an added `1`. Proving the sharp theorem requires an independent rational-phase estimate with pole-order control. Encoding inversion as a high power loses the degree bound, and the available Gauss/Jacobi identities do not supply the needed conductor/genus and Hasse--Weil layers. |

Chapter 3 has no open node: Proposition 12's affine-flat and equality-case slice layer is
formalized. Chapter 4 has no open node: its former frontier statements are associated with complete
declarations while their principal mathematical ingredients retain independent nodes. Chapter 2
has no open node: the binary-degree formula and Proposition 3 are formalized. The four Chapter 5
citation-recovery records remain outside the 31-node Chapter 5 graph until their source statements
are complete.

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
