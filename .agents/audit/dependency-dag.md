# CryptBoolean reviewed statement dependency DAG

## Graph contract

The `uses :=` relation in the Verso Blueprint records mathematical statement dependencies. It does
not record Lean imports, file inclusion, library provenance, presentation order, or the tactics used
by a proof. A declaration may reuse Mathlib or FABL internally without creating a Blueprint edge
unless a separate source-facing bridge statement is mathematically required.

The generated manifest is the machine-checked graph. This audit is its reviewed, human-readable
spine. The current baseline is:

| Chapter | Nodes | Formalized | Open | Associated declarations | Incoming edges |
|---|---:|---:|---:|---:|---:|
| Carlet Chapter 2 | 36 | 35 | 1 | 159 | 45 |
| Carlet Chapter 3 | 7 | 7 | 0 | 32 | 19 |
| Carlet Chapter 4 | 73 | 73 | 0 | 568 | 159 |
| **Total** | **116** | **115** | **1** | **759** | **223** |

An item marked `[open]` has a complete mathematical statement but no Lean association. In the
tables below, `consumer <- prerequisite-1, prerequisite-2` denotes one incoming edge from each
listed prerequisite.

## Chapter 2: representations and Fourier analysis

### Foundational roots and representation branches

```text
carlet-2-def-support-weight
  <- carlet-2-def-boolean-function
carlet-2-def-walsh-transform
  <- carlet-2-def-boolean-function
carlet-2-pseudoboolean-fourier
  <- carlet-2-def-boolean-function
carlet-2-anf-skeleton
  <- carlet-2-def-boolean-function
carlet-2-nnf-existence-uniqueness
  <- carlet-2-def-boolean-function
carlet-2-def-2-derivative
  <- carlet-2-def-boolean-function

carlet-2-balanced-zero-walsh
  <- carlet-2-def-support-weight, carlet-2-def-walsh-transform
carlet-2-def-hamming-distance
  <- carlet-2-def-support-weight
carlet-2-bridge-relative-hamming-distance
  <- carlet-2-def-hamming-distance

carlet-2-bridge-walsh-normalization
  <- carlet-2-def-walsh-transform
carlet-2-fourier-inversion
  <- carlet-2-bridge-walsh-normalization
carlet-2-parseval
  <- carlet-2-bridge-walsh-normalization
```

This branch keeps raw Hamming distance and raw Walsh sums canonical on the Carlet side. FABL's
relative distance and normalized Fourier coefficients enter only through the two explicit bridge
nodes.

### Algebraic and numerical representations

```text
carlet-2-anf-existence-uniqueness
  <- carlet-2-anf-skeleton
carlet-2-def-algebraic-degree
  <- carlet-2-anf-existence-uniqueness
carlet-2-support-degree-addition
  <- carlet-2-def-algebraic-degree
carlet-2-def-affine-functions
  <- carlet-2-def-algebraic-degree

carlet-2-affine-invariance
  <- carlet-2-def-algebraic-degree, carlet-2-def-affine-functions
carlet-2-restriction-recovery
  <- carlet-2-anf-existence-uniqueness, carlet-2-affine-invariance

carlet-2-prop-4-nnf-mobius
  <- carlet-2-nnf-existence-uniqueness
carlet-2-prop-5-nnf-integrality
  <- carlet-2-prop-4-nnf-mobius
```

The restriction theorem has two genuine mathematical prerequisites: unique ANF recovery and affine
invariance. Proposition 5 is now closed by transporting integer-valuedness through the unique NNF
coefficients and by proving the Boolean-valued square-sum criterion over the finite cube.

### Raw Fourier operations, convolution, and Poisson summation

```text
carlet-2-prop-6-fourier-shifts
  <- carlet-2-pseudoboolean-fourier
carlet-2-cor-2-fourier-involution
  <- carlet-2-pseudoboolean-fourier
carlet-2-prop-7-subspace-indicator
  <- carlet-2-pseudoboolean-fourier

carlet-2-poisson-normalized-specialization
  <- carlet-2-prop-6-fourier-shifts, carlet-2-prop-7-subspace-indicator
carlet-2-cor-1-poisson-summation
  <- carlet-2-prop-6-fourier-shifts, carlet-2-prop-7-subspace-indicator

carlet-2-prop-8-convolution
  <- carlet-2-def-convolution, carlet-2-pseudoboolean-fourier
carlet-2-rel-22-plancherel
  <- carlet-2-prop-8-convolution, carlet-2-cor-2-fourier-involution

carlet-2-spectral-support-bounds
  <- carlet-2-cor-1-poisson-summation, carlet-2-restriction-recovery,
     carlet-2-nnf-existence-uniqueness
```

The normalized Poisson theorem and Carlet's full Corollary 1 are separate consumers of the same two
prerequisites. The normalized identity is associated directly with FABL's theorem; the full raw
identity retains both modulation parameters and is proved locally. Relation (22) is the bilinear
Plancherel identity and depends on convolution plus Fourier involution. The spectral node composes
the raw/normalized support bridge, restriction monotonicity, the ANF lower bound, and the NNF upper
bound; its zero-function conventions are explicit in the source-facing statement.

### Derivatives and autocorrelation

```text
carlet-2-def-autocorrelation
  <- carlet-2-def-2-derivative, carlet-2-def-convolution
carlet-2-rel-25-wiener-khinchin
  <- carlet-2-def-autocorrelation, carlet-2-prop-8-convolution,
     carlet-2-def-walsh-transform
carlet-2-rel-26-total-autocorrelation
  <- carlet-2-rel-25-wiener-khinchin
```

Together with the convolution and Walsh-transform edges shown above, these nodes derive the raw
Wiener--Khinchin identity before summing it to obtain Relation (26).

### Finite-field branch

```text
carlet-2-trace-monomial-degree [open]
  <- carlet-2-absolute-trace, carlet-2-def-algebraic-degree
```

`carlet-2-univariate-representation` is an independent formalized source root: Carlet Relation (4)
is finite interpolation on `GF(2^n)` and has no mathematical edge from absolute trace. Mathlib's
Lagrange interpolation and finite-field trace implementation are perimeter provenance, not graph
nodes.

The Chapter 2 groups above contain exactly 45 incoming statement edges.

## Chapter 3: Reed--Muller coding

```text
carlet-3-affine-weight
  <- carlet-2-def-affine-functions, carlet-2-balanced-zero-walsh

carlet-3-reed-muller-code
  <- carlet-2-def-algebraic-degree, carlet-2-support-degree-addition,
     carlet-2-def-hamming-distance, carlet-2-def-affine-functions

carlet-3-theorem-1-order-one
  <- carlet-3-reed-muller-code, carlet-2-def-affine-functions,
     carlet-3-affine-weight, carlet-2-support-degree-addition,
     carlet-2-def-hamming-distance

carlet-3-theorem-1
  <- carlet-3-reed-muller-code, carlet-2-def-hamming-distance,
     carlet-2-anf-existence-uniqueness
carlet-3-prop-12
  <- carlet-3-theorem-1

carlet-3-reed-muller-dimension
  <- carlet-3-reed-muller-code, carlet-2-anf-existence-uniqueness
carlet-3-theorem-2
  <- carlet-3-reed-muller-code, carlet-3-reed-muller-dimension
```

These are exactly 19 Chapter 3 incoming edges. The `carlet-3-theorem-1-order-one` node remains a
derived `r = 1` specialization, while Carlet's general Theorem 1 is now independently associated
with its all-orders weight and distance declarations. The dimension theorem uses the ANF
coefficient linear equivalence, and Theorem 2 composes the nondegenerate Boolean-function pairing,
orthogonal-complement containment, and the dimension calculation. Proposition 12 composes the
affine-flat indicator normal form, its codimension--degree and weight laws, and equality-case slice
rigidity to classify every minimum-weight word.

## Chapter 4: Boolean functions and cryptography

Chapter 4 has 73 formalized nodes and no open node. Source-facing splits keep intermediate finite
or one-sided theorems distinct from the sharper conclusions they compose.

### Degree and first-order nonlinearity

```text
carlet-4-degree-count
  <- carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree

carlet-4-def-nonlinearity
  <- carlet-2-def-hamming-distance, carlet-2-def-affine-functions
carlet-4-nonlinearity-affine-invariance
  <- carlet-4-def-nonlinearity, carlet-2-affine-invariance
carlet-4-rel-35-nonlinearity-walsh
  <- carlet-4-def-nonlinearity, carlet-2-def-walsh-transform
carlet-4-rel-36-covering-radius-bent
  <- carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval,
     carlet-2-balanced-zero-walsh

carlet-4-random-nonlinearity-lower-bound
  <- carlet-4-rel-35-nonlinearity-walsh
carlet-4-rodier-lower-endpoint
  <- carlet-4-rel-35-nonlinearity-walsh
carlet-4-rodier-upper-endpoint-reduction
  <- carlet-4-rel-35-nonlinearity-walsh
carlet-4-rodier-pair-characteristic-moments
carlet-4-rodier-sharp-random-nonlinearity-interval
  <- carlet-4-rodier-lower-endpoint,
     carlet-4-rodier-upper-endpoint-reduction,
     carlet-4-rodier-pair-characteristic-moments
carlet-4-odd-dimension-exact-five
  <- carlet-4-odd-dimension-quadratic-covering-bounds, carlet-3-affine-weight,
     carlet-3-reed-muller-dimension, carlet-4-def-higher-order-nonlinearity
carlet-4-odd-dimension-quadratic-covering-bounds
  <- carlet-4-rel-35-nonlinearity-walsh, carlet-4-rel-36-covering-radius-bent
carlet-4-odd-dimension-exact-one-three
  <- carlet-4-odd-dimension-quadratic-covering-bounds
carlet-4-odd-dimension-best-nonlinearity
  <- carlet-4-odd-dimension-quadratic-covering-bounds,
     carlet-4-six-variable-covering-coset-coordinate,
     carlet-4-six-variable-degree-four-coset-coordinate
carlet-4-six-variable-covering-coset-coordinate
  <- carlet-4-rel-36-covering-radius-bent
carlet-4-six-variable-degree-four-coset-coordinate
  <- carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval,
     carlet-3-theorem-2
carlet-4-odd-dimension-strict-above-quadratic
  <- carlet-4-rel-35-nonlinearity-walsh
carlet-4-odd-dimension-balanced-above-quadratic
  <- carlet-4-rel-35-nonlinearity-walsh, carlet-2-balanced-zero-walsh
carlet-4-odd-dimension-pc-one-above-quadratic
  <- carlet-4-odd-dimension-balanced-above-quadratic,
     carlet-4-def-propagation-criteria
carlet-4-odd-dimension-degree-pred-above-quadratic
  <- carlet-4-odd-dimension-balanced-above-quadratic, carlet-3-prop-12,
     carlet-4-def-nonlinearity
carlet-4-reed-muller-coset-distance
  <- carlet-4-def-nonlinearity, carlet-3-reed-muller-code
carlet-4-derivative-nonlinearity-bounds
  <- carlet-4-def-nonlinearity, carlet-4-hyperplane-walsh-autocorrelation,
     carlet-2-def-2-derivative, carlet-2-def-autocorrelation
carlet-4-odd-weighting-nonlinearity
  <- carlet-4-def-nonlinearity
```

This family has 46 incoming edges. Relation (35) is the scaling junction from raw Hamming distance
and raw Walsh sums to the normalized FABL quantities used by the implementation. The covering-radius
and bent characterization remains a separate consumer of Relation (35), Parseval, and balancedness.
The Olejar--Stanek bound, Rodier's exact lower endpoint, its upper-endpoint event reduction, and the
pair characteristic moments remain separate formalized ingredients of Rodier's two-sided
interval. The coset-
distance equality carries the necessary pairwise-distinct-coset hypothesis omitted from Carlet's
printed sentence; its two-coset corollary assumes that the representative is non-affine.
The quadratic construction and covering-radius bound give the general odd-dimensional interval;
integrality closes the exact maxima in dimensions one and three, while a residual-code Hamming
argument closes dimension five. The Kavut--Yücel nine-variable Walsh certificate and complete bent
extensions prove strict improvement above the quadratic bound in every odd dimension above seven.
The balanced Maitra--Kavut--Yücel family is verified from its published construction. Linear
reindexing along a certified zero-autocorrelation basis and complete bent extensions prove the
separately cited `PC(1)` family in the stronger range of every odd dimension at least thirteen. A
Proposition 12 affine-line repair enforces degree `n-1` with loss at most two. The two six-variable
coordinate-covering facts, together with the relative-covering reduction and degree-five normal
form, compose the exact dimension-seven value.

### Higher-order nonlinearity

```text
carlet-4-def-higher-order-nonlinearity
  <- carlet-3-reed-muller-code, carlet-2-def-hamming-distance
carlet-4-higher-order-junta-distance
  <- carlet-4-def-higher-order-nonlinearity, carlet-2-def-algebraic-degree
carlet-4-higher-order-counting-criterion
  <- carlet-4-def-higher-order-nonlinearity, carlet-3-reed-muller-dimension
carlet-4-higher-order-asymptotic-lower-bound
  <- carlet-4-higher-order-counting-criterion
carlet-4-higher-order-plotkin-induction
  <- carlet-4-def-higher-order-nonlinearity
carlet-4-higher-order-order-two-moment-ratio
  <- carlet-4-def-higher-order-nonlinearity,
     carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval
carlet-4-higher-order-order-two-dual-moment-decomposition
  <- carlet-4-higher-order-order-two-moment-ratio, carlet-3-theorem-2
carlet-4-higher-order-order-two-weight-grouping
  <- carlet-4-higher-order-order-two-dual-moment-decomposition
carlet-4-higher-order-order-two-low-weight-support
  <- carlet-4-higher-order-order-two-weight-grouping, carlet-3-theorem-1
carlet-4-higher-order-order-two-weight-eight-bound
  <- carlet-4-higher-order-order-two-low-weight-support, carlet-3-prop-12
carlet-4-higher-order-order-two-weight-twelve-bound
  <- carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2
carlet-4-higher-order-order-two-weight-fourteen-bound
  <- carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2
carlet-4-higher-order-order-two-weight-sixteen-rank-reduction
  <- carlet-4-higher-order-order-two-low-weight-support, carlet-3-theorem-2
carlet-4-higher-order-order-two-weight-sixteen-rank-seven-classification
  <- carlet-4-higher-order-order-two-weight-sixteen-rank-reduction
carlet-4-higher-order-order-two-weight-sixteen-orbit-sos
carlet-4-higher-order-order-two-weight-sixteen-residual-cover
  <- carlet-4-higher-order-order-two-weight-sixteen-rank-reduction
carlet-4-higher-order-order-two-weight-sixteen-character-bound
  <- carlet-4-higher-order-order-two-weight-sixteen-rank-seven-classification,
     carlet-4-higher-order-order-two-weight-sixteen-orbit-sos,
     carlet-4-higher-order-order-two-weight-sixteen-residual-cover
carlet-4-higher-order-order-two-moment-difference
  <- carlet-4-higher-order-order-two-weight-eight-bound,
     carlet-4-higher-order-order-two-weight-twelve-bound,
     carlet-4-higher-order-order-two-weight-fourteen-bound,
     carlet-4-higher-order-order-two-weight-sixteen-character-bound
carlet-4-higher-order-order-two-asymptotic-upper
  <- carlet-4-higher-order-order-two-moment-ratio,
     carlet-4-higher-order-order-two-moment-difference
carlet-4-higher-order-general-r-propagation
  <- carlet-4-higher-order-plotkin-induction,
     carlet-4-higher-order-order-two-asymptotic-upper
carlet-4-higher-order-general-bounds
  <- carlet-4-higher-order-general-r-propagation,
     carlet-4-higher-order-order-two-weight-sixteen-character-bound
carlet-4-prop-13
  <- carlet-4-def-higher-order-nonlinearity, carlet-2-def-2-derivative
```

These are 41 incoming edges. The exact finite Hamming-ball counting criterion yields the cited
fixed-order asymptotic lower existence bound. The sharp upper bound is exposed as a mathematical
DAG. The
Plotkin recurrence propagates an order-two base. Consecutive moment ratios reduce that base to the
seventh/eighth moment difference; dual-code orthogonality and Krawtchouk inversion group the
difference by weights. The weights `8`, `12`, and `14` have separate affine-flat classifications
and character bounds. At weight `16`, affine-span rank is at most seven; the full-rank branch
produces a self-dual `[16,8,>=4]` code and splits into three canonical orbits, while the low-rank
branch has a coarse affine-mask cover. Independently of the classification, the three canonical
patterns satisfy their orbit sum-of-squares bounds. The classifier, orbit bounds, and residual
count meet only in the aggregate character bound, which feeds the moment difference, order-two
extraction, and general-order composition. The rank-seven classification supplies the common
hypothesis used by the aggregate character-bound consumer. Proposition 13 depends only on
the higher-order distance definition and the Boolean derivative; its two recursive lower bounds do
not require a separate source-facing autocorrelation node.

### Resiliency and propagation criteria

```text
carlet-4-def-resiliency-correlation-immunity
  <- carlet-2-balanced-zero-walsh
carlet-4-theorem-3
  <- carlet-4-def-resiliency-correlation-immunity, carlet-2-cor-1-poisson-summation,
     carlet-2-def-walsh-transform, carlet-2-balanced-zero-walsh
carlet-4-resiliency-support-dual-distance
  <- carlet-4-theorem-3, carlet-2-def-support-weight
carlet-4-code-generator-resilient
  <- carlet-4-def-resiliency-correlation-immunity
carlet-4-resiliency-translation-invariance
  <- carlet-4-theorem-3, carlet-2-prop-6-fourier-shifts
carlet-4-def-propagation-criteria
  <- carlet-2-def-2-derivative, carlet-2-def-autocorrelation,
     carlet-2-balanced-zero-walsh, carlet-4-def-resiliency-correlation-immunity
```

This family has 14 incoming edges. Theorem 3 is the Walsh-zero characterization linking the
restriction definition to Poisson summation; propagation criteria then reuse both the derivative
and resiliency branches.

### Linear structures and hyperplane spectra

```text
carlet-4-def-linear-kernel
  <- carlet-2-def-2-derivative
carlet-4-prop-14
  <- carlet-4-def-linear-kernel, carlet-2-def-affine-functions
carlet-4-linear-kernel-nonlinearity-bound
  <- carlet-4-prop-14, carlet-4-rel-36-covering-radius-bent

carlet-4-hyperplane-walsh-autocorrelation
  <- carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin
carlet-4-prop-15
  <- carlet-4-hyperplane-walsh-autocorrelation, carlet-4-def-linear-kernel,
     carlet-2-def-walsh-transform
carlet-4-distance-to-linear-structures
  <- carlet-4-def-linear-kernel, carlet-2-def-hamming-distance,
     carlet-2-def-autocorrelation, carlet-4-rel-36-covering-radius-bent
```

These nodes contribute 14 incoming edges. Proposition 14 supplies the affine-coordinate normal
form, whereas Proposition 15 passes through the hyperplane Walsh--autocorrelation identity; neither
edge is inferred merely from module proximity.

### Algebraic immunity and fast algebraic attacks

```text
carlet-4-def-annihilator-algebraic-immunity
  <- carlet-2-anf-existence-uniqueness, carlet-2-def-algebraic-degree,
     carlet-2-def-support-weight
carlet-4-low-degree-relation-equivalence
  <- carlet-4-def-annihilator-algebraic-immunity
carlet-4-annihilator-linear-system
  <- carlet-4-def-annihilator-algebraic-immunity, carlet-2-anf-existence-uniqueness,
     carlet-2-def-support-weight
carlet-4-ai-upper-bound
  <- carlet-4-low-degree-relation-equivalence, carlet-4-annihilator-linear-system,
     carlet-4-prop-14
carlet-4-fast-algebraic-optimality
  <- carlet-4-def-annihilator-algebraic-immunity,
     carlet-4-annihilator-linear-system
```

This branch has 12 incoming edges. The upper bound composes the low-degree relation equivalence,
the ANF evaluation system, and Proposition 14's coordinate separation rather than treating its
dimension count as an isolated root.

### Autocorrelation indicators and fourth Walsh moments

```text
carlet-4-def-autocorrelation-indicators
  <- carlet-2-def-autocorrelation
carlet-4-autocorrelation-indicator-bounds
  <- carlet-4-def-autocorrelation-indicators, carlet-4-def-linear-kernel,
     carlet-2-balanced-zero-walsh
carlet-4-second-derivative-sum
  <- carlet-4-def-autocorrelation-indicators, carlet-2-rel-26-total-autocorrelation
carlet-4-rel-39-fourth-walsh-moment
  <- carlet-4-def-autocorrelation-indicators, carlet-2-rel-25-wiener-khinchin,
     carlet-2-rel-22-plancherel
carlet-4-indicator-nonlinearity-spectral-support
  <- carlet-4-def-nonlinearity, carlet-4-rel-39-fourth-walsh-moment,
     carlet-2-parseval, carlet-2-spectral-support-bounds,
     carlet-4-rel-36-covering-radius-bent
```

These are 14 incoming edges. Relation (39) depends on the indicator definition together with the
raw Wiener--Khinchin and Plancherel identities. Its nonlinearity and support consequences remain a
separate five-prerequisite node.

### Maximum correlation and generalized linear-structure distance

```text
carlet-4-def-maximum-correlation
  <- carlet-4-def-higher-order-nonlinearity,
     carlet-4-def-resiliency-correlation-immunity, carlet-2-balanced-zero-walsh
carlet-4-rel-40-maximum-correlation-bound
  <- carlet-4-def-maximum-correlation, carlet-4-def-nonlinearity,
     carlet-2-def-walsh-transform, carlet-2-cor-1-poisson-summation
carlet-4-generalized-linear-structure-distance
  <- carlet-4-def-linear-kernel, carlet-2-def-hamming-distance
```

This family has 9 incoming edges. Maximum correlation connects higher-order approximation,
resiliency, and Walsh restriction formulas; generalized linear-structure distance is independent of
Relation (40) and depends only on the linear kernel and Hamming distance.

### Other cryptographic complexity criteria

```text
carlet-4-other-complexity-definitions
  <- carlet-2-def-algebraic-degree, carlet-2-affine-invariance,
     carlet-2-spectral-support-bounds
carlet-4-kth-nonhomomorphicity
  <- carlet-2-def-walsh-transform, carlet-2-parseval,
     carlet-4-rel-36-covering-radius-bent
carlet-4-affine-reindex-first-resilient
  <- carlet-4-theorem-3, carlet-4-resiliency-translation-invariance,
     carlet-2-def-affine-functions
```

These final nodes contribute 9 incoming edges. The `k`th nonhomomorphicity node follows Carlet's
name for the even-output tuple count and records that reference [357] instead calls that count
homomorphicity and reserves nonhomomorphicity for the complementary odd-output count. Across all
eight Chapter 4 families, the reviewed counts are
`46 + 41 + 14 + 14 + 12 + 14 + 9 + 9 = 159` incoming edges.

## Remaining proof frontier

One source node remains open: the Chapter 2 trace-monomial proposition. Its Blueprint prerequisites
are formalized, but it requires a genuine missing mathematical layer rather than another already
inventoried node:

- `carlet-2-trace-monomial-degree` (Carlet Proposition 3) lacks the bridge identifying coordinate
  ANF degree on `V_n` with the maximum binary exponent weight in the univariate finite-field
  representation. It also lacks cyclotomic-orbit noncancellation showing that nonzeroness forces an
  orbit coefficient of binary weight `w_2(k)` to survive. The pinned FABL and Mathlib surfaces do
  not expose either result.
Proposition 12 is closed: Chapter 3's affine-flat and equality-case slice layer proves the exact
source classification. Chapter 4 is closed: Rodier's interval, the exact dimension-seven maximum,
and the sharp higher-order upper bound are associated with their complete production proofs, while
their mathematical ingredients remain separately visible in the graph.

## Machine verification

The current counts and edge set are enforced by
`blueprint-verso/scripts/validate_manifest.py`. The style and association split are enforced by
`blueprint-verso/scripts/check_statement_style.py`, which runs through the site driver. Before a
handoff, run from the repository root:

```bash
lake build CryptBoolean
./.github/scripts/forbidden_tokens.sh
./.github/scripts/audit_axioms.sh
./blueprint-verso/scripts/site.sh build
```

The inventories under `.agents/inventory/`, the Verso `uses :=` metadata, this audit, and the
manifest validator must be changed together whenever the reviewed graph changes.
