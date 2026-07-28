# CryptBoolean reviewed statement dependency DAG

## Graph contract

The `uses :=` relation in the Verso Blueprint records mathematical statement dependencies. It does
not record Lean imports, file inclusion, library provenance, presentation order, or the tactics used
by a proof. A declaration may reuse Mathlib or FABL internally without creating a Blueprint edge
unless a separate source-facing mathematical statement is required.

The generated manifest is the machine-checked graph. This audit is its reviewed, human-readable
spine. The current baseline is:

| Chapter | Nodes | Formalized | Open | Associated declarations | Incoming edges |
|---|---:|---:|---:|---:|---:|
| Carlet Chapter 2 | 41 | 41 | 0 | 174 | 56 |
| Carlet Chapter 3 | 7 | 7 | 0 | 32 | 19 |
| Carlet Chapter 4 | 73 | 73 | 0 | 568 | 159 |
| Carlet Chapter 5 | 31 | 28 | 3 | 203 | 70 |
| Carlet Chapter 6 | 57 | 57 | 0 | 361 | 163 |
| **Total** | **209** | **206** | **3** | **1338** | **467** |

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
carlet-2-relative-hamming-normalization
  <- carlet-2-def-hamming-distance

carlet-2-walsh-normalization
  <- carlet-2-def-walsh-transform
carlet-2-fourier-inversion
  <- carlet-2-walsh-normalization
carlet-2-parseval
  <- carlet-2-walsh-normalization
```

This branch keeps raw Hamming distance and raw Walsh sums canonical on the Carlet side. Two scaling
theorems relate them to FABL's relative distance and normalized Fourier coefficients.

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
carlet-2-rel-30-nnf-fourier
  <- carlet-2-nnf-existence-uniqueness, carlet-2-pseudoboolean-fourier,
     carlet-2-prop-7-subspace-indicator
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
carlet-2-prop-11-walsh-divisibility
  <- carlet-2-def-algebraic-degree, carlet-2-def-walsh-transform
```

The normalized Poisson theorem and Carlet's full Corollary 1 are separate consumers of the same two
prerequisites. The normalized identity is associated directly with FABL's theorem; the full raw
identity retains both modulation parameters and is proved locally. Relation (22) is the bilinear
Plancherel identity and depends on convolution plus Fourier involution. The spectral theorem composes
the raw/normalized support identity, restriction monotonicity, the ANF lower bound, and the NNF upper
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
carlet-2-prop-9-restriction-square
  <- carlet-2-cor-1-poisson-summation, carlet-2-rel-25-wiener-khinchin,
     carlet-2-def-2-derivative
```

Together with the convolution and Walsh-transform edges shown above, these nodes derive the raw
Wiener--Khinchin identity before summing it to obtain Relation (26).

### Finite-field branch

```text
carlet-2-trace-pairing-coordinates
  <- carlet-2-absolute-trace
carlet-2-univariate-binary-degree
  <- carlet-2-univariate-representation, carlet-2-def-algebraic-degree
carlet-2-trace-monomial-degree
  <- carlet-2-absolute-trace, carlet-2-univariate-binary-degree
```

`carlet-2-univariate-representation` is an independent formalized source root: Carlet Relation (4)
is finite interpolation on `GF(2^n)` and has no mathematical edge from absolute trace. Mathlib's
Lagrange interpolation and finite-field trace implementation are perimeter provenance, not graph
nodes. The unnumbered p. 17 binary-degree formula is a separate source-facing consumer of the
canonical representation and coordinate ANF degree; Proposition 3 then specializes it through the
explicit Frobenius orbit of a trace monomial. The trace-pairing coordinate theorem is used by both
the Chapter 5 quadratic representation and its character-sum reduction. Proposition 3 follows from
the binary-degree formula and cyclic-orbit weight invariance.

The Chapter 2 groups above contain exactly 56 incoming statement edges.

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
the ANF evaluation system, and Proposition 14's coordinate separation; its dimension count is one
part of that argument.

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

## Chapter 5: restricted-weight and restricted-spectrum classes

Chapter 5 has 31 reviewed statements: 28 formalized and 3 open. Its affine, quadratic,
restriction, normality, covering-sequence, and character-sum arguments remain compositional.

### Affine and quadratic functions

```text
carlet-5-affine-walsh-spectrum
  <- carlet-2-def-walsh-transform, carlet-3-affine-weight
carlet-5-def-maiorana-mcfarland
  <- carlet-2-def-affine-functions
carlet-5-def-quadratic-symplectic-form
  <- carlet-3-reed-muller-code, carlet-2-def-2-derivative,
     carlet-4-def-linear-kernel
carlet-5-rel-41-quadratic-kernel-sum
  <- carlet-5-def-quadratic-symplectic-form,
     carlet-2-rel-26-total-autocorrelation, carlet-3-affine-weight
carlet-5-theorem-4
  <- carlet-5-rel-41-quadratic-kernel-sum, carlet-2-balanced-zero-walsh
carlet-5-quadratic-balanced-iff-derivative-one
  <- carlet-5-theorem-4, carlet-5-def-quadratic-symplectic-form
carlet-5-quadratic-symplectic-rank-even
  <- carlet-5-theorem-4, carlet-5-affine-walsh-spectrum, carlet-2-parseval
carlet-5-quadratic-weight-nonlinearity-values
  <- carlet-5-theorem-4, carlet-5-quadratic-symplectic-rank-even,
     carlet-5-affine-walsh-spectrum, carlet-4-rel-35-nonlinearity-walsh
carlet-5-theorem-5
  <- carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-4,
     carlet-2-affine-invariance
carlet-5-quadraticization-step
  <- carlet-2-def-walsh-transform
carlet-5-degree-three-walsh-lift
  <- carlet-5-quadraticization-step, carlet-2-anf-existence-uniqueness,
     carlet-2-def-algebraic-degree
carlet-5-quadratic-trace-representation
  <- carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-5,
     carlet-2-absolute-trace, carlet-2-trace-monomial-degree,
     carlet-2-trace-pairing-coordinates
carlet-5-def-quadratic-semi-bent
  <- carlet-5-quadratic-weight-nonlinearity-values,
     carlet-5-quadratic-trace-representation
```

These nodes contribute 34 incoming edges. Relation (41), raw Parseval, and the affine Walsh
spectrum compose the proved weight, balancedness, derivative, and even-rank restrictions. The
displayed half-power formula in Theorem 4 explicitly assumes `n > 0`; its balancedness and
even-rank consequences are compiled in their valid assumption-free forms. The odd/even quadratic
trace representation composes the quadratic symplectic classification, Theorem 5 normal form,
absolute trace, Proposition 3, and the shared trace-pairing coordinate theorem. The quadratic
semi-bent predicate includes the required nonlinearity condition on the coefficients of the cited
trace family.

### Flat indicators, affine restrictions, and normality

```text
carlet-5-flat-indicator-walsh-nonlinearity
  <- carlet-3-prop-12, carlet-2-def-walsh-transform,
     carlet-4-rel-35-nonlinearity-walsh
carlet-5-rel-42-restriction-nonlinearity
  <- carlet-2-cor-1-poisson-summation, carlet-4-rel-35-nonlinearity-walsh
carlet-5-affine-flat-restriction-bound
  <- carlet-5-rel-42-restriction-nonlinearity, carlet-2-def-affine-functions,
     carlet-2-balanced-zero-walsh
carlet-5-def-4-normality
  <- carlet-4-other-complexity-definitions
carlet-5-random-nonnormality
  <- carlet-5-def-4-normality, carlet-4-degree-count
```

This family contributes 11 incoming edges. The flat-indicator node corrects the printed
nonlinearity conclusion in codimension one, where the indicator is affine and has nonlinearity
zero; the printed value `2^(n-r)` is retained for `r >= 2`. Relation (42) is proved from the full
Poisson formula using a coordinate equivalence onto the direction subspace; a complementary-
subspace wrapper recovers Carlet's `E,E'` presentation. Its natural-number half-power form assumes
`1 <= k`, while the division-free and real-cast forms are total for every `k`. Equality composes
with affine extension and Walsh cancellation to give balancedness on every other coset.

### Covering and partial covering sequences

```text
carlet-5-def-5-covering-sequence
  <- carlet-2-def-2-derivative
carlet-5-covering-sequence-balancedness
  <- carlet-5-def-5-covering-sequence, carlet-2-balanced-zero-walsh
carlet-5-covering-sequence-walsh-characterization
  <- carlet-5-def-5-covering-sequence, carlet-2-pseudoboolean-fourier,
     carlet-2-def-walsh-transform
carlet-5-covering-sequence-resiliency
  <- carlet-5-covering-sequence-walsh-characterization,
     carlet-5-covering-sequence-balancedness, carlet-4-theorem-3
carlet-5-def-regular-function
  <- carlet-5-def-5-covering-sequence, carlet-5-covering-sequence-resiliency
carlet-5-def-6-partial-covering-sequence
  <- carlet-5-def-5-covering-sequence
carlet-5-derivative-space-partial-covering-sequence
  <- carlet-5-def-6-partial-covering-sequence, carlet-2-def-2-derivative
carlet-5-theorem-6
  <- carlet-5-def-6-partial-covering-sequence, carlet-2-prop-6-fourier-shifts,
     carlet-2-def-walsh-transform
carlet-5-theorem-6-weight-corollary
  <- carlet-5-theorem-6, carlet-2-balanced-zero-walsh
```

These nodes contribute 19 incoming edges. The canonical interface keeps Carlet's printed
integer-valued sequences and unnormalized integer Walsh transform. The Walsh characterization,
balancedness equivalence, feasible-order resiliency consequences, regular-family generalization,
the derivative-space representative construction, and Theorem 6 are compiled separately. The
weight corollary is proved first in a division-free form valid even when the displayed quotient is
undefined.

### Character-sum bounds

```text
carlet-5-theorem-7-weil-bound [open]
carlet-5-trace-character-sum-walsh
  <- carlet-2-def-walsh-transform, carlet-2-trace-pairing-coordinates,
     carlet-4-rel-35-nonlinearity-walsh
carlet-5-weil-nonlinearity-bound [open]
  <- carlet-5-theorem-7-weil-bound, carlet-5-trace-character-sum-walsh
carlet-5-reciprocal-character-sum-bound [open]
  <- carlet-2-absolute-trace
```

This branch contributes 6 incoming edges. The Chapter 2 trace-pairing theorem identifies every
cube Walsh character with a unique finite-field trace character, and the Chapter 5 theorem derives
the exact nonlinearity reduction from a uniform complete-sum bound. The Weil theorem is an
independent open source root; its binary nonlinearity consequence and the reciprocal-polynomial
bound remain separate because the former is an additive-character theorem and the latter is a
rational-function estimate. Across the four Chapter 5 families, the reviewed counts are
`34 + 11 + 19 + 6 = 70` incoming edges.

## Chapter 6: bent functions

Chapter 6 has 57 reviewed statements, all formalized by 361 proved declarations with 163 incoming
statement edges. Its graph reuses the Chapter 2 raw Walsh, Fourier, NNF, Poisson, derivative, and
trace layers; the Chapter 3 Reed--Muller layer; the Chapter 4 nonlinearity, propagation,
support-code, and linear-structure layers; and the Chapter 5 quadratic, restriction, trace, and
normality layers.

### Bentness, duality, and algebraic degree

```text
carlet-6-def-7-bent
  <- carlet-4-rel-36-covering-radius-bent, carlet-4-nonlinearity-affine-invariance,
     carlet-2-def-walsh-transform, carlet-2-def-hamming-distance
carlet-6-lemma-2-walsh-congruence
  <- carlet-6-def-7-bent, carlet-2-parseval
carlet-6-theorem-8-perfect-nonlinearity
  <- carlet-6-def-7-bent, carlet-2-rel-25-wiener-khinchin,
     carlet-4-def-propagation-criteria
carlet-6-prop-16-support-code
  <- carlet-6-def-7-bent, carlet-4-resiliency-support-dual-distance,
     carlet-2-balanced-zero-walsh, carlet-2-parseval

carlet-6-dual
  <- carlet-6-def-7-bent, carlet-2-def-walsh-transform, carlet-2-fourier-inversion
carlet-6-rel-44-dual-isometry
  <- carlet-6-dual, carlet-2-rel-22-plancherel, carlet-2-def-hamming-distance
carlet-6-rel-45-dual-derivatives
  <- carlet-6-dual, carlet-6-rel-44-dual-isometry, carlet-2-prop-6-fourier-shifts,
     carlet-2-def-2-derivative
carlet-6-dual-nnf
  <- carlet-6-dual, carlet-2-nnf-existence-uniqueness, carlet-2-rel-30-nnf-fourier
carlet-6-prop-17-dual-nnf-divisibility
  <- carlet-6-dual-nnf, carlet-6-lemma-2-walsh-congruence,
     carlet-2-prop-5-nnf-integrality
carlet-6-half-degree-anf-complement
  <- carlet-6-prop-17-dual-nnf-divisibility, carlet-6-dual-nnf,
     carlet-2-anf-existence-uniqueness
carlet-6-rel-46-dual-poisson
  <- carlet-6-dual, carlet-2-cor-1-poisson-summation

carlet-6-quadratic-bent-characterization
  <- carlet-6-def-7-bent, carlet-5-def-quadratic-symplectic-form, carlet-5-theorem-5,
     carlet-5-quadratic-weight-nonlinearity-values
carlet-6-prop-18-rothaus-degree-bound
  <- carlet-6-prop-17-dual-nnf-divisibility, carlet-6-dual,
     carlet-2-def-algebraic-degree
carlet-6-prop-19
  <- carlet-6-rel-46-dual-poisson, carlet-6-prop-18-rothaus-degree-bound, carlet-6-dual,
     carlet-2-anf-existence-uniqueness
```

The duality branch keeps Carlet's unnormalized integer Walsh convention. Proposition 17 is proved
through the NNF Fourier formula and its divisibility conditions; reducing the half-degree identity
modulo two gives the complementary ANF-coefficient relation. Proposition 19 composes Relation (46)
with a reusable McEliece--Ax character-sum divisibility theorem, the exact two-adic valuation of a
top-degree ANF slice, and the dual Rothaus bound.

### Primary and secondary constructions

```text
carlet-6-maiorana-mcfarland
  <- carlet-6-def-7-bent, carlet-5-def-maiorana-mcfarland,
     carlet-5-affine-walsh-spectrum
carlet-6-prop-20-general-maiorana-mcfarland
  <- carlet-6-maiorana-mcfarland, carlet-5-affine-flat-restriction-bound,
     carlet-6-def-7-bent
carlet-6-partial-spread-construction
  <- carlet-6-theorem-12-geometric-characterization

carlet-6-direct-sum
  <- carlet-6-def-7-bent, carlet-6-dual
carlet-6-rothaus-construction
  <- carlet-6-theorem-10-slice-construction, carlet-6-cor-4-three-function-construction
carlet-6-theorem-9-flat-switching
  <- carlet-6-theorem-8-perfect-nonlinearity, carlet-6-rel-46-dual-poisson,
     carlet-2-prop-11-walsh-divisibility, carlet-3-prop-12
carlet-6-theorem-10-slice-construction
  <- carlet-6-def-7-bent, carlet-6-dual
carlet-6-indirect-sum
  <- carlet-6-theorem-10-slice-construction
carlet-6-prop-21-permutation-reindexing
  <- carlet-6-def-7-bent, carlet-2-def-hamming-distance
carlet-6-prop-22-three-function-identity
  <- carlet-2-pseudoboolean-fourier, carlet-2-def-walsh-transform
carlet-6-cor-4-three-function-construction
  <- carlet-6-prop-22-three-function-identity, carlet-6-lemma-2-walsh-congruence,
     carlet-6-dual

carlet-6-theorem-11-hyperplane-restrictions
  <- carlet-2-prop-9-restriction-square, carlet-6-def-7-bent
carlet-6-hyperplane-restriction-plateaued
  <- carlet-6-theorem-11-hyperplane-restrictions, carlet-6-def-plateaued,
     carlet-4-rel-35-nonlinearity-walsh
```

The flat-switching proof composes the Chapter 2 Walsh-divisibility theorem with the Chapter 3
minimum-weight affine-flat classification. The general slice construction owns the indirect-sum
and Rothaus specializations. The hyperplane decomposition uses the exact restriction-square
identity rather than introducing a second spectral normalization.

### Counting and three characterizations

```text
carlet-6-maiorana-mcfarland-count
  <- carlet-6-maiorana-mcfarland
carlet-6-naive-bent-count-bound
  <- carlet-6-prop-18-rothaus-degree-bound, carlet-3-reed-muller-dimension

carlet-6-prop-23-nnf-characterization
  <- carlet-6-lemma-2-walsh-congruence, carlet-2-rel-30-nnf-fourier,
     carlet-2-prop-4-nnf-mobius, carlet-2-prop-5-nnf-integrality
carlet-6-lemma-3-subspace-indicators
carlet-6-theorem-12-geometric-characterization
  <- carlet-6-prop-23-nnf-characterization, carlet-6-lemma-3-subspace-indicators,
     carlet-6-lemma-2-walsh-congruence, carlet-2-prop-7-subspace-indicator,
     carlet-6-dual
carlet-6-prop-24-second-order-characterization
  <- carlet-6-theorem-8-perfect-nonlinearity, carlet-4-autocorrelation-indicator-bounds,
     carlet-4-second-derivative-sum, carlet-2-def-convolution,
     carlet-2-prop-8-convolution, carlet-2-fourier-inversion
```

Lemma 3 is an independent finite-dimensional subspace-indicator root. Theorem 12 combines it with
the NNF congruence criterion and the half-dimensional indicator transform; its exact generalized
partial-spread case also transports the dual through perpendicular subspaces. Proposition 24 is
proved by Fourier transforming the triple convolution of the sign function.

### Hyper-bent functions and superclasses

```text
carlet-6-def-hyper-bent
  <- carlet-2-absolute-trace, carlet-2-trace-pairing-coordinates, carlet-6-def-7-bent
carlet-6-lemma-4-subfield-intersection
  <- carlet-6-def-hyper-bent, carlet-2-absolute-trace
carlet-6-prop-25-psap-hyper-bent
  <- carlet-6-def-hyper-bent, carlet-6-lemma-4-subfield-intersection,
     carlet-6-partial-spread-construction, carlet-5-quadratic-trace-representation

carlet-6-prop-26-partially-bent
  <- carlet-2-rel-25-wiener-khinchin, carlet-2-parseval,
     carlet-4-def-linear-kernel, carlet-6-def-plateaued
carlet-6-prop-27-fourier-uncertainty
  <- carlet-2-pseudoboolean-fourier, carlet-2-parseval,
     carlet-2-cor-1-poisson-summation
carlet-6-def-partial-bent
  <- carlet-2-pseudoboolean-fourier
carlet-6-partial-bent-duality
  <- carlet-6-def-partial-bent, carlet-2-cor-2-fourier-involution
carlet-6-partial-bent-degree-bound
  <- carlet-6-def-partial-bent, carlet-6-prop-18-rothaus-degree-bound
carlet-6-partial-bent-types
  <- carlet-6-def-partial-bent, carlet-2-parseval
carlet-6-partial-bent-disjoint-support-sum
  <- carlet-6-def-partial-bent, carlet-6-partial-bent-types,
     carlet-2-pseudoboolean-fourier
carlet-6-def-plateaued
  <- carlet-2-def-walsh-transform, carlet-2-parseval, carlet-6-def-7-bent
carlet-6-plateaued-support-nonlinearity
  <- carlet-6-def-plateaued, carlet-4-rel-35-nonlinearity-walsh, carlet-2-parseval
carlet-6-prop-28-second-order-plateaued
  <- carlet-6-def-plateaued, carlet-6-prop-24-second-order-characterization
carlet-6-plateaued-coset-orphan
  <- carlet-6-def-plateaued, carlet-6-plateaued-support-nonlinearity,
     carlet-3-reed-muller-code, carlet-4-def-nonlinearity, carlet-2-parseval
```

The finite-field hyper-bent predicate is reduced to ordinary cube bentness through the Chapter 2
trace-pairing equivalence. Proposition 26 reuses Wiener--Khinchin and the Fourier uncertainty
equality case to recover the bent-plus-affine complementary decomposition. Plateauedness keeps a
positive integer Walsh amplitude and derives its power-of-two form through Parseval. Under the
source's exact punctured two-level definition, Fourier involution proves partial-bent duality and
Parseval gives the corrected type formula; explicit two-variable examples refute the printed
degree bound and disjoint-support closure. The orphan theorem uses the necessary non-affine
hypothesis.

### Normal extensions and Kerdock codes

```text
carlet-6-def-8-normal-extension
  <- carlet-6-def-7-bent
carlet-6-normal-extension-composition-duality
  <- carlet-6-def-8-normal-extension, carlet-6-dual, carlet-6-rel-46-dual-poisson
carlet-6-normal-zero-dimensional-characterization
  <- carlet-6-def-8-normal-extension, carlet-5-def-4-normality,
     carlet-2-affine-invariance
carlet-6-prop-29-direct-sum-normality
  <- carlet-6-direct-sum, carlet-6-def-8-normal-extension,
     carlet-6-normal-zero-dimensional-characterization,
     carlet-5-affine-flat-restriction-bound
carlet-6-prop-30-normality-descends
  <- carlet-6-def-8-normal-extension, carlet-6-normal-zero-dimensional-characterization,
     carlet-6-prop-31-normal-extension-replacement,
     carlet-5-affine-flat-restriction-bound
carlet-6-prop-31-normal-extension-replacement
  <- carlet-6-def-8-normal-extension, carlet-6-normal-extension-composition-duality,
     carlet-6-rel-46-dual-poisson

carlet-6-rel-56-complete-quadratic
  <- carlet-6-quadratic-bent-characterization, carlet-2-def-support-weight
carlet-6-kerdock-parameters
  <- carlet-6-def-7-bent, carlet-3-reed-muller-code,
     carlet-4-reed-muller-coset-distance
carlet-6-kerdock-field-trace-identity
  <- carlet-6-rel-56-complete-quadratic, carlet-2-absolute-trace,
     carlet-6-kerdock-field-construction
carlet-6-kerdock-field-construction
  <- carlet-5-quadratic-trace-representation, carlet-6-quadratic-bent-characterization,
     carlet-6-kerdock-parameters, carlet-2-absolute-trace,
     carlet-2-trace-pairing-coordinates
```

The zero-dimensional normal-extension statement distinguishes the source's linear-subspace
convention from Chapter 5's affine-flat convention and supplies the necessary affine-equivalence
correction with an explicit two-variable counterexample. Proposition 31 is proved through the
Poisson formula. The Kerdock parameter theorem consumes only a finite quadratic representative
family with pairwise bent sums. The direct trace expression allowed by Carlet's footnote 44 now
constructs such a family and proves its parameters; the separate coordinate theorem proves the
self-dual-normal-basis identity under its explicit Frobenius, trace, and trace-pairing hypotheses
without conflating it with the coordinate-invariant construction.

These Chapter 6 families contain exactly 163 incoming statement edges.

## Remaining proof frontier

Three source statements remain open, all in the analytic Chapter 5 character-sum branch. Their complete
statements remain visible without placeholder associations:

- `carlet-5-theorem-7-weil-bound` and `carlet-5-weil-nonlinearity-bound` require the analytic
  additive-character Weil estimate. The trace-pairing coordinate identification and the
  Walsh/nonlinearity reduction are already closed by `carlet-2-trace-pairing-coordinates` and
  `carlet-5-trace-character-sum-walsh`.
- `carlet-5-reciprocal-character-sum-bound` requires the separate rational-function
  additive-character estimate.

Four further Chapter 5 citation-recovery records are intentionally outside the 31-node graph until
their primary-source parameters support complete statements; they do not affect the manifest
counts or edges.

Proposition 12 is closed: Chapter 3's affine-flat and equality-case slice layer proves the exact
source classification. Chapter 4 is closed: Rodier's interval, the exact dimension-seven maximum,
and the sharp higher-order upper bound are associated with their complete production proofs, while
their mathematical ingredients remain separately visible in the graph. Chapter 5's quadratic
normal form, quadratic trace representation, Relation (42), random-nonnormality limit, and
trace-character reduction are closed; the three analytic open nodes above define the remaining
reviewed frontier. Chapter 6 is closed: all 57 nodes have proved associations, while its nineteen
source-recovery records remain outside the graph until their cited statements or certificates can
be recovered faithfully.

## Machine verification

The current counts and edge set are enforced by
`blueprint-verso/scripts/validate_manifest.py`. The style and association split are enforced by
`blueprint-verso/scripts/check_statement_style.py`, which runs through the site driver. Local
handoff verification uses the narrow affected module and lightweight text gates:

```bash
lake build CryptBoolean.Carlet.Chapter06
./.github/scripts/forbidden_tokens.sh
python3 ./blueprint-verso/scripts/check_statement_style.py
```

The root build, axiom audit, complete Blueprint build, and publication build run in GitHub Actions;
they are intentionally not run on the development machine.

The inventories under `.agents/inventory/`, the Verso `uses :=` metadata, this audit, and the
manifest validator must be changed together whenever the reviewed graph changes.
