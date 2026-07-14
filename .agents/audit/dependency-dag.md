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
| Carlet Chapter 3 | 7 | 6 | 1 | 21 | 19 |
| **Total** | **43** | **41** | **2** | **180** | **64** |

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
carlet-3-prop-12 [open]
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
orthogonal-complement containment, and the dimension calculation.

## Remaining proof frontier

Only two source nodes remain open. Their reviewed Blueprint prerequisites are formalized, but each
requires a genuine missing mathematical layer rather than another already inventoried node:

- `carlet-2-trace-monomial-degree` (Carlet Proposition 3) lacks the bridge identifying coordinate
  ANF degree on `V_n` with the maximum binary exponent weight in the univariate finite-field
  representation. It also lacks cyclotomic-orbit noncancellation showing that nonzeroness forces an
  orbit coefficient of binary weight `w_2(k)` to survive. The pinned FABL and Mathlib surfaces do
  not expose either result.
- `carlet-3-prop-12` lacks a normal form for arbitrary affine flats, the theorem that an affine-flat
  indicator has algebraic degree equal to its codimension, and the equality-case slice
  infrastructure needed to classify every minimum-weight Reed--Muller word. The pinned FABL and
  Mathlib surfaces do not supply this package.

These blockers are independent. Closing either requires adding the smallest used bridge layer and
then associating the exact source proposition; no placeholder declaration or weakened statement is
part of the frontier.

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
