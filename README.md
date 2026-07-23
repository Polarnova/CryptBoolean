# CryptBoolean: Cryptographic Boolean Functions in Lean

CryptBoolean is a Lean 4 and Mathlib formalization of cryptographic Boolean functions, guided by
Claude Carlet's *Boolean Functions for Cryptography and Error Correcting Codes*. It develops the
algebraic, spectral, coding-theoretic, and cryptographic theory as a reusable theorem library.

The project uses [FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis and its
canonical ANF, algebraic-degree, affine-function, and derivative APIs. CryptBoolean imports those
APIs directly and supplies explicit bridges between FABL's normalized coefficients and Carlet's raw
Walsh transform.

## Status

The verified production surface currently covers selected results from Carlet Chapters 2--4.
Every Blueprint node has a complete mathematical statement and reviewed dependencies. Formalized
nodes are associated with compiled Lean declarations; open source theorems remain visible without
placeholder associations.

| Chapter | Subject | Statements | Formalized | Open | Lean declarations | Dependency edges |
|---|---|---:|---:|---:|---:|---:|
| 2 | Representations and Fourier/Walsh transforms | 36 | 35 | 1 | 159 | 45 |
| 3 | Boolean functions and Reed--Muller coding | 7 | 7 | 0 | 32 | 19 |
| 4 | Cryptographic criteria | 73 | 73 | 0 | 568 | 159 |
| **Total** |  | **116** | **115** | **1** | **759** | **223** |

The Chapter 2 surface includes algebraic and numerical normal forms, Walsh and pseudo-Boolean
Fourier transforms, inversion and Plancherel identities, the full raw Poisson formula, the
numerical-normal-form integrality criterion, affine invariance, restriction recovery,
spectral-support bounds, derivatives, autocorrelation, and finite-field representations. Chapter 3
defines Reed--Muller codes and proves the general distance bound, dimension and cardinality
formulas, duality theorem, and Proposition 12's classification of minimum-weight words as affine-
flat indicators. Chapter 4 now compiles the reviewed finite theory of nonlinearity, higher-order
nonlinearity, resiliency and propagation, linear structures, algebraic immunity, autocorrelation,
maximum correlation, and the remaining complexity criteria.

One source node remains open: Carlet Proposition 3 still requires the finite-field coordinate and
cyclotomic-orbit noncancellation bridge. Chapter 4 is source-complete. Its last closures are
Rodier's sharp random-nonlinearity interval, the exact dimension-seven maximum, and the sharp
fixed-order higher-order asymptotic upper bound. The latter is exposed through separate formal
nodes for the moment ratio, dual-code weight decomposition, low-weight estimates, the exact
weight-`16` rank-seven classification and character bound, and finite Plotkin propagation.
Strict improvement over
the quadratic bound in every odd dimension above seven follows from a kernel-checked Kavut--Yücel
certificate. The balanced Maitra--Kavut--Yücel family is proved for every odd dimension at least
thirteen; a linear reindexing and complete bent extensions give `PC(1)` witnesses over the same
range; and a Proposition 12 affine-line repair gives balanced degree-`n-1` witnesses for every odd
dimension at least fifteen.

Two source-fidelity distinctions are explicit in the formalized Chapter 4 surface. Carlet's Reed--
Muller coset-distance formula needs pairwise distinct cosets (and, for the two-coset corollary, a
non-affine representative). Carlet calls the even-output tuple count `k`th nonhomomorphicity,
whereas reference [357] calls that same count homomorphicity and uses nonhomomorphicity for its
odd-output complement.

The production library contains zero `sorry`, project-defined axioms, unsafe declarations, or
native proof shortcuts.

## Using CryptBoolean

The repository pins Lean and Mathlib `v4.32.0` and the latest stable FABL release, currently
`v0.5.6`. After cloning, fetch and verify the precompiled dependencies, then build CryptBoolean:

```bash
lake exe cache get
./.github/scripts/require_latest_fabl_release.sh
lake build CryptBoolean
```

The release check downloads FABL and ProbabilityApproximation archives on Linux x86-64 and macOS
arm64 and fails instead of compiling their source when a matching verified asset is unavailable.
An hourly workflow, also callable by a FABL release dispatch, opens an exact-pin upgrade pull
request whenever FABL publishes a newer stable release. It updates the Lean toolchain and both Lake
manifests, runs the complete CryptBoolean and Blueprint build in GitHub Actions, and merges only a
green dependency update.

The root module imports every verified production module:

```lean
import CryptBoolean
```

Source modules follow Carlet's chapters under `CryptBoolean/Carlet`. Representation bridges live
under `CryptBoolean/Bridge`.

## Book and dependency graph

The Verso Blueprint presents source-facing statements beside their Lean declarations and records
the reviewed dependency graph. Statement blocks contain only mathematics; implementation and
normalization notes are rendered separately. GitHub Actions performs the full publication build.
For a local preview after the root library is current:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve dev
```

Then open [http://localhost:8000/](http://localhost:8000/). Generated files live under
`blueprint-verso/_out/`. Pushes to `main` run the same checked build and automatically publish the
book through GitHub Pages at
[polarnova.github.io/CryptBoolean](https://polarnova.github.io/CryptBoolean/).
The `dev` profile retains fidelity metadata for review; public CI uses the default `release`
profile and omits those tags from the reading view.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the contributor contract and verification workflow.

## References and prior work

The reader-facing Blueprint generates a sorted References page from the single
[`references.bib`](blueprint-verso/CryptBooleanBlueprint/references.bib) database. Source notes use
the same citation keys, so papers, stable URLs, and DOIs are maintained in one place.

- Claude Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*, 2010.
- Thomas W. Cusick and Pantelimon Stănică, *Cryptographic Boolean Functions and Applications*,
  second edition, 2017.
- Ryan O'Donnell, *Analysis of Boolean Functions*, May 2021 edition, formalized by
  [FABL](https://github.com/Polarnova/FABL).
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  CryptBoolean.
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint), used for the source-facing book
  and dependency graph.
