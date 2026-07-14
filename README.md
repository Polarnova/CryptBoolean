# CryptBoolean: Cryptographic Boolean Functions in Lean

CryptBoolean is a Lean 4 and Mathlib formalization of cryptographic Boolean functions, guided by
Claude Carlet's *Boolean Functions for Cryptography and Error Correcting Codes*. It develops the
algebraic, spectral, coding-theoretic, and cryptographic theory as a reusable theorem library.

The project uses [FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis and supplies
explicit bridges between FABL's normalized coefficients and Carlet's raw Walsh transform.

## Status

The verified production surface currently covers selected results from Carlet Chapters 2 and 3.
Every Blueprint node has a complete mathematical statement and reviewed dependencies. Formalized
nodes are associated with compiled Lean declarations; open source theorems remain visible without
placeholder associations.

| Chapter | Subject | Statements | Formalized | Open | Lean declarations | Dependency edges |
|---|---|---:|---:|---:|---:|---:|
| 2 | Representations and Fourier/Walsh transforms | 36 | 35 | 1 | 159 | 45 |
| 3 | Boolean functions and Reed--Muller coding | 7 | 6 | 1 | 21 | 19 |
| **Total** |  | **43** | **41** | **2** | **180** | **64** |

The Chapter 2 surface includes algebraic and numerical normal forms, Walsh and pseudo-Boolean
Fourier transforms, inversion and Plancherel identities, the full raw Poisson formula, the
numerical-normal-form integrality criterion, affine invariance, restriction recovery,
spectral-support bounds, derivatives, autocorrelation, and finite-field representations. Chapter 3
defines Reed--Muller codes and proves the general distance bound, dimension and cardinality
formulas, and duality theorem.

Exactly two source statements remain open. Carlet Proposition 3 requires a finite-field coordinate
bridge identifying ANF degree with the maximum binary weight of a univariate exponent, together
with noncancellation along the relevant cyclotomic orbit. Carlet Chapter 3 Proposition 12 requires
an arbitrary affine-flat normal form, the codimension--degree theorem for affine-flat indicators,
and equality-case slice infrastructure for the minimum-weight classification.

The production library contains zero `sorry`, project-defined axioms, unsafe declarations, or
native proof shortcuts.

## Using CryptBoolean

The repository pins Lean, Mathlib, and FABL. After cloning, obtain the precompiled Mathlib cache and
build the verified library:

```bash
lake exe cache get
lake build CryptBoolean
```

The root module imports every verified production module:

```lean
import CryptBoolean
```

Source modules follow Carlet's chapters under `CryptBoolean/Carlet`. Representation bridges live
under `CryptBoolean/Bridge`.

## Book and dependency graph

The Verso Blueprint presents source-facing statements beside their Lean declarations and records
the reviewed dependency graph. Statement blocks contain only mathematics; implementation and
normalization notes are rendered separately. Build and serve it locally with:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve
```

Then open [http://localhost:8000/](http://localhost:8000/). Generated files live under
`blueprint-verso/_out/`. Pushes to `main` run the same checked build and automatically publish the
book through GitHub Pages at
[polarnova.github.io/CryptBoolean](https://polarnova.github.io/CryptBoolean/).

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the contributor contract and verification workflow.

## References and prior work

- Claude Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*, 2010.
- Thomas W. Cusick and Pantelimon Stănică, *Cryptographic Boolean Functions and Applications*,
  second edition, 2009.
- Ryan O'Donnell, *Analysis of Boolean Functions*, May 2021 edition, formalized by
  [FABL](https://github.com/Polarnova/FABL).
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  CryptBoolean.
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint), used for the source-facing book
  and dependency graph.
