# CryptBoolean: Cryptographic Boolean Functions in Lean

CryptBoolean is a Lean 4 and Mathlib formalization of cryptographic Boolean functions, guided by
Claude Carlet's *Boolean Functions for Cryptography and Error Correcting Codes*. It develops the
algebraic, spectral, coding-theoretic, and cryptographic theory as a reusable theorem library.

The project uses [FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis and supplies
explicit bridges between FABL's normalized coefficients and Carlet's raw Walsh transform.

## Status

The verified production surface currently covers selected results from Carlet Chapters 2 and 3.
Every entry in the table has a complete Blueprint statement, compiled Lean declarations, and
reviewed mathematical dependencies.

| Chapter | Subject | Verified statements | Lean declarations | Dependency edges |
|---|---|---:|---:|---:|
| 2 | Representations and Fourier/Walsh transforms | 21 | 106 | 23 |
| 3 | Boolean functions and Reed--Muller coding | 2 | 8 | 3 |
| **Total** |  | **23** | **114** | **26** |

The Chapter 2 surface includes algebraic and numerical normal forms, Walsh and pseudo-Boolean
Fourier transforms, inversion and Plancherel identities, subspace indicators, Poisson summation,
derivatives, autocorrelation, finite-field trace and univariate representation, Hamming distance,
and affine functions. Chapter 3 begins the Reed--Muller development with the first-order distance
bound.

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
the reviewed dependency graph. Build and serve it locally with:

```bash
cd blueprint-verso
lake exe cache get
./scripts/site.sh serve
```

Then open [http://localhost:8000/](http://localhost:8000/). Generated files live under
`blueprint-verso/_out/`.

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the source-inventory, dependency, proof, Blueprint, and verification
contracts. [`SPEC.md`](SPEC.md) defines the mathematical architecture and representation bridges.
[`PLAN.md`](PLAN.md) records the Carlet-first coverage plan.

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
