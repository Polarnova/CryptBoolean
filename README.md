# CryptBoolean: Cryptographic Boolean Functions in Lean

[![CI](https://github.com/Polarnova/CryptBoolean/actions/workflows/ci.yml/badge.svg)](https://github.com/Polarnova/CryptBoolean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/Polarnova/CryptBoolean)](https://github.com/Polarnova/CryptBoolean/releases)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.0-blue)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/Verso-Blueprint-5b4b8a)](https://polarnova.github.io/CryptBoolean/)
[![License](https://img.shields.io/github/license/Polarnova/CryptBoolean)](LICENSE)

CryptBoolean is a Lean 4 and Mathlib library for the theory of cryptographic Boolean functions. Its
main source is Claude Carlet's *Boolean Functions for Cryptography and Error Correcting Codes*,
with supplementary results from Cusick--Stănică. The library uses
[FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis, algebraic normal forms,
algebraic degree, affine functions, and derivatives.

Read the [interactive Blueprint](https://polarnova.github.io/CryptBoolean/) for the mathematical
statements, Lean declarations, references, and proof-dependency graph.

## Mathematical scope

The current library covers Carlet Chapters 2--5:

- **Representations and transforms:** support and weight, algebraic and numerical normal forms,
  Walsh and pseudo-Boolean Fourier transforms, inversion, Parseval and Poisson formulas,
  derivatives, autocorrelation, restrictions, affine invariance, and finite-field representations.
- **Reed--Muller codes:** minimum distance, dimension, cardinality, duality, and Proposition 12's
  classification of minimum-weight words as indicators of affine flats.
- **Cryptographic criteria:** nonlinearity and higher-order nonlinearity, correlation immunity,
  resiliency, propagation criteria, linear structures, algebraic immunity, autocorrelation
  indicators, and maximum correlation. This includes the exact seven-variable maximum and sharp
  fixed-order asymptotic bounds for higher-order nonlinearity.
- **Function classes:** affine and quadratic spectra, quadratic trace representations,
  affine-flat indicators, restriction nonlinearity, normality, covering sequences, and
  trace-character reductions for finite-field character-sum bounds.

Chapters 2--4 are source-complete. Chapter 2 includes the exact univariate binary-degree bridge,
Carlet Proposition 3 on trace-monomial degree, and the trace-pairing bridge. Chapter 5 has three
visible analytic open statements: the Weil character-sum bound, its nonlinearity corollary, and the
reciprocal character-sum bound. Every associated Lean declaration is proved and kernel-checked.

Carlet's Walsh transform is an unnormalized integer sum, whereas FABL uses normalized Fourier
coefficients. CryptBoolean provides explicit scaling theorems between these conventions. Its
canonical scalar Boolean functions have type `FABL.F₂Cube n → FABL.𝔽₂`.

## Using CryptBoolean

Release `v0.4.0` uses Lean and Mathlib `v4.32.0` and pins FABL `v0.5.6`. Add the package to a
downstream `lakefile.toml`:

```toml
[[require]]
name = "CryptBooleanFunction"
git = "https://github.com/Polarnova/CryptBoolean.git"
rev = "v0.4.0"
```

On Linux x86-64 and macOS arm64, obtain the verified release archive with:

```bash
lake update
lake exe cache get
lake build @CryptBooleanFunction:release
```

Import the complete public library with:

```lean
import CryptBoolean
```

For source development, clone the repository, fetch the dependency archives, and build the root
module:

```bash
git clone https://github.com/Polarnova/CryptBoolean.git
cd CryptBoolean
lake update
lake exe cache get
./.github/scripts/require_latest_fabl_release.sh
lake build CryptBoolean
```

Production modules follow Carlet's chapters and mathematical representation boundaries under
`CryptBoolean/Carlet`.

## Blueprint

The [Verso Blueprint](https://github.com/leanprover/verso-blueprint) is the reader-facing
mathematical text. Its References page is generated from
[`references.bib`](blueprint-verso/CryptBooleanBlueprint/references.bib).

After the root library is current, preview the development edition locally with:

```bash
cd blueprint-verso
lake update
lake exe cache get
./scripts/site.sh serve dev
```

Then open [http://localhost:8000/](http://localhost:8000/).

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the source-fidelity, Mathlib and FABL reuse, proof, Blueprint, and
verification conventions.

## References

- Claude Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*, 2010.
- Thomas W. Cusick and Pantelimon Stănică, *Cryptographic Boolean Functions and Applications*,
  second edition, 2017.
- Ryan O'Donnell, [*Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386), May 2021
  edition, formalized by [FABL](https://github.com/Polarnova/FABL).
- [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical foundation used by
  CryptBoolean.
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint), used for the mathematical text
  and dependency graph.

## License

CryptBoolean is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
