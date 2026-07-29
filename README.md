# CryptBoolean: Cryptographic Boolean Functions in Lean

[![CI](https://github.com/Polarnova/CryptBoolean/actions/workflows/ci.yml/badge.svg)](https://github.com/Polarnova/CryptBoolean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/Polarnova/CryptBoolean)](https://github.com/Polarnova/CryptBoolean/releases)
[![Lean 4](https://img.shields.io/badge/Lean-4.32.0-blue)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/Verso-Blueprint-5b4b8a)](https://polarnova.github.io/CryptBoolean/)
[![License](https://img.shields.io/github/license/Polarnova/CryptBoolean)](LICENSE)

CryptBoolean formalizes cryptographic Boolean-function theory in Lean 4 and Mathlib, following
Claude Carlet and supplementary results from Cusick--Stănică. It reuses
[FABL](https://github.com/Polarnova/FABL) for Boolean Fourier analysis and algebraic normal forms.

Read the [interactive Blueprint](https://polarnova.github.io/CryptBoolean/) for the mathematical
statements, Lean declarations, references, and proof-dependency graph.

## Mathematical scope

Release `v0.6.5` covers Carlet Chapters 2--9:

- Chapters 2--3: representations, Walsh analysis, finite fields, and Reed--Muller codes.
- Chapters 4--7: cryptographic criteria, affine and quadratic classes, bent functions, and resilient
  functions.
- Chapter 8: strict avalanche and propagation criteria.
- Chapter 9: algebraic immune functions.

The only open Blueprint statements are three Chapter 5 analytic results: the Weil character-sum
bound, its nonlinearity corollary, and the reciprocal character-sum bound. All linked Lean
declarations are proved and kernel-checked.

## Using CryptBoolean

CryptBoolean uses Lean and Mathlib `v4.32.0` and pins FABL `v0.5.6`. Add it to a downstream
`lakefile.toml`:

```toml
[[require]]
name = "CryptBooleanFunction"
git = "https://github.com/Polarnova/CryptBoolean.git"
rev = "v0.6.5"
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

## Contributing

Read [`AGENTS.md`](AGENTS.md) for the source-fidelity, Mathlib and FABL reuse, proof, Blueprint, and
verification conventions.

## License

CryptBoolean is released under the Apache License 2.0. See [`LICENSE`](LICENSE).
