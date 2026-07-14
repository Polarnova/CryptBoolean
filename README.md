# CryptBooleanFunction

CryptBooleanFunction is a Lean 4 and Mathlib formalization of cryptographic Boolean
functions. Its primary source is Claude Carlet's *Boolean Functions for Cryptography and Error
Correcting Codes*. Thomas W. Cusick and Pantelimon Stănică's *Cryptographic Boolean Functions and
Applications* is a secondary source for independent statements and later application-oriented
extensions.

The project is a sibling of [FABL](../FABL/README.md), not a replacement for it. FABL develops
analysis of Boolean functions from O'Donnell's book. CryptBooleanFunction reuses that analytic
foundation and develops the algebraic, coding-theoretic, and cryptographic branch: algebraic normal
forms, Reed-Muller codes, nonlinearity, correlation immunity, propagation criteria, bent functions,
resilient functions, and algebraic immunity.

## Status

The Lean package is bootstrapped with a Git-pinned FABL dependency at revision
`34334a1b0c8dd806c076444a0875caf29ba5e248`. The production root is `CryptBoolean`.
The compiled Chapter 2 foundations cover the scalar Boolean-function domain, support and weight
definitions, balancedness, the raw integer Walsh transform, and the explicit normalization bridge
to FABL's `vectorFourierCoeff`. Chapter 2's Fourier layer adds Walsh inversion for the sign view
and the Parseval identity `∑ₐ W_f(a)² = (2ⁿ)²`, both obtained by composition over FABL through the
normalization bridge. Every Boolean function has a unique algebraic
normal form (`CryptBoolean.existsUnique_anfEval`), proved through the characteristic-two Möbius
inverse `S ↦ ∑_{T⊆S} f(1_T)` and zeta-transform injectivity on the subset lattice, reusing FABL's
subset-indicator bridge.

The dependency-ready Chapter 2 surface now also includes the numerical normal form and its real
Möbius formula, the raw pseudo-Boolean Fourier transform, shift/involution/convolution/Plancherel
laws, subspace indicators and Poisson summation, derivatives and autocorrelation, Mathlib-backed
absolute trace and finite-field Lagrange representation, raw/relative Hamming-distance scaling,
and the characterization and weight of affine functions. The Blueprint records four remaining
source-facing Chapter 2 families as open: Proposition 5's integrality criterion, trace-monomial
degree formulas, the complete affine-change/restriction laws, and spectral-support bounds. Thus
the downstream interface is closed without mislabeling full source coverage as complete.

Chapter 3 has begun with `reedMuller r n` as the subspace of functions of algebraic degree at most
`r`. The first-order case of Carlet's Theorem 1 is compiled: nonzero degree-at-most-one functions
have weight at least `2^(n-1)`, hence distinct `R(1,n)` codewords have that distance lower bound.
The general-order theorem, equality classification, dimension formula, and duality remain explicit
open nodes.

Current verification commands:

```bash
lake build CryptBoolean
./scripts/forbidden_tokens.sh
./scripts/audit_axioms.sh
(cd blueprint-verso && lake build CryptBooleanBlueprint)
./blueprint-verso/scripts/site.sh
```

On pushes to `main`, the CI workflow builds the same verified HTML tree and deploys it through
GitHub Pages. The repository must use **GitHub Actions** as its Pages source; no generated site
files are committed.

The two local PDFs are source material only and must not be committed. Generated Blueprint output,
Lake build products, and temporary extraction files are ignored.

The current FABL baseline is sufficient to begin. Its Chapters 1--3 provide compiled public APIs
for the binary and sign cubes, normalized Fourier and Walsh coefficients, Fourier expansion,
Parseval and Plancherel identities, Hamming distance, balancedness, restrictions, subspaces, and
discrete derivatives. CryptBooleanFunction does not need to wait for all of FABL to be complete.

## Scope

The first release target is complete, source-faithful coverage of Carlet's Chapters 2--10:

| Chapter | Subject |
|---|---|
| 2 | Representations and Fourier/Walsh transforms |
| 3 | Boolean functions and Reed-Muller coding |
| 4 | Cryptographic criteria |
| 5 | Affine, quadratic, flat-indicator, normal, and related classes |
| 6 | Bent functions |
| 7 | Resilient functions |
| 8 | Strict avalanche and propagation criteria |
| 9 | Algebraic immunity |
| 10 | Symmetric and rotation-symmetric functions |

Carlet's introductory cryptosystem discussion supplies motivation, not an obligation to formalize
an operational model of every cipher mentioned. References to the separate vectorial-Boolean-
function chapter are outside the first release unless a scalar theorem depends on a precisely
stated vectorial lemma.

Cusick--Stănică is handled by delta, not by duplication. Its Fourier, propagation, correlation-
immune, resilient, and bent chapters map onto the same canonical declarations used for Carlet.
Independent results are added after the Carlet closure audit. Stream-cipher, block-cipher, AES, and
Boolean Cayley-graph chapters are later extensions with their own semantic prerequisites.

## Relationship to FABL

CryptBooleanFunction imports FABL for analytic infrastructure and owns only cryptographic concepts
or explicit representation bridges. In particular:

- FABL's `vectorFourierCoeff` is a normalized expectation; Carlet's Walsh transform is an
  unnormalized integer sum. Their scaling law is an early required bridge.
- FABL's `fourierDegree` and `vectorFourierDegree` are real Fourier degrees. Carlet's algebraic
  degree is the degree of the algebraic normal form over `𝔽₂`; the APIs must never identify them.
- FABL's Chapters 1--3 already suffice for the Fourier, distance, restriction, derivative, and
  subspace parts of the project.
- FABL Chapter 6 will overlap with `𝔽₂`-polynomial representation. Before either project publishes
  overlapping stable APIs, the shared ownership must be reconciled by reuse or a narrow bridge.
- FABL Chapter 8 may later improve generalized-domain and Abelian-group interfaces. It is not a
  prerequisite for scalar functions on `𝔽₂ⁿ`.
- FABL Chapters 9--10 may support a few asymptotic or moment bounds. Only those dependent nodes
  should wait; bent, resilient, propagation, and algebraic-immunity foundations should not.

No Carlet milestone has "FABL complete" as a dependency.

## Architecture

The planned production tree follows Carlet's chapters and mathematical boundaries. Stable chapter
aggregates will compose smaller proof-bearing modules; there will be no generic `Core`, `Common`,
or `Utils` dumping ground.

The canonical cryptographic Boolean function is bit-valued on the additive binary cube:

```lean
FABL.F₂Cube n → FABL.𝔽₂
```

Sign-valued and real-valued views are introduced only through explicit FABL bridges. Pure
definitions and proofs form the library. PDF extraction, inventory generation, rendering, and CI
remain at the repository edge.

See [SPEC.md](SPEC.md) for the normative design contract and [PLAN.md](PLAN.md) for the Carlet-first
dependency plan.

## Sources

- Claude Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*, 2010.
- Thomas W. Cusick and Pantelimon Stănică, *Cryptographic Boolean Functions and Applications*,
  second edition, 2009.
- Ryan O'Donnell, *Analysis of Boolean Functions*, May 2021 edition, formalized by FABL.
