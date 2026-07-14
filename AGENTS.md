# CryptBoolean contributor contract

## Mission and sources of truth

CryptBoolean formalizes cryptographic Boolean-function theory in Lean 4 and Mathlib. Claude
Carlet's *Boolean Functions for Cryptography and Error Correcting Codes* is the primary statement
spine. Cusick--Stănică supplies independent results and later application-oriented extensions. FABL
is a pinned upstream dependency for Boolean Fourier analysis.

1. The source books determine mathematical scope and human-readable statements.
2. Production declarations under `CryptBoolean/**/*.lean` determine formal statements and proofs.
3. Verso sources under `blueprint-verso/CryptBooleanBlueprint/**/*.lean` associate source-facing
   statements with compiled declarations and record the reviewed mathematical dependency DAG.
4. Inventories under `inventory/` record reviewed source coverage and open statement families.

Never silently weaken a source statement, add an assumption, change its domain, or conflate two
normalizations. Record deliberate generalizations and representation bridges in the matching Verso
node and production declaration.

## Current verified surface

The Blueprint baseline is 23 proof-complete statement nodes, 114 associated Lean declarations, and
26 reviewed dependency edges.

- Chapter 2 contributes 21 nodes, 106 declarations, and 23 incoming edges. It covers the scalar
  Boolean-function domain, support and weight, balancedness, raw Walsh transforms, the scaling
  bridge to FABL, Walsh inversion, Parseval, algebraic and numerical normal forms, raw
  pseudo-Boolean Fourier operations, subspace indicators, Poisson summation, derivatives,
  autocorrelation, finite-field trace and representation, distance scaling, and affine functions.
- Chapter 3 contributes 2 nodes, 8 declarations, and 3 incoming edges. It defines `reedMuller r n` and proves
  the first-order distance lower bound.
- Open Chapter 2 families are the numerical-normal-form integrality criterion, trace-monomial degree
  formulas, affine-change and restriction laws, and spectral-support bounds.
- Open Chapter 3 families include the general-order distance theorem, equality classification,
  dimension formula, and duality.

These counts must agree with `blueprint-verso/scripts/validate_manifest.py`. Update the validator,
inventory, Verso nodes, and this baseline together whenever verified coverage changes.

## Scope

The first release targets source-faithful coverage of Carlet Chapters 2--10:

| Chapter | Subject |
|---|---|
| 2 | Representations and Fourier/Walsh transforms |
| 3 | Boolean functions and Reed--Muller coding |
| 4 | Cryptographic criteria |
| 5 | Affine, quadratic, flat-indicator, normal, and related classes |
| 6 | Bent functions |
| 7 | Resilient functions |
| 8 | Strict avalanche and propagation criteria |
| 9 | Algebraic immunity |
| 10 | Symmetric and rotation-symmetric functions |

Carlet's introductory cryptosystem discussion is motivation rather than a requirement to formalize
every cited cipher. Vectorial Boolean functions remain outside the first release unless a scalar
theorem needs a precise vectorial lemma.

Cusick--Stănică coverage is added by delta after the Carlet closure audit. Shared Fourier,
propagation, correlation-immunity, resilience, and bent results use the same canonical declarations.
Stream-cipher, block-cipher, AES, and Boolean Cayley-graph results require their own semantic layers.

## Architecture

- Production Lean lives under `CryptBoolean/` and contains pure mathematics only.
- The root module `CryptBoolean.lean` is the verified production surface. A file unreachable from
  the root is an incomplete library artifact.
- Modules follow Carlet's chapters and mathematical boundaries. Avoid generic `Core`, `Common`,
  `Utils`, or `ToMathlib` dumping grounds.
- The canonical scalar cryptographic Boolean function is `FABL.F₂Cube n → FABL.𝔽₂`.
- Sign-valued, real-valued, and finite-field views cross explicit representation bridges.
- PDF extraction, inventory maintenance, Blueprint rendering, CI, and audits remain at the
  repository perimeter.
- Add a helper only when a production theorem uses it. Extract shared logic only after genuine
  cross-module reuse appears.

## Dependency policy

- FABL is imported from Git at revision `34334a1b0c8dd806c076444a0875caf29ba5e248`.
- Search pinned FABL and Mathlib before adding a local type, definition, theorem, or proof helper.
- Local declarations must express cryptographic concepts, representation bridges, or proof lemmas
  used by a production theorem.
- Carlet's Walsh transform is an unnormalized integer sum. FABL's `vectorFourierCoeff` is a
  normalized expectation. Every reuse of FABL Fourier results must pass through the scaling theorem.
- Carlet's algebraic degree is the degree of the algebraic normal form over `𝔽₂`. FABL's Fourier
  degree is a distinct concept.
- Full FABL completion is not a project gate. Depend only on the upstream declarations required by
  the active theorem.

## Formalization loop

1. Add or refine the source-facing inventory in `inventory/`.
2. Search FABL and Mathlib for reusable declarations.
3. Add the minimal Lean signature under the relevant chapter module.
4. Record the complete reviewed statement and dependency edges in the matching Verso source.
5. Close dependency-ready leaves before opening broader theorem nodes.
6. Keep exploratory `sorry` in isolated temporary WIP files; never commit or root-import them.
7. Run the narrowest affected module build, then the root build.
8. Run forbidden-token, axiom, Blueprint, manifest, and fidelity audits before claiming closure.

Never change a target statement, representation, or dependency edge merely to make a proof pass.
When blocked, record the exact goal, searched declarations, attempted proof shapes, and the smallest
missing lemma. Do not leave speculative APIs or unrelated refactors.

## Proof and code policy

- `admit`, project-defined `axiom`, `unsafe`, and `native_decide` are forbidden.
- The production root and every completion commit contain zero `sorry`.
- Avoid global simplifier attributes and global heartbeat changes for local proof repair.
- Use Mathlib naming, documentation, formatting, imports, and canonical normal forms.
- Keep foundational proofs readable and use automation only for stable, bounded steps.
- Every production declaration belongs to an inventoried source item, an explicit representation
  bridge, or a proof dependency used by such an item.

## Blueprint contract

Each reviewed item has one complete human-readable statement, genuine compiled declarations,
fidelity metadata, and reviewed `uses` dependencies. Dependency edges describe mathematical proof
dependencies rather than Lean imports or presentation state.

Include active chapters in the Blueprint aggregate throughout development so open nodes remain
visible. A missing declaration association honestly represents unfinished work. Never attach a
placeholder declaration or weaken a statement to manufacture completion.

Generated HTML, manifests, graphs, and caches under `blueprint-verso/_out/` are build artifacts.
Edit only Lean sources and scripts.

## Build and verification flow

Run dependency setup after the first clone or an intentional toolchain change:

```bash
lake update
lake exe cache get
cd blueprint-verso
lake update
lake exe cache get
```

During proof development, build the narrowest affected module. Before a handoff, run from the
repository root:

```bash
lake build CryptBoolean
./scripts/forbidden_tokens.sh
./scripts/audit_axioms.sh
./blueprint-verso/scripts/site.sh build
```

The root build verifies production reachability. The forbidden-token scan rejects incomplete or
unsafe proof mechanisms. The axiom audit rejects `sorryAx` dependencies. The site build compiles the
Verso sources, validates declaration presence and proof status, checks the dependency graph, and
validates the manifest counts.

## Version-control boundaries

- The local Carlet PDF and Cusick--Stănică PDF directory are source references only. Never stage,
  commit, or force-add them.
- Never commit `.lake/`, temporary extraction data, generated Blueprint `_out/`, browser QA output,
  or local caches.
- Track Lean and Verso sources, toolchain files, Lake configuration and manifests, CI, scripts,
  inventories, audits, and project documentation.
- Before a release commit, run the complete verification flow, inspect ignored source material, and
  inspect the full staged file list.
- Do not commit, push, add a remote, or rewrite history unless the user explicitly requests it.
