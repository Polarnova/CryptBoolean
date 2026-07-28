# CryptBoolean contributor contract

## Required agent reading

Before planning, formalizing, or reviewing the library, read `.agents/SPEC.md` and
`.agents/PLAN.md`. Review `.agents/inventory/` for source coverage and open statement families.
Consult `.agents/audit/dependency-dag.md` for the reviewed proof structure and
`.agents/audit/fidelity.md` for statement-to-declaration fidelity. These files are internal working
contracts; public project documentation is written for readers of the mathematics.

## Mission and sources of truth

CryptBoolean formalizes cryptographic Boolean-function theory in Lean 4 and Mathlib. Claude
Carlet's *Boolean Functions for Cryptography and Error Correcting Codes* is the primary statement
spine. Cusick--Stănică supplies independent results and later application-oriented extensions. FABL
is a pinned upstream dependency for Boolean Fourier analysis.

1. The source books determine mathematical scope and human-readable statements.
2. Production declarations under `CryptBoolean/**/*.lean` determine formal statements and proofs.
3. Verso sources under `blueprint-verso/CryptBooleanBlueprint/**/*.lean` associate source-facing
   statements with compiled declarations and record the reviewed mathematical dependency DAG.
4. Inventories under `.agents/inventory/` record reviewed source coverage and open statement
   families.

Never silently weaken a source statement, add an assumption, change its domain, or conflate two
normalizations. Record deliberate generalizations and cross-representation identities in the
matching Verso entry and production declaration.

## Current verified surface

The Blueprint baseline is 209 source-facing statement nodes: 206 formalized nodes associated with
1338 proved Lean declarations and 3 visibly open nodes, connected by 467 reviewed dependency
edges.

- Chapter 2 contributes 41 formalized nodes, 174 declarations, and 56 incoming
  edges. It covers the scalar
  Boolean-function domain, support and weight, balancedness, raw Walsh transforms, the scaling
  identity for FABL coefficients, Walsh inversion, Parseval, algebraic and numerical normal forms, raw
  pseudo-Boolean Fourier operations, the full raw Poisson formula, derivatives, autocorrelation,
  finite-field trace and representation, distance scaling, affine invariance, restriction recovery,
  spectral-support bounds, the NNF Fourier formula, restriction-square identities, Walsh
  divisibility, the coordinate/univariate binary-degree formula, trace-monomial degree, and
  trace-pairing coordinates.
- Chapter 3 contributes 7 formalized nodes, 32 declarations, and 19 incoming edges. It defines
  `reedMuller r n` and proves the affine-weight theorem, general-order distance theorem,
  Proposition 12's minimum-weight affine-flat classification, dimension and cardinality formulas,
  and duality.
- Chapter 4 contributes 73 formalized nodes, 568 declarations, and 159 incoming edges. Its compiled
  surface covers the reviewed finite theory of nonlinearity, higher-order nonlinearity, resiliency
  and propagation, linear structures, algebraic immunity, autocorrelation, maximum correlation,
  and related complexity criteria, including the sharp random-nonlinearity interval, the exact
  dimension-seven maximum, and the sharp fixed-order higher-order asymptotic upper bound.
- Chapter 5 contributes 31 nodes (28 formalized and 3 open), 203 declarations, and 70 incoming
  edges. Its statements cover
  affine spectra, quadratic polar forms, weights and affine normal forms, the exact quadratic
  weight and nonlinearity value sets, quadraticization Walsh lifts, affine-flat indicator spectra
  and nonlinearity, the full restriction bound and its equality case, exact random nonnormality,
  covering-sequence consequences, quadratic trace representation, and the conditional
  character-sum/nonlinearity reduction.
- Chapter 6 contributes 57 formalized nodes, 361 declarations, and 163 incoming edges. It covers
  bentness, duality, algebraic-degree bounds and Relation (47), primary and secondary
  constructions, decompositions and counting, NNF, geometric and second-order characterizations,
  hyper-bent functions, partially bent and plateaued superclasses, normal extensions, and the
  Kerdock field construction and parameters. The proof of Relation (47) includes the reusable
  McEliece--Ax character-sum divisibility theorem.
- Chapter 2 has no open source node. Its binary-degree formula and trace-pairing coordinates,
  together with cyclotomic-orbit noncancellation, close Carlet Proposition 3 on trace-monomial
  algebraic degree.
- Chapter 4 has no open source node. Its higher-order closure composes the moment-ratio reduction,
  dual-code weight decomposition, exact weight-`16` rank-seven classification, character-sum
  estimate, and finite Plotkin induction; these remain separate formalized nodes so that the proof
  structure is visible in the Blueprint.
- Chapter 6 has no open source node. Its finite proofs reuse the canonical FABL Fourier, ANF,
  algebraic-degree, affine, and derivative APIs together with the preceding Carlet Walsh,
  Reed--Muller, nonlinearity, quadratic, trace, restriction, and normality layers.
- The three open Chapter 5 nodes are the analytic Weil character-sum bound, its nonlinearity
  corollary, and the reciprocal character-sum bound.
- Carlet's Reed--Muller coset-distance equality is formalized with the necessary pairwise-distinct-
  coset hypothesis; the two-coset corollary assumes a non-affine representative. The formalized
  `k`th nonhomomorphicity count follows Carlet's even-output naming while recording reference
  [357]'s opposite convention.

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

Carlet's introductory cryptosystem discussion supplies motivation; formalizing every cited cipher
is outside the requirement. Vectorial Boolean functions remain outside the first release unless a scalar
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
- Sign-valued, real-valued, and finite-field views are related by explicit representation theorems.
- PDF extraction, inventory maintenance, Blueprint rendering, CI, and internal audits remain at the
  repository perimeter. Agent-facing specifications, plans, and audit records live under `.agents/`.
- Add a helper only when a production theorem uses it. Extract shared logic only after genuine
  cross-module reuse appears.

## Dependency policy

- FABL is imported from the exact release tag `v0.5.6`; CI requires it to match FABL's latest stable
  GitHub release and verifies the downloaded archive before compiling CryptBoolean.
- The hourly FABL updater (and its release-dispatch entry point) changes the exact pin through a
  pull request, resolves both manifests, and merges only after the complete cloud CI succeeds.
- Search pinned FABL and Mathlib before adding a local type, definition, theorem, or proof helper.
- Pinned FABL `v0.5.6` canonically owns the ANF, algebraic-degree, affine-function, and derivative
  APIs used by CryptBoolean. Import them directly and add only source-facing or cross-representation
  theorems required by Carlet statements.
- Local declarations must express cryptographic concepts, representation or scaling laws, or proof lemmas
  used by a production theorem.
- Carlet's Walsh transform is an unnormalized integer sum. FABL's `vectorFourierCoeff` is a
  normalized expectation. Every reuse of FABL Fourier results must pass through the scaling theorem.
- Carlet's algebraic degree is the degree of the algebraic normal form over `𝔽₂`. FABL's Fourier
  degree is a distinct concept.
- Full FABL completion is not a project gate. Depend only on the upstream declarations required by
  the active theorem.

## Formalization loop

1. Add or refine the source-facing inventory in `.agents/inventory/`.
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
  or scaling theorem, or a proof dependency used by such an item.

## Blueprint contract

Each reviewed item has one complete human-readable statement, genuine compiled declarations,
fidelity metadata, and reviewed `uses` dependencies. Dependency edges describe mathematical proof
dependencies; Lean imports and presentation state are excluded.

Every statement block begins with its source result name or a descriptive mathematical title and
states the mathematical domains, hypotheses, quantifiers, and conclusion. Do not put repository
links, implementation provenance, library reuse, proof narration, or completion status inside a
statement block. Reader prose following a block is retained only when it adds mathematical content,
such as a proof idea, a necessary domain convention, or a source correction. Encode fidelity
distinctions in tags and internal audits.

Public mathematical prose uses standard terminology from the source or the literature. Do not coin
compound names from implementation structure. In particular, public theorem titles and exposition
do not use `bridge`, `project bridge`, `schema`, `pipeline`, `interface`, `node`, `compiled`, or
`associated` as substitutes for a mathematical relation. Name the actual relation: scaling
identity, coordinate representation, equivalence, reduction, specialization, or corollary. Use
negation and contrast only when they change the mathematical claim, state a necessary hypothesis,
or correct the source; otherwise write the positive statement directly.

The public Blueprint omits Carlet's introductory Chapter 1 and therefore numbers Carlet Chapters
2--10 as reader Chapters 1--9. Reader headings have only chapter and section levels: Verso generates
the numbers `x` and `x.y`, while heading text contains no written numeric prefix. Source subsections
are grouped into clear reader sections in mathematical order. Internal module names, statement
identifiers, inventories, tags, and source citations retain Carlet's original numbers. Production
Lean modules may follow mathematical dependency boundaries. Run
`blueprint-verso/scripts/check_statement_style.py` through the site build to enforce the public
language and heading-depth rules.

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
./.github/scripts/require_latest_fabl_release.sh
cd blueprint-verso
lake update
lake exe cache get
```

Local verification is deliberately lightweight. A contributor may run text audits, manifest
validators, and a known-small affected Lean module. Never run the root library build, the complete
Verso build, or a site/publication build on the development machine: these workloads have repeatedly
exhausted local memory and made the machine unresponsive. Push the reviewed changes and let GitHub
Actions run the complete verification flow:

```bash
./.github/scripts/forbidden_tokens.sh
python3 ./blueprint-verso/scripts/check_statement_style.py
```

In GitHub Actions, the root build verifies production reachability. The forbidden-token scan rejects
incomplete or unsafe proof mechanisms. The axiom audit rejects `sorryAx` dependencies. The
`site.sh build release`
is the default publication build: it removes fidelity tags from reader-facing HTML while retaining
them in the validated manifest. `site.sh build dev` and `site.sh serve dev` retain those tags for
formalization review. The site build compiles the Verso sources, validates declaration presence and
proof status, checks the dependency graph, and validates the manifest counts. Pushes to `main` run
these gates before the checked Blueprint artifact is deployed automatically to GitHub Pages.

The Blueprint package shares the root `.lake/packages` directory and checks the completed
CryptBoolean build with `lake --no-build`; it never recompiles the production library. Full root,
Blueprint, and publication builds run only in GitHub Actions. GitHub caches the production and
Blueprint build artifacts by source hash. Local proof work uses the FABL release archive and, only
when demonstrably small, the narrowest relevant CryptBoolean module build.

## Version-control boundaries

- The local Carlet PDF and Cusick--Stănică PDF directory are source references only. Never stage,
  commit, or force-add them.
- Never commit `.lake/`, temporary extraction data, generated Blueprint `_out/`, browser QA output,
  or local caches.
- Track Lean and Verso sources, toolchain files, Lake configuration and manifests, CI, scripts,
  inventories, audits, and project documentation.
- Before a release commit, run the lightweight local audits, inspect ignored source material and the
  full staged file list, then require the complete GitHub Actions verification flow to pass before
  publishing or moving a release tag.
- Do not commit, push, add a remote, or rewrite history unless the user explicitly requests it.
