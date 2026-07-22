# CryptBooleanFunction specification

## Mission

CryptBooleanFunction formalizes the scalar theory of cryptographic Boolean functions in Lean 4.
Carlet determines the primary mathematical scope and statement fidelity. FABL supplies reusable
analysis on the Boolean cube. Cusick--Stănică supplies independent results and a second source for
cross-checking shared material.

`CryptBooleanFunction` is the project and repository name. Production Lean uses the concise root
module and namespace `CryptBoolean`.

The project optimizes for a small, compositional theorem API. A declaration is introduced only for
a source item, a representation bridge required by a source item, or a proof lemma used by a
production theorem.

## Sources of truth

The sources are ordered as follows:

1. Carlet determines the first-release mathematical scope and complete human-readable statements.
2. Production declarations under `CryptBoolean/**/*.lean` determine formal statements and proofs.
3. Verso Blueprint sources associate source statements with compiled declarations and record the
   reviewed mathematical dependency DAG.
4. Inventories under `.agents/inventory/` record reviewed coverage and open statement families;
   `.agents/audit/` records the reviewed dependency and fidelity crosswalks.
5. Cusick--Stănică determines independent post-Carlet additions and may expose a discrepancy that
   requires a documented source comparison.

The local PDFs are normative references but are never committed. Generated text, images, HTML,
PDFs, manifests, graphs, and caches are not sources of truth.

## Current verified baseline

The reviewed Blueprint contains 43 source-facing statements, of which 41 are associated with 180
proved Lean declarations and 2 remain visibly open, connected by 64 mathematical dependency edges.
Chapter 2 contributes 36 statements (35 formalized and 1 open), 159 declarations, and 45 incoming
edges. Chapter 3 contributes 7 statements (6 formalized and 1 open), 21 declarations, and 19
incoming edges.

The completed Chapter 2 frontier includes Proposition 5's numerical-normal-form integrality
criterion, the full raw Poisson formula, affine invariance, restriction recovery, and the
spectral-support bounds. The completed Chapter 3 frontier includes the general Reed--Muller distance
theorem, dimension and cardinality formulas, and duality.

The only open Chapter 2 item is Carlet Proposition 3. Its smallest missing layer is a finite-field
coordinate theorem identifying ANF degree with the maximum binary weight in the univariate support,
together with noncancellation along the cyclotomic orbit of a trace monomial. The only open Chapter
3 item is Carlet Proposition 12. It requires arbitrary affine-flat normal form, the
codimension--degree theorem for affine-flat indicators, and equality-case slice infrastructure.

A bare theorem number is not a stable identifier because numbering can restart or be reused.
Inventory identifiers include source, chapter or section, item kind, and printed number, for
example `carlet-6-prop-19` or `cusick-5-thm-18`. Unnumbered equations and claims receive a location-
based identifier and an exact source citation.

## Coverage boundary

The Carlet target includes every definition, lemma, proposition, theorem, corollary, named
construction, and unnumbered support result required by Chapters 2--10. Qualitative descriptions of
attacks or ciphers become prose context unless the source states a mathematical claim with enough
semantics to formalize faithfully.

The first release excludes:

- a general implementation model for block or stream ciphers;
- vectorial Boolean functions beyond narrow scalar dependencies;
- the separate vectorial chapter referenced by Carlet but absent from the supplied PDF;
- security claims quantified over efficient adversaries without an explicit computation model;
- duplicate declarations for a result already owned by FABL or an earlier Carlet item.

Cusick--Stănică Chapters 2--5 are a source-comparison layer over the Carlet API. Chapters 6--8 are
separate extension campaigns after the Carlet release because they introduce pseudorandom
generators, LFSRs, concrete ciphers, AES, and graph theory.

## Pure architecture

Production Lean is the pure controller layer. It contains finite algebraic structures, total
definitions, and proofs. It performs no file, terminal, network, rendering, or logging effects.

The imperative perimeter has two disjoint responsibilities:

- perception: extract PDF text, locate source items, and produce review inputs;
- action: build Lean, validate the Blueprint, render artifacts, run CI, and publish a checked Pages
  artifact from `main`.

The perimeter may report failures. Production mathematical functions do not throw or return
sentinel values. Partial mathematical notions use a proposition, subtype, `Option`, or an explicit
result type whose cases are exhaustive.

## Physical module structure

The production tree is chapter-aligned:

```text
CryptBoolean/
  Bridge/
    FABL.lean
  Carlet/
    Chapter02/
    Chapter03/
    Chapter04/
    Chapter05/
    Chapter06/
    Chapter07/
    Chapter08/
    Chapter09/
    Chapter10/
  Cusick/
```

Each chapter exposes a stable aggregate import. A large chapter is split only at a mathematical or
representation boundary. `Bridge/FABL.lean` contains only cross-representation and normalization
laws used by production Carlet modules. It must not become a second Boolean-function library.

The root module imports every completed production module. A file unreachable from the root is not
part of the verified library.

## Canonical representations

### Boolean functions

The canonical cryptographic Boolean function is

```lean
FABL.F₂Cube n → FABL.𝔽₂
```

This matches Carlet's Boolean logic, addition, algebraic normal form, derivatives, and affine
transformations. The project reuses `FABL.𝔽₂`, `FABL.F₂Cube`, `FABL.f₂DotProduct`, and the explicit
binary/sign cube equivalence.

The following are views, not alternative global definitions:

- pseudo-Boolean view: `FABL.F₂Cube n → ℝ`;
- sign encoding: `x ↦ (-1)^(f x)` through FABL's existing encoding;
- truth table: a finite vector or function enumeration derived from the canonical function;
- support: the finite set of inputs on which the value is one.

### Walsh normalization

Carlet's Walsh transform is an integer-valued unnormalized sum. Its primary API therefore retains
integrality. FABL's vector Fourier coefficient is normalized over the same cube. The bridge must
prove, with the project's chosen sign convention,

```text
CarletWalsh(f, a) = 2^n * FABL.vectorFourierCoeff(sign(f), a).
```

Every reuse of FABL Fourier theorems passes through this law. The project must not silently rename a
normalized coefficient as a Walsh value.

### Algebraic normal form

Algebraic normal form is represented by coefficients indexed by finite coordinate subsets, with
coefficients in `𝔽₂`. Evaluation is the finite sum of square-free monomials. The first public API
must include existence, uniqueness, evaluation, support, and algebraic degree.

Algebraic degree and FABL's real Fourier degree remain distinct types of information with distinct
names. Any inequality between them is a theorem, not a definitional equality.

Univariate representation over `𝔽₂ⁿ`, trace representations, and normal numerical form are separate
adapters added only when a Carlet statement needs them. They must reuse Mathlib finite-field and
polynomial infrastructure rather than encode finite fields as tables.

### Distances and criteria

Hamming weight and raw Hamming distance are natural numbers. Relative distance reuses FABL's
normalized distance only through an explicit scaling theorem.

Nonlinearity is defined primarily as minimum Hamming distance to the affine functions. Its maximum-
Walsh-magnitude formula is proved from that definition.

Balancedness, correlation immunity, resiliency, strict avalanche, propagation criteria, linear
structures, bentness, plateauedness, normality, and algebraic immunity are total predicates over
their parameters. Maximum orders or minima over finite families use finite extrema with explicit
empty-family behavior where the source permits an empty case.

## Required foundational bridges

The first dependency layer must prove and then reuse:

1. bit-function to sign-function evaluation;
2. raw Walsh sum to normalized FABL vector Fourier coefficient;
3. raw and relative Hamming distance scaling;
4. support cardinality to Hamming weight;
5. weight to the Walsh value at zero;
6. balancedness to vanishing zero-frequency Walsh value;
7. affine characters to FABL's vector Walsh characters;
8. binary derivatives to FABL sign-cube restrictions or derivatives where their statements agree.

These are bridges between domains, not duplicate proof stacks.

## FABL dependency policy

The Lean package pins FABL at release `v0.5.6`. Repository documentation and CI use the Git
dependency and its verified Lake release archive, never a developer's local absolute path.

Before adding a declaration, contributors search the pinned FABL public surface and pinned Mathlib.
A stronger existing theorem is specialized or bridged. A new local declaration is permitted only
for a genuine cryptographic concept or a demonstrated gap.

Future FABL chapters create targeted convergence gates:

| FABL area | CryptBooleanFunction policy |
|---|---|
| Chapters 1--3 | Required initial dependency; already sufficient to start |
| Chapter 6 `𝔽₂` polynomials | Reconcile ANF ownership before stable overlapping APIs are released |
| Chapter 8 generalized domains | Reuse when generalized Abelian or product-domain results are needed |
| Chapters 9--10 hypercontractivity | Wait only for nodes whose proofs genuinely require these bounds |
| Chapter 11 Gaussian/invariance theory | No first-release dependency identified |

Full FABL completion is not a project gate.

## Coding-theory boundary

Carlet Chapter 3 requires Reed-Muller codes and their distance interpretation. Mathlib's Hamming
distance is reused. A minimal Reed-Muller code is introduced as the finite family or subspace of
Boolean functions with bounded algebraic degree. A general coding-theory framework is added only if
two distinct production chapters require the same abstraction.

Kerdock codes and later constructions may need a richer code API. That is a downstream extraction,
not a reason to pre-build an unused hierarchy.

## Statement and proof workflow

1. Inventory the complete Carlet Chapters 2--10 statement set before claiming chapter coverage.
2. Record full source-facing statements and reviewed dependency edges in Verso.
3. Classify each item as direct FABL reuse, direct Mathlib reuse, specialization, representation
   bridge, or genuine local theorem.
4. Formalize signatures without changing domains, hypotheses, normalization, or quantifiers.
5. Close dependency-ready leaves and run the narrowest module build.
6. Close a chapter only after statement-fidelity, root-build, forbidden-token, Blueprint, and
   rendered-artifact checks pass.

Production and completion branches contain no `sorry`, `admit`, project-defined `axiom`, `unsafe`,
or `native_decide`. A missing declaration association is the honest representation of an unfinished
Blueprint node. No placeholder declaration may manufacture completion.

### Blueprint statement contract

Every reviewed item has one complete human-readable mathematical statement. The statement begins
with its source result name or an explicit project-bridge label and gives the domains, hypotheses,
quantifiers, and conclusion needed to read it independently of the implementation.

A statement block never contains repository links, library provenance, implementation summaries,
proof narration, or completion status. Direct FABL or Mathlib reuse, representation choices,
specialization or generalization boundaries, and proof-engineering context belong in metadata or a
separate `Formalization note`. Formalized nodes associate genuine compiled declarations; open nodes
remain visible without a declaration association. The site build runs
`blueprint-verso/scripts/check_statement_style.py` to enforce this boundary.

## Cusick--Stănică integration

After Carlet is closed, build a source crosswalk:

| Cusick--Stănică area | Canonical destination |
|---|---|
| Chapter 2 Fourier analysis | Carlet Chapters 2--4 bridge and Fourier API |
| Chapter 3 avalanche and propagation | Carlet Chapters 4 and 8 |
| Chapter 4 correlation immunity and resiliency | Carlet Chapters 4 and 7 |
| Chapter 5 bent functions | Carlet Chapter 6 |
| Chapter 6 stream ciphers | Separate operational and complexity extension |
| Chapter 7 block ciphers and AES | Separate finite-field and cipher-semantics extension |
| Chapter 8 Boolean Cayley graphs | Graph-theoretic extension reusing the canonical Walsh API |

Shared statements receive additional source metadata, not duplicate theorem names.

## Completion criteria

The Carlet milestone is complete only when:

- every in-scope item from Chapters 2--10 has a full reviewed source statement;
- every item is linked to real compiled declarations;
- all dependency edges are mathematically reviewed;
- all representation and normalization differences are explicit;
- the root build, `./.github/scripts/forbidden_tokens.sh`, and
  `./.github/scripts/audit_axioms.sh` pass;
- the Blueprint manifest and graph pass strict validation;
- generated HTML and PDF artifacts pass visual review;
- the PDFs and generated artifacts remain untracked.
