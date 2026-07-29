# CryptBooleanFunction specification

## Mission

CryptBooleanFunction formalizes the scalar theory of cryptographic Boolean functions in Lean 4.
Carlet determines the primary mathematical scope and statement fidelity. FABL supplies reusable
analysis on the Boolean cube. Cusick--Stănică supplies independent results and a second source for
cross-checking shared material.

`CryptBooleanFunction` is the project and repository name. Production Lean uses the concise root
module and namespace `CryptBoolean`.

The project optimizes for a small, compositional theorem API. A declaration is introduced only for
a source item, a cross-representation law required by a source item, or a proof lemma used by a
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

The reviewed Blueprint contains 261 source-facing statements, of which 258 are associated with
1642 proved Lean declarations and 3 remain visibly open, connected by 607 mathematical dependency
edges. Chapter 2 contributes 41 formalized statements, 174 declarations, and 56
incoming edges. Chapter 3 contributes 7 formalized statements, 32 declarations, and 19 incoming
edges. Chapter 4 contributes 73 formalized statements, 568 declarations, and 159 incoming edges.
Chapter 5 contributes 31 statements (28 formalized and 3 open), 203 declarations, and 70 incoming
edges. Chapter 6 contributes 70 formalized statements, 441 declarations, and 189 incoming edges.
Chapter 7 contributes 39 formalized statements, 224 declarations, and 114 incoming edges.

The completed Chapter 2 frontier includes Proposition 5's numerical-normal-form integrality
criterion, the full raw Poisson formula, affine invariance, restriction recovery, the
spectral-support bounds, Relation (30)'s NNF Fourier formula, Proposition 9's restriction-square
identity, Proposition 11's Walsh-divisibility degree bound, the coordinate/univariate
binary-degree formula, Proposition 3 on trace monomials, and trace-pairing coordinates. The
completed Chapter 3 frontier includes
the general Reed--Muller distance theorem, Proposition 12's minimum-weight affine-flat
classification, dimension and cardinality formulas, and duality.

The Chapter 4 inventory is source-reviewed and Blueprint-synchronized. Its 73 formalized nodes
cover the reviewed finite theory of nonlinearity, higher-order nonlinearity, resiliency and
propagation, linear structures, algebraic immunity, autocorrelation, maximum correlation, and the
remaining complexity criteria. Rodier's sharp random-nonlinearity interval, the exact
dimension-seven maximum, and the sharp fixed-order higher-order asymptotic upper bound are now
closed as independent source-facing nodes. The higher-order proof exposes its moment-ratio,
dual-code, low-weight, weight-`16` rank-seven classification, character-sum, and finite Plotkin
components as separate mathematical statements in the final asymptotic argument.

The Chapter 5 inventory is source-reviewed and Blueprint-synchronized. Its compiled nodes cover
affine Walsh spectra, quadratic polar forms, kernel sums, exact weight and nonlinearity value sets,
even rank, the complete quadratic affine normal form, quadraticization, affine-flat indicator
spectra, restriction nonlinearity including the equality case, fixed-dimension normality, the exact
random-nonnormality limit, covering-sequence definitions and consequences, and the conditional
trace-character/nonlinearity reduction. The quadratic trace representation is closed for both odd
and even dimensions. The three open nodes preserve the complete analytic source statements for the
Weil character-sum bound, its nonlinearity corollary, and the reciprocal character-sum bound.

The Chapter 6 inventory is source-reviewed and Blueprint-synchronized. Its 70 formalized nodes
cover the spectral, derivative, Hadamard-matrix, difference-set, and strongly regular Cayley-graph characterizations of bentness,
duality, the balanced-hyperplane and codimension-two decomposition theorems, the Rothaus and
McEliece--Ax algebraic-degree bounds, primary and secondary constructions including Classes D₀,
D, and C and the two promoted Theorem 10 specializations, decompositions, the exact `PS_ap`
count, NNF,
geometric and second-order characterizations, hyper-bent functions, partially bent
and plateaued superclasses, normal extensions, and the explicit finite-field Kerdock family and
code parameters. The proofs reuse FABL's canonical Fourier, ANF, degree, affine, and derivative
interfaces and the Chapter 2--5 Walsh, Reed--Muller, nonlinearity, quadratic, trace, restriction,
and normality layers.

The Chapter 7 inventory is source-reviewed and Blueprint-synchronized. Its 39 formalized nodes
cover Siegenthaler degree bounds, Walsh and weight divisibility, degree-sensitive and
entropy-refined nonlinearity bounds, maximum correlation, the sharp resiliency--propagation
tradeoff, primary and secondary constructions, exact degree and nonlinearity formulas, and finite
counting bounds. The proofs reuse the established Chapter 2--6 representations and the canonical
FABL algebraic-degree, affine, derivative, and Fourier APIs.

Chapter 2 has no open node: the finite-field coordinate theorem identifies ANF degree with the
maximum binary weight in the univariate support, cyclotomic-orbit noncancellation closes Carlet
Proposition 3, and the trace-pairing coordinate theorem is compiled. Chapter 3 likewise has no open node: the
affine-flat normal form, codimension--degree theorem, and equality-case slice infrastructure compose
into the exact Proposition 12 classification.

Chapter 6 has no open node. Its source corrections are explicit: Proposition 16 uses the necessary
dimension lower bound; the partial-spread constructions use their valid positive range; the
punctured two-level partial-bent definition yields a corrected type formula and counterexamples to
two printed consequences; Langevin's orphan statement assumes a non-affine representative; and the
self-dual-normal-basis Kerdock identity states its coordinate hypotheses.

Chapter 7 has no open node. Its fidelity record makes explicit the positive propagation order in
the tradeoff equality case, the positive entropy domain in Relation (58), the binary
Maiorana--McFarland endpoint, the hypotheses needed by the concatenation and indirect-sum degree
formulas, the positive-degree linear-pullback range, Dobbertin's dimension range, and the exceptional
two-dimensional count.

Source-facing splits remain explicit in Chapter 4. Rodier's one-sided lower endpoint and sharp
interval have distinct nodes, as do the finite Hamming-ball and Plotkin lemmas and the resulting
higher-order asymptotic estimate. The Reed--Muller coset-distance theorem
adds the mathematically necessary distinct-coset hypothesis omitted from the printed sentence. The
`k`th nonhomomorphicity declarations follow Carlet's name for the even-output tuple count while
recording that reference [357] uses that name for the complementary odd-output count.

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
  BooleanFunction.lean
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
representation boundary. `BooleanFunction.lean` defines the canonical scalar function type and its
sign representation by direct reuse of FABL.

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
integrality. FABL's vector Fourier coefficient is normalized over the same cube. Their relation must
prove, with the project's chosen sign convention,

```text
CarletWalsh(f, a) = 2^n * FABL.vectorFourierCoeff(sign(f), a).
```

Every reuse of FABL Fourier theorems passes through this law. The project must not silently rename a
normalized coefficient as a Walsh value.

### Algebraic normal form

Algebraic normal form reuses FABL's coefficients indexed by finite coordinate subsets, with
coefficients in `𝔽₂`, together with its evaluation, support, uniqueness, and algebraic-degree APIs.
CryptBoolean adds only the Carlet-facing statements and cross-representation laws that consume this
canonical surface.

Algebraic degree and FABL's real Fourier degree remain distinct types of information with distinct
names. Any inequality between them is a theorem, not a definitional equality.

Univariate representation over `𝔽₂ⁿ`, trace representations, and normal numerical form are separate
adapters added only when a Carlet statement needs them. They must reuse Mathlib finite-field and
polynomial infrastructure; finite fields are not encoded as tables.

### Distances and criteria

Hamming weight and raw Hamming distance are natural numbers. Relative distance reuses FABL's
normalized distance only through an explicit scaling theorem.

Nonlinearity is defined primarily as minimum Hamming distance to the affine functions. Its maximum-
Walsh-magnitude formula is proved from that definition.

Balancedness, correlation immunity, resiliency, strict avalanche, propagation criteria, linear
structures, bentness, plateauedness, normality, and algebraic immunity are total predicates over
their parameters. Maximum orders or minima over finite families use finite extrema with explicit
empty-family behavior where the source permits an empty case.

## Required foundational identities and correspondences

The first dependency layer must prove and then reuse:

1. bit-function to sign-function evaluation;
2. raw Walsh sum to normalized FABL vector Fourier coefficient;
3. raw and relative Hamming distance scaling;
4. support cardinality to Hamming weight;
5. weight to the Walsh value at zero;
6. balancedness to vanishing zero-frequency Walsh value;
7. affine characters to FABL's vector Walsh characters;
8. direct reuse of FABL's binary derivatives, with sign-cube or restriction identities only where a
   Carlet statement changes representation.

Together these laws relate the domains through a single proof stack.

## FABL dependency policy

The Lean package pins FABL at release `v0.5.6`. Repository documentation and CI use the Git
dependency and its verified Lake release archive, never a developer's local absolute path.

Before adding a declaration, contributors search the pinned FABL public surface and pinned Mathlib.
A stronger existing theorem is specialized through an explicit conversion theorem. A new local declaration is permitted only
for a genuine cryptographic concept or a demonstrated gap.

Pinned FABL APIs and later FABL chapters create only targeted convergence gates:

| FABL area | CryptBooleanFunction policy |
|---|---|
| Pinned `v0.5.6` Boolean-function APIs | Canonical owner of ANF, degree, affine, and derivative operations; import directly and add only required conversion laws |
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
3. Classify each item as direct FABL reuse, direct Mathlib reuse, specialization,
   cross-representation law, or genuine local theorem.
4. Formalize signatures without changing domains, hypotheses, normalization, or quantifiers.
5. Close dependency-ready leaves and run a narrow module build locally only when it is known to be
   small; send every heavy or transitive rebuild to GitHub Actions.
6. Close a chapter only after the GitHub Actions statement-fidelity, root-build, forbidden-token,
   Blueprint, and rendered-artifact checks pass.

The development machine is not a full-build runner. Never run the root CryptBoolean build, complete
Verso compilation, or site/publication build locally. Local checks are limited to source inspection,
text and manifest validators, and demonstrably small affected modules. GitHub Actions owns all heavy
verification and retains build caches keyed by the relevant sources.

Production and completion branches contain no `sorry`, `admit`, project-defined `axiom`, `unsafe`,
or `native_decide`. A missing declaration association is the honest representation of an unfinished
Blueprint node. No placeholder declaration may manufacture completion.

### Blueprint statement contract

Every reviewed item has one complete human-readable mathematical statement. The statement begins
with its source result name or a descriptive mathematical title and gives the domains, hypotheses,
quantifiers, and conclusion needed to read it independently of the implementation.

A statement block never contains repository links, library provenance, implementation summaries,
proof narration, or completion status. Direct FABL or Mathlib reuse, representation choices, and
specialization or generalization boundaries belong in metadata or concise mathematical prose after
the block. API provenance and proof-engineering narration are omitted from reader text. Formalized
entries associate genuine compiled declarations; open entries remain visible without a declaration
association.

Public theorem titles and exposition use standard source terminology. Implementation nouns do not
serve as mathematical names. Use the precise relation being stated: scaling identity, coordinate
representation, equivalence, reduction, specialization, or corollary. Negation and contrast are
retained only for a mathematical hypothesis, conclusion, source correction, or genuine distinction.

The public Blueprint omits Carlet's introductory Chapter 1 and numbers Carlet Chapters 2--10 as
reader Chapters 1--9. Its headings use only chapter and section levels; Verso supplies `x` and `x.y`
automatically, and heading text never repeats those numbers. Source subsections are grouped into
clear reader sections in mathematical order. Internal module names, statement identifiers,
inventories, tags, and citations retain Carlet's original numbers. Lean modules may follow proof
dependencies. The site build runs `blueprint-verso/scripts/check_statement_style.py` to enforce the
public language and heading-depth rules.

## Cusick--Stănică integration

After Carlet is closed, build a source crosswalk:

| Cusick--Stănică area | Canonical destination |
|---|---|
| Chapter 2 Fourier analysis | Carlet Chapters 2--4 normalization and Fourier API |
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
