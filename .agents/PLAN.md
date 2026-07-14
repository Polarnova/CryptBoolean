# CryptBooleanFunction implementation plan

## Baseline and planning facts

CryptBoolean pins FABL at revision `34334a1b0c8dd806c076444a0875caf29ba5e248`. Its public root
exposes the binary cube, sign cube, dot product, representation equivalence, normalized Fourier
coefficients, Fourier expansion, Plancherel, relative Hamming distance, balancedness, restrictions,
and derivatives needed for the first CryptBooleanFunction layer.

The current Blueprint baseline contains 43 source-facing statement nodes: 41 formalized nodes
associated with 180 proved Lean declarations and 2 visibly open nodes, connected by 64 reviewed
dependency edges. Chapter 2 contributes 36 nodes (35 formalized and 1 open), 159 declarations, and
45 incoming edges. Chapter 3 contributes 7 nodes (6 formalized and 1 open), 21 declarations, and 19
incoming edges. These counts are a synchronized verification contract shared by the inventories,
Verso sources, `blueprint-verso/scripts/validate_manifest.py`, and `AGENTS.md`.

Automated PDF text extraction finds 93 numbered definition/theorem/proposition/lemma/corollary
headings in Carlet and 240 in Cusick--Stănică. These are lower-bound discovery counts, not coverage
counts: unnumbered claims, equations, constructions, and extraction errors still require manual
inventory.

The governing sequencing rule is dependency readiness, not printed order. Carlet remains the
statement spine even when a later chapter supplies an earlier theorem's proof.

## Dependency spine

```text
FABL Chapters 1--3
        |
        v
binary/sign/Walsh bridges ---- ANF and algebraic degree
        |                           |
        +------------+--------------+
                     v
          weight, distance, affine functions
                     |
        +------------+-------------+
        |                          |
        v                          v
Reed-Muller/nonlinearity   derivatives/autocorrelation
        |                          |
        +------------+-------------+
                     v
     cryptographic criteria and tractable classes
             |          |          |
             v          v          v
           bent      resilient   propagation
             \          |          /
              +---------+---------+
                        v
               algebraic immunity
                        |
                        v
                symmetric functions
```

## Phase 0 - Repository bootstrap

Status: complete.

Deliverables:

- initialize the Lean package on the same Lean/Mathlib toolchain as the pinned FABL revision;
- add an exact Git dependency on FABL;
- create the `CryptBoolean` root import and chapter aggregates;
- add Verso Blueprint, strict manifest validation, forbidden-token checks, CI, and checked automatic
  GitHub Pages deployment from `main`;
- ignore both source PDFs and all generated artifacts;
- add a minimal import probe proving that the required FABL public API is reachable.

Exit gate: the empty composition surface builds without placeholder declarations, the strict
tooling pipeline runs, and no local filesystem path appears in package metadata.

## Phase 1 - Complete Carlet inventory

Status: in progress. Reviewed Chapter 2 and Chapter 3 items live under `.agents/inventory/`; later
chapters are not yet inventoried.

Read Chapters 2--10 in full and create one Blueprint node per in-scope item. Record full statements,
source locations, representation decisions, and mathematical dependencies. Mark referenced results
from the absent vectorial chapter as external dependencies instead of inventing them.

Each statement block contains only the source result label and rigorous mathematics: domains,
quantifiers, hypotheses, and conclusion. Repository links, FABL or Mathlib reuse, proof narration,
fidelity classification, and completion status belong in metadata or a separate `Formalization
note`, never in the theorem position.

In parallel with manual review, produce a source crosswalk for repeated numbering and for claims
that are stated in one section and proved later.

Exit gate: the complete Carlet inventory is visible, incomplete nodes are honest, chapter aggregates
render, and no proof work has silently expanded or reduced scope.

## Phase 2 - Chapter 2 foundations

Status: 35 of 36 source-facing nodes are formalized. This phase now includes Proposition 5's
numerical-normal-form integrality criterion, full raw Poisson summation, affine invariance,
restriction recovery, and both spectral-support bounds. The only open node is Carlet Proposition 3
on the algebraic degree of trace monomials.

The precise Proposition 3 frontier is a bridge from univariate finite-field exponents to coordinate
ANF degree: coordinate algebraic degree must equal the maximum binary weight in the univariate
support, and the coefficients along the relevant cyclotomic orbit must be shown not to cancel.

### 2A. Boolean representations

- canonical bit-valued functions on `𝔽₂ⁿ`;
- support, truth tables, weight, and Hamming distance;
- affine maps, translations, and coordinate changes;
- explicit bit/sign/real views using FABL.

### 2B. Algebraic normal form

- square-free monomial evaluation over `𝔽₂`;
- Möbius/ANF coefficient transform;
- existence and uniqueness;
- algebraic support and algebraic degree;
- affine invariance and restriction laws required downstream.

This work uses Carlet-facing names. Before FABL Chapter 6 exposes a stable overlapping API, perform
an ownership review and replace duplication with reuse or a narrow bridge.

### 2C. Fourier and Walsh

- raw integer Walsh transform;
- normalized FABL coefficient bridge;
- inversion, Parseval/Plancherel specializations, convolution, and subspace formulas;
- support and spectral magnitude results;
- normal numerical form only when its first theorem is ready.

### 2D. Finite-field representation

- reuse Mathlib Galois-field and polynomial APIs;
- univariate representation over `𝔽₂ⁿ`;
- trace representations and degree statements required by Carlet.

Exit gate: every later chapter can state weight, Walsh, ANF, degree, derivative, affine-equivalence,
and restriction claims without introducing a second representation.

## Phase 3 - Chapter 3 coding

Status: 6 of 7 source-facing nodes are formalized. The production surface defines `reedMuller r n`
and proves the affine-weight theorem, the derived first-order distance result, Carlet's general-order
Theorem 1, the dimension and cardinality formulas, and Theorem 2 on duality. Only Proposition 12's
minimum-weight equality classification remains open.

The precise Proposition 12 frontier is an arbitrary affine-flat normal form, the theorem that an
affine-flat indicator has algebraic degree equal to its codimension, and equality-case slice
infrastructure strengthening the general lower-bound induction.

- define Reed-Muller function families from bounded algebraic degree;
- relate evaluation vectors, Hamming weight, and minimum distance;
- prove the distance-to-code interpretation of higher-order nonlinearity;
- add only the code operations used by Carlet.

Do not build a general coding framework in advance. Revisit the abstraction only when Kerdock codes
or a second production use requires it.

Exit gate: Chapter 3 is source-complete and Chapter 4 can define nonlinearity by distance to the
first-order Reed-Muller family.

## Phase 4 - Chapter 4 cryptographic criteria

Close the criteria in dependency order:

1. algebraic degree;
2. nonlinearity and its maximum-Walsh formula;
3. balancedness, correlation immunity, and resiliency;
4. strict avalanche and propagation criteria;
5. linear structures and derivative characterizations;
6. algebraic immunity and annihilators;
7. remaining explicitly mathematical criteria.

This phase establishes the vocabulary used by all class and construction chapters.

## Phase 5 - Chapter 5 tractable classes

Formalize affine and quadratic functions first, then indicators of flats, normal functions, partial
covering sequences, and low-univariate-degree functions. Reuse Mathlib quadratic-form and finite-
field results where they match the source domain.

Exit gate: all weight, Walsh-spectrum, and nonlinearity restrictions claimed in Chapter 5 are
compiled and available to the bent/resilient construction phases.

## Phase 6 - Chapter 6 bent functions

Order the work by prerequisites rather than subsection number:

- spectral and derivative characterizations of bentness;
- dual bent function and normalization laws;
- algebraic-degree bounds;
- primary constructions;
- secondary constructions and decompositions;
- counting and characterization results;
- hyper-bent, partially bent, partial bent, and plateaued functions;
- normality questions and Kerdock-code results.

Finite-field constructions wait for Phase 2D. Kerdock results wait for the minimal Chapter 3 code
API. Spectral characterizations do not wait for either.

## Phase 7 - Chapter 7 resilient functions

- spectral characterization of correlation immunity and resiliency;
- algebraic-degree and nonlinearity bounds;
- maximum correlation with subsets;
- relationships with propagation and other criteria;
- primary and secondary constructions;
- counting results.

The Siegenthaler-type degree tradeoff is a planned FABL Chapter 6 overlap. Keep the Carlet-facing
theorem canonical in this project until the cross-project ownership review determines the shared
implementation.

## Phase 8 - Chapter 8 propagation criteria

- binary derivative and autocorrelation foundations;
- `PC(l)`, strict avalanche, and their characterizations;
- construction theorems;
- order-`k` propagation and extended propagation criteria.

This phase should reuse the Phase 4 predicates and derivative bridge rather than introduce parallel
definitions.

## Phase 9 - Chapter 9 algebraic immunity

- annihilator spaces and the standard algebraic-immunity minimum;
- general bounds and relationships with weight, normality, and nonlinearity;
- random and monomial-function results whose prerequisites are available;
- constructions attaining high algebraic immunity;
- parameter tables represented as proved finite computations only when the source supplies complete
  data and the computation is independently checkable.

No hard-coded table is evidence for a theorem. Data-dependent claims need an explicit checked input
artifact and a verified evaluator.

## Phase 10 - Chapter 10 symmetric functions

- symmetric-function representation and elementary-symmetric ANF;
- Walsh transform and nonlinearity;
- resiliency and algebraic immunity;
- rotation-symmetric and Matriochka-symmetric superclasses.

This phase reuses the general criteria and does not redefine them for symmetric functions.

## Phase 11 - Carlet closure

Run a statement-to-declaration audit across Chapters 2--10. Resolve every source discrepancy,
normalization bridge, referenced external lemma, and generalization. Then run the root build,
forbidden-token scan, strict Blueprint build, dependency-graph validation, and visual HTML/PDF QA.

The repository-level verification commands are `lake build CryptBoolean`,
`./.github/scripts/forbidden_tokens.sh`, `./.github/scripts/audit_axioms.sh`, and
`./blueprint-verso/scripts/site.sh build`.

Publish a Carlet coverage release only after every node is compiled and the complete dependency
closure is green.

## Phase 12 - Cusick--Stănică delta

First associate overlapping Chapters 2--5 statements with existing declarations. Add only genuinely
independent results. Then open separate scoped campaigns for:

- LFSRs, linear complexity, Berlekamp--Massey, and de Bruijn sequences;
- stream-cipher generators and their attack models;
- block ciphers, AES finite-field representations, and explicit round semantics;
- Boolean Cayley graphs and their spectral properties.

Polynomial-time security claims require a selected computation and adversary model. They must not
be encoded as informal asymptotic prose or trusted runtime annotations.

## Work that can start before later FABL chapters

- the complete Carlet inventory and Blueprint;
- the Lean repository and pinned FABL integration;
- bit/sign/real representation bridges;
- raw Walsh normalization and Fourier reuse;
- weight, distance, affine functions, balancedness, and nonlinearity;
- ANF, algebraic degree, Reed-Muller families, and algebraic immunity;
- derivative/autocorrelation definitions and spectral criteria;
- the spectral cores of bent, resilient, and propagation theory.

## Targeted waits and convergence gates

| Work item | Gate | Reason |
|---|---|---|
| Stable shared ANF API | FABL Chapter 6 ownership review | Avoid two public `𝔽₂`-polynomial foundations |
| Generalized Abelian/product Fourier refactor | FABL Chapter 8 or an immediate Carlet theorem | Current scalar `𝔽₂ⁿ` API is already sufficient |
| Hypercontractive asymptotic bounds | FABL Chapters 9--10 when a proof needs them | Do not block finite algebraic foundations |
| Kerdock-code layer | Minimal Reed-Muller/code API | Coding structure, not full FABL, is the prerequisite |
| Finite-field bent constructions | Phase 2D | Need trace and univariate polynomial infrastructure |
| Cusick stream/block-cipher security claims | Explicit operational and complexity model | FABL completion alone would not supply the semantics |

There is no task that must wait for FABL Chapters 1--11 as a whole.
