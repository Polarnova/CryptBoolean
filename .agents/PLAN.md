# CryptBooleanFunction implementation plan

## Baseline and planning facts

CryptBoolean pins FABL at release `v0.5.6`. Its public root exposes the binary cube, sign cube, dot
product, representation equivalence, normalized Fourier coefficients, Fourier expansion,
Plancherel, relative Hamming distance, balancedness, restrictions, ANF, algebraic degree, affine
functions, and derivatives needed by CryptBoolean. FABL is the canonical owner of those shared APIs;
this project imports them directly and adds only source-facing or cross-representation laws.

The current Blueprint baseline contains 149 source-facing statement nodes: 146 formalized nodes
associated with 961 proved Lean declarations and 3 visibly open nodes, connected by 296 reviewed
dependency edges. Chapter 2 contributes 38 formalized nodes, 166 declarations, and 48 incoming
edges. Chapter 3 contributes 7 formalized nodes, 32 declarations, and 19 incoming
edges. Chapter 4 contributes 73 formalized nodes, 568 declarations, and 159 incoming edges. Chapter
5 contributes 31 nodes (28 formalized and 3 open), 195 declarations, and 70 incoming edges. These
counts are a synchronized verification contract shared by the inventories,
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
binary/sign/Walsh identities --- ANF and algebraic degree
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

Status: in progress. Reviewed Chapter 2 and Chapter 3 items live under `.agents/inventory/`.
Chapter 4's 73-item inventory and Chapter 5's 31 mathematical statements are
source-reviewed and Blueprint-synchronized; Chapters 6--10 are not yet inventoried.

Read Chapters 2--10 in full and create one Blueprint node per in-scope item. Record full statements,
source locations, representation decisions, and mathematical dependencies. Mark referenced results
from the absent vectorial chapter as external dependencies instead of inventing them.

Each statement block contains only the source result label and rigorous mathematics: domains,
quantifiers, hypotheses, and conclusion. Repository links, FABL or Mathlib reuse, proof narration,
fidelity classification, and completion status belong in internal metadata. Reader prose after a
statement is retained only when it adds mathematical content.

The public Blueprint omits Carlet Chapter 1 and numbers Carlet Chapters 2--10 as reader Chapters
1--9. It preserves Carlet's titles, section nesting, and order; internal identifiers and citations
retain the source numbers. Lean modules and the proof plan may follow dependency order.

In parallel with manual review, produce a source crosswalk for repeated numbering and for claims
that are stated in one section and proved later.

Exit gate: the complete Carlet inventory is visible, incomplete nodes are honest, chapter aggregates
render, and no proof work has silently expanded or reduced scope.

## Phase 2 - Chapter 2 foundations

Status: complete. All 38 source-facing nodes are formalized by 166 proved declarations with 48
reviewed dependency edges. This phase includes Proposition 5's numerical-normal-form integrality
criterion, full raw Poisson summation, affine invariance, restriction recovery, both
spectral-support bounds, the coordinate/univariate binary-degree formula, Carlet Proposition 3 on
trace-monomial degree, and trace-pairing coordinates.

Proposition 3 is closed by composing the exact binary-exponent-weight/coordinate-ANF-degree formula
with noncancellation along the trace monomial's cyclotomic orbit.

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

Pinned FABL `v0.5.6` canonically owns the ANF and algebraic-degree APIs. CryptBoolean imports that
surface directly and keeps only the Carlet-facing statements and narrow representation laws.

### 2C. Fourier and Walsh

- raw integer Walsh transform;
- normalized FABL coefficient scaling identity;
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

Status: complete. All 7 source-facing nodes are formalized by 32 proved declarations. The
production surface defines `reedMuller r n` and proves the affine-weight theorem, the derived first-
order distance result, Carlet's general-order Theorem 1, Proposition 12's minimum-weight equality
classification, the dimension and cardinality formulas, and Theorem 2 on duality.

Proposition 12 is closed by composing an arbitrary affine-flat indicator normal form, the theorem
that its algebraic degree equals its codimension, and equality-case slice rigidity for the converse
classification.

- define Reed-Muller function families from bounded algebraic degree;
- relate evaluation vectors, Hamming weight, and minimum distance;
- prove the distance-to-code interpretation of higher-order nonlinearity;
- add only the code operations used by Carlet.

Do not build a general coding framework in advance. Revisit the abstraction only when Kerdock codes
or a second production use requires it.

Exit gate: achieved. Chapter 3 is source-complete and its distance, classification, dimension, and
duality surface supports Chapter 4's nonlinearity definitions.

## Phase 4 - Chapter 4 cryptographic criteria

Status: complete. All 73 source-facing nodes are formalized by 568 proved declarations with 159
reviewed dependency edges. The compiled surface establishes the vocabulary used by all class and
construction chapters: degree, nonlinearity, higher-order distance, resiliency, propagation,
linear structures, algebraic immunity, autocorrelation, maximum correlation, and the remaining
explicit complexity criteria.

The last three closures are Rodier's sharp random-nonlinearity interval, the exact best
nonlinearity in dimension seven, and the sharp fixed-order higher-order asymptotic upper bound. The
last proof is factored through separate formal nodes for the moment ratio, dual-code weight
decomposition, low-weight terms, the weight-`16` rank-seven classification and character bound,
and finite Plotkin induction.

Maintain the corrected fidelity boundary while closing them: the Reed--Muller coset formula uses
distinct cosets, and the `k`th nonhomomorphicity node records Carlet's even-output naming separately
from reference [357]'s complementary convention.

## Phase 5 - Chapter 5 tractable classes

Status: complete at the reviewed algebraic and combinatorial boundary. Twenty-eight of 31 reviewed
nodes are formalized by 195 proved declarations.
The compiled surface includes affine spectra, quadratic polar and weight theory, the complete
quadratic affine normal form, exact quadratic weight and nonlinearity value sets, even quadratic
rank, quadraticization and its iterated degree-three Walsh lift, flat-indicator spectra,
restriction nonlinearity with its equality case, exact random nonnormality, covering-sequence
consequences, the odd- and even-dimensional quadratic trace representations, and the
trace-character/nonlinearity reduction. Three analytic nodes remain open: the Weil character-sum
bound, its nonlinearity corollary, and the reciprocal character-sum bound.

Formalize affine and quadratic functions first, then indicators of flats, normal functions, partial
covering sequences, and low-univariate-degree functions. Reuse Mathlib quadratic-form and finite-
field results where they match the source domain.

Exit gate: achieved for every dependency-ready Chapter 5 statement. The three explicitly open
analytic nodes form a separate Artin--Schreier/Hasse--Weil frontier and do not block the
bent/resilient construction phases.

## Phase 6 - Chapter 6 bent functions

Order proof work by prerequisites; retain the source subsection order in the public Blueprint:

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

FABL `v0.5.6` already supplies the Siegenthaler-type degree tradeoff. Reuse it through the exact
Carlet representation theorem.

## Phase 8 - Chapter 8 propagation criteria

- binary derivative and autocorrelation foundations;
- `PC(l)`, strict avalanche, and their characterizations;
- construction theorems;
- order-`k` propagation and extended propagation criteria.

This phase reuses the Phase 4 predicates and derivative correspondence.

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
normalization identity, referenced external lemma, and generalization. Then have GitHub Actions run
the root build, forbidden-token scan, strict Blueprint build, dependency-graph validation, and
rendered-artifact QA.

The repository-level verification commands are `lake build CryptBoolean`,
`./.github/scripts/forbidden_tokens.sh`, `./.github/scripts/audit_axioms.sh`, and
`./blueprint-verso/scripts/site.sh build release`; they run in GitHub Actions, not on the development
machine. Local work uses lightweight text and manifest checks plus a known-small module build when
needed. Never start a root, complete Blueprint, or publication build locally.

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
- bit/sign/real representation theorems;
- raw Walsh normalization and Fourier reuse;
- weight, distance, affine functions, balancedness, and nonlinearity;
- ANF, algebraic degree, Reed-Muller families, and algebraic immunity;
- derivative/autocorrelation definitions and spectral criteria;
- the spectral cores of bent, resilient, and propagation theory.

## Targeted waits and convergence gates

| Work item | Gate | Reason |
|---|---|---|
| Generalized Abelian/product Fourier refactor | FABL Chapter 8 or an immediate Carlet theorem | Current scalar `𝔽₂ⁿ` API is already sufficient |
| Hypercontractive asymptotic bounds | FABL Chapters 9--10 when a proof needs them | Do not block finite algebraic foundations |
| Kerdock-code layer | Minimal Reed-Muller/code API | Coding structure, not full FABL, is the prerequisite |
| Finite-field bent constructions | Phase 2D | Need trace and univariate polynomial infrastructure |
| Cusick stream/block-cipher security claims | Explicit operational and complexity model | FABL completion alone would not supply the semantics |

There is no task that must wait for FABL Chapters 1--11 as a whole.
