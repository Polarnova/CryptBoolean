# CryptBoolean statement-to-declaration fidelity audit

## Audit contract

Carlet supplies the source-facing mathematics. Production declarations under `CryptBoolean/`
supply the compiled theorem signatures and proofs. Verso nodes under
`blueprint-verso/CryptBooleanBlueprint/` must keep those two layers visibly aligned without turning
implementation provenance into theorem prose.

Each statement block therefore begins with the printed source result or an explicit project-bridge
label and states its domains, hypotheses, quantifiers, and conclusion. Repository links, reuse of
FABL or Mathlib, proof narration, and completion status belong in a separate `Formalization note`.
An open source result has no `lean :=` association and no placeholder declaration.

The generated manifest currently verifies the following baseline:

| Chapter | Statements | Formalized | Open | Associated declarations | Incoming statement edges |
|---|---:|---:|---:|---:|---:|
| Carlet Chapter 2 | 36 | 35 | 1 | 159 | 45 |
| Carlet Chapter 3 | 7 | 6 | 1 | 21 | 19 |
| **Total** | **43** | **41** | **2** | **180** | **64** |

The manifest count is an association count, not a claim that every printed result in Carlet
Chapters 2--3 is complete. Coverage outside these 43 reviewed nodes remains governed by the
inventories under `.agents/inventory/`.

## Corrected source mappings

| Blueprint item | Reviewed source statement | Fidelity decision |
|---|---|---|
| `carlet-2-def-support-weight` | Carlet p. 8: `w_H(f)` is the cardinality of the support of `f`. | The public weight is Mathlib's `hammingNorm`; `hammingWeight_eq_card_support` proves that this reused definition is exactly Carlet's support cardinality. |
| `carlet-2-univariate-representation` | Carlet Relation (4), p. 15: every map `F : GF(2^n) -> GF(2^n)` has a unique representing polynomial of degree `< 2^n`. | The earlier Relation (9) attribution was incorrect. The theorem is now cited as Relation (4), and it has no mathematical dependency edge from absolute trace. Mathlib interpolation is implementation provenance only. |
| `carlet-2-absolute-trace` | Carlet p. 15: the absolute trace has the Frobenius-sum formula, its trace pairing is nondegenerate, it is surjective, and a trace-one element lifts Boolean functions. | `traceForm_nondegenerate` and `Algebra.trace_surjective` are associated directly because their Mathlib statements are the exact mathematical facts; local declarations supply the binary-field specialization, explicit surjectivity theorem, and trace lift. |
| `carlet-2-prop-5-nnf-integrality` | Carlet Proposition 5, p. 21: the NNF is integer-valued exactly when all coefficients are integral, and under that condition it is Boolean-valued exactly when its square sum equals its sum. | The four associated predicates/theorems preserve both biconditionals and the integer-coefficient hypothesis; no finite test table replaces the quantified statement. |
| `carlet-2-affine-invariance` | Carlet p. 12: algebraic degree is invariant under affine automorphisms of `V_n`. | The proof first establishes nonincrease for arbitrary affine maps through ANF substitution and then applies the result to an affine equivalence and its inverse. The 13 associated declarations expose only helpers used in that composition. |
| `carlet-2-restriction-recovery` | Carlet pp. 13--14: a degree-at-most-`d` function is recovered by the stated binomial-parity formula from inputs of weight at most `d`, and therefore from every affine-automorphism image of that set. | The associated declarations prove the exact coefficient formula and both uniqueness consequences. The final consequence is restricted to affine automorphisms, not arbitrary affine maps. |
| `carlet-2-poisson-normalized-specialization` | The compiled theorem is the normalized coset-average identity `|E|⁻¹ sum_(h in E) phi(h+z) = sum_(u in E^perp) (-1)^(u dot z) phi_tilde(u)`. | This derived specialization is associated directly with `FABL.poissonSummationFormula`; it remains distinct from the raw source corollary. |
| `carlet-2-cor-1-poisson-summation` | Carlet Corollary 1, Relation (17), p. 25, with arbitrary `a,b in V_n` and the modulated sums over `a+E` and `b+E^perp`. | `rawPoissonSummationFormula` proves the complete raw identity. The normalized specialization is not presented as if it alone proved the full corollary. |
| `carlet-2-rel-22-plancherel` | Carlet Relation (22), p. 27: `sum_u phi_hat(u) psi_hat(u) = 2^n sum_x phi(x) psi(x)`. | The associated declaration proves the bilinear identity. Corollary 3 is recorded only as the consequence obtained by setting `psi = phi`; it is not used to relabel a weaker square-sum statement as Relation (22). |
| `carlet-2-spectral-support-bounds` | Carlet Section 2.2.2, p. 32: Fourier-support cardinality does not increase under coordinate restriction, is at least `2^d` for a nonzero Boolean function of algebraic degree `d`, and is at most the low-weight binomial sum for a nonzero function of numerical degree `D`. | The 24 declarations reuse FABL's normalized Fourier support and restriction results through explicit raw-scaling bridges. Nonzero hypotheses are stated because the project assigns degree zero to the zero function; the Lean upper bound is deliberately stronger and also covers zero. |
| `carlet-3-theorem-1-order-one` | The `r = 1` consequence of Carlet Theorem 1: nonzero degree-at-most-one functions have weight at least `2^(n-1)`, equivalently distinct words of `R(1,n)` have that distance lower bound. | This is explicitly tagged as a derived specialization and is formalized independently. |
| `carlet-3-theorem-1` | Carlet Theorem 1, p. 36: for every `0 <= r <= n`, distinct degree-at-most-`r` functions have Hamming distance at least `2^(n-r)`. | The two all-orders declarations prove the equivalent nonzero-weight and code-distance forms. The separately retained `r = 1` node is only a derived specialization. |
| `carlet-3-reed-muller-dimension` | Carlet p. 38: `dim R(r,n) = sum_(i=0)^r C(n,i)` and the code cardinality is the corresponding power of two. | The coefficient restriction is implemented as a linear equivalence; `reedMuller_finrank` proves the dimension formula and `reedMuller_card` derives cardinality from it. |
| `carlet-3-theorem-2` | Carlet Theorem 2, pp. 38--39: for `r<n`, `R(r,n)^⊥ = R(n-r-1,n)` under the Boolean-function pairing. | The six declarations define the bilinear pairing and dual, prove nondegeneracy and one containment, and close equality by the verified dimension formula. |

## Reviewed formalized surface

The 41 formalized statement nodes are split by mathematical result rather than by implementation
module summaries. The fidelity column records how the compiled declarations meet the displayed
source mathematics.

| Family | Formalized Blueprint items | Fidelity | Lean declarations |
|---|---|---|---:|
| Boolean foundations and raw Walsh transform | `carlet-2-def-boolean-function`, `carlet-2-def-support-weight`, `carlet-2-def-walsh-transform`, `carlet-2-bridge-walsh-normalization`, `carlet-2-balanced-zero-walsh` | Exact definitions/results plus explicit Walsh and Mathlib-Hamming bridges | 19 |
| Algebraic normal form | `carlet-2-anf-skeleton`, `carlet-2-anf-existence-uniqueness` | Exact, with the explicit zero-degree convention | 18 |
| Numerical normal form | `carlet-2-nnf-existence-uniqueness`, `carlet-2-prop-4-nnf-mobius`, `carlet-2-prop-5-nnf-integrality` | Exact | 19 |
| Algebraic degree, distance, and affine functions | `carlet-2-def-algebraic-degree`, `carlet-2-support-degree-addition`, `carlet-2-def-hamming-distance`, `carlet-2-bridge-relative-hamming-distance`, `carlet-2-def-affine-functions` | Exact source items plus explicit relative-distance bridge and derived addition law | 18 |
| Affine invariance | `carlet-2-affine-invariance` | Exact source theorem with used ANF-substitution proof layer | 13 |
| Restriction recovery | `carlet-2-restriction-recovery` | Exact formula and affine-automorphism consequence | 10 |
| Raw pseudo-Boolean Fourier operations | `carlet-2-pseudoboolean-fourier`, `carlet-2-prop-6-fourier-shifts`, `carlet-2-cor-2-fourier-involution`, `carlet-2-prop-7-subspace-indicator`, `carlet-2-poisson-normalized-specialization`, `carlet-2-cor-1-poisson-summation`, `carlet-2-def-convolution`, `carlet-2-prop-8-convolution`, `carlet-2-rel-22-plancherel` | Exact raw results plus one explicitly labelled direct-FABL normalized specialization | 13 |
| Spectral-support bounds | `carlet-2-spectral-support-bounds` | Exact with explicit zero-function conventions and raw/normalized bridges | 24 |
| Walsh inversion and Parseval for sign views | `carlet-2-fourier-inversion`, `carlet-2-parseval` | Exact sign-function specializations | 5 |
| Derivatives and autocorrelation | `carlet-2-def-2-derivative`, `carlet-2-def-autocorrelation`, `carlet-2-rel-25-wiener-khinchin`, `carlet-2-rel-26-total-autocorrelation` | Exact | 6 |
| Finite-field representation | `carlet-2-absolute-trace`, `carlet-2-univariate-representation` | Exact, with direct Mathlib trace reuse and interpolation provenance | 14 |
| Reed--Muller foundations | `carlet-3-affine-weight`, `carlet-3-reed-muller-code`, `carlet-3-theorem-1-order-one` | Exact source items plus explicitly derived order-one specialization | 11 |
| General Reed--Muller distance | `carlet-3-theorem-1` | Exact all-orders theorem | 2 |
| Reed--Muller dimension | `carlet-3-reed-muller-dimension` | Exact | 2 |
| Reed--Muller duality | `carlet-3-theorem-2` | Exact | 6 |
| **Total** | **41 items** |  | **180** |

The following distinctions are part of the fidelity boundary:

- Carlet's Walsh and pseudo-Boolean Fourier transforms are unnormalized sums. FABL's Fourier
  coefficients and convolution are normalized. Every reuse crosses an explicit scaling theorem.
- Carlet's algebraic degree is the degree of the unique algebraic normal form over `F_2`; it is not
  FABL's real Fourier degree.
- Hamming distance is a natural-number cardinality. Its relation to FABL relative distance is a
  separate normalization bridge; Mathlib's `hammingNorm` and `hammingDist` are reused only where
  their cardinality statements are proved to coincide with Carlet's definitions.
- The absolute trace, its Frobenius formula, trace-pairing nondegeneracy, and surjectivity are
  mathematical statements. Exact Mathlib theorems may therefore be associated directly, while
  library provenance remains outside the statement block.
- The normalized Poisson specialization is direct FABL reuse. Carlet's raw Corollary 1 is a
  separate local theorem with both modulation parameters.
- Spectral-support lower and upper bounds distinguish the zero-function convention explicitly;
  the formal upper bound strengthens the source statement by also covering zero.
- Carlet's general Reed--Muller distance theorem is associated independently of its derived
  order-one specialization. Dimension and orthogonal duality use linear structure rather than a
  set-cardinality surrogate.
- Definitions, bridge laws, source propositions, and derived consequences have separate Blueprint
  nodes when their quantifiers or conclusions differ.

## Open source statements

Exactly two open nodes state the complete reviewed mathematics and intentionally have no Lean
declaration association.

| Blueprint item | Source location | Exact blocker |
|---|---|---|
| `carlet-2-trace-monomial-degree` | Carlet Proposition 3, pp. 17--18 | Missing the bridge between coordinate ANF degree on `V_n` and maximum binary exponent weight in the univariate finite-field representation, together with cyclotomic-orbit noncancellation proving that a surviving nonzero orbit coefficient has weight `w_2(k)`. Pinned FABL and Mathlib expose neither result. |
| `carlet-3-prop-12` | Carlet Proposition 12, pp. 36--37 | Missing arbitrary affine-flat normal form, the codimension-equals-degree theorem for affine-flat indicators, and equality-case slice infrastructure for classifying all minimum-weight words. Pinned FABL and Mathlib do not supply this package. |

## Verification perimeter

The statement-style gate runs as part of the site build and rejects implementation prose, links,
missing mathematical notation, or inconsistent open/formalized metadata inside statement blocks.
The strict manifest validator checks the exact statement split, declaration presence and proof
status, graph node set, open-node set, and edge count.

Run from the repository root:

```bash
lake build CryptBoolean
./.github/scripts/forbidden_tokens.sh
./.github/scripts/audit_axioms.sh
./blueprint-verso/scripts/site.sh build
```

Source fidelity still requires human comparison with Carlet; compilation and manifest validation
alone do not establish that a statement has the correct domain, hypotheses, normalization, or
quantifiers.
