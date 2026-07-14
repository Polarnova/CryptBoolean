# CryptBoolean fidelity audit

## Initial reviewed items

| Inventory id | Source-facing statement | Formal declarations | Fidelity status |
|---|---|---|---|
| `carlet-2-def-boolean-function` | Scalar Boolean functions are maps from the binary vector space to the binary field. | `CryptBoolean.BooleanFunction` | Exact domain, using FABL's `F₂Cube` and `𝔽₂`. |
| `carlet-2-def-support-weight` | Support is the one-set; weight is support cardinality. | `CryptBoolean.support`, `CryptBoolean.hammingWeight`, `CryptBoolean.mem_support` | Exact finite-set representation. |
| `carlet-2-def-walsh-transform` | The Walsh transform is the raw integer sum `∑ x, (-1)^(f x + a·x)`. | `CryptBoolean.bitSignInt`, `CryptBoolean.walshTerm`, `CryptBoolean.walshTransform` | Exact unnormalized integer API; no normalized coefficient is renamed as Walsh. |
| `carlet-2-bridge-walsh-normalization` | Raw Walsh equals `2^n` times the normalized FABL vector Fourier coefficient of the real sign encoding. | `CryptBoolean.walshTerm_cast_eq_realSignView_mul_character`, `CryptBoolean.walshTransform_cast_eq_sum_realSignView_mul_character`, `CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff` | Explicit normalization bridge; depends on FABL's sign convention and `vectorFourierCoeff_eq_expect`. |
| `carlet-2-balanced-zero-walsh` | Balancedness is equivalent to the zero Walsh coefficient vanishing; quantitatively `W_f(0)=2^n-2 wt(f)`. | `CryptBoolean.IsBalanced`, `CryptBoolean.walshTransform_zero_eq_two_pow_sub_two_weight`, `CryptBoolean.isBalanced_iff_walshTransform_zero_eq_zero` | Exact finite-cardinality bridge from support weight to zero-frequency Walsh. |
| `carlet-2-fourier-inversion` | The sign view is recovered from its Walsh spectrum: `(-1)^{f(x)} = 2^{-n} ∑ₐ W_f(a) χ_a(x)`. | `CryptBoolean.two_pow_mul_realSignView_eq_sum_walshTransform_mul_character`, `CryptBoolean.realSignView_eq_inv_two_pow_mul_sum_walshTransform_mul_character` | Walsh inversion for the sign view via FABL `vector_fourier_expansion` and the normalization bridge; stated on `realSignView`, not silently on the bit function. |
| `carlet-2-parseval` | Parseval for the raw Walsh transform: `∑ₐ W_f(a)² = (2^n)²`, equivalently the normalized sign-view spectrum sums to one. | `CryptBoolean.realSignView_mul_self`, `CryptBoolean.sum_vectorFourierCoeff_realSignView_sq`, `CryptBoolean.sum_walshTransform_sq_eq_two_pow_sq` | Parseval via FABL `vector_plancherel`; scaled by `(2^n)²` through the normalization bridge to keep the raw integer convention. |
| `carlet-2-anf-skeleton` | Algebraic normal forms are square-free coefficient families over coordinate subsets, evaluated by finite sums of monomials, with support and algebraic degree read from nonzero coefficients. | `CryptBoolean.ANFCoefficients`, `CryptBoolean.anfMonomial`, `CryptBoolean.anfEval`, `CryptBoolean.anfSupport`, `CryptBoolean.algebraicDegree`, `CryptBoolean.mem_anfSupport`, `CryptBoolean.anfMonomial_empty`, `CryptBoolean.anfEval_zero`, `CryptBoolean.anfEval_add`, `CryptBoolean.algebraicDegree_le_dimension` | Representation skeleton only; it intentionally does not claim full ANF existence or uniqueness yet. Algebraic degree remains a separate API from FABL real Fourier degree. |
| `carlet-2-anf-existence-uniqueness` | Every Boolean function has a unique algebraic normal form over `𝔽₂`. | `CryptBoolean.anfCoeff`, `CryptBoolean.anfEval_anfCoeff`, `CryptBoolean.anfEval_injective`, `CryptBoolean.existsUnique_anfEval` (with supporting `CryptBoolean.anfMonomial_f₂CubeOfFinset`, `CryptBoolean.anfEval_f₂CubeOfFinset`, `CryptBoolean.anfEval_anfCoeff_f₂CubeOfFinset`, `CryptBoolean.anfCoeff_unique_of_powerset_sum`) | Exact `∃!` statement over square-free coefficient families. Existence uses the characteristic-two Möbius inverse `S ↦ ∑_{T⊆S} f(1_T)`; the interval-parity count `#[T,U]=2^{|U|-|T|}` kills off-diagonal terms in char two. Uniqueness is zeta-transform injectivity on the subset lattice, reusing FABL's `f₂CubeOfFinset` indicator bridge with no added axioms. |

## Expanded Chapter 2 closure

| Inventory group | Formal declarations | Fidelity status |
|---|---|---|
| Raw pseudo-Boolean Fourier operations | `rawFourierTransform`, `rawFourierTransform_modulate_translate`, `rawFourierTransform_involution`, `rawFourierTransform_rawConvolution`, `sum_rawFourierTransform_mul` | Carlet's unnormalized convention is retained. Every normalized FABL reuse passes through `rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff`. |
| Subspaces and Poisson summation | `rawFourierTransform_setIndicator_submodule`, `poissonSummationFormula` | Proposition 7 has the exact raw cardinality factor. Poisson summation delegates to FABL's stronger finite-subspace result. |
| Derivatives and autocorrelation | `booleanDerivative`, `autocorrelation`, `rawFourierTransform_autocorrelation`, `sum_autocorrelation_eq_walshTransform_zero_sq` | Exact bit-valued derivative and real autocorrelation; Wiener--Khinchin is composed through raw convolution. |
| Numerical normal form | `existsUnique_numericalEval`, `numericalCoeff_eq_mobius_sum` | Exact multilinear real representation and Proposition 4 Möbius formula; shares the generic subset-zeta injectivity lemma with ANF. |
| Finite-field representation | `absoluteTrace`, `algebraMap_absoluteTrace_eq_sum_frobenius`, `existsUnique_univariateRepresentation` | Uses Mathlib finite fields, field trace, trace-form nondegeneracy, and Lagrange interpolation; no finite-field tables. |
| Degree, distance, and affine functions | `functionAlgebraicDegree`, `hammingDistance`, `hammingDistance_eq_two_pow_mul_relativeHammingDist`, `exists_affineFunction_of_functionAlgebraicDegree_le_one`, `hammingWeight_affineFunction_of_ne_zero` | Algebraic and Fourier degrees remain separate. Raw distance reuses Mathlib and has an explicit scaling bridge to FABL. |

## Chapter 3 progress

| Inventory id | Source-facing statement | Formal declarations | Fidelity status |
|---|---|---|---|
| `carlet-3-reed-muller-code` | `R(r,n)` is the linear family of functions of degree at most `r`. | `reedMuller`, `mem_reedMuller_iff`, `reedMuller_mono` | Exact minimal coding boundary, represented as a `Submodule`; no unused general code hierarchy. |
| `carlet-3-theorem-1-order-one` | Nonzero degree-at-most-one functions have weight at least `2^(n-1)`, hence the same distance lower bound for distinct `R(1,n)` words. | `two_pow_sub_one_le_hammingWeight_of_degree_le_one`, `reedMuller_one_distance_lower_bound` | Exact first-order specialization of Theorem 1, proved from the affine characterization and balancedness. |

## Known open inventory nodes

Chapter 2 still has four visible source-facing families: Proposition 5 integrality, trace-monomial
degree, complete affine-change/restriction laws, and spectral-support bounds. Chapter 3 keeps the
general form of Theorem 1, Proposition 12, the dimension formula, and Theorem 2 open. None has a
placeholder Lean declaration or a proof-complete Blueprint association.
