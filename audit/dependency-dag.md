# CryptBoolean dependency DAG

## Initial Carlet Chapter 2 leaf closure

```text
FABL.F₂Cube, FABL.𝔽₂
  -> CryptBoolean.BooleanFunction
  -> CryptBoolean.realSignView
  -> CryptBoolean.support
  -> CryptBoolean.hammingWeight

CryptBoolean.BooleanFunction, FABL.f₂DotProduct
  -> CryptBoolean.bitSignInt
  -> CryptBoolean.walshTerm
  -> CryptBoolean.walshTransform

CryptBoolean.walshTransform, FABL.vectorWalshCharacter, FABL.vectorFourierCoeff
  -> CryptBoolean.walshTerm_cast_eq_realSignView_mul_character
  -> CryptBoolean.walshTransform_cast_eq_sum_realSignView_mul_character
  -> CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff


CryptBoolean.support, CryptBoolean.hammingWeight, CryptBoolean.walshTransform
  -> CryptBoolean.IsBalanced
  -> CryptBoolean.walshTransform_zero_eq_card_sub_two_weight
  -> CryptBoolean.walshTransform_zero_eq_two_pow_sub_two_weight
  -> CryptBoolean.isBalanced_iff_walshTransform_zero_eq_zero

CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff, FABL.vector_fourier_expansion
  -> CryptBoolean.two_pow_mul_realSignView_eq_sum_walshTransform_mul_character
  -> CryptBoolean.realSignView_eq_inv_two_pow_mul_sum_walshTransform_mul_character

CryptBoolean.walshTransform_eq_two_pow_mul_vectorFourierCoeff, FABL.vector_plancherel
  -> CryptBoolean.realSignView_mul_self
  -> CryptBoolean.sum_vectorFourierCoeff_realSignView_sq
  -> CryptBoolean.sum_walshTransform_sq_eq_two_pow_sq

CryptBoolean.BooleanFunction, FABL.F₂Cube, FABL.𝔽₂
  -> CryptBoolean.ANFCoefficients
  -> CryptBoolean.anfMonomial
  -> CryptBoolean.anfEval
  -> CryptBoolean.anfSupport
  -> CryptBoolean.algebraicDegree
  -> CryptBoolean.mem_anfSupport
  -> CryptBoolean.anfMonomial_empty
  -> CryptBoolean.anfEval_zero
  -> CryptBoolean.anfEval_add
  -> CryptBoolean.algebraicDegree_le_dimension

CryptBoolean.anfEval, CryptBoolean.anfMonomial, FABL.f₂CubeOfFinset, FABL.f₂CubeEquivFinset
  -> CryptBoolean.anfMonomial_f₂CubeOfFinset
  -> CryptBoolean.anfEval_f₂CubeOfFinset
  -> CryptBoolean.anfCoeff
  -> CryptBoolean.anfEval_anfCoeff_f₂CubeOfFinset
  -> CryptBoolean.anfEval_anfCoeff
  -> CryptBoolean.anfCoeff_unique_of_powerset_sum
  -> CryptBoolean.anfEval_injective
  -> CryptBoolean.existsUnique_anfEval
```

The Blueprint graph is the machine-checked statement-level DAG for these nodes. This file records the reviewed mathematical spine used to select the first dependency-ready leaf.

## Expanded Chapter 2 and first Chapter 3 leaf

```text
FABL.vectorFourierCoeff, FABL.convolution, FABL.vector_plancherel
  -> rawFourierTransform_eq_two_pow_mul_vectorFourierCoeff
  -> rawFourierTransform_modulate_translate
  -> rawFourierTransform_involution
  -> rawFourierTransform_rawConvolution
  -> sum_rawFourierTransform_mul
  -> rawFourierTransform_autocorrelation

FABL subspace indicator spectrum, FABL.poissonSummationFormula
  -> rawFourierTransform_setIndicator_submodule
  -> poissonSummationFormula

Mathlib finite-field trace, trace-form nondegeneracy, Lagrange interpolation
  -> absoluteTrace
  -> exists_absoluteTrace_eq_one
  -> existsUnique_univariateRepresentation

generic subset-zeta injectivity
  -> ANF existence/uniqueness
  -> NNF existence/uniqueness
  -> numerical Möbius formula

ANF existence/uniqueness
  -> functionAlgebraicDegree
  -> affine characterization and affine weight
  -> reedMuller
  -> first-order Reed--Muller distance bound
```

The generated manifest currently checks 23 proved statement blocks, 114 associated Lean
declarations, and 26 reviewed dependency edges. Open source nodes are recorded in the inventories
and rendered chapter prose, not represented by placeholder declarations.
