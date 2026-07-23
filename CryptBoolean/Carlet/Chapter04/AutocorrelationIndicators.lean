/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.Derivatives

/-!
# Carlet Chapter 4 autocorrelation indicators

The sum-of-squares and absolute indicators measure the global autocorrelation of a Boolean
function. Both are invariant under affine equivalence.
-/

open Finset
open scoped BigOperators BooleanCube NNReal

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Carlet's sum-of-squares indicator `V(f)`. -/
noncomputable def sumOfSquaresIndicator (f : BooleanFunction n) : ℝ :=
  ∑ e, autocorrelation f e ^ 2

/-- Carlet's absolute indicator. In dimension zero the empty supremum is defined to be zero. -/
noncomputable def absoluteIndicator (f : BooleanFunction n) : ℝ :=
  (((Finset.univ.erase (0 : FABL.F₂Cube n)).sup fun e ↦
    Real.toNNReal |autocorrelation f e| : ℝ≥0) : ℝ)

/-- Binary differentiation commutes with an affine input equivalence, with directions transformed
by its linear part. -/
theorem booleanDerivative_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (e x : FABL.F₂Cube n) :
    FABL.booleanDerivative (f ∘ L) e x =
      FABL.booleanDerivative f (L.linear e) (L x) := by
  rw [FABL.booleanDerivative, FABL.booleanDerivative]
  change f (L x) + f (L (x + e)) =
    f (L x) + f (L x + L.linear e)
  have hL : L (x + e) = L x + L.linear e := by
    simpa [add_comm] using L.toAffineMap.map_vadd x e
  rw [hL]

/-- Autocorrelation is reindexed by the linear part of an affine input equivalence. -/
theorem autocorrelation_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n)
    (e : FABL.F₂Cube n) :
    autocorrelation (f ∘ L) e = autocorrelation f (L.linear e) := by
  unfold autocorrelation
  calc
    ∑ x, realSignView (FABL.booleanDerivative (f ∘ L) e) x =
        ∑ x, realSignView (FABL.booleanDerivative f (L.linear e)) (L x) := by
      apply Finset.sum_congr rfl
      intro x _
      change
        FABL.signValue (FABL.signEncode (FABL.booleanDerivative (f ∘ L) e x)) =
          FABL.signValue
            (FABL.signEncode (FABL.booleanDerivative f (L.linear e) (L x)))
      exact congrArg (fun b : FABL.𝔽₂ ↦ FABL.signValue (FABL.signEncode b))
        (booleanDerivative_comp_affineEquiv f L e x)
    _ = ∑ x, realSignView (FABL.booleanDerivative f (L.linear e)) x :=
      Equiv.sum_comp L.toEquiv _

/-- The sum-of-squares indicator is invariant under affine equivalence. -/
theorem sumOfSquaresIndicator_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    sumOfSquaresIndicator (f ∘ L) = sumOfSquaresIndicator f := by
  rw [sumOfSquaresIndicator, sumOfSquaresIndicator]
  simp_rw [autocorrelation_comp_affineEquiv]
  exact Equiv.sum_comp L.linear.toEquiv (fun e ↦ autocorrelation f e ^ 2)

/-- The absolute indicator is invariant under affine equivalence. -/
theorem absoluteIndicator_comp_affineEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    absoluteIndicator (f ∘ L) = absoluteIndicator f := by
  classical
  let directions := Finset.univ.erase (0 : FABL.F₂Cube n)
  let value : FABL.F₂Cube n → ℝ≥0 :=
    fun e ↦ Real.toNNReal |autocorrelation f e|
  have himage : directions.image L.linear = directions := by
    ext e
    simp only [directions, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (L.linear.map_ne_zero_iff).2 hd
    · intro he
      refine ⟨L.linear.symm e, ?_, L.linear.apply_symm_apply e⟩
      exact (L.linear.symm.map_ne_zero_iff).2 he
  have hsup : directions.sup (fun e ↦ value (L.linear e)) = directions.sup value := by
    calc
      directions.sup (fun e ↦ value (L.linear e)) =
          (directions.image L.linear).sup value :=
        (Finset.sup_image directions L.linear value).symm
      _ = directions.sup value := by rw [himage]
  exact congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) (by
    simpa [absoluteIndicator, directions, value, autocorrelation_comp_affineEquiv] using hsup)

/-- The absolute indicator of a zero-variable Boolean function follows the empty-family
convention. -/
@[simp] theorem absoluteIndicator_zero_dimension (f : BooleanFunction 0) :
    absoluteIndicator f = 0 := by
  classical
  simp [absoluteIndicator]

end CryptBoolean
