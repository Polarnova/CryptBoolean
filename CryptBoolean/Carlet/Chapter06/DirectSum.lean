/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity
public import CryptBoolean.Carlet.Chapter06.Dual

/-!
# Direct sums of bent Boolean functions

Carlet Section 6.4.2: the raw Walsh transform of a Boolean direct sum factors, and the
direct sum of two bent functions is bent.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- A function is decomposable with block sizes `n` and `m` when an affine
change of variables turns it into a sum of functions on the two disjoint
blocks. -/
def IsDecomposable
    (h : BooleanFunction (n + m)) : Prop :=
  ∃ f : BooleanFunction n, ∃ g : BooleanFunction m,
    ∃ L : FABL.F₂Cube (n + m) ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube (n + m),
      h = booleanDirectSum f g ∘ L

/-- Every direct sum is decomposable. -/
theorem isDecomposable_booleanDirectSum
    (f : BooleanFunction n) (g : BooleanFunction m) :
    IsDecomposable (booleanDirectSum f g) := by
  refine ⟨f, g, AffineEquiv.refl FABL.𝔽₂ (FABL.F₂Cube (n + m)), ?_⟩
  rfl

/-- Carlet's direct-sum Walsh identity. -/
theorem walshTransform_directSum
    (f : BooleanFunction n) (g : BooleanFunction m)
    (a : FABL.F₂Cube n) (b : FABL.F₂Cube m) :
    walshTransform (booleanDirectSum f g) (Fin.append a b) =
      walshTransform f a * walshTransform g b :=
  walshTransform_booleanDirectSum_append f g a b

/-- The Boolean direct sum of two bent functions is bent. -/
theorem isBent_booleanDirectSum
    {f : BooleanFunction n} {g : BooleanFunction m}
    (hf : IsBent f) (hg : IsBent g) :
    IsBent (booleanDirectSum f g) := by
  change FABL.IsBent (realSignView (booleanDirectSum f g))
  rw [realSignView_booleanDirectSum]
  exact FABL.IsBent.directProduct
    (even_of_isBent f hf) (even_of_isBent g hg) hf hg

/-- The dual of a direct sum is the direct sum of the two duals. -/
theorem bentDual_booleanDirectSum_append
    {f : BooleanFunction n} {g : BooleanFunction m}
    (hf : IsBent f) (hg : IsBent g)
    (a : FABL.F₂Cube n) (b : FABL.F₂Cube m) :
    bentDual (booleanDirectSum f g) (Fin.append a b) =
      bentDual f a + bentDual g b := by
  have hsum := isBent_booleanDirectSum hf hg
  have hfactor := walshTransform_directSum f g a b
  rw [walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual f hf a,
    walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual g hg b] at hfactor
  rw [walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
    (booleanDirectSum f g) hsum (Fin.append a b)] at hfactor
  have hhalf : (n + m) / 2 = n / 2 + m / 2 := by
    rcases even_of_isBent f hf with ⟨r, hr⟩
    rcases even_of_isBent g hg with ⟨s, hs⟩
    omega
  rw [hhalf, pow_add] at hfactor
  have hsign :
      bitSignInt (bentDual (booleanDirectSum f g) (Fin.append a b)) =
        bitSignInt (bentDual f a) * bitSignInt (bentDual g b) := by
    apply mul_right_cancel₀
      (by positivity : (2 ^ (n / 2) : ℤ) * 2 ^ (m / 2) ≠ 0)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hfactor
  rw [← bitSignInt_add] at hsign
  exact bitSignInt_injective hsign

end CryptBoolean
