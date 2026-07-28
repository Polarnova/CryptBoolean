/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter06.Dual
public import CryptBoolean.Carlet.Chapter05.Affine
public import FABL.Chapter06.Constructions.MaioranaMcFarlandPermutation

/-!
# Carlet Chapter 6 Maiorana--McFarland construction

The original Maiorana--McFarland construction and its exact raw Walsh spectrum.
-/

open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The original permutation construction belongs to the Maiorana--McFarland
class introduced in Chapter 5. -/
theorem isMaioranaMcFarland_of_eq_permutation
    (f : BooleanFunction (n + n)) (g : BooleanFunction n)
    (π : Equiv.Perm (FABL.F₂Cube n))
    (hf : ∀ x y : FABL.F₂Cube n,
      f (FABL.joinF₂CubeBlocks x y) =
        FABL.f₂DotProduct x (π y) + g y) :
    IsMaioranaMcFarland f := by
  intro y
  refine ⟨g y, π y, fun x ↦ ?_⟩
  change f (FABL.joinF₂CubeBlocks x y) = _
  rw [hf]
  have hdot : FABL.f₂DotProduct x (π y) =
      FABL.f₂DotProduct (π y) x := by
    exact dotProduct_comm x (π y)
  rw [FABL.affineFunction, hdot, add_comm]

private theorem realSignView_eq_maioranaMcFarlandPermutation
    (f : BooleanFunction (n + n)) (g : BooleanFunction n)
    (π : Equiv.Perm (FABL.F₂Cube n))
    (hf : ∀ x y : FABL.F₂Cube n,
      f (FABL.joinF₂CubeBlocks x y) =
        FABL.f₂DotProduct x (π y) + g y) :
    realSignView f =
      FABL.maioranaMcFarlandPermutation π (fun y ↦ FABL.signEncode (g y)) := by
  funext z
  let x := (FABL.f₂CubeBlockEquiv n z).1
  let y := (FABL.f₂CubeBlockEquiv n z).2
  have hz : FABL.joinF₂CubeBlocks x y = z :=
    (FABL.f₂CubeBlockEquiv n).symm_apply_apply z
  rw [← hz, FABL.maioranaMcFarlandPermutation_joinF₂CubeBlocks]
  change FABL.signValue
      (FABL.signEncode (f (FABL.joinF₂CubeBlocks x y))) = _
  rw [hf,
    FABL.signValue_signEncode_eq_binarySign,
    FABL.signValue_signEncode_eq_binarySign,
    AddChar.map_add_eq_mul]

/-- Carlet relation (48): the exact raw Walsh transform of the original
Maiorana--McFarland construction. -/
theorem walshTransform_maioranaMcFarlandPermutation
    (f : BooleanFunction (n + n)) (g : BooleanFunction n)
    (π : Equiv.Perm (FABL.F₂Cube n))
    (hf : ∀ x y : FABL.F₂Cube n,
      f (FABL.joinF₂CubeBlocks x y) =
        FABL.f₂DotProduct x (π y) + g y)
    (a b : FABL.F₂Cube n) :
    walshTransform f (FABL.joinF₂CubeBlocks a b) =
      bitSignInt (g (π.symm a) + FABL.f₂DotProduct b (π.symm a)) *
        (2 ^ n : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  rw [walshTransform_eq_two_pow_mul_vectorFourierCoeff,
    realSignView_eq_maioranaMcFarlandPermutation f g π hf,
    FABL.vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks]
  push_cast
  rw [
    bitSignInt_cast, FABL.signValue_signEncode_eq_binarySign,
    FABL.vectorWalshCharacter_apply]
  rw [AddChar.map_add_eq_mul]
  norm_num [pow_add]
  field_simp

/-- Every Boolean function satisfying Carlet relation (48) is bent. -/
theorem isBent_of_maioranaMcFarlandPermutation
    (f : BooleanFunction (n + n)) (g : BooleanFunction n)
    (π : Equiv.Perm (FABL.F₂Cube n))
    (hf : ∀ x y : FABL.F₂Cube n,
      f (FABL.joinF₂CubeBlocks x y) =
        FABL.f₂DotProduct x (π y) + g y) :
    IsBent f := by
  change FABL.IsBent (realSignView f)
  rw [realSignView_eq_maioranaMcFarlandPermutation f g π hf]
  exact FABL.isBent_maioranaMcFarlandPermutation π
    (fun y ↦ FABL.signEncode (g y))

/-- The dual of the original Maiorana--McFarland construction is obtained by
applying the inverse permutation to the first frequency block. -/
theorem bentDual_maioranaMcFarlandPermutation
    (f : BooleanFunction (n + n)) (g : BooleanFunction n)
    (π : Equiv.Perm (FABL.F₂Cube n))
    (hf : ∀ x y : FABL.F₂Cube n,
      f (FABL.joinF₂CubeBlocks x y) =
        FABL.f₂DotProduct x (π y) + g y)
    (a b : FABL.F₂Cube n) :
    bentDual f (FABL.joinF₂CubeBlocks a b) =
      FABL.f₂DotProduct b (π.symm a) + g (π.symm a) := by
  have hbent := isBent_of_maioranaMcFarlandPermutation f g π hf
  have hdual := walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
    f hbent (FABL.joinF₂CubeBlocks a b)
  have hspectrum := walshTransform_maioranaMcFarlandPermutation
    f g π hf a b
  have hhalf : (n + n) / 2 = n := by omega
  rw [hhalf, hspectrum] at hdual
  have hsign :
      bitSignInt (bentDual f (FABL.joinF₂CubeBlocks a b)) =
        bitSignInt
          (FABL.f₂DotProduct b (π.symm a) + g (π.symm a)) := by
    apply mul_right_cancel₀ (by positivity : (2 ^ n : ℤ) ≠ 0)
    simpa [add_comm, mul_comm] using hdual.symm
  exact bitSignInt_injective hsign

end CryptBoolean
