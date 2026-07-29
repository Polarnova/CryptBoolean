/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.Dobbertin
public import CryptBoolean.Carlet.Chapter08.AffineFlatWalshCharacterization

/-!
# Propagation obstruction for Dobbertin's construction

The zero-first-block Walsh spectrum contradicts Proposition 35 at every
propagation level at least half the ambient dimension.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m : ℕ}

/-- Carlet Section 8.1.2: Dobbertin's balanced modification of a normal bent
function cannot satisfy `PC(l)` when `l` is at least half the dimension. -/
theorem not_satisfiesPropagationCriterion_dobbertinConstruction
    (f : BooleanFunction (m + m)) (g : BooleanFunction m)
    (_hm : 0 < m) (hf : IsBent f)
    (hflat : ∀ x : FABL.F₂Cube m, f (Fin.append x 0) = 0)
    (hg : IsBalanced g) (l : ℕ) (hlower : m ≤ l) (_hupper : l ≤ m + m) :
    ¬ SatisfiesPropagationCriterion l (dobbertinConstruction f g) := by
  classical
  intro hpc
  let u : FABL.F₂Cube (m + m) :=
    Fin.append (0 : FABL.F₂Cube m) (1 : FABL.F₂Cube m)
  have huCard : (FABL.f₂Support u).card = m := by
    rw [show u = Fin.append (0 : FABL.F₂Cube m) 1 from rfl,
      card_f₂Support_append]
    simp [FABL.f₂Support]
  have huWeight : m + m - l ≤ (FABL.f₂Support u).card := by
    rw [huCard]
    omega
  have hproposition :=
    (satisfiesPropagationCriterion_iff_predecessorWalshSquareSum
      l (dobbertinConstruction f g)).mp hpc u 0 huWeight
  have hsumZero :
      predecessorWalshSquareSum (dobbertinConstruction f g) u 0 = 0 := by
    unfold predecessorWalshSquareSum
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    let p := (Fin.appendEquiv m m).symm w
    have hp : Fin.append p.1 p.2 = w :=
      (Fin.appendEquiv m m).apply_symm_apply w
    have hpFirst : p.1 = 0 := by
      funext i
      by_contra hi
      have hwSupport :
          Fin.castAdd m i ∈ FABL.f₂Support w := by
        rw [← hp, FABL.mem_f₂Support]
        simpa using hi
      have huSupport := hw.2 hwSupport
      have huValue := (FABL.mem_f₂Support u (Fin.castAdd m i)).mp huSupport
      exact huValue (by simp [u])
    have hwRepresentation : Fin.append (0 : FABL.F₂Cube m) p.2 = w := by
      simpa [hpFirst] using hp
    rw [add_zero, ← hwRepresentation,
      walshTransform_dobbertinConstruction_zeroFirstBlock
        f g hf hflat hg]
    norm_num
  rw [hsumZero] at hproposition
  have hpositive : 0 < (2 : ℝ) ^ (m + m + (FABL.f₂Support u).card) := by
    positivity
  linarith

end CryptBoolean
