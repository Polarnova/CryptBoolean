/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter08.AlgebraicDegree

/-!
# Algebraic degree under strict avalanche of order

Preneel's corrected algebraic-degree bound for the strict avalanche
criterion of order `k`.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private noncomputable def coordinateSubsetEquiv
    (J : Finset (Fin n)) : FABL.F₂Cube J.card ≃ Finset J :=
  (FABL.f₂CubeEquivFinset J.card).trans J.equivFin.symm.finsetCongr

private theorem zeroExtension_eq_f₂CubeOfFinset_liftFreeFrequency
    (J : Finset (Fin n)) (x : FABL.F₂Cube J.card) :
    Function.extend (FABL.freeCoordinateEmbedding J) x 0 =
      FABL.f₂CubeOfFinset
        (FABL.liftFreeFrequency (coordinateSubsetEquiv J x)) := by
  classical
  funext i
  by_cases hi : i ∈ J
  · let j : J := ⟨i, hi⟩
    let q : Fin J.card := J.equivFin j
    have hqi : FABL.freeCoordinateEmbedding J q = i := by
      dsimp [q, j]
      exact FABL.freeCoordinateEmbedding_equivFin J ⟨i, hi⟩
    rw [← hqi, (FABL.freeCoordinateEmbedding J).injective.extend_apply,
      FABL.f₂CubeOfFinset_apply]
    have hmem :
        FABL.freeCoordinateEmbedding J q ∈
            FABL.liftFreeFrequency (coordinateSubsetEquiv J x) ↔
          x q ≠ 0 := by
      have hsimplified :
          (∃ hi' : i ∈ J, x (J.equivFin ⟨i, hi'⟩) ≠ 0) ↔ x q ≠ 0 := by
        constructor
        · rintro ⟨hi', hx⟩
          simpa only [Subsingleton.elim hi' hi, q, j] using hx
        · intro hx
          exact ⟨hi, by simpa only [q, j] using hx⟩
      simpa [coordinateSubsetEquiv, Equiv.finsetCongr_apply,
        FABL.liftFreeFrequency, q, j, FABL.f₂Support] using hsimplified
    by_cases hx : x q = 0
    · simp [hmem, hx]
    · have hxone : x q = 1 := Fin.eq_one_of_ne_zero _ hx
      simp [hmem, hxone]
  · have hnotImage : ¬ ∃ q, FABL.freeCoordinateEmbedding J q = i := by
      rintro ⟨q, hqi⟩
      apply hi
      rw [← hqi]
      change (J.equivFin.symm q : Fin n) ∈ J
      exact (J.equivFin.symm q).property
    rw [Function.extend_apply' x (0 : FABL.F₂Cube n) i hnotImage,
      FABL.f₂CubeOfFinset_apply]
    have hnotMem :
        i ∉ FABL.liftFreeFrequency (coordinateSubsetEquiv J x) := by
      intro himem
      obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp himem
      exact hi (hji ▸ j.property)
    simp [hnotMem]

private noncomputable def freeFrequencyPowersetEquiv
    (J : Finset (Fin n)) : Finset J ≃ ↥J.powerset where
  toFun S := ⟨FABL.liftFreeFrequency S, by
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hi
    exact hji ▸ j.property⟩
  invFun U := FABL.freeFrequencyPart J U.1
  left_inv S := by
    ext i
    simp [FABL.freeFrequencyPart, FABL.liftFreeFrequency]
  right_inv U := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ J
    · let j : J := ⟨i, hi⟩
      change i ∈ FABL.liftFreeFrequency
          (FABL.freeFrequencyPart J U.1) ↔ i ∈ U.1
      constructor
      · intro h
        obtain ⟨q, hq, hqi⟩ := Finset.mem_map.mp h
        have hqj : q = j := Subtype.ext hqi
        subst q
        exact (FABL.mem_freeFrequencyPart J U.1 j).mp hq
      · intro h
        apply Finset.mem_map.mpr
        exact ⟨j, (FABL.mem_freeFrequencyPart J U.1 j).mpr h, rfl⟩
    · have hiU : i ∉ U.1 := fun hiU ↦ hi (Finset.mem_powerset.mp U.2 hiU)
      simp [FABL.liftFreeFrequency, hi, hiU]

/-- The top ANF coefficient of a zero-fixed coordinate restriction is the
ambient coefficient on its free-coordinate set. -/
theorem anfCoeff_coordinateRestriction_zeroFixed_univ
    (f : BooleanFunction n) (J : Finset (Fin n)) :
    FABL.anfCoeff (coordinateRestriction f J (fun _ ↦ 1)) Finset.univ =
      FABL.anfCoeff f J := by
  classical
  rw [FABL.anfCoeff_univ_eq_sum_f₂BooleanFunction]
  unfold FABL.anfCoeff
  calc
    (∑ x : FABL.F₂Cube J.card,
        coordinateRestriction f J (fun _ ↦ 1) x) =
        ∑ T : Finset J,
          f (FABL.f₂CubeOfFinset (FABL.liftFreeFrequency T)) := by
      apply Fintype.sum_equiv (coordinateSubsetEquiv J)
      intro x
      rw [coordinateRestriction_zeroFixed_apply,
        zeroExtension_eq_f₂CubeOfFinset_liftFreeFrequency]
    _ = ∑ U : ↥J.powerset, f (FABL.f₂CubeOfFinset U.1) := by
      apply Fintype.sum_equiv (freeFrequencyPowersetEquiv J)
      intro T
      rfl
    _ = ∑ U ∈ J.powerset, f (FABL.f₂CubeOfFinset U) := by
      symm
      exact Finset.sum_subtype J.powerset (fun U ↦ Iff.rfl)
        (fun U ↦ f (FABL.f₂CubeOfFinset U))

/-- Every restriction fixing exactly `k` coordinates of a function satisfying
SAC of order `k` has degree at most `n-k-1`, provided at least three
coordinates remain free. -/
theorem coordinateRestriction_degree_le_of_satisfiesStrictAvalancheCriterionOfOrder
    (f : BooleanFunction n) (k : ℕ) (hkn : k + 3 ≤ n)
    (hf : SatisfiesStrictAvalancheCriterionOfOrder k f)
    (J : Finset (Fin n)) (z : FABL.FixedSignCube J)
    (hfixed : Fintype.card (FABL.FixedIndex J) = k) :
    FABL.functionAlgebraicDegree (coordinateRestriction f J z) ≤
      n - k - 1 := by
  have hJle : J.card ≤ n := by
    simpa using Finset.card_le_univ J
  have hcomplement : n - J.card = k := by
    simpa [FABL.FixedIndex] using hfixed
  have hJcard : J.card = n - k := by omega
  have hdegree :=
    functionAlgebraicDegree_le_pred_of_satisfiesPropagationCriterion
      (coordinateRestriction f J z) 1 (by omega) (by omega) (by omega)
        (hf J z hfixed)
  simpa [hJcard] using hdegree

/-- Preneel's corrected SAC-of-order bound: if `k+3 ≤ n`, then a
function satisfying SAC of order `k` has degree at most `n-k-1`. -/
theorem functionAlgebraicDegree_le_of_satisfiesStrictAvalancheCriterionOfOrder
    (f : BooleanFunction n) (k : ℕ) (hkn : k + 3 ≤ n)
    (hf : SatisfiesStrictAvalancheCriterionOfOrder k f) :
    FABL.functionAlgebraicDegree f ≤ n - k - 1 := by
  classical
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hcard
  have hSle : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hSlarge : n - k ≤ S.card := by omega
  have hSthree : 3 ≤ S.card := by omega
  have hkRange : k ≤ n - 1 := by omega
  have hlowerOrder :
      SatisfiesPropagationCriterionOfOrder 1 (n - S.card) f :=
    (show SatisfiesPropagationCriterionOfOrder 1 k f from hf).mono_order
      hkRange (by omega)
  have hfixed : Fintype.card (FABL.FixedIndex S) = n - S.card := by
    simp [FABL.FixedIndex]
  have hrestrictionDegree :=
    functionAlgebraicDegree_le_pred_of_satisfiesPropagationCriterion
      (coordinateRestriction f S (fun _ ↦ 1)) 1 hSthree
        (by omega) (by omega) (hlowerOrder S (fun _ ↦ 1) hfixed)
  have htop :
      FABL.anfCoeff (coordinateRestriction f S (fun _ ↦ 1))
          Finset.univ ≠ 0 := by
    rw [anfCoeff_coordinateRestriction_zeroFixed_univ]
    exact hcoeff
  change FABL.algebraicDegree
      (FABL.anfCoeff (coordinateRestriction f S (fun _ ↦ 1))) ≤
        S.card - 1 at hrestrictionDegree
  have htopCard :=
    (FABL.algebraicDegree_le_iff
      (FABL.anfCoeff (coordinateRestriction f S (fun _ ↦ 1)))
      (S.card - 1)).mp hrestrictionDegree Finset.univ htop
  have : S.card ≤ S.card - 1 := by simpa using htopCard
  omega

end CryptBoolean
