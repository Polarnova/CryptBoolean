/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.ANF

/-!
# Carlet Chapter 2 algebraic normal form existence and uniqueness

Existence and uniqueness of the algebraic normal form of a scalar Boolean function
over `𝔽₂`, via the characteristic-two Möbius/zeta transform on the subset lattice.
The canonical coefficient family is the zeta-inverse `S ↦ ∑_{T ⊆ S} f(1_T)`, and the
interval-parity argument `#[T, U] = 2^{|U|-|T|}` collapses every off-diagonal term in
characteristic two.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Equality of all Boolean-lattice zeta sums determines the coefficient family. -/
theorem coefficients_eq_of_powerset_sum_eq {R : Type*} [AddCommMonoid R]
    [IsRightCancelAdd R] (c d : Finset (Fin n) → R)
    (h : ∀ U : Finset (Fin n), (∑ T ∈ U.powerset, c T) = ∑ T ∈ U.powerset, d T) :
    c = d := by
  classical
  funext S
  induction S using Finset.strongInduction with
  | _ S ih =>
    have hself : S ∈ S.powerset := Finset.mem_powerset.mpr (subset_refl S)
    have hc : c S + ∑ T ∈ S.powerset.erase S, c T = ∑ T ∈ S.powerset, c T :=
      Finset.add_sum_erase _ _ hself
    have hd : d S + ∑ T ∈ S.powerset.erase S, d T = ∑ T ∈ S.powerset, d T :=
      Finset.add_sum_erase _ _ hself
    have htail : (∑ T ∈ S.powerset.erase S, c T) =
        ∑ T ∈ S.powerset.erase S, d T := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [Finset.mem_erase, Finset.mem_powerset] at hT
      exact ih T (hT.2.ssubset_of_ne hT.1)
    have hsum := h S
    rw [← hc, ← hd, htail] at hsum
    exact add_right_cancel hsum

/-- The square-free monomial evaluated at a subset indicator is one exactly on subsets. -/
theorem anfMonomial_f₂CubeOfFinset (S U : Finset (Fin n)) :
    anfMonomial S (FABL.f₂CubeOfFinset U) = if S ⊆ U then 1 else 0 := by
  classical
  rw [anfMonomial]
  simp only [FABL.f₂CubeOfFinset_apply]
  by_cases h : S ⊆ U
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i hi => if_pos (h hi))
  · rw [if_neg h]
    obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hiS (if_neg hiU)

/-- ANF evaluation at a subset indicator is the zeta partial sum over the powerset. -/
theorem anfEval_f₂CubeOfFinset (c : ANFCoefficients n) (U : Finset (Fin n)) :
    anfEval c (FABL.f₂CubeOfFinset U) = ∑ S ∈ U.powerset, c S := by
  classical
  rw [anfEval]
  calc
    ∑ S, c S * anfMonomial S (FABL.f₂CubeOfFinset U)
        = ∑ S, (if S ⊆ U then c S else 0) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [anfMonomial_f₂CubeOfFinset]
          by_cases h : S ⊆ U <;> simp [h]
    _ = ∑ S ∈ Finset.univ.filter (fun S => S ⊆ U), c S := by
          rw [Finset.sum_filter]
    _ = ∑ S ∈ U.powerset, c S := by
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext S
          simp [Finset.mem_powerset]

/-- The canonical `𝔽₂` Möbius-inverse coefficient family of a Boolean function. -/
noncomputable def anfCoeff (f : BooleanFunction n) : ANFCoefficients n :=
  fun S => ∑ T ∈ S.powerset, f (FABL.f₂CubeOfFinset T)

/-- Existence at an indicator input: the canonical coefficients reproduce `f` on every `1_U`. -/
theorem anfEval_anfCoeff_f₂CubeOfFinset (f : BooleanFunction n) (U : Finset (Fin n)) :
    anfEval (anfCoeff f) (FABL.f₂CubeOfFinset U) = f (FABL.f₂CubeOfFinset U) := by
  classical
  rw [anfEval_f₂CubeOfFinset]
  simp only [anfCoeff]
  have step1 : ∀ S ∈ U.powerset,
      (∑ T ∈ S.powerset, f (FABL.f₂CubeOfFinset T))
        = ∑ T ∈ U.powerset, (if T ⊆ S then f (FABL.f₂CubeOfFinset T) else 0) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hsub : S.powerset = U.powerset.filter (fun T => T ⊆ S) := by
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨h.trans hS, h⟩, fun h => h.2⟩
    rw [hsub, Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset, (if T ⊆ S then f (FABL.f₂CubeOfFinset T) else 0))
        = if T = U then f (FABL.f₂CubeOfFinset U) else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hset : U.powerset.filter (fun S => T ⊆ S) = Finset.Icc T U := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [← Finset.sum_filter, hset, Finset.sum_const, Finset.card_Icc_finset hT]
    by_cases hTU : T = U
    · subst hTU
      rw [if_pos rfl, Nat.sub_self, pow_zero, one_nsmul]
    · rw [if_neg hTU]
      have hlt : T.card < U.card := Finset.card_lt_card (hT.ssubset_of_ne hTU)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hlt).ne'
      rw [hm, pow_succ, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero]
  rw [Finset.sum_congr rfl step2, Finset.sum_ite_eq' U.powerset U,
    if_pos (Finset.mem_powerset.mpr (subset_refl U))]

/-- Existence: the canonical coefficient family evaluates to the original Boolean function. -/
theorem anfEval_anfCoeff (f : BooleanFunction n) : anfEval (anfCoeff f) = f := by
  classical
  funext x
  have hx : FABL.f₂CubeOfFinset (FABL.f₂Support x) = x := by
    simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply x
  rw [← hx, anfEval_anfCoeff_f₂CubeOfFinset]

/-- Uniqueness of the zeta transform on the subset lattice: equal powerset partial sums
force equal coefficient families. -/
theorem anfCoeff_unique_of_powerset_sum (c d : ANFCoefficients n)
    (h : ∀ U : Finset (Fin n), (∑ T ∈ U.powerset, c T) = ∑ T ∈ U.powerset, d T) :
    c = d := by
  exact coefficients_eq_of_powerset_sum_eq c d h

/-- Uniqueness: coefficient families with equal ANF evaluation are equal. -/
theorem anfEval_injective {c d : ANFCoefficients n} (h : anfEval c = anfEval d) :
    c = d := by
  apply anfCoeff_unique_of_powerset_sum
  intro U
  rw [← anfEval_f₂CubeOfFinset, ← anfEval_f₂CubeOfFinset, h]

/-- Carlet, Section 2.1: every Boolean function has a unique algebraic normal form. -/
theorem existsUnique_anfEval (f : BooleanFunction n) :
    ∃! c : ANFCoefficients n, anfEval c = f := by
  refine ⟨anfCoeff f, anfEval_anfCoeff f, ?_⟩
  intro c hc
  exact anfEval_injective (hc.trans (anfEval_anfCoeff f).symm)

end CryptBoolean
