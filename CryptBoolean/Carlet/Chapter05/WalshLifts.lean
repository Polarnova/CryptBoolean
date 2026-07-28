/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.AlgebraicDegree

/-!
# Carlet Chapter 5 Walsh-preserving quadraticization
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Replace one product of Boolean functions by a quadratic term in two fresh variables. -/
def quadraticizationLift
    (f₁ f₂ f₃ : BooleanFunction n) : BooleanFunction (n + 2) :=
  fun z ↦
    let p := (Fin.appendEquiv n 2).symm z
    p.2 0 * p.2 1 + p.2 0 * f₁ p.1 + p.2 1 * f₂ p.1 + f₃ p.1

@[simp] theorem quadraticizationLift_append
    (f₁ f₂ f₃ : BooleanFunction n) (x : FABL.F₂Cube n) (y₁ y₂ : FABL.𝔽₂) :
    quadraticizationLift f₁ f₂ f₃ (Fin.append x ![y₁, y₂]) =
      y₁ * y₂ + y₁ * f₁ x + y₂ * f₂ x + f₃ x := by
  simp [quadraticizationLift]

private theorem sum_bitSignInt_quadraticization (c₁ c₂ c₃ : FABL.𝔽₂) :
    (∑ y₁ : FABL.𝔽₂, ∑ y₂ : FABL.𝔽₂,
        bitSignInt (y₁ * y₂ + y₁ * c₁ + y₂ * c₂ + c₃)) =
      2 * bitSignInt (c₁ * c₂ + c₃) := by
  fin_cases c₁ <;> fin_cases c₂ <;> fin_cases c₃ <;>
    decide

/-- One quadraticization step doubles the zero-frequency raw Walsh coefficient. -/
theorem walshTransform_quadraticizationLift_zero
    (f₁ f₂ f₃ : BooleanFunction n) :
    walshTransform (quadraticizationLift f₁ f₂ f₃) 0 =
      2 * walshTransform (fun x ↦ f₁ x * f₂ x + f₃ x) 0 := by
  classical
  rw [walshTransform]
  calc
    ∑ z : FABL.F₂Cube (n + 2),
        walshTerm (quadraticizationLift f₁ f₂ f₃) 0 z =
        ∑ p : FABL.F₂Cube n × FABL.F₂Cube 2,
          walshTerm (quadraticizationLift f₁ f₂ f₃) 0
            (Fin.append p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.appendEquiv n 2)
        (fun p ↦ walshTerm (quadraticizationLift f₁ f₂ f₃) 0
          (Fin.append p.1 p.2))
        (fun z ↦ walshTerm (quadraticizationLift f₁ f₂ f₃) 0 z)
        (fun _ ↦ rfl)).symm
    _ = ∑ x : FABL.F₂Cube n, ∑ y : FABL.F₂Cube 2,
          walshTerm (quadraticizationLift f₁ f₂ f₃) 0 (Fin.append x y) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : FABL.F₂Cube n, ∑ y₁ : FABL.𝔽₂, ∑ y₂ : FABL.𝔽₂,
          bitSignInt (y₁ * y₂ + y₁ * f₁ x + y₂ * f₂ x + f₃ x) := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        ∑ y : FABL.F₂Cube 2,
            walshTerm (quadraticizationLift f₁ f₂ f₃) 0 (Fin.append x y) =
            ∑ p : FABL.𝔽₂ × FABL.𝔽₂,
              walshTerm (quadraticizationLift f₁ f₂ f₃) 0
                (Fin.append x ![p.1, p.2]) := by
          exact Fintype.sum_equiv (finTwoArrowEquiv FABL.𝔽₂)
            (fun y ↦ walshTerm (quadraticizationLift f₁ f₂ f₃) 0
              (Fin.append x y))
            (fun p ↦ walshTerm (quadraticizationLift f₁ f₂ f₃) 0
              (Fin.append x ![p.1, p.2]))
            (fun y ↦ by
              have hy :
                  ![((finTwoArrowEquiv FABL.𝔽₂) y).1,
                    ((finTwoArrowEquiv FABL.𝔽₂) y).2] = y := by
                simpa only [finTwoArrowEquiv_symm_apply] using
                  (finTwoArrowEquiv FABL.𝔽₂).symm_apply_apply y
              rw [hy])
        _ = _ := by
          rw [Fintype.sum_prod_type]
          simp only [walshTerm_zero, quadraticizationLift_append]
    _ = ∑ x : FABL.F₂Cube n,
          2 * bitSignInt (f₁ x * f₂ x + f₃ x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact sum_bitSignInt_quadraticization (f₁ x) (f₂ x) (f₃ x)
    _ = 2 * ∑ x : FABL.F₂Cube n,
          walshTerm (fun z ↦ f₁ z * f₂ z + f₃ z) 0 x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [walshTerm_zero]

private def monomialListEval
    (P : List (Finset (Fin n))) : BooleanFunction n :=
  P.map FABL.anfMonomial |>.sum

private def cubicExcess (P : List (Finset (Fin n))) : ℕ :=
  (P.map fun S ↦ S.card - 3).sum

private def embedMonomial (S : Finset (Fin n)) : Finset (Fin (n + 2)) :=
  S.map (Fin.castAddEmb 2)

@[simp] private theorem card_embedMonomial (S : Finset (Fin n)) :
    (embedMonomial S).card = S.card := by
  simp [embedMonomial]

@[simp] private theorem anfMonomial_embedMonomial_append
    (S : Finset (Fin n)) (x : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    FABL.anfMonomial (embedMonomial S) (Fin.append x y) =
      FABL.anfMonomial S x := by
  classical
  simp [embedMonomial, FABL.anfMonomial]

private def freshZero : Fin (n + 2) := Fin.natAdd n 0
private def freshOne : Fin (n + 2) := Fin.natAdd n 1

@[simp] private theorem freshZero_ne_freshOne :
    (freshZero : Fin (n + 2)) ≠ freshOne := by
  simp [freshZero, freshOne]

@[simp] private theorem freshZero_not_mem_embedMonomial (S : Finset (Fin n)) :
    (freshZero : Fin (n + 2)) ∉ embedMonomial S := by
  simp only [embedMonomial, Finset.mem_map, Fin.castAddEmb_apply, not_exists, not_and]
  intro i _ h
  have hv := congrArg Fin.val h
  simp [freshZero] at hv
  omega

@[simp] private theorem freshOne_not_mem_embedMonomial (S : Finset (Fin n)) :
    (freshOne : Fin (n + 2)) ∉ embedMonomial S := by
  simp only [embedMonomial, Finset.mem_map, Fin.castAddEmb_apply, not_exists, not_and]
  intro i _ h
  have hv := congrArg Fin.val h
  simp [freshOne] at hv
  omega

@[simp] private theorem anfMonomial_freshPair_append
    (x : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    FABL.anfMonomial ({freshZero, freshOne} : Finset (Fin (n + 2)))
        (Fin.append x y) = y 0 * y 1 := by
  simp [FABL.anfMonomial, freshZero, freshOne]

@[simp] private theorem anfMonomial_insert_freshZero_embedMonomial_append
    (S : Finset (Fin n)) (x : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    FABL.anfMonomial (insert freshZero (embedMonomial S)) (Fin.append x y) =
      y 0 * FABL.anfMonomial S x := by
  rw [← Finset.singleton_union]
  rw [← FABL.anfMonomial_mul]
  rw [anfMonomial_embedMonomial_append]
  simp [FABL.anfMonomial, freshZero]

@[simp] private theorem anfMonomial_insert_freshOne_embedMonomial_append
    (S : Finset (Fin n)) (x : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    FABL.anfMonomial (insert freshOne (embedMonomial S)) (Fin.append x y) =
      y 1 * FABL.anfMonomial S x := by
  rw [← Finset.singleton_union]
  rw [← FABL.anfMonomial_mul]
  rw [anfMonomial_embedMonomial_append]
  simp [FABL.anfMonomial, freshOne]

private def breakTerms (A B : Finset (Fin n))
    (R : List (Finset (Fin n))) : List (Finset (Fin (n + 2))) :=
  [{freshZero, freshOne},
    insert freshZero (embedMonomial A),
    insert freshOne (embedMonomial B)] ++ R.map embedMonomial

@[simp] private theorem monomialListEval_apply
    (P : List (Finset (Fin n))) (x : FABL.F₂Cube n) :
    monomialListEval P x = (P.map fun S ↦ FABL.anfMonomial S x).sum := by
  induction P with
  | nil => simp [monomialListEval]
  | cons S P ih =>
      change (FABL.anfMonomial S + monomialListEval P) x = _
      rw [Pi.add_apply, ih]
      rfl

@[simp] private theorem monomialListEval_map_embed_append
    (R : List (Finset (Fin n))) (x : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    monomialListEval (R.map embedMonomial) (Fin.append x y) =
      monomialListEval R x := by
  induction R with
  | nil => simp [monomialListEval]
  | cons S R ih =>
      change FABL.anfMonomial (embedMonomial S) (Fin.append x y) +
          monomialListEval (R.map embedMonomial) (Fin.append x y) =
        FABL.anfMonomial S x + monomialListEval R x
      rw [anfMonomial_embedMonomial_append, ih]

private theorem monomialListEval_breakTerms
    (A B : Finset (Fin n)) (R : List (Finset (Fin n))) :
    monomialListEval (breakTerms A B R) =
      quadraticizationLift (FABL.anfMonomial A) (FABL.anfMonomial B)
        (monomialListEval R) := by
  funext z
  let p := (Fin.appendEquiv n 2).symm z
  have hz : Fin.append p.1 p.2 = z := (Fin.appendEquiv n 2).apply_symm_apply z
  rw [← hz]
  have hp2 : p.2 = ![p.2 0, p.2 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hp2]
  rw [quadraticizationLift_append]
  change
    FABL.anfMonomial ({freshZero, freshOne} : Finset (Fin (n + 2)))
          (Fin.append p.1 ![p.2 0, p.2 1]) +
        (FABL.anfMonomial (insert freshZero (embedMonomial A))
            (Fin.append p.1 ![p.2 0, p.2 1]) +
          (FABL.anfMonomial (insert freshOne (embedMonomial B))
              (Fin.append p.1 ![p.2 0, p.2 1]) +
            monomialListEval (R.map embedMonomial)
              (Fin.append p.1 ![p.2 0, p.2 1]))) = _
  rw [anfMonomial_freshPair_append,
    anfMonomial_insert_freshZero_embedMonomial_append,
    anfMonomial_insert_freshOne_embedMonomial_append,
    monomialListEval_map_embed_append]
  simp
  ring

@[simp] private theorem cubicExcess_map_embedMonomial
    (R : List (Finset (Fin n))) :
    cubicExcess (R.map embedMonomial) = cubicExcess R := by
  induction R with
  | nil => simp [cubicExcess]
  | cons S R ih =>
      change ((embedMonomial S).card - 3) +
          cubicExcess (R.map embedMonomial) =
        (S.card - 3) + cubicExcess R
      rw [card_embedMonomial, ih]

private theorem cubicExcess_breakTerms_lt
    (S A : Finset (Fin n)) (R : List (Finset (Fin n)))
    (hA : A ⊆ S) (hAcard : A.card = 2) (hScard : 3 < S.card) :
    cubicExcess (breakTerms A (S \ A) R) <
      (S.card - 3) + cubicExcess R := by
  have hBcard : (S \ A).card = S.card - 2 := by
    rw [Finset.card_sdiff_of_subset hA, hAcard]
  have hmap := cubicExcess_map_embedMonomial (n := n) R
  unfold cubicExcess at hmap
  simp only [List.map_map] at hmap
  have hpair :
      ({freshZero, freshOne} : Finset (Fin (n + 2))).card = 2 := by
    simp
  have hzero :
      (insert freshZero (embedMonomial A)).card = A.card + 1 := by
    rw [Finset.card_insert_of_notMem (freshZero_not_mem_embedMonomial A),
      card_embedMonomial, Nat.add_comm]
  have hone :
      (insert freshOne (embedMonomial (S \ A))).card = (S \ A).card + 1 := by
    rw [Finset.card_insert_of_notMem (freshOne_not_mem_embedMonomial (S \ A)),
      card_embedMonomial, Nat.add_comm]
  simp only [cubicExcess, breakTerms, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
  rw [hpair, hzero, hone, hAcard, hBcard]
  rw [List.map_map]
  rw [hmap]
  omega

private theorem functionAlgebraicDegree_monomialListEval_le_three
    (P : List (Finset (Fin n)))
    (hP : ∀ S ∈ P, S.card ≤ 3) :
    FABL.functionAlgebraicDegree (monomialListEval P) ≤ 3 := by
  induction P with
  | nil => simp [monomialListEval]
  | cons S P ih =>
      have hS := hP S (by simp)
      have htail : ∀ T ∈ P, T.card ≤ 3 := by
        intro T hT
        exact hP T (by simp [hT])
      change FABL.functionAlgebraicDegree
          (FABL.anfMonomial S + monomialListEval P) ≤ 3
      exact (FABL.functionAlgebraicDegree_add_le_max
          (FABL.anfMonomial S) (monomialListEval P)).trans
        (max_le
          (by simpa [FABL.functionAlgebraicDegree_anfMonomial] using hS)
          (ih htail))

private theorem monomialListEval_anfSupport_toList
    (g : BooleanFunction n) :
    monomialListEval (FABL.anfSupport (FABL.anfCoeff g)).toList = g := by
  classical
  funext x
  rw [← congrFun (FABL.anfEval_anfCoeff g) x]
  rw [monomialListEval_apply, FABL.anfEval]
  rw [Finset.sum_map_toList]
  rw [FABL.anfSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : FABL.anfCoeff g S = 0
  · simp [hS]
  · have hSone : FABL.anfCoeff g S = 1 := Fin.eq_one_of_ne_zero _ hS
    simp [hSone]

private def liftDimension (n : ℕ) : ℕ → ℕ
  | 0 => n
  | m + 1 => liftDimension (n + 2) m

@[simp] private theorem liftDimension_zero (n : ℕ) :
    liftDimension n 0 = n := rfl

@[simp] private theorem liftDimension_succ (n m : ℕ) :
    liftDimension n (m + 1) = liftDimension (n + 2) m := rfl

private theorem liftDimension_eq (n m : ℕ) :
    liftDimension n m = n + 2 * m := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
      rw [liftDimension_succ, ih]
      omega

private theorem exists_cubicWalshLift_monomialList
    (P : List (Finset (Fin n))) :
    ∃ (m : ℕ) (F : BooleanFunction (liftDimension n m)),
      FABL.functionAlgebraicDegree F ≤ 3 ∧
        walshTransform F 0 = 2 ^ m * walshTransform (monomialListEval P) 0 := by
  induction e : cubicExcess P using Nat.strong_induction_on generalizing n P with
  | h e ih =>
      by_cases hP : ∀ S ∈ P, S.card ≤ 3
      · exact ⟨0, monomialListEval P,
          functionAlgebraicDegree_monomialListEval_le_three P hP,
          by rw [pow_zero, one_mul]; rfl⟩
      · push Not at hP
        obtain ⟨S, hSP, hScard⟩ := hP
        obtain ⟨pre, post, hPsplit, _⟩ := List.eq_append_cons_of_mem hSP
        obtain ⟨A, hAS, hAcard⟩ :=
          Finset.exists_subset_card_eq (show 2 ≤ S.card by omega)
        let R := pre ++ post
        let P' := breakTerms A (S \ A) R
        have hRmeasure :
            cubicExcess R = cubicExcess pre + cubicExcess post := by
          simp [R, cubicExcess, List.map_append]
        have hPmeasure :
            cubicExcess P =
              cubicExcess pre + (S.card - 3) + cubicExcess post := by
          rw [hPsplit]
          simp [cubicExcess, List.map_append, add_assoc]
        have hdecrease : cubicExcess P' < cubicExcess P := by
          have hbreak := cubicExcess_breakTerms_lt S A R hAS hAcard hScard
          change cubicExcess P' < (S.card - 3) + cubicExcess R at hbreak
          rw [hRmeasure] at hbreak
          rw [hPmeasure]
          omega
        obtain ⟨m, F, hFdegree, hFWalsh⟩ :=
          ih (cubicExcess P') (by omega) (n := n + 2) (P := P') rfl
        refine ⟨m + 1, ?_⟩
        rw [liftDimension_succ]
        refine ⟨F, hFdegree, ?_⟩
        have hAunion : A ∪ (S \ A) = S := Finset.union_sdiff_of_subset hAS
        have hsource :
            (fun x ↦ FABL.anfMonomial A x * FABL.anfMonomial (S \ A) x +
              monomialListEval R x) = monomialListEval P := by
          funext x
          rw [FABL.anfMonomial_mul, hAunion, hPsplit]
          simp [R, monomialListEval, List.map_append]
          ac_rfl
        have hstep :
            walshTransform (monomialListEval P') 0 =
              2 * walshTransform (monomialListEval P) 0 := by
          change walshTransform
              (monomialListEval (breakTerms A (S \ A) R)) 0 = _
          rw [monomialListEval_breakTerms]
          rw [walshTransform_quadraticizationLift_zero]
          rw [hsource]
        rw [hFWalsh, hstep]
        ring

/-- Every Boolean zero-frequency Walsh coefficient is, up to a power of two,
realized by a Boolean function of algebraic degree at most three. -/
theorem exists_degree_le_three_walshTransform_zero_lift
    (g : BooleanFunction n) :
    ∃ (m : ℕ) (F : BooleanFunction (n + 2 * m)),
      FABL.functionAlgebraicDegree F ≤ 3 ∧
        walshTransform F 0 = 2 ^ m * walshTransform g 0 := by
  classical
  obtain ⟨m, F, hdegree, hWalsh⟩ :=
    exists_cubicWalshLift_monomialList
      (FABL.anfSupport (FABL.anfCoeff g)).toList
  refine ⟨m, ?_⟩
  rw [← liftDimension_eq n m]
  refine ⟨F, hdegree, ?_⟩
  rw [hWalsh, monomialListEval_anfSupport_toList]

end CryptBoolean
