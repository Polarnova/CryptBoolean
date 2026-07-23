/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity
public import CryptBoolean.Carlet.Chapter04.PropagationCriteria
public import CryptBoolean.Carlet.Chapter04.AutocorrelationIndicators
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity
public import CryptBoolean.Carlet.Chapter04.DistanceToLinearStructures
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Propagation criterion with high nonlinearity

An explicit basis of zero-autocorrelation directions for the balanced
Maitra--Kavut--Yücel seed yields a linearly equivalent function satisfying
the first propagation criterion. Complete bent extensions preserve the
criterion and the strict improvement over the odd-dimensional quadratic bound.
-/

open Finset Module
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- Thirteen independent zero-autocorrelation directions for the
Maitra--Kavut--Yücel seed. -/
def maitraKavutYucelZeroAutocorrelationBasis :
    Fin 13 → FABL.F₂Cube 13 :=
  ![FABL.f₂CubeOfFinset {0, 5},
    FABL.f₂CubeOfFinset {2, 6},
    FABL.f₂CubeOfFinset {0, 1, 2, 3, 6},
    FABL.f₂CubeOfFinset {0, 2, 3, 5, 6},
    FABL.f₂CubeOfFinset {0, 1, 4, 5, 6},
    FABL.f₂CubeOfFinset {1, 2, 4, 5, 6},
    FABL.f₂CubeOfFinset {3, 7},
    FABL.f₂CubeOfFinset {1, 3, 7},
    FABL.f₂CubeOfFinset {3, 8},
    FABL.f₂CubeOfFinset {0, 9},
    FABL.f₂CubeOfFinset {0, 10},
    FABL.f₂CubeOfFinset {0, 11},
    FABL.f₂CubeOfFinset {0, 12}]

/-- The thirteen certified directions form a basis of the binary cube. -/
theorem maitraKavutYucelZeroAutocorrelationBasis_independent :
    LinearIndependent FABL.𝔽₂ maitraKavutYucelZeroAutocorrelationBasis := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (0 : Fin 13)
  have h1 := congrFun hg (1 : Fin 13)
  have h2 := congrFun hg (2 : Fin 13)
  have h3 := congrFun hg (3 : Fin 13)
  have h4 := congrFun hg (4 : Fin 13)
  have h5 := congrFun hg (5 : Fin 13)
  have h6 := congrFun hg (6 : Fin 13)
  have h7 := congrFun hg (7 : Fin 13)
  have h8 := congrFun hg (8 : Fin 13)
  have h9 := congrFun hg (9 : Fin 13)
  have h10 := congrFun hg (10 : Fin 13)
  have h11 := congrFun hg (11 : Fin 13)
  have h12 := congrFun hg (12 : Fin 13)
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h0
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h1
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h2
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h3
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h4
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h5
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h6
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h7
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h8
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h9
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h10
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h11
  simp +decide [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    maitraKavutYucelZeroAutocorrelationBasis, FABL.f₂CubeOfFinset,
    Fin.sum_univ_succ] at h12
  fin_cases i
  · change g 0 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero,
      show (4 : FABL.𝔽₂) = 0 by decide]))
      h0 + h2 + h3 + h6 + h7 + h8 + h9 + h10 + h11 + h12
  · change g 1 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      h3 + h4 + h6 + h7 + h8
  · change g 2 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero,
      show (4 : FABL.𝔽₂) = 0 by decide]))
      h0 + h2 + h4 + h5 + h6 + h9 + h10 + h11 + h12
  · change g 3 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero,
      show (4 : FABL.𝔽₂) = 0 by decide]))
      h0 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11 + h12
  · change g 4 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h2 + h6
  · change g 5 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      h2 + h4 + h6
  · change g 6 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero,
      show (4 : FABL.𝔽₂) = 0 by decide]))
      h0 + h1 + h2 + h5 + h6 + h7 + h9 + h10 + h11 + h12
  · change g 7 = 0
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero,
      show (4 : FABL.𝔽₂) = 0 by decide]))
      h0 + h1 + h2 + h5 + h6 + h9 + h10 + h11 + h12
  · change g 8 = 0
    linear_combination (norm := norm_num) h8
  · change g 9 = 0
    linear_combination (norm := norm_num) h9
  · change g 10 = 0
    linear_combination (norm := norm_num) h10
  · change g 11 = 0
    linear_combination (norm := norm_num) h11
  · change g 12 = 0
    linear_combination (norm := norm_num) h12

private theorem booleanDerivative_booleanDirectSum_append
    {k l : ℕ} (f : BooleanFunction k) (g : BooleanFunction l)
    (a : FABL.F₂Cube k) (b : FABL.F₂Cube l) :
    FABL.booleanDerivative (booleanDirectSum f g) (Fin.append a b) =
      booleanDirectSum (FABL.booleanDerivative f a)
        (FABL.booleanDerivative g b) := by
  funext z
  let p := (Fin.appendEquiv k l).symm z
  have hz : Fin.append p.1 p.2 = z :=
    (Fin.appendEquiv k l).apply_symm_apply z
  rw [← hz]
  simp [FABL.booleanDerivative, booleanDirectSum]
  abel

/-- Autocorrelation factors over Boolean direct sums on disjoint coordinate blocks. -/
theorem autocorrelation_booleanDirectSum_append
    {k l : ℕ} (f : BooleanFunction k) (g : BooleanFunction l)
    (a : FABL.F₂Cube k) (b : FABL.F₂Cube l) :
    autocorrelation (booleanDirectSum f g) (Fin.append a b) =
      autocorrelation f a * autocorrelation g b := by
  classical
  rw [autocorrelation, booleanDerivative_booleanDirectSum_append,
    realSignView_booleanDirectSum]
  unfold FABL.bentDirectProduct
  calc
    (∑ x : FABL.F₂Cube (k + l),
        realSignView (FABL.booleanDerivative f a)
            ((Fin.appendEquiv k l).symm x).1 *
          realSignView (FABL.booleanDerivative g b)
            ((Fin.appendEquiv k l).symm x).2) =
        ∑ p : FABL.F₂Cube k × FABL.F₂Cube l,
          realSignView (FABL.booleanDerivative f a) p.1 *
            realSignView (FABL.booleanDerivative g b) p.2 := by
      exact Equiv.sum_comp (Fin.appendEquiv k l).symm
        (fun p : FABL.F₂Cube k × FABL.F₂Cube l ↦
          realSignView (FABL.booleanDerivative f a) p.1 *
            realSignView (FABL.booleanDerivative g b) p.2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_mul_sum]
      rfl

private def autocorrelationSummand {k : ℕ}
    (f : BooleanFunction k) (a x : FABL.F₂Cube k) : ℝ :=
  realSignView f x * realSignView f (x + a)

private theorem realSignView_flipOn {k : ℕ}
    (f : BooleanFunction k) (P : Finset (FABL.F₂Cube k))
    (x : FABL.F₂Cube k) :
    realSignView (flipOn f P) x =
      if x ∈ P then -realSignView f x else realSignView f x := by
  by_cases hx : x ∈ P
  · rw [if_pos hx]
    change FABL.signValue (FABL.signEncode (f x + if x ∈ P then 1 else 0)) =
      -FABL.signValue (FABL.signEncode (f x))
    rw [if_pos hx]
    rw [FABL.signValue_signEncode_eq_binarySign,
      FABL.signValue_signEncode_eq_binarySign, AddChar.map_add_eq_mul,
      FABL.binarySign_one]
    ring
  · rw [if_neg hx]
    change FABL.signValue (FABL.signEncode (f x + if x ∈ P then 1 else 0)) =
      FABL.signValue (FABL.signEncode (f x))
    rw [if_neg hx, add_zero]

private theorem autocorrelationSummand_add_self {k : ℕ}
    (f : BooleanFunction k) (a x : FABL.F₂Cube k) :
    autocorrelationSummand f a (x + a) = autocorrelationSummand f a x := by
  rw [autocorrelationSummand, autocorrelationSummand, add_assoc,
    ZModModule.add_self, add_zero, mul_comm]

private theorem autocorrelation_flipOn_of_isolated {k : ℕ}
    (f : BooleanFunction k) (P : Finset (FABL.F₂Cube k))
    (a : FABL.F₂Cube k)
    (hisolated : ∀ p ∈ P, p + a ∉ P) :
    autocorrelation (flipOn f P) a =
      autocorrelation f a -
        4 * ∑ p ∈ P, autocorrelationSummand f a p := by
  have hpoint (x : FABL.F₂Cube k) :
      realSignView (FABL.booleanDerivative (flipOn f P) a) x =
        autocorrelationSummand f a x -
          2 * (if x ∈ P then autocorrelationSummand f a x else 0) -
          2 * (if x + a ∈ P then autocorrelationSummand f a x else 0) := by
    rw [realSignView_booleanDerivative, realSignView_flipOn,
      realSignView_flipOn]
    by_cases hx : x ∈ P
    · have hxa := hisolated x hx
      simp [hx, hxa, autocorrelationSummand]
      ring
    · by_cases hxa : x + a ∈ P
      · simp [hx, hxa, autocorrelationSummand]
        ring
      · simp [hx, hxa, autocorrelationSummand]
  have htranslate :
      (∑ x : FABL.F₂Cube k,
          if x + a ∈ P then autocorrelationSummand f a x else 0) =
        ∑ x : FABL.F₂Cube k,
          if x ∈ P then autocorrelationSummand f a x else 0 := by
    rw [← Equiv.sum_comp (Equiv.addRight a)]
    apply Finset.sum_congr rfl
    intro x _hx
    change (if (x + a) + a ∈ P then
      autocorrelationSummand f a (x + a) else 0) =
        if x ∈ P then autocorrelationSummand f a x else 0
    rw [add_assoc, ZModModule.add_self, add_zero]
    rw [autocorrelationSummand_add_self]
  have hfilter :
      (∑ x : FABL.F₂Cube k,
          if x ∈ P then autocorrelationSummand f a x else 0) =
        ∑ p ∈ P, autocorrelationSummand f a p := by
    simp
  unfold autocorrelation
  rw [show (∑ x : FABL.F₂Cube k,
      realSignView (FABL.booleanDerivative (flipOn f P) a) x) =
      ∑ x : FABL.F₂Cube k,
        (autocorrelationSummand f a x -
          2 * (if x ∈ P then autocorrelationSummand f a x else 0) -
          2 * (if x + a ∈ P then autocorrelationSummand f a x else 0)) by
    apply Finset.sum_congr rfl
    intro x _hx
    exact hpoint x]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, htranslate, hfilter]
  rw [show (∑ x : FABL.F₂Cube k, autocorrelationSummand f a x) =
      ∑ x, realSignView (FABL.booleanDerivative f a) x by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [realSignView_booleanDerivative]
    rfl]
  ring

private def maitraKavutYucelIsolatedDirectionCertificate
    (a : FABL.F₂Cube 13) : Bool :=
  MaitraKavutYucel.flipPointList13.all fun p ↦
    decide (p + a ∉ MaitraKavutYucel.flipPoints13)

private theorem maitraKavutYucelIsolatedDirectionCertificate_sound
    (a : FABL.F₂Cube 13)
    (hcertificate : maitraKavutYucelIsolatedDirectionCertificate a = true) :
    ∀ p ∈ MaitraKavutYucel.flipPoints13,
      p + a ∉
        MaitraKavutYucel.flipPoints13 := by
  intro p hp
  have hpList : p ∈ MaitraKavutYucel.flipPointList13 := by
    simpa [MaitraKavutYucel.flipPoints13] using hp
  exact of_decide_eq_true
    (List.all_eq_true.mp hcertificate p hpList)

private theorem maitraKavutYucelIsolatedDirectionCertificate_zero :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 0) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_one :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 1) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_two :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 2) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_three :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 3) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_four :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 4) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_five :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 5) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_six :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 6) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_seven :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 7) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_eight :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 8) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_nine :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 9) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_ten :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 10) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_eleven :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 11) = true := by decide

private theorem maitraKavutYucelIsolatedDirectionCertificate_twelve :
    maitraKavutYucelIsolatedDirectionCertificate
      (maitraKavutYucelZeroAutocorrelationBasis 12) = true := by decide

private theorem maitraKavutYucelZeroAutocorrelationBasis_isolated (i : Fin 13) :
    ∀ p ∈ MaitraKavutYucel.flipPoints13,
      p + maitraKavutYucelZeroAutocorrelationBasis i ∉
        MaitraKavutYucel.flipPoints13 := by
  fin_cases i
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_zero
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_one
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_two
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_three
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_four
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_five
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_six
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_seven
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_eight
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_nine
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_ten
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_eleven
  · exact maitraKavutYucelIsolatedDirectionCertificate_sound _
      maitraKavutYucelIsolatedDirectionCertificate_twelve

private def maitraKavutYucelFlipCorrectionInt
    (a : FABL.F₂Cube 13) : ℤ :=
  ∑ p ∈ MaitraKavutYucel.flipPoints13,
    bitSignInt (FABL.booleanDerivative MaitraKavutYucel.initialFunction13 a p)

private theorem autocorrelationSummand_eq_bitSignInt_cast
    {k : ℕ} (f : BooleanFunction k) (a x : FABL.F₂Cube k) :
    autocorrelationSummand f a x =
      (bitSignInt (FABL.booleanDerivative f a x) : ℝ) := by
  rw [autocorrelationSummand, ← realSignView_booleanDerivative, bitSignInt_cast]
  exact FABL.signValue_signEncode_eq_binarySign _

private theorem maitraKavutYucelFlipCorrection_eq_cast
    (a : FABL.F₂Cube 13) :
    (∑ p ∈ MaitraKavutYucel.flipPoints13,
      autocorrelationSummand MaitraKavutYucel.initialFunction13
        a p) = (maitraKavutYucelFlipCorrectionInt a : ℝ) := by
  rw [maitraKavutYucelFlipCorrectionInt, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact autocorrelationSummand_eq_bitSignInt_cast _ _ _

private theorem maitraKavutYucelFlipCorrectionInt_zero :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 0) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_one :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 1) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_two :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 2) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_three :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 3) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_four :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 4) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_five :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 5) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_six :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 6) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_seven :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 7) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_eight :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 8) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_nine :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 9) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_ten :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 10) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_eleven :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 11) = 0 := by decide

private theorem maitraKavutYucelFlipCorrectionInt_twelve :
    maitraKavutYucelFlipCorrectionInt
      (maitraKavutYucelZeroAutocorrelationBasis 12) = 0 := by decide

private theorem maitraKavutYucelZeroAutocorrelationBasis_flipCorrection
    (i : Fin 13) :
    (∑ p ∈ MaitraKavutYucel.flipPoints13,
      autocorrelationSummand MaitraKavutYucel.initialFunction13
        (maitraKavutYucelZeroAutocorrelationBasis i) p) = 0 := by
  rw [maitraKavutYucelFlipCorrection_eq_cast]
  fin_cases i
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_zero
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_one
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_two
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_three
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_four
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_five
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_six
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_seven
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_eight
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_nine
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_ten
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_eleven
  · simpa [maitraKavutYucelZeroAutocorrelationBasis] using
      congrArg (fun z : ℤ ↦ (z : ℝ)) maitraKavutYucelFlipCorrectionInt_twelve

private def fastWeight : (k : ℕ) → BooleanFunction k → ℕ
  | 0, f => if f 0 = 1 then 1 else 0
  | k + 1, f =>
      fastWeight k (fun x ↦ f (Fin.cons 0 x)) +
        fastWeight k (fun x ↦ f (Fin.cons 1 x))

private theorem fastWeight_eq_sum (k : ℕ) (f : BooleanFunction k) :
    fastWeight k f = ∑ x, if f x = 1 then 1 else 0 := by
  induction k with
  | zero =>
      let c := f 0
      have hf : f = fun _ ↦ c := by
        funext x
        simp only [c]
        rw [Subsingleton.elim x 0]
      rw [hf]
      simp [fastWeight]
  | succ k ih =>
      rw [fastWeight, ih, ih]
      rw [← Equiv.sum_comp (Fin.consEquiv
        (fun _ : Fin (k + 1) ↦ FABL.𝔽₂)), Fintype.sum_prod_type]
      change (∑ b : FABL.𝔽₂, ∑ x : FABL.F₂Cube k,
        (if f (Fin.cons b x) = 1 then 1 else 0)) = _
      rw [show (Finset.univ : Finset FABL.𝔽₂) = {0, 1} by rfl]
      simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
        not_false_eq_true, Finset.sum_singleton]
      change
        ((∑ x, if f (Fin.cons 0 x) = 1 then 1 else 0) +
          ∑ x, if f (Fin.cons 1 x) = 1 then 1 else 0) = _
      rfl

private theorem hammingWeight_eq_fastWeight
    (k : ℕ) (f : BooleanFunction k) :
    hammingWeight f = fastWeight k f := by
  rw [hammingWeight_eq_card_support, fastWeight_eq_sum, ← Finset.sum_filter]
  simp [support, FABL.f₂OneSupport]

private theorem seed33_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 33)) = 256 := by decide
private theorem seed68_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 68)) = 256 := by decide
private theorem seed79_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 79)) = 256 := by decide
private theorem seed109_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 109)) = 256 := by decide
private theorem seed115_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 115)) = 256 := by decide
private theorem seed118_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 118)) = 256 := by decide
private theorem seed136_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 136)) = 256 := by decide
private theorem seed138_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 138)) = 256 := by decide
private theorem seed264_certificate :
    fastWeight 9 (FABL.booleanDerivative
      MaitraKavutYucel.shiftedSeedFunction9 (f₂CubeOfNat 9 264)) = 256 := by decide
private theorem bent1_certificate :
    fastWeight 4 (FABL.booleanDerivative
      MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 1)) = 8 := by decide
private theorem bent2_certificate :
    fastWeight 4 (FABL.booleanDerivative
      MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 2)) = 8 := by decide
private theorem bent4_certificate :
    fastWeight 4 (FABL.booleanDerivative
      MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 4)) = 8 := by decide
private theorem bent8_certificate :
    fastWeight 4 (FABL.booleanDerivative
      MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 8)) = 8 := by decide

private def maitraKavutYucelZeroAutocorrelationBasisNatIndex : Fin 13 → ℕ :=
  ![33, 68, 79, 109, 115, 118, 136, 138, 264, 513, 1025, 2049, 4097]

private theorem maitraKavutYucelZeroAutocorrelationBasis_eq_f₂CubeOfNat
    (i : Fin 13) :
    maitraKavutYucelZeroAutocorrelationBasis i =
      f₂CubeOfNat 13 (maitraKavutYucelZeroAutocorrelationBasisNatIndex i) := by
  fin_cases i <;> decide

private theorem direction33_append : f₂CubeOfNat 13 33 =
    Fin.append (f₂CubeOfNat 9 33) (0 : FABL.F₂Cube 4) := by decide
private theorem direction68_append : f₂CubeOfNat 13 68 =
    Fin.append (f₂CubeOfNat 9 68) (0 : FABL.F₂Cube 4) := by decide
private theorem direction79_append : f₂CubeOfNat 13 79 =
    Fin.append (f₂CubeOfNat 9 79) (0 : FABL.F₂Cube 4) := by decide
private theorem direction109_append : f₂CubeOfNat 13 109 =
    Fin.append (f₂CubeOfNat 9 109) (0 : FABL.F₂Cube 4) := by decide
private theorem direction115_append : f₂CubeOfNat 13 115 =
    Fin.append (f₂CubeOfNat 9 115) (0 : FABL.F₂Cube 4) := by decide
private theorem direction118_append : f₂CubeOfNat 13 118 =
    Fin.append (f₂CubeOfNat 9 118) (0 : FABL.F₂Cube 4) := by decide
private theorem direction136_append : f₂CubeOfNat 13 136 =
    Fin.append (f₂CubeOfNat 9 136) (0 : FABL.F₂Cube 4) := by decide
private theorem direction138_append : f₂CubeOfNat 13 138 =
    Fin.append (f₂CubeOfNat 9 138) (0 : FABL.F₂Cube 4) := by decide
private theorem direction264_append : f₂CubeOfNat 13 264 =
    Fin.append (f₂CubeOfNat 9 264) (0 : FABL.F₂Cube 4) := by decide
private theorem direction513_append : f₂CubeOfNat 13 513 =
    Fin.append (f₂CubeOfNat 9 1) (f₂CubeOfNat 4 1) := by decide
private theorem direction1025_append : f₂CubeOfNat 13 1025 =
    Fin.append (f₂CubeOfNat 9 1) (f₂CubeOfNat 4 2) := by decide
private theorem direction2049_append : f₂CubeOfNat 13 2049 =
    Fin.append (f₂CubeOfNat 9 1) (f₂CubeOfNat 4 4) := by decide
private theorem direction4097_append : f₂CubeOfNat 13 4097 =
    Fin.append (f₂CubeOfNat 9 1) (f₂CubeOfNat 4 8) := by decide

private theorem bentAutocorrelation1 :
    autocorrelation MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 1) = 0 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, bent1_certificate]
  norm_num

private theorem bentAutocorrelation2 :
    autocorrelation MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 2) = 0 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, bent2_certificate]
  norm_num

private theorem bentAutocorrelation4 :
    autocorrelation MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 4) = 0 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, bent4_certificate]
  norm_num

private theorem bentAutocorrelation8 :
    autocorrelation MaitraKavutYucel.bentFunction4 (f₂CubeOfNat 4 8) = 0 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, bent8_certificate]
  norm_num

private theorem initialAutocorrelation33 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 33) = 0 := by
  rw [direction33_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed33_certificate]
  norm_num

private theorem initialAutocorrelation68 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 68) = 0 := by
  rw [direction68_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed68_certificate]
  norm_num

private theorem initialAutocorrelation79 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 79) = 0 := by
  rw [direction79_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed79_certificate]
  norm_num

private theorem initialAutocorrelation109 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 109) = 0 := by
  rw [direction109_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed109_certificate]
  norm_num

private theorem initialAutocorrelation115 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 115) = 0 := by
  rw [direction115_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed115_certificate]
  norm_num

private theorem initialAutocorrelation118 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 118) = 0 := by
  rw [direction118_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed118_certificate]
  norm_num

private theorem initialAutocorrelation136 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 136) = 0 := by
  rw [direction136_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed136_certificate]
  norm_num

private theorem initialAutocorrelation138 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 138) = 0 := by
  rw [direction138_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed138_certificate]
  norm_num

private theorem initialAutocorrelation264 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 264) = 0 := by
  rw [direction264_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append,
    autocorrelation_eq_two_pow_sub_two_derivative_weight,
    hammingWeight_eq_fastWeight, seed264_certificate]
  norm_num

private theorem initialAutocorrelation513 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 513) = 0 := by
  rw [direction513_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append, bentAutocorrelation1]
  norm_num

private theorem initialAutocorrelation1025 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 1025) = 0 := by
  rw [direction1025_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append, bentAutocorrelation2]
  norm_num

private theorem initialAutocorrelation2049 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 2049) = 0 := by
  rw [direction2049_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append, bentAutocorrelation4]
  norm_num

private theorem initialAutocorrelation4097 :
    autocorrelation MaitraKavutYucel.initialFunction13 (f₂CubeOfNat 13 4097) = 0 := by
  rw [direction4097_append, MaitraKavutYucel.initialFunction13,
    autocorrelation_booleanDirectSum_append, bentAutocorrelation8]
  norm_num

private theorem initialAutocorrelation_basisNatIndex (i : Fin 13) :
    autocorrelation MaitraKavutYucel.initialFunction13
      (f₂CubeOfNat 13 (maitraKavutYucelZeroAutocorrelationBasisNatIndex i)) = 0 := by
  fin_cases i
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation33
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation68
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation79
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation109
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation115
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation118
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation136
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation138
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation264
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation513
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation1025
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation2049
  · simpa [maitraKavutYucelZeroAutocorrelationBasisNatIndex] using
      initialAutocorrelation4097

private theorem maitraKavutYucelInitialAutocorrelation_zero (i : Fin 13) :
    autocorrelation MaitraKavutYucel.initialFunction13
      (maitraKavutYucelZeroAutocorrelationBasis i) = 0 := by
  rw [maitraKavutYucelZeroAutocorrelationBasis_eq_f₂CubeOfNat]
  exact initialAutocorrelation_basisNatIndex i

private theorem maitraKavutYucelZeroAutocorrelationBasis_zero (i : Fin 13) :
    autocorrelation maitraKavutYucelFunction13
      (maitraKavutYucelZeroAutocorrelationBasis i) = 0 := by
  rw [maitraKavutYucelFunction13,
    autocorrelation_flipOn_of_isolated
      MaitraKavutYucel.initialFunction13 MaitraKavutYucel.flipPoints13
      (maitraKavutYucelZeroAutocorrelationBasis i)
      (maitraKavutYucelZeroAutocorrelationBasis_isolated i),
    maitraKavutYucelInitialAutocorrelation_zero i,
    maitraKavutYucelZeroAutocorrelationBasis_flipCorrection i]
  norm_num

/-- The linear input reindexing determined by the certified
zero-autocorrelation basis. -/
noncomputable def maitraKavutYucelPCOneReindex :
    FABL.F₂Cube 13 ≃ₗ[FABL.𝔽₂] FABL.F₂Cube 13 :=
  (Pi.basisFun FABL.𝔽₂ (Fin 13)).equiv
    (basisOfLinearIndependentOfCardEqFinrank'
      maitraKavutYucelZeroAutocorrelationBasis
      maitraKavutYucelZeroAutocorrelationBasis_independent (by
        simp [Module.finrank_fintype_fun_eq_card]))
    (Equiv.refl (Fin 13))

private theorem maitraKavutYucelPCOneReindex_single (i : Fin 13) :
    maitraKavutYucelPCOneReindex (FABL.f₂CubeOfFinset {i}) =
      maitraKavutYucelZeroAutocorrelationBasis i := by
  have hsingle : FABL.f₂CubeOfFinset {i} =
      (Pi.basisFun FABL.𝔽₂ (Fin 13)) i := by
    ext j
    simp [FABL.f₂CubeOfFinset, Pi.single_apply]
  rw [hsingle]
  unfold maitraKavutYucelPCOneReindex
  rw [Basis.equiv_apply]
  simp

/-- The reindexed thirteen-variable seed. -/
noncomputable def maitraKavutYucelPCOneFunction13 : BooleanFunction 13 :=
  maitraKavutYucelFunction13 ∘ maitraKavutYucelPCOneReindex

private theorem f₂Support_nonempty_of_ne_zero
    (u : FABL.F₂Cube n) (hu : u ≠ 0) :
    (FABL.f₂Support u).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hsupport
  apply hu
  apply (FABL.f₂CubeEquivFinset n).injective
  change FABL.f₂Support u = FABL.f₂Support (0 : FABL.F₂Cube n)
  rw [hsupport]
  ext i
  simp [FABL.f₂Support]

/-- The reindexed thirteen-variable seed satisfies `PC(1)`. -/
theorem satisfiesPropagationCriterion_one_maitraKavutYucelPCOneFunction13 :
    SatisfiesPropagationCriterion 1 maitraKavutYucelPCOneFunction13 := by
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero]
  intro a ha hweight
  have hcard : (FABL.f₂Support a).card = 1 :=
    Nat.le_antisymm hweight
      (Finset.card_pos.mpr (f₂Support_nonempty_of_ne_zero a ha))
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have ha_single : a = FABL.f₂CubeOfFinset {i} := by
    apply (FABL.f₂CubeEquivFinset 13).injective
    simpa [hi] using
      ((FABL.f₂CubeEquivFinset 13).right_inv ({i} : Finset (Fin 13))).symm
  subst a
  rw [maitraKavutYucelPCOneFunction13]
  change autocorrelation
    (maitraKavutYucelFunction13 ∘ maitraKavutYucelPCOneReindex.toAffineEquiv)
      (FABL.f₂CubeOfFinset {i}) = 0
  rw [
    autocorrelation_comp_affineEquiv maitraKavutYucelFunction13
      maitraKavutYucelPCOneReindex.toAffineEquiv]
  change autocorrelation maitraKavutYucelFunction13
    (maitraKavutYucelPCOneReindex (FABL.f₂CubeOfFinset {i})) = 0
  rw [maitraKavutYucelPCOneReindex_single]
  exact maitraKavutYucelZeroAutocorrelationBasis_zero i

/-- Linear reindexing preserves the seed's nonlinearity. -/
theorem nonlinearity_maitraKavutYucelPCOneFunction13 :
    nonlinearity maitraKavutYucelPCOneFunction13 = 4036 := by
  rw [maitraKavutYucelPCOneFunction13]
  change nonlinearity
    (maitraKavutYucelFunction13 ∘ maitraKavutYucelPCOneReindex.toAffineEquiv) = 4036
  rw [
    nonlinearity_comp_affineEquiv maitraKavutYucelFunction13
      maitraKavutYucelPCOneReindex.toAffineEquiv,
    nonlinearity_maitraKavutYucelFunction13]

private theorem card_f₂Support_left_le_append
    {k l : ℕ} (a : FABL.F₂Cube k) (b : FABL.F₂Cube l) :
    (FABL.f₂Support a).card ≤
      (FABL.f₂Support (Fin.append a b)).card := by
  apply Finset.card_le_card_of_injOn (Fin.castAdd l)
  · intro i hi
    exact (FABL.mem_f₂Support _ _).2 (by
      rw [Fin.append_left]
      exact (FABL.mem_f₂Support _ _).1 hi)
  · exact (Fin.castAdd_injective k l).injOn

private theorem card_f₂Support_right_le_append
    {k l : ℕ} (a : FABL.F₂Cube k) (b : FABL.F₂Cube l) :
    (FABL.f₂Support b).card ≤
      (FABL.f₂Support (Fin.append a b)).card := by
  apply Finset.card_le_card_of_injOn (Fin.natAdd k)
  · intro i hi
    exact (FABL.mem_f₂Support _ _).2 (by
      rw [Fin.append_right]
      exact (FABL.mem_f₂Support _ _).1 hi)
  · exact (Fin.natAdd_injective l k).injOn

/-- Boolean direct sums preserve `PC(1)`. -/
theorem satisfiesPropagationCriterion_one_booleanDirectSum
    {k l : ℕ} (f : BooleanFunction k) (g : BooleanFunction l)
    (hf : SatisfiesPropagationCriterion 1 f)
    (hg : SatisfiesPropagationCriterion 1 g) :
    SatisfiesPropagationCriterion 1 (booleanDirectSum f g) := by
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero]
  intro d hd hweight
  let p := (Fin.appendEquiv k l).symm d
  have hp : Fin.append p.1 p.2 = d :=
    (Fin.appendEquiv k l).apply_symm_apply d
  rw [← hp, autocorrelation_booleanDirectSum_append]
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero] at hf hg
  by_cases hleft : p.1 = 0
  · have hright : p.2 ≠ 0 := by
      intro hright
      apply hd
      rw [← hp, hleft, hright]
      funext i
      exact Fin.addCases (fun j ↦ by simp) (fun j ↦ by simp) i
    have hrightWeight : (FABL.f₂Support p.2).card ≤ 1 :=
      (card_f₂Support_right_le_append p.1 p.2).trans (by
        simpa [hp] using hweight)
    rw [hg p.2 hright hrightWeight, mul_zero]
  · have hleftWeight : (FABL.f₂Support p.1).card ≤ 1 :=
      (card_f₂Support_left_le_append p.1 p.2).trans (by
        simpa [hp] using hweight)
    rw [hf p.1 hleft hleftWeight, zero_mul]

private theorem satisfiesPropagationCriterion_one_innerProductModTwoBit
    (m : ℕ) :
    SatisfiesPropagationCriterion 1
      (FABL.innerProductModTwoBit : BooleanFunction (m + m)) := by
  rw [satisfiesPropagationCriterion_iff_autocorrelation_eq_zero]
  intro a ha _hweight
  have hbent :
      IsBent (FABL.innerProductModTwoBit : BooleanFunction (m + m)) := by
    change FABL.IsBent (FABL.innerProductModTwo m)
    exact FABL.isBent_innerProductModTwo m
  have hindicator :
      absoluteIndicator
          (FABL.innerProductModTwoBit : BooleanFunction (m + m)) = 0 :=
    (absoluteIndicator_eq_zero_iff_isBent _).2 hbent
  have hle := abs_autocorrelation_le_absoluteIndicator
    (FABL.innerProductModTwoBit : BooleanFunction (m + m)) ha
  rw [hindicator] at hle
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- Complete inner-product bent extensions preserve `PC(1)`. -/
theorem satisfiesPropagationCriterion_one_completeBentExtension
    {k : ℕ} (f : BooleanFunction k) (m : ℕ)
    (hf : SatisfiesPropagationCriterion 1 f) :
    SatisfiesPropagationCriterion 1 (completeBentExtension f m) := by
  exact satisfiesPropagationCriterion_one_booleanDirectSum
    f FABL.innerProductModTwoBit hf
      (satisfiesPropagationCriterion_one_innerProductModTwoBit m)

/-- The `PC(1)` Maitra--Kavut--Yücel seed completed by `m` inner-product
bent pairs. -/
noncomputable def maitraKavutYucelPCOneBentExtension (m : ℕ) :
    BooleanFunction (13 + (m + m)) :=
  completeBentExtension maitraKavutYucelPCOneFunction13 m

/-- Every complete bent extension of the reindexed seed satisfies `PC(1)`. -/
theorem satisfiesPropagationCriterion_one_maitraKavutYucelPCOneBentExtension
    (m : ℕ) :
    SatisfiesPropagationCriterion 1
      (maitraKavutYucelPCOneBentExtension m) := by
  exact satisfiesPropagationCriterion_one_completeBentExtension
    maitraKavutYucelPCOneFunction13 m
      satisfiesPropagationCriterion_one_maitraKavutYucelPCOneFunction13

private theorem maxWalshMagnitude_maitraKavutYucelPCOneFunction13 :
    maxWalshMagnitude maitraKavutYucelPCOneFunction13 = 120 := by
  have hrelation :=
    two_mul_nonlinearity_add_maxWalshMagnitude
      maitraKavutYucelPCOneFunction13
  rw [nonlinearity_maitraKavutYucelPCOneFunction13] at hrelation
  norm_num at hrelation ⊢
  omega

/-- The exact maximum Walsh magnitude of every complete bent extension. -/
theorem maxWalshMagnitude_maitraKavutYucelPCOneBentExtension
    (m : ℕ) :
    maxWalshMagnitude (maitraKavutYucelPCOneBentExtension m) =
      120 * 2 ^ m := by
  rw [maitraKavutYucelPCOneBentExtension,
    maxWalshMagnitude_completeBentExtension,
    maxWalshMagnitude_maitraKavutYucelPCOneFunction13]

/-- The exact nonlinearity of every complete bent extension. -/
theorem nonlinearity_maitraKavutYucelPCOneBentExtension
    (m : ℕ) :
    nonlinearity (maitraKavutYucelPCOneBentExtension m) =
      2 ^ (12 + (m + m)) - 60 * 2 ^ m := by
  have hrelation := two_mul_nonlinearity_add_maxWalshMagnitude
    (maitraKavutYucelPCOneBentExtension m)
  rw [maxWalshMagnitude_maitraKavutYucelPCOneBentExtension] at hrelation
  have hpow : 2 ^ (13 + (m + m)) = 2 * 2 ^ (12 + (m + m)) := by
    rw [show 13 + (m + m) = (12 + (m + m)) + 1 by omega, pow_succ]
    ring
  rw [hpow] at hrelation
  omega

/-- The complete bent extensions strictly exceed the odd-dimensional
quadratic nonlinearity bound. -/
theorem quadraticBound_lt_nonlinearity_maitraKavutYucelPCOneBentExtension
    (m : ℕ) :
    2 ^ (12 + (m + m)) - 2 ^ (6 + m) <
      nonlinearity (maitraKavutYucelPCOneBentExtension m) := by
  rw [nonlinearity_maitraKavutYucelPCOneBentExtension]
  have hsmall : 60 * 2 ^ m < 64 * 2 ^ m := by
    have hpositive : 0 < 2 ^ m := Nat.pow_pos (by omega)
    omega
  have hsix : 2 ^ (6 + m) = 64 * 2 ^ m := by
    rw [pow_add]
    norm_num
  have hlarge : 64 * 2 ^ m ≤ 2 ^ (12 + (m + m)) := by
    rw [← hsix]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [hsix]
  exact Nat.sub_lt_sub_left (hsmall.trans_le hlarge) hsmall

/-- For every odd dimension at least thirteen, some Boolean function satisfies
`PC(1)` and has nonlinearity strictly above the quadratic bound. -/
theorem exists_pc_one_nonlinearity_gt_quadraticBound_of_odd
    {n : ℕ} (hn : Odd n) (hn13 : 13 ≤ n) :
    ∃ f : BooleanFunction n, SatisfiesPropagationCriterion 1 f ∧
      2 ^ (n - 1) - 2 ^ ((n - 1) / 2) < nonlinearity f := by
  obtain ⟨k, hk⟩ := hn
  have hk6 : 6 ≤ k := by omega
  let m := k - 6
  have hnform : n = 13 + (m + m) := by
    dsimp [m]
    omega
  rw [hnform]
  refine ⟨maitraKavutYucelPCOneBentExtension m,
    satisfiesPropagationCriterion_one_maitraKavutYucelPCOneBentExtension m, ?_⟩
  have hsub : 13 + (m + m) - 1 = 12 + (m + m) := by omega
  have hhalf : (12 + (m + m)) / 2 = 6 + m := by omega
  simpa only [hsub, hhalf] using
    quadraticBound_lt_nonlinearity_maitraKavutYucelPCOneBentExtension m

end CryptBoolean
