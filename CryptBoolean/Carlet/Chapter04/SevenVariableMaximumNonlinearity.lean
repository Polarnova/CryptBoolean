/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.DegreeRepairNonlinearity
public import FABL.Chapter06.F₂Polynomials.Interpolation

/-!
# Seven-variable maximum nonlinearity

The point-indicator quotient reduction in Hou's proof of the covering radius
of the first-order Reed--Muller code in dimension seven.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private theorem two_eq_zero_f₂ : (2 : FABL.𝔽₂) = 0 :=
  ZMod.natCast_self 2

private theorem anfCoeff_pointIndicator
    (a : FABL.F₂Cube n) (S : Finset (Fin n)) :
    FABL.anfCoeff (FABL.f₂PointIndicator a) S =
      if FABL.f₂Support a ⊆ S then 1 else 0 := by
  classical
  rw [FABL.anfCoeff]
  have hcubeeq (T : Finset (Fin n)) :
      FABL.f₂CubeOfFinset T = a ↔ T = FABL.f₂Support a := by
    constructor
    · intro h
      calc
        T = FABL.f₂Support (FABL.f₂CubeOfFinset T) := by
          simpa using (FABL.f₂CubeEquivFinset n).apply_symm_apply T |>.symm
        _ = FABL.f₂Support a := congrArg FABL.f₂Support h
    · intro h
      subst T
      simpa using (FABL.f₂CubeEquivFinset n).symm_apply_apply a
  simp_rw [FABL.f₂PointIndicator_eq_ite, hcubeeq]
  by_cases ha : FABL.f₂Support a ⊆ S
  · rw [if_pos ha]
    have hmem : FABL.f₂Support a ∈ S.powerset := by simpa
    simp [hmem]
  · rw [if_neg ha]
    have hnotmem : FABL.f₂Support a ∉ S.powerset := by simpa
    simp [hnotmem]

private theorem anfCoeff_pointIndicator_univ
    (a : FABL.F₂Cube n) :
    FABL.anfCoeff (FABL.f₂PointIndicator a) Finset.univ = 1 := by
  rw [anfCoeff_pointIndicator]
  simp

private theorem anfCoeff_pointIndicator_erase
    (a : FABL.F₂Cube n) (i : Fin n) :
    FABL.anfCoeff (FABL.f₂PointIndicator a) (Finset.univ.erase i) = 1 + a i := by
  rw [anfCoeff_pointIndicator]
  by_cases hai : a i = 0
  · have hsub : FABL.f₂Support a ⊆ Finset.univ.erase i := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hji
      subst j
      exact (FABL.mem_f₂Support a i).mp hj hai
    rw [if_pos hsub, hai]
    norm_num [two_eq_zero_f₂]
  · have hi : i ∈ FABL.f₂Support a := (FABL.mem_f₂Support a i).2 hai
    have hnot : ¬FABL.f₂Support a ⊆ Finset.univ.erase i := by
      intro hsub
      exact (Finset.mem_erase.mp (hsub hi)).1 rfl
    have hai1 : a i = 1 := Fin.eq_one_of_ne_zero _ hai
    rw [if_neg hnot, hai1]
    ring_nf
    simp only [two_eq_zero_f₂]

private theorem finset_fin_seven_eq_univ_or_erase_of_five_lt_card
    (S : Finset (Fin 7)) (hS : 5 < S.card) :
    S = Finset.univ ∨ ∃ i : Fin 7, S = Finset.univ.erase i := by
  have hcard : S.card ≤ 7 := by simpa using Finset.card_le_univ S
  have hcases : S.card = 6 ∨ S.card = 7 := by omega
  rcases hcases with h | h
  · right
    have hcompl : Sᶜ.card = 1 := by
      rw [Finset.card_compl]
      norm_num [h]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
    refine ⟨i, ?_⟩
    ext j
    have hcompmem : j ∈ Sᶜ ↔ j = i := by rw [hi]; simp
    by_cases hji : j = i
    · subst j
      have : i ∉ S := by
        intro hiS
        have : i ∉ Sᶜ := by simp [hiS]
        exact this (by simp [hi])
      simp [this]
    · have : j ∈ S := by
        by_contra hjS
        have : j ∈ Sᶜ := by simp [hjS]
        exact hji (hcompmem.mp this)
      simp [this, hji]
  · left
    exact Finset.eq_univ_of_card S (by simpa using h)

private noncomputable def degreeSixProfile (f : BooleanFunction 7) : FABL.F₂Cube 7 :=
  fun i ↦ FABL.anfCoeff f (Finset.univ.erase i)

private noncomputable def oddPoint (f : BooleanFunction 7) : FABL.F₂Cube 7 :=
  fun i ↦ 1 + degreeSixProfile f i

private theorem add_oddPoint_degree_le_five
    (f : BooleanFunction 7)
    (htop : FABL.anfCoeff f Finset.univ = 1) :
    FABL.functionAlgebraicDegree
      (f + FABL.f₂PointIndicator (oddPoint f)) ≤ 5 := by
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hcard
  have hcard' : 5 < S.card := Nat.lt_of_not_ge hcard
  rcases finset_fin_seven_eq_univ_or_erase_of_five_lt_card S hcard' with
      rfl | ⟨i, rfl⟩
  · apply hcoeff
    rw [FABL.anfCoeff_add]
    change FABL.anfCoeff f Finset.univ +
      FABL.anfCoeff (FABL.f₂PointIndicator (oddPoint f)) Finset.univ = 0
    rw [htop, anfCoeff_pointIndicator_univ]
    ring_nf
    simp only [two_eq_zero_f₂]
  · apply hcoeff
    rw [FABL.anfCoeff_add]
    change FABL.anfCoeff f (Finset.univ.erase i) +
      FABL.anfCoeff (FABL.f₂PointIndicator (oddPoint f))
        (Finset.univ.erase i) = 0
    rw [anfCoeff_pointIndicator_erase]
    simp only [oddPoint, degreeSixProfile]
    ring_nf
    simp only [two_eq_zero_f₂, zero_add, mul_zero]

private theorem add_two_points_degree_le_five
    (f : BooleanFunction 7)
    (htop : FABL.anfCoeff f Finset.univ = 0) :
    FABL.functionAlgebraicDegree
      (f + FABL.f₂PointIndicator 0 +
        FABL.f₂PointIndicator (degreeSixProfile f)) ≤ 5 := by
  rw [FABL.functionAlgebraicDegree, FABL.algebraicDegree_le_iff]
  intro S hcoeff
  by_contra hcard
  have hcard' : 5 < S.card := Nat.lt_of_not_ge hcard
  rcases finset_fin_seven_eq_univ_or_erase_of_five_lt_card S hcard' with
      rfl | ⟨i, rfl⟩
  · apply hcoeff
    rw [FABL.anfCoeff_add, FABL.anfCoeff_add]
    change (FABL.anfCoeff f Finset.univ +
      FABL.anfCoeff (FABL.f₂PointIndicator 0) Finset.univ) +
      FABL.anfCoeff (FABL.f₂PointIndicator (degreeSixProfile f))
        Finset.univ = 0
    rw [htop, anfCoeff_pointIndicator_univ,
      anfCoeff_pointIndicator_univ]
    ring_nf
    simp only [two_eq_zero_f₂]
  · apply hcoeff
    rw [FABL.anfCoeff_add, FABL.anfCoeff_add]
    change (FABL.anfCoeff f (Finset.univ.erase i) +
      FABL.anfCoeff (FABL.f₂PointIndicator 0) (Finset.univ.erase i)) +
      FABL.anfCoeff (FABL.f₂PointIndicator (degreeSixProfile f))
        (Finset.univ.erase i) = 0
    rw [anfCoeff_pointIndicator_erase,
      anfCoeff_pointIndicator_erase]
    simp only [degreeSixProfile, Pi.zero_apply]
    ring_nf
    simp only [two_eq_zero_f₂, zero_add, mul_zero]

private theorem support_f₂PointIndicator
    (a : FABL.F₂Cube n) :
    support (FABL.f₂PointIndicator a) = {a} := by
  classical
  ext x
  simp [mem_support, FABL.f₂PointIndicator_eq_ite]

private theorem hammingWeight_f₂PointIndicator
    (a : FABL.F₂Cube n) :
    hammingWeight (FABL.f₂PointIndicator a) = 1 := by
  rw [hammingWeight_eq_card_support, support_f₂PointIndicator]
  simp

private theorem hammingDistance_add_pointIndicator
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    hammingDistance f (f + FABL.f₂PointIndicator a) = 1 := by
  rw [hammingDistance_eq_hammingWeight_add]
  have hcancel : f + (f + FABL.f₂PointIndicator a) =
      FABL.f₂PointIndicator a := by
    funext x
    simp only [Pi.add_apply]
    exact CharTwo.add_cancel_left _ _
  rw [hcancel, hammingWeight_f₂PointIndicator]

private theorem support_add_pointIndicator_of_eq_one
    (f : BooleanFunction n) (a : FABL.F₂Cube n) (ha : f a = 1) :
    support (f + FABL.f₂PointIndicator a) = (support f).erase a := by
  classical
  ext x
  by_cases hxa : x = a
  · subst x
    simp [mem_support, FABL.f₂PointIndicator_eq_ite, ha]
  · simp [mem_support, FABL.f₂PointIndicator_eq_ite, hxa]

private theorem hammingWeight_add_pointIndicator_add_one
    (f : BooleanFunction n) (a : FABL.F₂Cube n) (ha : f a = 1) :
    hammingWeight (f + FABL.f₂PointIndicator a) + 1 = hammingWeight f := by
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support,
    support_add_pointIndicator_of_eq_one f a ha]
  exact Finset.card_erase_add_one ((mem_support f a).2 ha)

private theorem hammingDistance_add_pointIndicator_add_one
    (f g : BooleanFunction n) (a : FABL.F₂Cube n)
    (ha : (f + g) a = 1) :
    hammingDistance (f + FABL.f₂PointIndicator a) g + 1 =
      hammingDistance f g := by
  rw [hammingDistance_eq_hammingWeight_add,
    hammingDistance_eq_hammingWeight_add]
  have hreassoc :
      (f + FABL.f₂PointIndicator a) + g =
        (f + g) + FABL.f₂PointIndicator a := by
    funext x
    simp only [Pi.add_apply]
    ac_rfl
  rw [hreassoc]
  exact hammingWeight_add_pointIndicator_add_one (f + g) a ha

private theorem even_hammingWeight_of_degree_le_five
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    Even (hammingWeight f) := by
  rw [hammingWeight_eq_card_support]
  apply Nat.not_odd_iff_even.mp
  intro hodd
  have hdegree :=
    (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
      f (by omega)).2 hodd
  omega

private theorem nonlinearity_ne_fifty_five_of_degree_le_five
    (f : BooleanFunction 7) (hf : FABL.functionAlgebraicDegree f ≤ 5) :
    nonlinearity f ≠ 55 := by
  classical
  intro hnonlinearity
  unfold nonlinearity at hnonlinearity
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube 7)))
    Finset.univ_nonempty
    (fun q ↦ hammingDistance f (FABL.affineFunction q.1 q.2))
  have hdistance := hmin
  rw [hnonlinearity] at hdistance
  rw [hammingDistance_eq_hammingWeight_add] at hdistance
  have haffine : FABL.functionAlgebraicDegree
      (FABL.affineFunction p.1 p.2) ≤ 1 := by
    exact FABL.functionAlgebraicDegree_affineFunction_le_one p.1 p.2
  have hsumdegree : FABL.functionAlgebraicDegree
      (f + FABL.affineFunction p.1 p.2) ≤ 5 :=
    (FABL.functionAlgebraicDegree_add_le_max f
      (FABL.affineFunction p.1 p.2)).trans (by omega)
  obtain ⟨k, hk⟩ := even_hammingWeight_of_degree_le_five
    (f + FABL.affineFunction p.1 p.2) hsumdegree
  omega

/-- Hou's quotient reduction: a radius-`56` bound on the degree-at-most-five
subcode, together with a minimum leader through every coordinate of each
radius-`56` coset, bounds every seven-variable Boolean function by `56`. -/
theorem nonlinearity_le_fifty_six_of_degree_five_covering
    (hleader : ∀ g : BooleanFunction 7,
      FABL.functionAlgebraicDegree g ≤ 5 → nonlinearity g = 56 →
        ∀ x : FABL.F₂Cube 7, ∃ b a,
          hammingDistance g (FABL.affineFunction b a) = 56 ∧
            (g + FABL.affineFunction b a) x = 1)
    (f : BooleanFunction 7) :
    nonlinearity f ≤ 56 := by
  classical
  by_cases htop : FABL.anfCoeff f Finset.univ = 0
  · let v := degreeSixProfile f
    let g := f + FABL.f₂PointIndicator 0 + FABL.f₂PointIndicator v
    have hgdegree : FABL.functionAlgebraicDegree g ≤ 5 := by
      simpa [g, v] using add_two_points_degree_le_five f htop
    have hgupper := nonlinearity_le_56_of_degree_le_five_seven g hgdegree
    have hgne : nonlinearity g ≠ 55 :=
      nonlinearity_ne_fifty_five_of_degree_le_five g hgdegree
    by_cases hgsmall : nonlinearity g ≤ 54
    · have hfg : hammingDistance f g ≤ 2 := by
        have htriangle := hammingDist_triangle f
          (f + FABL.f₂PointIndicator 0) g
        change hammingDistance f g ≤
          hammingDistance f (f + FABL.f₂PointIndicator 0) +
            hammingDistance (f + FABL.f₂PointIndicator 0) g at htriangle
        have hfirst := hammingDistance_add_pointIndicator f
          (0 : FABL.F₂Cube 7)
        have hsecond : hammingDistance (f + FABL.f₂PointIndicator 0) g = 1 := by
          have hrewrite : g =
              (f + FABL.f₂PointIndicator 0) + FABL.f₂PointIndicator v := by
            simp only [g]
          rw [hrewrite]
          exact hammingDistance_add_pointIndicator
            (f + FABL.f₂PointIndicator 0) v
        omega
      exact (nonlinearity_le_hammingDistance_add_nonlinearity f g).trans (by omega)
    · have hge : 55 ≤ nonlinearity g := by omega
      have hgeq : nonlinearity g = 56 := by omega
      obtain ⟨b, a, hdist, herror⟩ := hleader g hgdegree hgeq 0
      let h := g + FABL.f₂PointIndicator 0
      have hhcandidate : nonlinearity h ≤ 55 := by
        have hdrop := hammingDistance_add_pointIndicator_add_one
          g (FABL.affineFunction b a) 0 herror
        have hdistance : hammingDistance h (FABL.affineFunction b a) = 55 := by
          change hammingDistance (g + FABL.f₂PointIndicator 0)
            (FABL.affineFunction b a) = 55
          omega
        exact Finset.inf'_le
          (fun q : FABL.𝔽₂ × FABL.F₂Cube 7 ↦
            hammingDistance h (FABL.affineFunction q.1 q.2))
          (Finset.mem_univ (b, a)) |>.trans_eq hdistance
      have hfh : hammingDistance f h = 1 := by
        have hrewrite : h = f + FABL.f₂PointIndicator v := by
          change ((f + FABL.f₂PointIndicator 0) +
              FABL.f₂PointIndicator v) + FABL.f₂PointIndicator 0 =
            f + FABL.f₂PointIndicator v
          calc
            ((f + FABL.f₂PointIndicator 0) +
                FABL.f₂PointIndicator v) + FABL.f₂PointIndicator 0 =
                (f + FABL.f₂PointIndicator v) +
                  (FABL.f₂PointIndicator 0 + FABL.f₂PointIndicator 0) := by
              funext y
              simp only [Pi.add_apply]
              abel
            _ = f + FABL.f₂PointIndicator v := by
              rw [CharTwo.add_self_eq_zero, add_zero]
        rw [hrewrite]
        exact hammingDistance_add_pointIndicator f v
      exact (nonlinearity_le_hammingDistance_add_nonlinearity f h).trans (by omega)
  · have htopone : FABL.anfCoeff f Finset.univ = 1 :=
      Fin.eq_one_of_ne_zero _ htop
    let x := oddPoint f
    let g := f + FABL.f₂PointIndicator x
    have hgdegree : FABL.functionAlgebraicDegree g ≤ 5 := by
      simpa [g, x] using add_oddPoint_degree_le_five f htopone
    have hgupper := nonlinearity_le_56_of_degree_le_five_seven g hgdegree
    by_cases hgsmall : nonlinearity g ≤ 55
    · have hfg : hammingDistance f g = 1 := by
        rw [show g = f + FABL.f₂PointIndicator x by rfl]
        exact hammingDistance_add_pointIndicator f x
      exact (nonlinearity_le_hammingDistance_add_nonlinearity f g).trans (by omega)
    · have hgeq : nonlinearity g = 56 := by omega
      obtain ⟨b, a, hdist, herror⟩ := hleader g hgdegree hgeq x
      have hdrop := hammingDistance_add_pointIndicator_add_one
        g (FABL.affineFunction b a) x herror
      have hfgfun : f = g + FABL.f₂PointIndicator x := by
        funext y
        change f y = (f y + FABL.f₂PointIndicator x y) +
          FABL.f₂PointIndicator x y
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [← hfgfun] at hdrop
      have hcandidate : hammingDistance f (FABL.affineFunction b a) = 55 := by
        omega
      calc
        nonlinearity f ≤ hammingDistance f (FABL.affineFunction b a) :=
          Finset.inf'_le
            (fun q : FABL.𝔽₂ × FABL.F₂Cube 7 ↦
              hammingDistance f (FABL.affineFunction q.1 q.2))
            (Finset.mem_univ (b, a))
        _ = 55 := hcandidate
        _ ≤ 56 := by omega

/-- Carlet's exact best nonlinearity in seven variables. -/
theorem maximumNonlinearity_seven : maximumNonlinearity 7 = 56 := by
  apply Nat.le_antisymm
  · obtain ⟨f, hf⟩ := exists_nonlinearity_eq_maximumNonlinearity 7
    rw [← hf]
    exact nonlinearity_le_fifty_six_of_degree_five_covering
      exists_minimum_affine_error_one_at_of_degree_le_five_nonlinearity_eq_56_seven f
  · have hlower := quadraticBound_le_maximumNonlinearity_of_odd
      (n := 7) (by decide)
    norm_num at hlower ⊢
    exact hlower

end CryptBoolean
