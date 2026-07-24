/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerDuality
public import CryptBoolean.Carlet.Chapter03.ReedMullerMinimumWeight

/-!
# A low-weight restriction for codimension-three Reed--Muller codes

The weight-ten exclusion needed by the Carlet--Mesnager moment argument.
The proof is the codimension-three instance of the Kasami--Tokura low-weight
restriction, obtained directly from the Plotkin slices and the affine-flat
classification of minimum-weight words.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- A Boolean function of non-full algebraic degree has even Hamming
weight. -/
theorem even_hammingWeight_of_degree_lt_dimension
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f < n) :
    Even (hammingWeight f) := by
  rw [hammingWeight_eq_card_support]
  apply Nat.not_odd_iff_even.mp
  intro hodd
  have hfull :=
    (FABL.functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
      f (by omega)).2 (by
        simpa only [support, FABL.f₂OneSupport] using hodd)
  omega

private theorem support_inter_firstCoordinateSlices_eq_singleton_separator
    {m : ℕ} (u w v : BooleanFunction m)
    (hvu : v = u + w)
    (p : FABL.F₂Cube m)
    (hp : support u ∩ support w = {p})
    (H : Submodule FABL.𝔽₂ (FABL.F₂Cube m))
    (a : FABL.F₂Cube m)
    (hsupport : (support v : Set (FABL.F₂Cube m)) =
      FABL.binaryAffineSubspace H a) :
    ∃ ell : BooleanFunction m,
      ell ∈ reedMuller 1 m ∧ support u ∩ support ell = {p} := by
  have hpInter : p ∈ support u ∩ support w := by
    rw [hp]
    simp
  have hpData := Finset.mem_inter.mp hpInter
  have hpu : u p = 1 := (mem_support u p).mp hpData.1
  have hpw : w p = 1 := (mem_support w p).mp hpData.2
  have hpv : v p = 0 := by
    rw [hvu, Pi.add_apply, hpu, hpw]
    exact CharTwo.add_self_eq_zero 1
  have hpNotMem : p ∉ FABL.binaryAffineSubspace H a := by
    intro hpA
    have hpSupport : p ∈ (support v : Set (FABL.F₂Cube m)) := by
      rw [hsupport]
      exact hpA
    have hpOne := (mem_support v p).mp hpSupport
    exact zero_ne_one (hpv.symm.trans hpOne)
  have hpParity :=
    not_congr
      (FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity
        H a p) |>.mp hpNotMem
  push Not at hpParity
  obtain ⟨gamma, hgamma, hgammaNe⟩ := hpParity
  let ell : BooleanFunction m :=
    FABL.affineFunction (FABL.f₂DotProduct gamma a) gamma
  have hellMem : ell ∈ reedMuller 1 m := by
    exact affineFunction_mem_reedMuller_one _ _
  have hellZero {x : FABL.F₂Cube m}
      (hx : x ∈ FABL.binaryAffineSubspace H a) : ell x = 0 := by
    have hxParity :=
      (FABL.mem_binaryAffineSubspace_iff_forall_perpendicular_parity
        H a x).mp hx gamma hgamma
    simp only [ell, FABL.affineFunction]
    rw [hxParity]
    exact CharTwo.add_self_eq_zero _
  have hellP : ell p = 1 := by
    simp only [ell, FABL.affineFunction]
    apply Fin.eq_one_of_ne_zero
    intro hzero
    apply hgammaNe
    have heq := add_eq_zero_iff_eq_neg.mp hzero
    exact (heq.trans
      (ZMod.neg_eq_self_mod_two (FABL.f₂DotProduct gamma p))).symm
  refine ⟨ell, hellMem, ?_⟩
  ext x
  constructor
  · intro hx
    have hxData := Finset.mem_inter.mp hx
    have hxu : u x = 1 := (mem_support u x).mp hxData.1
    have hxell : ell x = 1 := (mem_support ell x).mp hxData.2
    have hxNotAffine : x ∉ FABL.binaryAffineSubspace H a := by
      intro hxAffine
      have hxzero := hellZero hxAffine
      exact zero_ne_one (hxzero.symm.trans hxell)
    have hxv : v x = 0 := by
      by_contra hxne
      have hxone : v x = 1 := Fin.eq_one_of_ne_zero _ hxne
      have hxSupport : x ∈ (support v : Set (FABL.F₂Cube m)) :=
        (mem_support v x).mpr hxone
      rw [hsupport] at hxSupport
      exact hxNotAffine hxSupport
    have hxw : w x = 1 := by
      rw [hvu, Pi.add_apply, hxu] at hxv
      have heq := add_eq_zero_iff_eq_neg.mp hxv
      exact (heq.trans (ZMod.neg_eq_self_mod_two (w x))).symm
    have hxPair : x ∈ support u ∩ support w :=
      Finset.mem_inter.mpr
        ⟨(mem_support u x).mpr hxu, (mem_support w x).mpr hxw⟩
    rw [hp] at hxPair
    exact hxPair
  · intro hx
    have hxp : x = p := by simpa using hx
    subst x
    exact Finset.mem_inter.mpr
      ⟨hpData.1, (mem_support ell p).mpr hellP⟩

/-- The codimension-three Reed--Muller code has no word of Hamming weight
ten. This is the only Kasami--Tokura weight-spectrum exclusion needed by the
seventh/eighth moment comparison. -/
theorem hammingWeight_ne_ten_of_mem_reedMuller_codimension_three
    (h : BooleanFunction n) (hn : 3 ≤ n)
    (hmem : h ∈ reedMuller (n - 3) n) :
    hammingWeight h ≠ 10 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hweight
      by_cases hnThree : n = 3
      · subst n
        have hupper : hammingWeight h ≤ 2 ^ 3 := by
          rw [hammingWeight_eq_card_support, ← card_f₂Cube 3]
          exact Finset.card_le_card (Finset.subset_univ _)
        omega
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hm : 3 ≤ m := by omega
        have hdegree :
            FABL.functionAlgebraicDegree h ≤ m - 2 := by
          have hdegree' :
              FABL.functionAlgebraicDegree h ≤ (m + 1) - 3 := by
            simpa only [mem_reedMuller_iff] using hmem
          omega
        let u : BooleanFunction m := firstCoordinateSlice h 0
        let w : BooleanFunction m := firstCoordinateSlice h 1
        let v : BooleanFunction m := u + w
        have huDegree : FABL.functionAlgebraicDegree u ≤ m - 2 := by
          simpa only [u] using
            (firstCoordinateSlice_degree_le h 0 hdegree)
        have hwDegree : FABL.functionAlgebraicDegree w ≤ m - 2 := by
          simpa only [w] using
            (firstCoordinateSlice_degree_le h 1 hdegree)
        have hvDegree : FABL.functionAlgebraicDegree v ≤ m - 3 := by
          have hvDegree' :=
            firstCoordinateDifference_degree_le_pred h hdegree
          simpa only [v, u, w, show m - 2 - 1 = m - 3 by omega] using
            hvDegree'
        have hvMem : v ∈ reedMuller (m - 3) m := by
          simpa only [mem_reedMuller_iff] using hvDegree
        have hslices : hammingWeight u + hammingWeight w = 10 := by
          have hsplit := hammingWeight_firstCoordinateSlices h
          rw [hweight] at hsplit
          simpa only [u, w] using hsplit.symm
        have hweightIdentity :
            hammingWeight v + 2 * (support u ∩ support w).card = 10 := by
          have hadd := hammingWeight_add_add_two_mul_card_inter u w
          rw [hslices] at hadd
          simpa only [v] using hadd
        by_cases hvZero : v = 0
        · have huw : u = w := by
            funext x
            have hzero := congrFun hvZero x
            simp only [v, Pi.add_apply, Pi.zero_apply] at hzero
            have heq := add_eq_zero_iff_eq_neg.mp hzero
            exact heq.trans (ZMod.neg_eq_self_mod_two (w x))
          rw [huw] at hslices
          have hwOdd : Odd (hammingWeight w) := by
            use 2
            omega
          have hwEven := even_hammingWeight_of_degree_lt_dimension w (by
            omega)
          exact (Nat.not_odd_iff_even.mpr hwEven) hwOdd
        · have hvLower :=
            two_pow_sub_le_hammingWeight_of_degree_le v hvDegree hvZero
          have hmSub : m - (m - 3) = 3 := by omega
          rw [hmSub] at hvLower
          norm_num at hvLower
          have hvUpper : hammingWeight v ≤ 10 := by omega
          have hvEven := even_hammingWeight_of_degree_lt_dimension v (by
            omega)
          obtain ⟨k, hk⟩ := hvEven
          have hvNotTen : hammingWeight v ≠ 10 :=
            ih m (by omega) v hm hvMem
          have hvWeight : hammingWeight v = 8 := by omega
          have hinterCard : (support u ∩ support w).card = 1 := by
            omega
          obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hinterCard
          have hvDegreeEq : FABL.functionAlgebraicDegree v = m - 3 := by
            apply Nat.le_antisymm hvDegree
            by_cases hmThree : m = 3
            · omega
            · have hmFour : 4 ≤ m := by omega
              by_contra hnot
              have hvDegreeFour :
                  FABL.functionAlgebraicDegree v ≤ m - 4 := by omega
              have hvLowerFour :=
                two_pow_sub_le_hammingWeight_of_degree_le
                  v hvDegreeFour hvZero
              have hmSubFour : m - (m - 4) = 4 := by omega
              rw [hmSubFour, hvWeight] at hvLowerFour
              norm_num at hvLowerFour
          have hvWeightPower : hammingWeight v = 2 ^ (m - (m - 3)) := by
            rw [hvWeight]
            norm_num [show m - (m - 3) = 3 by omega]
          obtain ⟨H, a, _hHrank, hvIndicator⟩ :=
            (degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator
              v (r := m - 3) (by omega)).mp
                ⟨hvDegreeEq, hvWeightPower⟩
          have hsupport : (support v : Set (FABL.F₂Cube m)) =
              FABL.binaryAffineSubspace H a :=
            (eq_affineFlatIndicator_iff_support_eq v H a).mp hvIndicator
          obtain ⟨ell, hellMem, hinterEll⟩ :=
            support_inter_firstCoordinateSlices_eq_singleton_separator
              u w v rfl p hp H a hsupport
          have huMem : u ∈ reedMuller (m - 2) m := by
            simpa only [mem_reedMuller_iff] using huDegree
          have huDual : u ∈ reedMullerDual 1 m := by
            rw [reedMullerDual_eq (r := 1) (n := m) (by omega)]
            simpa only [show m - 1 - 1 = m - 2 by omega] using huMem
          rw [reedMullerDual,
            LinearMap.BilinForm.mem_orthogonal_iff] at huDual
          have hpairReverse := huDual ell hellMem
          have hpair : booleanFunctionPairing m u ell = 0 := by
            rw [booleanFunctionPairing_apply]
            calc
              (∑ x, u x * ell x) = ∑ x, ell x * u x := by
                apply Finset.sum_congr rfl
                intro x _hx
                exact mul_comm _ _
              _ = 0 := hpairReverse
          have hinterEven :=
            even_card_support_inter_of_pairing_eq_zero u ell hpair
          rw [hinterEll] at hinterEven
          norm_num at hinterEven

end CryptBoolean
