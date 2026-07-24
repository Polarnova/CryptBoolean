/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightFourteen
public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightAffineSpan
public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightSpectrum
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity

/-!
# The weight-fourteen affine-flat classification

The Kasami--Tokura classification specialized to weight fourteen in the
codimension-three Reed--Muller code.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

open FABL

variable {n : ℕ}

noncomputable local instance weightFourteenClassificationAffineSubspaceFintype :
    Fintype (AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

noncomputable local instance weightFourteenClassificationSubmoduleFintype :
    Fintype (Submodule FABL.𝔽₂ (FABL.F₂Cube n)) :=
  Fintype.ofFinite _

private theorem hammingWeight_le_cube_card
    (f : BooleanFunction n) :
    hammingWeight f ≤ 2 ^ n := by
  rw [hammingWeight_eq_card_support, ← card_f₂Cube n]
  exact Finset.card_le_card (Finset.subset_univ _)

private theorem four_le_dimension_of_weight_fourteen
    (h : BooleanFunction n) (hweight : hammingWeight h = 14) :
    4 ≤ n := by
  have hle := hammingWeight_le_cube_card h
  rw [hweight] at hle
  by_contra hn
  have hn' : n ≤ 3 := by omega
  interval_cases n <;> norm_num at hle

private noncomputable def singletonDirectionMap
    (v : FABL.F₂Cube n) : FABL.𝔽₂ →ₗ[FABL.𝔽₂] FABL.F₂Cube n where
  toFun c := c • v
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

private theorem singletonDirectionMap_injective
    {v : FABL.F₂Cube n} (hv : v ≠ 0) :
    Function.Injective (singletonDirectionMap v) := by
  intro a b hab
  change a • v = b • v at hab
  exact smul_left_injective FABL.𝔽₂ hv hab

private noncomputable def firstCoordinateVector (m : ℕ) :
    FABL.F₂Cube (m + 1) :=
  Pi.single 0 1

private theorem firstCoordinateVector_ne_zero (m : ℕ) :
    firstCoordinateVector m ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [firstCoordinateVector] at h0

private theorem exists_linearEquiv_firstCoordinate_eq
    {m : ℕ} (a : FABL.F₂Cube (m + 1)) (ha : a ≠ 0) :
    ∃ L : FABL.F₂Cube (m + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1),
      L (firstCoordinateVector m) = a := by
  let e₀ := LinearEquiv.ofInjective
    (singletonDirectionMap (firstCoordinateVector m))
    (singletonDirectionMap_injective (firstCoordinateVector_ne_zero m))
  let eₐ := LinearEquiv.ofInjective
    (singletonDirectionMap a) (singletonDirectionMap_injective ha)
  let e : LinearMap.range (singletonDirectionMap (firstCoordinateVector m))
      ≃ₗ[FABL.𝔽₂] LinearMap.range (singletonDirectionMap a) :=
    e₀.symm.trans eₐ
  obtain ⟨L, hL⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨L, ?_⟩
  let x : LinearMap.range (singletonDirectionMap (firstCoordinateVector m)) :=
    ⟨firstCoordinateVector m, ⟨1, by simp [singletonDirectionMap]⟩⟩
  have hx := hL x
  change L (firstCoordinateVector m) = a
  calc
    L (firstCoordinateVector m) = (e x : FABL.F₂Cube (m + 1)) := hx.symm
    _ = a := by
      change eₐ (e₀.symm x) = a
      have he₀ : e₀ (1 : FABL.𝔽₂) = x := by
        apply Subtype.ext
        change (singletonDirectionMap (firstCoordinateVector m)) 1 =
          firstCoordinateVector m
        simp [singletonDirectionMap]
      rw [← he₀, e₀.symm_apply_apply]
      change (singletonDirectionMap a) 1 = a
      simp [singletonDirectionMap]

private theorem hammingWeight_comp_linearEquiv
    (f : BooleanFunction n)
    (L : FABL.F₂Cube n ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n) :
    hammingWeight (f ∘ L) = hammingWeight f := by
  classical
  rw [hammingWeight_eq_card_support, hammingWeight_eq_card_support]
  simp only [support, FABL.f₂OneSupport, Function.comp_apply]
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp L.toEquiv
    (fun x ↦ if f x = 1 then (1 : ℕ) else 0)

private theorem firstCoordinateSlice_zero_eq_one_of_period
    {m : ℕ} (f : BooleanFunction (m + 1))
    (hperiod : FABL.booleanDerivative f (firstCoordinateVector m) = 0) :
    firstCoordinateSlice f 0 = firstCoordinateSlice f 1 := by
  funext x
  have hx := congrFun hperiod (Fin.cons 0 x)
  simp only [FABL.booleanDerivative, Pi.zero_apply] at hx
  have hadd : Fin.cons 0 x + firstCoordinateVector m = Fin.cons 1 x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [firstCoordinateVector]
    · simp [firstCoordinateVector]
  rw [hadd] at hx
  exact add_eq_zero_iff_eq_neg.mp hx |>.trans (by
    exact ZMod.neg_eq_self_mod_two _)

private theorem no_nonzero_period_of_weight_fourteen
    (h : BooleanFunction n)
    (hn : 4 ≤ n)
    (hdegree : FABL.functionAlgebraicDegree h ≤ n - 3)
    (hweight : hammingWeight h = 14)
    (a : FABL.F₂Cube n) (ha : a ≠ 0) :
    FABL.booleanDerivative h a ≠ 0 := by
  intro hperiod
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨L, hLa⟩ := exists_linearEquiv_firstCoordinate_eq a ha
  let f : BooleanFunction (m + 1) := h ∘ L
  have hfPeriod : FABL.booleanDerivative f (firstCoordinateVector m) = 0 := by
    funext x
    simp only [f, FABL.booleanDerivative, Function.comp_apply, L.map_add, hLa]
    exact congrFun hperiod (L x)
  let g : BooleanFunction m := firstCoordinateSlice f 0
  have hslices : firstCoordinateSlice f 0 = firstCoordinateSlice f 1 :=
    firstCoordinateSlice_zero_eq_one_of_period f hfPeriod
  have hfWeight : hammingWeight f = 14 := by
    simpa only [f] using (hammingWeight_comp_linearEquiv h L).trans hweight
  have hsliceWeight := hammingWeight_firstCoordinateSlices f
  have hgWeight : hammingWeight g = 7 := by
    change hammingWeight (firstCoordinateSlice f 0) = 7
    have htwice : 14 = hammingWeight (firstCoordinateSlice f 0) +
        hammingWeight (firstCoordinateSlice f 0) := by
      calc
        14 = hammingWeight f := hfWeight.symm
        _ = hammingWeight (firstCoordinateSlice f 0) +
            hammingWeight (firstCoordinateSlice f 1) := hsliceWeight
        _ = _ := by rw [← hslices]
    omega
  have hfDegree : FABL.functionAlgebraicDegree f ≤ m - 2 := by
    have hcomp := FABL.functionAlgebraicDegree_comp_affineEquiv
      h L.toAffineEquiv
    change FABL.functionAlgebraicDegree f =
      FABL.functionAlgebraicDegree h at hcomp
    rw [hcomp]
    simpa only [show m + 1 - 3 = m - 2 by omega] using hdegree
  have hgDegree : FABL.functionAlgebraicDegree g ≤ m - 2 := by
    exact (firstCoordinateSlice_degree_le f 0 hfDegree)
  have heven := even_hammingWeight_of_degree_lt_dimension g
    (hgDegree.trans_lt (by omega))
  rw [hgWeight] at heven
  norm_num at heven

private noncomputable def supportPairSum
    (t : Finset (FABL.F₂Cube n)) : FABL.F₂Cube n :=
  ∑ x ∈ t, x

private theorem exists_four_support_points_same_sum
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hspan : Module.finrank FABL.𝔽₂ (supportDifferenceSpan h p) ≤ 6)
    (hweight : hammingWeight h = 14) :
    ∃ x y z w : FABL.F₂Cube n,
      x ∈ support h ∧ y ∈ support h ∧
      z ∈ support h ∧ w ∈ support h ∧
      x ≠ y ∧ z ≠ w ∧
      Disjoint ({x, y} : Finset (FABL.F₂Cube n)) {z, w} ∧
      x + y = z + w := by
  classical
  let pairs := (support h).powersetCard 2
  let E := supportDifferenceSpan h p
  have hsupportCard : (support h).card = 14 := by
    simpa only [hammingWeight_eq_card_support] using hweight
  have hpairsCard : pairs.card = 91 := by
    simp only [pairs, Finset.card_powersetCard, hsupportCard]
    norm_num [Nat.choose]
  have hsumMem : ∀ t ∈ pairs, supportPairSum t ∈ E := by
    intro t ht
    have htdata := Finset.mem_powersetCard.mp ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htdata.2
    simp only [supportPairSum, Finset.sum_insert, Finset.mem_singleton,
      hxy, not_false_eq_true, Finset.sum_singleton]
    have hxMem : x ∈ ({x, y} : Finset (FABL.F₂Cube n)) := by simp
    have hyMem : y ∈ ({x, y} : Finset (FABL.F₂Cube n)) := by simp
    have hx := support_subset_binaryAffineSubspace_supportDifferenceSpan h p
      (htdata.1 hxMem)
    have hy := support_subset_binaryAffineSubspace_supportDifferenceSpan h p
      (htdata.1 hyMem)
    change x ∈ FABL.binaryAffineSubspace (supportDifferenceSpan h p) p at hx
    change y ∈ FABL.binaryAffineSubspace (supportDifferenceSpan h p) p at hy
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hx hy
    have hsum : x + y = (x + p) + (y + p) := by
      calc
        x + y = (x + y) + (p + p) := by
          rw [ZModModule.add_self, add_zero]
        _ = (x + p) + (y + p) := by abel
    rw [hsum]
    exact E.add_mem hx hy
  let pairToE : {t // t ∈ pairs} → E := fun t ↦
    ⟨supportPairSum t.1, hsumMem t.1 t.2⟩
  have hECard : Fintype.card E ≤ 64 := by
    rw [← Nat.card_eq_fintype_card]
    rw [Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := E)]
    have := hspan
    interval_cases Module.finrank FABL.𝔽₂ E <;> norm_num
  have hpigeon : Fintype.card E < Fintype.card {t // t ∈ pairs} := by
    rw [Fintype.card_coe, hpairsCard]
    omega
  obtain ⟨A, B, hAB, hsum⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt pairToE hpigeon
  have hAdata := Finset.mem_powersetCard.mp A.2
  have hBdata := Finset.mem_powersetCard.mp B.2
  obtain ⟨x, y, hxy, hA⟩ := Finset.card_eq_two.mp hAdata.2
  obtain ⟨z, w, hzw, hB⟩ := Finset.card_eq_two.mp hBdata.2
  have hpairSum : x + y = z + w := by
    have hval := congrArg Subtype.val hsum
    simpa [pairToE, supportPairSum, hA, hB, hxy, hzw] using hval
  have hdisjoint : Disjoint ({x, y} : Finset (FABL.F₂Cube n)) {z, w} := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    have hqA' : q ∈ A.1 := by simpa only [hA] using hqA
    have hqB' : q ∈ B.1 := by simpa only [hB] using hqB
    have hAeraseCard : (A.1.erase q).card = 1 := by
      rw [Finset.card_erase_of_mem hqA', hAdata.2]
    have hBeraseCard : (B.1.erase q).card = 1 := by
      rw [Finset.card_erase_of_mem hqB', hBdata.2]
    obtain ⟨u, hAu⟩ := Finset.card_eq_one.mp hAeraseCard
    obtain ⟨v, hBv⟩ := Finset.card_eq_one.mp hBeraseCard
    have hsumErase : supportPairSum (A.1.erase q) =
        supportPairSum (B.1.erase q) := by
      have hA_sum := Finset.sum_erase_add (s := A.1) (f := fun x ↦ x) hqA'
      have hB_sum := Finset.sum_erase_add (s := B.1) (f := fun x ↦ x) hqB'
      have hsumVal := congrArg Subtype.val hsum
      simp only [pairToE] at hsumVal
      simp only [supportPairSum]
      simp only [supportPairSum] at hsumVal
      rw [← hA_sum, ← hB_sum] at hsumVal
      exact add_right_cancel hsumVal
    have huv : u = v := by
      simpa [supportPairSum, hAu, hBv] using hsumErase
    apply hAB
    apply Subtype.ext
    rw [← Finset.insert_erase hqA', ← Finset.insert_erase hqB',
      hAu, hBv, huv]
  refine ⟨x, y, z, w, ?_, ?_, ?_, ?_, hxy, hzw, hdisjoint, hpairSum⟩
  · exact hAdata.1 (by simp [hA])
  · exact hAdata.1 (by simp [hA])
  · exact hBdata.1 (by simp [hB])
  · exact hBdata.1 (by simp [hB])

private theorem booleanDerivative_self_direction
    (f : BooleanFunction n) (a : FABL.F₂Cube n) :
    FABL.booleanDerivative (FABL.booleanDerivative f a) a = 0 := by
  funext x
  simp only [FABL.booleanDerivative, Pi.zero_apply]
  have harg : x + a + a = x := by
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [harg]
  calc
    (f x + f (x + a)) + (f (x + a) + f x) =
        (f x + f x) + (f (x + a) + f (x + a)) := by abel
    _ = 0 := by
      rw [ZModModule.add_self, ZModModule.add_self, add_zero]

private theorem booleanDerivative_value_add_direction
    (f : BooleanFunction n) (a x : FABL.F₂Cube n) :
    FABL.booleanDerivative f a (x + a) =
      FABL.booleanDerivative f a x := by
  simp only [FABL.booleanDerivative]
  have harg : x + a + a = x := by
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [harg]
  exact add_comm _ _

private theorem hammingWeight_booleanDerivative_eq_sixteen_of_le_twenty
    (h : BooleanFunction n)
    (hn : 4 ≤ n)
    (hdegree : FABL.functionAlgebraicDegree h ≤ n - 3)
    (hweight : hammingWeight h = 14)
    (a : FABL.F₂Cube n) (ha : a ≠ 0)
    (hupper : hammingWeight (FABL.booleanDerivative h a) ≤ 20) :
    hammingWeight (FABL.booleanDerivative h a) = 16 := by
  let d := FABL.booleanDerivative h a
  have hdNe : d ≠ 0 :=
    no_nonzero_period_of_weight_fourteen h hn hdegree hweight a ha
  have hdDegree : FABL.functionAlgebraicDegree d ≤ n - 4 := by
    exact (FABL.functionAlgebraicDegree_booleanDerivative_le h a).trans
      (by omega)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨L, hLa⟩ := exists_linearEquiv_firstCoordinate_eq a ha
  let f : BooleanFunction (m + 1) := d ∘ L
  have hfPeriod : FABL.booleanDerivative f (firstCoordinateVector m) = 0 := by
    funext x
    simp only [f, FABL.booleanDerivative, Function.comp_apply, L.map_add, hLa]
    exact congrFun (booleanDerivative_self_direction h a) (L x)
  let g : BooleanFunction m := firstCoordinateSlice f 0
  have hslices : firstCoordinateSlice f 0 = firstCoordinateSlice f 1 :=
    firstCoordinateSlice_zero_eq_one_of_period f hfPeriod
  have hfWeight : hammingWeight f = hammingWeight d :=
    hammingWeight_comp_linearEquiv d L
  have hsliceWeight := hammingWeight_firstCoordinateSlices f
  have htwice : hammingWeight d = 2 * hammingWeight g := by
    change hammingWeight d = 2 * hammingWeight (firstCoordinateSlice f 0)
    calc
      hammingWeight d = hammingWeight f := hfWeight.symm
      _ = hammingWeight (firstCoordinateSlice f 0) +
          hammingWeight (firstCoordinateSlice f 1) := hsliceWeight
      _ = 2 * hammingWeight (firstCoordinateSlice f 0) := by
        rw [← hslices, two_mul]
  have hfDegree : FABL.functionAlgebraicDegree f ≤ m - 3 := by
    have hcomp := FABL.functionAlgebraicDegree_comp_affineEquiv
      d L.toAffineEquiv
    change FABL.functionAlgebraicDegree f =
      FABL.functionAlgebraicDegree d at hcomp
    rw [hcomp]
    simpa only [show m + 1 - 4 = m - 3 by omega] using hdDegree
  have hgDegree : FABL.functionAlgebraicDegree g ≤ m - 3 :=
    firstCoordinateSlice_degree_le f 0 hfDegree
  have hgNe : g ≠ 0 := by
    intro hg
    apply hdNe
    apply hammingNorm_eq_zero.mp
    change hammingWeight d = 0
    rw [htwice]
    simp [g, hg]
  have hglower := two_pow_sub_le_hammingWeight_of_degree_le
    g hgDegree hgNe
  have hm : 3 ≤ m := by omega
  have hexponent : m - (m - 3) = 3 := by omega
  rw [hexponent] at hglower
  norm_num at hglower
  have hgupper : hammingWeight g ≤ 10 := by
    have := hupper
    change hammingWeight d ≤ 20 at this
    rw [htwice] at this
    omega
  have hgeven := even_hammingWeight_of_degree_lt_dimension g
    (hgDegree.trans_lt (by omega))
  have hgNotTen : hammingWeight g ≠ 10 := by
    apply hammingWeight_ne_ten_of_mem_reedMuller_codimension_three g hm
    simpa only [mem_reedMuller_iff] using hgDegree
  obtain ⟨k, hk⟩ := hgeven
  have hgWeight : hammingWeight g = 8 := by omega
  rw [htwice, hgWeight]

private theorem exists_weight_sixteen_derivative
    (h : BooleanFunction n)
    (hn : 4 ≤ n)
    (hdegree : FABL.functionAlgebraicDegree h ≤ n - 3)
    (hweight : hammingWeight h = 14) :
    ∃ a : FABL.F₂Cube n, a ≠ 0 ∧
      hammingWeight (FABL.booleanDerivative h a) = 16 := by
  have hsupportNonempty : (support h).Nonempty := by
    apply Finset.card_pos.mp
    rw [← hammingWeight_eq_card_support, hweight]
    norm_num
  obtain ⟨p, hp⟩ := hsupportNonempty
  have hmem : h ∈ reedMuller (n - 3) n := by
    simpa only [mem_reedMuller_iff] using hdegree
  have hspan := finrank_supportDifferenceSpan_le_six_of_weight_fourteen
    h p hp (by omega) hmem hweight
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hxy, hzw,
    hdisjoint, hpairsum⟩ :=
    exists_four_support_points_same_sum h p hspan hweight
  let a := x + y
  have ha : a ≠ 0 := by
    intro haZero
    apply hxy
    have := add_eq_zero_iff_eq_neg.mp haZero
    exact this.trans (by
      funext i
      exact ZMod.neg_eq_self_mod_two (y i))
  let t : BooleanFunction n := fun q ↦ h (q + a)
  have hfourSubset : ({x, y} ∪ {z, w} : Finset (FABL.F₂Cube n)) ⊆
      support h ∩ support t := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [Finset.mem_inter, mem_support]
    rcases hq with (hqx | hqy) | (hqz | hqw)
    · subst q
      refine ⟨(mem_support h x).mp hx, ?_⟩
      change h (x + (x + y)) = 1
      have harg : x + (x + y) = y := by
        rw [← add_assoc, ZModModule.add_self, zero_add]
      rw [harg]
      exact (mem_support h y).mp hy
    · subst q
      refine ⟨(mem_support h y).mp hy, ?_⟩
      change h (y + (x + y)) = 1
      have harg : y + (x + y) = x := by
        calc
          y + (x + y) = x + (y + y) := by abel
          _ = x := by rw [ZModModule.add_self, add_zero]
      rw [harg]
      exact (mem_support h x).mp hx
    · subst q
      refine ⟨(mem_support h z).mp hz, ?_⟩
      change h (z + (x + y)) = 1
      have harg : z + (x + y) = w := by
        rw [hpairsum]
        rw [← add_assoc, ZModModule.add_self, zero_add]
      rw [harg]
      exact (mem_support h w).mp hw
    · subst q
      refine ⟨(mem_support h w).mp hw, ?_⟩
      change h (w + (x + y)) = 1
      have harg : w + (x + y) = z := by
        rw [hpairsum]
        calc
          w + (z + w) = z + (w + w) := by abel
          _ = z := by rw [ZModModule.add_self, add_zero]
      rw [harg]
      exact (mem_support h z).mp hz
  have hfourCard : ({x, y} ∪ {z, w} : Finset (FABL.F₂Cube n)).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    simp [hxy, hzw]
  have hinterLower : 4 ≤ (support h ∩ support t).card := by
    rw [← hfourCard]
    exact Finset.card_mono hfourSubset
  have htWeight : hammingWeight t = 14 := by
    simpa only [t, hweight] using hammingWeight_translate h a
  have hidentity := hammingWeight_add_add_two_mul_card_support_inter h t
  have hderivative : h + t = FABL.booleanDerivative h a := rfl
  rw [hderivative, hweight, htWeight] at hidentity
  have hupper : hammingWeight (FABL.booleanDerivative h a) ≤ 20 := by
    omega
  exact ⟨a, ha,
    hammingWeight_booleanDerivative_eq_sixteen_of_le_twenty
      h hn hdegree hweight a ha hupper⟩

private theorem exists_derivative_affine_four_flat
    (h : BooleanFunction n)
    (hn : 4 ≤ n)
    (hdegree : FABL.functionAlgebraicDegree h ≤ n - 3)
    (hweight : hammingWeight h = 14) :
    ∃ (a : FABL.F₂Cube n)
      (D : Submodule FABL.𝔽₂ (FABL.F₂Cube n))
      (b : FABL.F₂Cube n),
      a ≠ 0 ∧ Module.finrank FABL.𝔽₂ D = 4 ∧ a ∈ D ∧
        FABL.booleanDerivative h a = affineFlatIndicator D b := by
  obtain ⟨a, ha, hdWeight⟩ :=
    exists_weight_sixteen_derivative h hn hdegree hweight
  let d := FABL.booleanDerivative h a
  have hdNe : d ≠ 0 := by
    intro hdZero
    have : FABL.booleanDerivative h a = 0 := hdZero
    rw [this] at hdWeight
    simp at hdWeight
  have hdDegreeLe : FABL.functionAlgebraicDegree d ≤ n - 4 := by
    exact (FABL.functionAlgebraicDegree_booleanDerivative_le h a).trans
      (by omega)
  have hdDegree : FABL.functionAlgebraicDegree d = n - 4 := by
    by_contra hne
    have hlt : FABL.functionAlgebraicDegree d < n - 4 :=
      lt_of_le_of_ne hdDegreeLe hne
    by_cases hnFour : n = 4
    · subst n
      norm_num at hlt
    · have hnFive : 5 ≤ n := by omega
      have hsmall : FABL.functionAlgebraicDegree d ≤ n - 5 := by omega
      have hlower := two_pow_sub_le_hammingWeight_of_degree_le d hsmall hdNe
      have hexponent : n - (n - 5) = 5 := by omega
      rw [hexponent, hdWeight] at hlower
      norm_num at hlower
  have hpower : 2 ^ (n - (n - 4)) = 16 := by
    have : n - (n - 4) = 4 := by omega
    rw [this]
    norm_num
  obtain ⟨D, b, hDrank, hdIndicator⟩ :=
    (degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator
      d (r := n - 4) (by omega)).mp
        ⟨hdDegree, by simpa only [hpower] using hdWeight⟩
  have hDrankFour : Module.finrank FABL.𝔽₂ D = 4 := by
    simpa only [show n - (n - 4) = 4 by omega] using hDrank
  have hbMem : b ∈ FABL.binaryAffineSubspace D b := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact D.zero_mem
  have hbaMem : b + a ∈ FABL.binaryAffineSubspace D b := by
    have hdAtB : d b = 1 := by
      rw [hdIndicator]
      simp [affineFlatIndicator, hbMem]
    have hdAtBA : d (b + a) = 1 := by
      have heq : d (b + a) = d b := by
        dsimp only [d]
        simp only [FABL.booleanDerivative]
        have harg : b + a + a = b := by
          rw [add_assoc, ZModModule.add_self, add_zero]
        rw [harg]
        exact add_comm _ _
      rw [heq, hdAtB]
    rw [hdIndicator] at hdAtBA
    exact (affineFlatIndicator_apply_eq_one_iff D b (b + a)).mp hdAtBA
  have haD : a ∈ D := by
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem] at hbaMem
    have harg : b + a + b = a := by
      calc
        b + a + b = a + (b + b) := by abel
        _ = a := by rw [ZModModule.add_self, add_zero]
    rwa [harg] at hbaMem
  exact ⟨a, D, b, ha, hDrankFour, haD, hdIndicator⟩

private theorem add_direction_mem_pair_iff
    (a p x : FABL.F₂Cube n) :
    x + a ∈ ({p, p + a} : Finset (FABL.F₂Cube n)) ↔
      x ∈ ({p, p + a} : Finset (FABL.F₂Cube n)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      calc
        x = (x + a) + a := by
          rw [add_assoc, ZModModule.add_self, add_zero]
        _ = p + a := by rw [h]
    · left
      calc
        x = (x + a) + a := by
          rw [add_assoc, ZModModule.add_self, add_zero]
        _ = p := by
          rw [h, add_assoc, ZModModule.add_self, add_zero]
  · rintro (rfl | rfl)
    · right; rfl
    · left
      rw [add_assoc, ZModModule.add_self, add_zero]

private theorem card_direction_pair
    (a p : FABL.F₂Cube n) (ha : a ≠ 0) :
    ({p, p + a} : Finset (FABL.F₂Cube n)).card = 2 := by
  have hne : p + a ≠ p := by
    intro hpa
    apply ha
    apply add_left_cancel
    simpa only [add_zero] using hpa
  simp [Ne.symm hne]

private theorem exists_three_direction_pair_representatives
    (O : Finset (FABL.F₂Cube n))
    (a : FABL.F₂Cube n) (ha : a ≠ 0)
    (hcard : O.card = 6)
    (hinvariant : ∀ x, x ∈ O → x + a ∈ O) :
    ∃ p q r : FABL.F₂Cube n,
      O = {p, p + a} ∪ {q, q + a} ∪ {r, r + a} ∧
      Disjoint ({p, p + a} : Finset (FABL.F₂Cube n)) {q, q + a} ∧
      Disjoint (({p, p + a} ∪ {q, q + a}) :
        Finset (FABL.F₂Cube n)) {r, r + a} := by
  classical
  have hOne : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hOne
  let P : Finset (FABL.F₂Cube n) := {p, p + a}
  have hPsub : P ⊆ O := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hinvariant p hp
  have hPcard : P.card = 2 := card_direction_pair a p ha
  let O₁ := O \ P
  have hO₁card : O₁.card = 4 := by
    change (O \ P).card = 4
    rw [Finset.card_sdiff_of_subset hPsub, hcard, hPcard]
  have hO₁nonempty : O₁.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq⟩ := hO₁nonempty
  let Q : Finset (FABL.F₂Cube n) := {q, q + a}
  have hQsub : Q ⊆ O₁ := by
    intro x hx
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    have hqO : q ∈ O := (Finset.mem_sdiff.mp hq).1
    have hqNotP : q ∉ P := (Finset.mem_sdiff.mp hq).2
    rcases hx with rfl | rfl
    · exact hq
    · apply Finset.mem_sdiff.mpr
      refine ⟨hinvariant q hqO, ?_⟩
      simpa only [P, add_direction_mem_pair_iff] using hqNotP
  have hQcard : Q.card = 2 := card_direction_pair a q ha
  let O₂ := O₁ \ Q
  have hO₂card : O₂.card = 2 := by
    change (O₁ \ Q).card = 2
    rw [Finset.card_sdiff_of_subset hQsub, hO₁card, hQcard]
  have hO₂nonempty : O₂.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ := hO₂nonempty
  let R : Finset (FABL.F₂Cube n) := {r, r + a}
  have hRsub : R ⊆ O₂ := by
    intro x hx
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hx
    have hrO₁ : r ∈ O₁ := (Finset.mem_sdiff.mp hr).1
    have hrNotQ : r ∉ Q := (Finset.mem_sdiff.mp hr).2
    have hrO : r ∈ O := (Finset.mem_sdiff.mp hrO₁).1
    have hrNotP : r ∉ P := (Finset.mem_sdiff.mp hrO₁).2
    rcases hx with rfl | rfl
    · exact hr
    · apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_sdiff.mpr
        refine ⟨hinvariant r hrO, ?_⟩
        simpa only [P, add_direction_mem_pair_iff] using hrNotP
      · simpa only [Q, add_direction_mem_pair_iff] using hrNotQ
  have hRcard : R.card = 2 := card_direction_pair a r ha
  have hR_eq : O₂ = R := by
    symm
    apply Finset.eq_of_subset_of_card_le hRsub
    rw [hRcard, hO₂card]
  have hO₁eq : O₁ = Q ∪ R := by
    rw [← hR_eq]
    exact (Finset.union_sdiff_of_subset hQsub).symm
  have hOeq : O = P ∪ Q ∪ R := by
    calc
      O = P ∪ O₁ := (Finset.union_sdiff_of_subset hPsub).symm
      _ = P ∪ (Q ∪ R) := by rw [hO₁eq]
      _ = P ∪ Q ∪ R := by rw [Finset.union_assoc]
  have hPQdisjoint : Disjoint P Q := by
    exact Finset.disjoint_left.mpr (fun x hxP hxQ ↦
      (Finset.mem_sdiff.mp (hQsub hxQ)).2 hxP)
  have hPQRdisjoint : Disjoint (P ∪ Q) R := by
    exact Finset.disjoint_left.mpr (fun x hxPQ hxR ↦ by
      have hxO₂ := hRsub hxR
      have hxNotQ := (Finset.mem_sdiff.mp hxO₂).2
      have hxNotP := (Finset.mem_sdiff.mp
        (Finset.mem_sdiff.mp hxO₂).1).2
      exact (Finset.mem_union.mp hxPQ).elim hxNotP hxNotQ)
  exact ⟨p, q, r, by simpa only [P, Q, R] using hOeq,
    by simpa only [P, Q] using hPQdisjoint,
    by simpa only [P, Q, R] using hPQRdisjoint⟩

private noncomputable def commonSupportPairs
    (h : BooleanFunction n) (a : FABL.F₂Cube n) :
    Finset (FABL.F₂Cube n) :=
  support h ∩ support (fun x ↦ h (x + a))

@[simp] private theorem mem_commonSupportPairs
    (h : BooleanFunction n) (a x : FABL.F₂Cube n) :
    x ∈ commonSupportPairs h a ↔ h x = 1 ∧ h (x + a) = 1 := by
  simp [commonSupportPairs, mem_support]

private theorem commonSupportPairs_invariant
    (h : BooleanFunction n) (a x : FABL.F₂Cube n)
    (hx : x ∈ commonSupportPairs h a) :
    x + a ∈ commonSupportPairs h a := by
  rw [mem_commonSupportPairs] at hx ⊢
  refine ⟨hx.2, ?_⟩
  simpa only [add_assoc, ZModModule.add_self, add_zero] using hx.1

private theorem card_commonSupportPairs_of_weight_fourteen_derivative_sixteen
    (h : BooleanFunction n) (a : FABL.F₂Cube n)
    (hweight : hammingWeight h = 14)
    (hderivative : hammingWeight (FABL.booleanDerivative h a) = 16) :
    (commonSupportPairs h a).card = 6 := by
  let t : BooleanFunction n := fun x ↦ h (x + a)
  have htWeight : hammingWeight t = 14 := by
    simpa only [t, hweight] using hammingWeight_translate h a
  have hidentity := hammingWeight_add_add_two_mul_card_support_inter h t
  have hadd : h + t = FABL.booleanDerivative h a := rfl
  change (support h ∩ support t).card = 6
  rw [hadd, hderivative, hweight, htWeight] at hidentity
  omega

private theorem support_outside_derivative_subset_commonSupportPairs
    (h : BooleanFunction n) (a x : FABL.F₂Cube n)
    (hx : x ∈ support h)
    (hxd : x ∉ support (FABL.booleanDerivative h a)) :
    x ∈ commonSupportPairs h a := by
  rw [mem_commonSupportPairs]
  refine ⟨(mem_support h x).mp hx, ?_⟩
  have hdZero : FABL.booleanDerivative h a x = 0 := by
    by_contra hd
    exact hxd ((mem_support _ x).mpr (Fin.eq_one_of_ne_zero _ hd))
  rw [FABL.booleanDerivative, (mem_support h x).mp hx] at hdZero
  have hneg := add_eq_zero_iff_eq_neg.mp hdZero
  simpa only [ZMod.neg_eq_self_mod_two] using hneg.symm

private theorem commonSupportPairs_disjoint_derivativeSupport
    (h : BooleanFunction n) (a : FABL.F₂Cube n) :
    Disjoint (commonSupportPairs h a)
      (support (FABL.booleanDerivative h a)) := by
  rw [Finset.disjoint_left]
  intro x hxO hxd
  rw [mem_commonSupportPairs] at hxO
  have hdOne := (mem_support (FABL.booleanDerivative h a) x).mp hxd
  rw [FABL.booleanDerivative, hxO.1, hxO.2] at hdOne
  change (0 : FABL.𝔽₂) = 1 at hdOne
  exact zero_ne_one hdOne

private noncomputable def threePairDirection
    (a p q r : FABL.F₂Cube n) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  Submodule.span FABL.𝔽₂
    (↑({a, q + p, r + p} : Finset (FABL.F₂Cube n)) :
      Set (FABL.F₂Cube n))

private noncomputable def threePairFlat
    (a p q r : FABL.F₂Cube n) :
    AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.binaryAffineSubspace (threePairDirection a p q r) p

private theorem three_direction_pairs_subset_threePairFlat
    (a p q r : FABL.F₂Cube n) :
    ({p, p + a} ∪ {q, q + a} ∪ {r, r + a} :
      Finset (FABL.F₂Cube n)) ⊆
      binaryAffineFlatPoints (threePairFlat a p q r) := by
  intro x hx
  rw [mem_binaryAffineFlatPoints]
  unfold threePairFlat
  rw [
    FABL.mem_binaryAffineSubspace_iff_add_mem]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with ((hxp | hxpa) | (hxq | hxqa)) | (hxr | hxra)
  · subst x
    rw [ZModModule.add_self]
    exact Submodule.zero_mem _
  · subst x
    have harg : p + a + p = a := by
      calc
        p + a + p = a + (p + p) := by abel
        _ = a := by rw [ZModModule.add_self, add_zero]
    rw [harg]
    exact Submodule.subset_span (by simp)
  · subst x
    exact Submodule.subset_span (by simp)
  · subst x
    have ha : a ∈ threePairDirection a p q r :=
      Submodule.subset_span (by simp)
    have hqp : q + p ∈ threePairDirection a p q r :=
      Submodule.subset_span (by simp)
    have harg : q + a + p = a + (q + p) := by abel
    rw [harg]
    exact (threePairDirection a p q r).add_mem ha hqp
  · subst x
    exact Submodule.subset_span (by simp)
  · subst x
    have ha : a ∈ threePairDirection a p q r :=
      Submodule.subset_span (by simp)
    have hrp : r + p ∈ threePairDirection a p q r :=
      Submodule.subset_span (by simp)
    have harg : r + a + p = a + (r + p) := by abel
    rw [harg]
    exact (threePairDirection a p q r).add_mem ha hrp

private theorem finrank_threePairDirection_le_three
    (a p q r : FABL.F₂Cube n) :
    Module.finrank FABL.𝔽₂ (threePairDirection a p q r) ≤ 3 := by
  have hspan := finrank_span_finset_le_card (R := FABL.𝔽₂)
    ({a, q + p, r + p} : Finset (FABL.F₂Cube n))
  have hcard : ({a, q + p, r + p} :
      Finset (FABL.F₂Cube n)).card ≤ 3 := Finset.card_le_three
  rw [Set.finrank] at hspan
  unfold threePairDirection
  exact hspan.trans hcard

private theorem threePairFlat_ne_bot
    (a p q r : FABL.F₂Cube n) :
    threePairFlat a p q r ≠ ⊥ := by
  intro hbot
  have hp : p ∈ (⊥ : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) := by
    rw [← hbot]
    exact AffineSubspace.self_mem_mk' _ _
  rw [← SetLike.mem_coe, AffineSubspace.bot_coe] at hp
  exact hp

private theorem finrank_threePairDirection_eq_three_of_six_subset
    (O : Finset (FABL.F₂Cube n))
    (a p q r : FABL.F₂Cube n)
    (hOcard : O.card = 6)
    (hOsub : O ⊆ binaryAffineFlatPoints (threePairFlat a p q r)) :
    Module.finrank FABL.𝔽₂ (threePairDirection a p q r) = 3 := by
  have hcardFlat := card_binaryAffineFlatPoints (threePairFlat a p q r)
    (threePairFlat_ne_bot a p q r)
  rw [threePairFlat, FABL.binaryAffineSubspace_direction] at hcardFlat
  have hlower : 6 ≤ 2 ^ Module.finrank FABL.𝔽₂
      (threePairDirection a p q r) := by
    rw [← hcardFlat, ← hOcard]
    exact Finset.card_mono hOsub
  have hupper := finrank_threePairDirection_le_three a p q r
  interval_cases Module.finrank FABL.𝔽₂
    (threePairDirection a p q r)
  all_goals norm_num at hlower
  all_goals omega

private theorem threePairDirection_contains_direction
    (a p q r : FABL.F₂Cube n) :
    a ∈ threePairDirection a p q r := by
  apply Submodule.subset_span
  simp

private theorem threePairFlat_add_direction_mem_iff
    (a p q r x : FABL.F₂Cube n) :
    x + a ∈ threePairFlat a p q r ↔
      x ∈ threePairFlat a p q r := by
  unfold threePairFlat
  rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
    FABL.mem_binaryAffineSubspace_iff_add_mem]
  have ha := threePairDirection_contains_direction a p q r
  constructor
  · intro hx
    have := (threePairDirection a p q r).add_mem hx ha
    have harg : (x + a + p) + a = x + p := by
      calc
        (x + a + p) + a = x + p + (a + a) := by abel
        _ = x + p := by rw [ZModModule.add_self, add_zero]
    rwa [harg] at this
  · intro hx
    have := (threePairDirection a p q r).add_mem hx ha
    have harg : (x + p) + a = x + a + p := by abel
    rwa [harg] at this

/-- Kasami--Tokura's weight-fourteen existence classification. -/
theorem hasWeightFourteenFlatPairClassification (n : ℕ) :
    HasWeightFourteenFlatPairClassification n := by
  intro h hh
  have hhData : h ∈ reedMuller (n - 3) n ∧ hammingWeight h = 14 := by
    simpa only [orderTwoWeightFourteenDualWords, orderTwoDualWords,
      Finset.mem_filter, Finset.mem_univ, true_and] using hh
  have hmem := hhData.1
  have hweight := hhData.2
  have hn : 4 ≤ n := four_le_dimension_of_weight_fourteen h hweight
  have hdegree : FABL.functionAlgebraicDegree h ≤ n - 3 := by
    simpa only [mem_reedMuller_iff] using hmem
  obtain ⟨a, D, b, ha, hDrank, haD, hdIndicator⟩ :=
    exists_derivative_affine_four_flat h hn hdegree hweight
  let d := FABL.booleanDerivative h a
  let A : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.binaryAffineSubspace D b
  have hbA : b ∈ A := by
    change b ∈ FABL.binaryAffineSubspace D b
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact D.zero_mem
  have hdBinaryIndicator : d = binaryAffineFlatIndicator A := by
    change FABL.booleanDerivative h a = binaryAffineFlatIndicator A
    rw [hdIndicator]
    calc
      affineFlatIndicator D b = affineFlatIndicator A.direction b := by
        change affineFlatIndicator D b =
          affineFlatIndicator (FABL.binaryAffineSubspace D b).direction b
        rw [FABL.binaryAffineSubspace_direction]
      _ = binaryAffineFlatIndicator A :=
        (binaryAffineFlatIndicator_eq_affineFlatIndicator A b hbA).symm
  have hdWeight : hammingWeight d = 16 := by
    rw [hdBinaryIndicator,
      hammingWeight_binaryAffineFlatIndicator A]
    · change 2 ^ Module.finrank FABL.𝔽₂
          (FABL.binaryAffineSubspace D b).direction = 16
      rw [FABL.binaryAffineSubspace_direction, hDrank]
      norm_num
    · intro hbot
      have := hbA
      rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at this
      exact this
  let O := commonSupportPairs h a
  have hOcard : O.card = 6 := by
    exact card_commonSupportPairs_of_weight_fourteen_derivative_sixteen
      h a hweight hdWeight
  have hOinvariant : ∀ x, x ∈ O → x + a ∈ O := by
    intro x hx
    exact commonSupportPairs_invariant h a x hx
  obtain ⟨p, q, r, hOeq, hpqDisjoint, hpqrDisjoint⟩ :=
    exists_three_direction_pair_representatives O a ha hOcard hOinvariant
  let Kdir := threePairDirection a p q r
  let K := threePairFlat a p q r
  let Kpoints := binaryAffineFlatPoints K
  have hOsubK : O ⊆ Kpoints := by
    rw [hOeq]
    exact three_direction_pairs_subset_threePairFlat a p q r
  have hKrank : Module.finrank FABL.𝔽₂ Kdir = 3 := by
    exact finrank_threePairDirection_eq_three_of_six_subset
      O a p q r hOcard hOsubK
  have hKdirection : K.direction = Kdir := by
    change (threePairFlat a p q r).direction =
      threePairDirection a p q r
    rw [threePairFlat, FABL.binaryAffineSubspace_direction]
  have hKcard : Kpoints.card = 8 := by
    have hcard := card_binaryAffineFlatPoints K
      (threePairFlat_ne_bot a p q r)
    change Kpoints.card = 8
    rw [hcard]
    rw [hKdirection, hKrank]
    norm_num
  let C := Kpoints \ O
  have hCcard : C.card = 2 := by
    change (Kpoints \ O).card = 2
    rw [Finset.card_sdiff_of_subset hOsubK, hKcard, hOcard]
  have hCinvariant : ∀ x, x ∈ C → x + a ∈ C := by
    intro x hx
    have hxData := Finset.mem_sdiff.mp hx
    apply Finset.mem_sdiff.mpr
    constructor
    · have hxK : x ∈ K := (mem_binaryAffineFlatPoints K x).mp hxData.1
      apply (mem_binaryAffineFlatPoints K (x + a)).mpr
      exact (threePairFlat_add_direction_mem_iff a p q r x).mpr hxK
    · intro hxaO
      apply hxData.2
      have := hOinvariant (x + a) hxaO
      simpa only [add_assoc, ZModModule.add_self, add_zero] using this
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hCnonempty
  have hcAdd : c + a ∈ C := hCinvariant c hc
  have hcNe : c ≠ c + a := by
    intro heq
    apply ha
    apply add_left_cancel
    simpa only [add_zero] using heq.symm
  have hCeq : C = {c, c + a} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hpairSub : ({c, c + a} : Finset (FABL.F₂Cube n)) ⊆ C := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hc
        · exact hcAdd
      have hpairCard := card_direction_pair a c ha
      have heq : ({c, c + a} : Finset (FABL.F₂Cube n)) = C :=
        Finset.eq_of_subset_of_card_le hpairSub (by rw [hpairCard, hCcard])
      simpa only [heq] using hx
    · rw [hCcard]
      simp [hcNe]
  have hKne : K ≠ ⊥ := threePairFlat_ne_bot a p q r
  have hKrankDirection : Module.finrank FABL.𝔽₂ K.direction = 3 := by
    rw [hKdirection]
    exact hKrank
  have hKmem : K ∈ binaryAffineFlats 3 n := by
    simp only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hKne, hKrankDirection⟩
  have hKindicatorWeight :
      hammingWeight (binaryAffineFlatIndicator K) = 8 := by
    rw [hammingWeight_binaryAffineFlatIndicator K hKne,
      hKrankDirection]
    norm_num
  have hCsubsetDerivative : C ⊆ support d := by
    have hcDerivative : c ∈ support d := by
      by_contra hcNotDerivative
      have hcAddNotDerivative : c + a ∉ support d := by
        intro hcAddDerivative
        apply hcNotDerivative
        apply (mem_support d c).mpr
        have hvalue := booleanDerivative_value_add_direction h a c
        have hcAddOne := (mem_support d (c + a)).mp hcAddDerivative
        change d (c + a) = d c at hvalue
        rw [← hvalue]
        exact hcAddOne
      have hsupportInterK : support h ∩ Kpoints = O := by
        ext x
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hxSupport, hxK⟩
          by_cases hxO : x ∈ O
          · exact hxO
          · have hxC : x ∈ C := Finset.mem_sdiff.mpr ⟨hxK, hxO⟩
            rw [hCeq] at hxC
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
            have hxNotDerivative : x ∉ support d := by
              rcases hxC with rfl | rfl
              · exact hcNotDerivative
              · exact hcAddNotDerivative
            exact (hxO
              (support_outside_derivative_subset_commonSupportPairs
                h a x hxSupport hxNotDerivative)).elim
        · intro hxO
          have hxCommon := (mem_commonSupportPairs h a x).mp hxO
          exact ⟨(mem_support h x).mpr hxCommon.1, hOsubK hxO⟩
      have hinterCard : (support h ∩
          support (binaryAffineFlatIndicator K)).card = 6 := by
        rw [support_binaryAffineFlatIndicator, hsupportInterK, hOcard]
      have hsumWeight :=
        hammingWeight_add_add_two_mul_card_support_inter h
          (binaryAffineFlatIndicator K)
      rw [hweight, hKindicatorWeight, hinterCard] at hsumWeight
      have hten : hammingWeight
          (h + binaryAffineFlatIndicator K) = 10 := by omega
      have hsumMem : h + binaryAffineFlatIndicator K ∈
          reedMuller (n - 3) n :=
        (reedMuller (n - 3) n).add_mem hmem
          (binaryAffineFlatIndicator_mem_reedMuller K hKmem)
      exact hammingWeight_ne_ten_of_mem_reedMuller_codimension_three
        (h + binaryAffineFlatIndicator K) (by omega) hsumMem hten
    intro x hxC
    rw [hCeq] at hxC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
    rcases hxC with rfl | rfl
    · exact hcDerivative
    · apply (mem_support d (c + a)).mpr
      have hvalue := booleanDerivative_value_add_direction h a c
      change d (c + a) = d c at hvalue
      rw [hvalue]
      exact (mem_support d c).mp hcDerivative
  have hcDerivativeOne : d c = 1 :=
    (mem_support d c).mp (hCsubsetDerivative hc)
  have hsumAtC : h c + h (c + a) = 1 := by
    simpa only [d, FABL.booleanDerivative] using hcDerivativeOne
  have hsupportCcard : (support h ∩ C).card = 1 := by
    rw [hCeq]
    by_cases hcZero : h c = 0
    · have hcAddOne : h (c + a) = 1 := by
        simpa only [hcZero, zero_add] using hsumAtC
      have hcNotSupport : c ∉ support h := by
        intro hcSupport
        exact zero_ne_one (hcZero.symm.trans (mem_support h c |>.mp hcSupport))
      have hcAddSupport : c + a ∈ support h :=
        (mem_support h (c + a)).mpr hcAddOne
      have hinter : support h ∩ ({c, c + a} : Finset (FABL.F₂Cube n)) =
          {c + a} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxSupport, rfl | rfl⟩
          · exact (hcNotSupport hxSupport).elim
          · exact rfl
        · intro hx
          subst x
          exact ⟨hcAddSupport, Or.inr rfl⟩
      rw [hinter]
      simp
    · have hcOne : h c = 1 := Fin.eq_one_of_ne_zero _ hcZero
      have hcAddZero : h (c + a) = 0 := by
        have heq : 1 + h (c + a) = 1 + 0 := by
          simpa only [hcOne, add_zero] using hsumAtC
        exact add_left_cancel heq
      have hcSupport : c ∈ support h := (mem_support h c).mpr hcOne
      have hcAddNotSupport : c + a ∉ support h := by
        intro hcAddSupport
        exact zero_ne_one
          (hcAddZero.symm.trans (mem_support h (c + a) |>.mp hcAddSupport))
      have hinter : support h ∩ ({c, c + a} : Finset (FABL.F₂Cube n)) =
          {c} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hxSupport, rfl | rfl⟩
          · exact rfl
          · exact (hcAddNotSupport hxSupport).elim
        · intro hx
          subst x
          exact ⟨hcSupport, Or.inl rfl⟩
      rw [hinter]
      simp
  have hOsubSupport : O ⊆ support h := by
    intro x hxO
    exact (mem_support h x).mpr ((mem_commonSupportPairs h a x).mp hxO).1
  have hsupportInterKpoints :
      support h ∩ Kpoints = O ∪ (support h ∩ C) := by
    calc
      support h ∩ Kpoints = support h ∩ (O ∪ (Kpoints \ O)) := by
        rw [Finset.union_sdiff_of_subset hOsubK]
      _ = (support h ∩ O) ∪ (support h ∩ (Kpoints \ O)) := by
        exact Finset.inter_union_distrib_left _ _ _
      _ = O ∪ (support h ∩ C) := by
        rw [Finset.inter_eq_right.mpr hOsubSupport]
  have hOdisjointSupportC : Disjoint O (support h ∩ C) := by
    apply Disjoint.mono_right Finset.inter_subset_right
    change Disjoint O (Kpoints \ O)
    exact Finset.disjoint_sdiff
  have hsupportInterKcard : (support h ∩ Kpoints).card = 7 := by
    rw [hsupportInterKpoints,
      Finset.card_union_of_disjoint hOdisjointSupportC,
      hOcard, hsupportCcard]
  let g : BooleanFunction n := h + binaryAffineFlatIndicator K
  have hinterIndicatorCard :
      (support h ∩ support (binaryAffineFlatIndicator K)).card = 7 := by
    rw [support_binaryAffineFlatIndicator]
    exact hsupportInterKcard
  have hgWeight : hammingWeight g = 8 := by
    have hsumWeight :=
      hammingWeight_add_add_two_mul_card_support_inter h
        (binaryAffineFlatIndicator K)
    rw [hweight, hKindicatorWeight, hinterIndicatorCard] at hsumWeight
    change hammingWeight (h + binaryAffineFlatIndicator K) = 8
    omega
  have hgMem : g ∈ reedMuller (n - 3) n := by
    exact (reedMuller (n - 3) n).add_mem hmem
      (binaryAffineFlatIndicator_mem_reedMuller K hKmem)
  have hgDegreeLe : FABL.functionAlgebraicDegree g ≤ n - 3 := by
    simpa only [mem_reedMuller_iff] using hgMem
  have hgNe : g ≠ 0 := by
    intro hgZero
    rw [hgZero] at hgWeight
    norm_num at hgWeight
  have hgDegree : FABL.functionAlgebraicDegree g = n - 3 := by
    apply Nat.le_antisymm hgDegreeLe
    by_contra hnot
    have hgDegreeFour : FABL.functionAlgebraicDegree g ≤ n - 4 := by
      omega
    have hlower := two_pow_sub_le_hammingWeight_of_degree_le
      g hgDegreeFour hgNe
    have hsub : n - (n - 4) = 4 := by omega
    rw [hsub, hgWeight] at hlower
    norm_num at hlower
  have hgWeightPower : hammingWeight g = 2 ^ (n - (n - 3)) := by
    rw [hgWeight]
    norm_num [show n - (n - 3) = 3 by omega]
  obtain ⟨Hdir, u, hHrank, hgAffineIndicator⟩ :=
    (degree_eq_and_hammingWeight_eq_iff_exists_affineFlatIndicator
      g (r := n - 3) (by omega)).mp ⟨hgDegree, hgWeightPower⟩
  let H : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n) :=
    FABL.binaryAffineSubspace Hdir u
  have huH : u ∈ H := by
    change u ∈ FABL.binaryAffineSubspace Hdir u
    rw [FABL.mem_binaryAffineSubspace_iff_add_mem,
      ZModModule.add_self]
    exact Hdir.zero_mem
  have hHdirection : H.direction = Hdir := by
    change (FABL.binaryAffineSubspace Hdir u).direction = Hdir
    rw [FABL.binaryAffineSubspace_direction]
  have hHrankDirection : Module.finrank FABL.𝔽₂ H.direction = 3 := by
    rw [hHdirection, hHrank]
    omega
  have hHne : H ≠ ⊥ := by
    intro hbot
    have := huH
    rw [hbot, ← SetLike.mem_coe, AffineSubspace.bot_coe] at this
    exact this
  have hHmem : H ∈ binaryAffineFlats 3 n := by
    simp only [binaryAffineFlats, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hHne, hHrankDirection⟩
  have hgBinaryIndicator : g = binaryAffineFlatIndicator H := by
    calc
      g = affineFlatIndicator Hdir u := hgAffineIndicator
      _ = affineFlatIndicator H.direction u := by rw [hHdirection]
      _ = binaryAffineFlatIndicator H :=
        (binaryAffineFlatIndicator_eq_affineFlatIndicator H u huH).symm
  have hdecomposition :
      h = binaryAffineFlatIndicator H + binaryAffineFlatIndicator K := by
    funext x
    have hx := congrFun hgBinaryIndicator x
    change h x + binaryAffineFlatIndicator K x =
      binaryAffineFlatIndicator H x at hx
    calc
      h x = (h x + binaryAffineFlatIndicator K x) +
          binaryAffineFlatIndicator K x := by
            rw [add_assoc, ZModModule.add_self, add_zero]
      _ = binaryAffineFlatIndicator H x +
          binaryAffineFlatIndicator K x := by rw [hx]
  have hHindicatorWeight : hammingWeight (binaryAffineFlatIndicator H) = 8 := by
    rw [hammingWeight_binaryAffineFlatIndicator H hHne,
      hHrankDirection]
    norm_num
  have hflatSupportInterCard :
      (support (binaryAffineFlatIndicator H) ∩
        support (binaryAffineFlatIndicator K)).card = 1 := by
    have hweightIdentity :=
      hammingWeight_add_add_two_mul_card_support_inter
        (binaryAffineFlatIndicator H) (binaryAffineFlatIndicator K)
    rw [← hdecomposition, hweight, hHindicatorWeight,
      hKindicatorWeight] at hweightIdentity
    omega
  have hflatPointsInterCard :
      (binaryAffineFlatPoints H ∩ binaryAffineFlatPoints K).card = 1 := by
    simpa only [support_binaryAffineFlatIndicator] using hflatSupportInterCard
  obtain ⟨u₀, hflatPointsInter⟩ := Finset.card_eq_one.mp hflatPointsInterCard
  have hu₀Inter :
      u₀ ∈ binaryAffineFlatPoints H ∩ binaryAffineFlatPoints K := by
    rw [hflatPointsInter]
    simp
  have hu₀H : u₀ ∈ H :=
    (mem_binaryAffineFlatPoints H u₀).mp (Finset.mem_inter.mp hu₀Inter).1
  have hu₀K : u₀ ∈ K :=
    (mem_binaryAffineFlatPoints K u₀).mp (Finset.mem_inter.mp hu₀Inter).2
  have hHflat : FABL.binaryAffineSubspace Hdir u₀ = H := by
    calc
      FABL.binaryAffineSubspace Hdir u₀ =
          FABL.binaryAffineSubspace H.direction u₀ := by rw [hHdirection]
      _ = H := AffineSubspace.mk'_eq hu₀H
  have hKflat : FABL.binaryAffineSubspace Kdir u₀ = K := by
    calc
      FABL.binaryAffineSubspace Kdir u₀ =
          FABL.binaryAffineSubspace K.direction u₀ := by rw [hKdirection]
      _ = K := AffineSubspace.mk'_eq hu₀K
  have hAffineInterSet :
      ((H ⊓ K : AffineSubspace FABL.𝔽₂ (FABL.F₂Cube n)) :
        Set (FABL.F₂Cube n)) = {u₀} := by
    ext x
    change (x ∈ H ∧ x ∈ K) ↔ x = u₀
    have hx := congrArg (fun s : Finset (FABL.F₂Cube n) ↦ x ∈ s)
      hflatPointsInter
    exact Iff.of_eq (by
      simpa only [Finset.mem_inter, mem_binaryAffineFlatPoints,
        Finset.mem_singleton] using hx)
  have hInfDirection : (H ⊓ K).direction = ⊥ := by
    rw [AffineSubspace.direction_eq_vectorSpan, hAffineInterSet,
      vectorSpan_singleton]
  have hmeet : Hdir ⊓ Kdir = ⊥ := by
    calc
      Hdir ⊓ Kdir = H.direction ⊓ K.direction := by
        rw [hHdirection, hKdirection]
      _ = (H ⊓ K).direction :=
        (AffineSubspace.direction_inf_of_mem hu₀H hu₀K).symm
      _ = ⊥ := hInfDirection
  have hHrankThree : Module.finrank FABL.𝔽₂ Hdir = 3 := by
    omega
  have hpairMem :
      (Hdir, Kdir) ∈ transverseBinaryThreeSubspacePairs n := by
    have hpProduct : (Hdir, Kdir) ∈ binaryThreeSubspacePairs n := by
      change (Hdir, Kdir) ∈
        (binaryLinearSubspaces 3 n).product (binaryLinearSubspaces 3 n)
      exact Finset.mem_product.mpr
        ⟨(mem_binaryLinearSubspaces Hdir).mpr hHrankThree,
          (mem_binaryLinearSubspaces Kdir).mpr hKrank⟩
    have hpData :
        (Hdir, Kdir) ∈ binaryThreeSubspacePairs n ∧ Hdir ⊓ Kdir = ⊥ :=
      ⟨hpProduct, hmeet⟩
    simpa only [transverseBinaryThreeSubspacePairs,
      Finset.mem_filter] using hpData
  refine ⟨u₀, Hdir, Kdir, hpairMem, ?_⟩
  change binaryAffineFlatIndicator (FABL.binaryAffineSubspace Hdir u₀) +
      binaryAffineFlatIndicator (FABL.binaryAffineSubspace Kdir u₀) = h
  rw [hHflat, hKflat]
  exact hdecomposition.symm

end CryptBoolean
