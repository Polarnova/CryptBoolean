/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.OddDimensionBestNonlinearity
public import CryptBoolean.Carlet.Chapter04.HigherOrderNonlinearity

/-!
# Maximum nonlinearity in five variables

The quadratic construction gives nonlinearity twelve.  The matching upper bound is obtained from
the binary leader code on a hypothetical weight-thirteen coset leader, followed by a residual-code
and radius-one sphere-packing contradiction.
-/

open Function
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

private abbrev OneCoordinates {ι : Type*} (x : ι → FABL.𝔽₂) :=
  {i : ι // x i ≠ 0}

private abbrev ZeroCoordinates {ι : Type*} (x : ι → FABL.𝔽₂) :=
  {i : ι // x i = 0}

private def bitWeight (b : FABL.𝔽₂) : ℕ :=
  if b ≠ 0 then 1 else 0

private theorem hammingNorm_eq_sum_bitWeight
    {ι : Type*} [Fintype ι] (x : ι → FABL.𝔽₂) :
    hammingNorm x = ∑ i, bitWeight (x i) := by
  simp [hammingNorm, bitWeight, Finset.card_filter]

private theorem card_oneCoordinates
    {ι : Type*} [Fintype ι] (x : ι → FABL.𝔽₂) :
    Fintype.card (OneCoordinates x) = hammingNorm x := by
  rw [Fintype.card_subtype, hammingNorm]

private theorem card_zeroCoordinates
    {ι : Type*} [Fintype ι] (x : ι → FABL.𝔽₂) :
    Fintype.card (ZeroCoordinates x) = Fintype.card ι - hammingNorm x := by
  rw [Fintype.card_subtype, hammingNorm]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i ↦ x i ≠ 0)
  simp only [Finset.card_univ, not_ne_iff] at hpartition
  omega

private theorem bitWeight_add_intersection_identity (x y : FABL.𝔽₂) :
    bitWeight (x + y) + 2 * (if x ≠ 0 then bitWeight y else 0) =
      bitWeight x + bitWeight y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem sum_ite_nonzero_eq_sum_oneCoordinates
    {ι : Type*} [Fintype ι] (x y : ι → FABL.𝔽₂) :
    (∑ i, if x i ≠ 0 then bitWeight (y i) else 0) =
      ∑ j : OneCoordinates x, bitWeight (y j.1) := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun i ↦ x i ≠ 0)
    (by simp) (fun i ↦ bitWeight (y i))

private theorem hammingNorm_add_restrictOne_identity
    {ι : Type*} [Fintype ι] (x y : ι → FABL.𝔽₂) :
    hammingNorm (x + y) +
        2 * hammingNorm (fun j : OneCoordinates x ↦ y j.1) =
      hammingNorm x + hammingNorm y := by
  rw [hammingNorm_eq_sum_bitWeight, hammingNorm_eq_sum_bitWeight,
    hammingNorm_eq_sum_bitWeight, hammingNorm_eq_sum_bitWeight,
    ← sum_ite_nonzero_eq_sum_oneCoordinates x y, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    ∑ i, (bitWeight ((x + y) i) +
        2 * (if x i ≠ 0 then bitWeight (y i) else 0)) =
        ∑ i, (bitWeight (x i) + bitWeight (y i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using bitWeight_add_intersection_identity (x i) (y i)
    _ = (∑ i, bitWeight (x i)) + ∑ i, bitWeight (y i) :=
      Finset.sum_add_distrib

private theorem bitWeight_add_one (x : FABL.𝔽₂) :
    bitWeight (x + 1) + bitWeight x = 1 := by
  fin_cases x <;> decide

private theorem hammingNorm_add_one_add
    {ι : Type*} [Fintype ι] (x : ι → FABL.𝔽₂) :
    hammingNorm (x + 1) + hammingNorm x = Fintype.card ι := by
  rw [hammingNorm_eq_sum_bitWeight, hammingNorm_eq_sum_bitWeight,
    ← Finset.sum_add_distrib]
  calc
    ∑ i, (bitWeight ((x + 1) i) + bitWeight (x i)) =
        ∑ _i : ι, 1 := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using bitWeight_add_one (x i)
    _ = Fintype.card ι := by simp

private def radiusOneError {ι : Type*} [DecidableEq ι] :
    Option ι → (ι → FABL.𝔽₂)
  | none => 0
  | some i => Pi.single i 1

private theorem radiusOneError_injective
    {ι : Type*} [DecidableEq ι] :
    Function.Injective (radiusOneError (ι := ι)) := by
  intro e e' h
  cases e with
  | none =>
      cases e' with
      | none => rfl
      | some j =>
          exfalso
          have hj := congrFun h j
          simp [radiusOneError] at hj
  | some i =>
      cases e' with
      | none =>
          exfalso
          have hi := congrFun h i
          simp [radiusOneError] at hi
      | some j =>
          congr 1
          by_contra hij
          have hi := congrFun h i
          simp [radiusOneError, hij] at hi

private theorem hammingNorm_radiusOneError_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Option ι) :
    hammingNorm (radiusOneError e) ≤ 1 := by
  cases e with
  | none => simp [radiusOneError]
  | some i =>
      rw [radiusOneError, hammingNorm]
      have hsubset :
          (Finset.univ.filter fun j : ι ↦
            (Pi.single i (1 : FABL.𝔽₂) : ι → FABL.𝔽₂) j ≠ 0) ⊆ {i} := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simpa [Pi.single_apply] using hj
      exact (Finset.card_le_card hsubset).trans_eq (Finset.card_singleton i)

private def radiusOnePackingMap
    {ι : Type*} [DecidableEq ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) :
    C × Option ι → (ι → FABL.𝔽₂) :=
  fun p ↦ p.1.1 + radiusOneError p.2

private theorem radiusOnePackingMap_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂))
    (hmin : ∀ c d : C, c ≠ d → 3 ≤ hammingDist c.1 d.1) :
    Function.Injective (radiusOnePackingMap C) := by
  rintro ⟨c, e⟩ ⟨d, e'⟩ h
  by_cases hcd : c = d
  · subst d
    have herr : radiusOneError e = radiusOneError e' := add_left_cancel h
    rw [radiusOneError_injective herr]
  · have hthree : 3 ≤ hammingDist c.1 d.1 := hmin c d hcd
    have htriangle := hammingDist_triangle c.1
      (radiusOnePackingMap C (c, e)) d.1
    have hfirst :
        hammingDist c.1 (radiusOnePackingMap C (c, e)) =
          hammingNorm (radiusOneError e) := by
      rw [hammingDist_eq_hammingNorm]
      simp [radiusOnePackingMap]
    have hsecond :
        hammingDist (radiusOnePackingMap C (c, e)) d.1 =
          hammingNorm (radiusOneError e') := by
      rw [h, hammingDist_comm, hammingDist_eq_hammingNorm]
      simp [radiusOnePackingMap]
    rw [hfirst, hsecond] at htriangle
    have he := hammingNorm_radiusOneError_le_one e
    have he' := hammingNorm_radiusOneError_le_one e'
    omega

private theorem binaryRadiusOneHammingBound
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂))
    (hmin : ∀ c d : C, c ≠ d → 3 ≤ hammingDist c.1 d.1) :
    2 ^ Module.finrank FABL.𝔽₂ C * (Fintype.card ι + 1) ≤
      2 ^ Fintype.card ι := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have hcard := Fintype.card_le_of_injective
    (radiusOnePackingMap C) (radiusOnePackingMap_injective C hmin)
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fun] at hcard
  rw [← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := C),
    Nat.card_zmod] at hcard
  exact hcard

private def residualMap
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (c : C) :
    C →ₗ[FABL.𝔽₂] (ZeroCoordinates c.1 → FABL.𝔽₂) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def residualCode
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (c : C) :
    Submodule FABL.𝔽₂ (ZeroCoordinates c.1 → FABL.𝔽₂) :=
  LinearMap.range (residualMap C c)

private theorem bitWeight_add_residual_identity (x c : FABL.𝔽₂) :
    bitWeight x + bitWeight (x + c) =
      bitWeight c + 2 * (if c = 0 then bitWeight x else 0) := by
  fin_cases x <;> fin_cases c <;> decide

private theorem sum_ite_zero_eq_sum_zeroCoordinates
    {ι : Type*} [Fintype ι] (x c : ι → FABL.𝔽₂) :
    (∑ i, if c i = 0 then bitWeight (x i) else 0) =
      ∑ j : ZeroCoordinates c, bitWeight (x j.1) := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter fun i ↦ c i = 0)
    (by simp) (fun i ↦ bitWeight (x i))

private theorem hammingNorm_add_residual_identity
    {ι : Type*} [Fintype ι] (x c : ι → FABL.𝔽₂) :
    hammingNorm x + hammingNorm (x + c) =
      hammingNorm c +
        2 * hammingNorm (fun j : ZeroCoordinates c ↦ x j.1) := by
  rw [hammingNorm_eq_sum_bitWeight, hammingNorm_eq_sum_bitWeight,
    hammingNorm_eq_sum_bitWeight, hammingNorm_eq_sum_bitWeight,
    ← Finset.sum_add_distrib]
  calc
    ∑ i, (bitWeight (x i) + bitWeight ((x + c) i)) =
        ∑ i, (bitWeight (c i) +
          2 * (if c i = 0 then bitWeight (x i) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using bitWeight_add_residual_identity (x i) (c i)
    _ = (∑ i, bitWeight (c i)) +
        2 * ∑ i, (if c i = 0 then bitWeight (x i) else 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, bitWeight (c i)) +
        2 * ∑ j : ZeroCoordinates c, bitWeight (x j.1) := by
      rw [sum_ite_zero_eq_sum_zeroCoordinates]

private theorem neg_eq_self_submodule
    {ι : Type*}
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (x : C) :
    -x = x := by
  apply Subtype.ext
  funext i
  simp [ZMod.neg_eq_self_mod_two]

private theorem ker_residualMap_eq_span
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (c : C) (hc : c ≠ 0)
    (hmin : ∀ x : C, x ≠ 0 → hammingNorm c.1 ≤ hammingNorm x.1) :
    (residualMap C c).ker = FABL.𝔽₂ ∙ c := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_span_singleton]
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    by_cases hxc : x = c
    · exact ⟨1, by simp [hxc]⟩
    exfalso
    have hxc0 : x + c ≠ 0 := by
      intro hzero
      have hneg : x = -c := add_eq_zero_iff_eq_neg.mp hzero
      apply hxc
      rw [neg_eq_self_submodule C c] at hneg
      exact hneg
    have hxweight := hmin x hx0
    have hxcweight := hmin (x + c) hxc0
    have hmapzero : residualMap C c x = 0 := hx
    have hidentity := hammingNorm_add_residual_identity x.1 c.1
    change hammingNorm x.1 + hammingNorm (x + c).1 =
      hammingNorm c.1 + 2 * hammingNorm (residualMap C c x) at hidentity
    rw [hmapzero, hammingNorm_zero, mul_zero, add_zero] at hidentity
    have hcpos : 0 < hammingNorm c.1 := hammingNorm_pos_iff.mpr (by
      intro hzero
      apply hc
      exact Subtype.ext hzero)
    omega
  · intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    change residualMap C c (a • c) = 0
    by_cases ha : a = 0
    · subst a
      simp only [zero_smul]
      funext j
      rfl
    · have haone : a = 1 := Fin.eq_one_of_ne_zero a ha
      subst a
      simp only [one_smul]
      funext j
      exact j.2

private theorem finrank_residualCode
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (c : C) (hc : c ≠ 0)
    (hmin : ∀ x : C, x ≠ 0 → hammingNorm c.1 ≤ hammingNorm x.1) :
    Module.finrank FABL.𝔽₂ (residualCode C c) =
      Module.finrank FABL.𝔽₂ C - 1 := by
  have hrank := (residualMap C c).finrank_range_add_finrank_ker
  rw [ker_residualMap_eq_span C c hc hmin, finrank_span_singleton hc] at hrank
  exact Nat.eq_sub_of_add_eq hrank

private theorem residualCode_hammingNorm_ge_three
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂)) (c : C) (_hc : c ≠ 0)
    (hcweight : 5 ≤ hammingNorm c.1)
    (hmin : ∀ x : C, x ≠ 0 → hammingNorm c.1 ≤ hammingNorm x.1)
    (z : residualCode C c) (hz : z ≠ 0) :
    3 ≤ hammingNorm z.1 := by
  obtain ⟨x, hx⟩ := z.2
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    apply hz
    apply Subtype.ext
    simpa using hx.symm
  have hxc0 : x + c ≠ 0 := by
    intro hzero
    have hneg : x = -c := add_eq_zero_iff_eq_neg.mp hzero
    rw [neg_eq_self_submodule C c] at hneg
    subst x
    apply hz
    apply Subtype.ext
    rw [← hx]
    funext j
    exact j.2
  have hxweight := hmin x hx0
  have hxcweight := hmin (x + c) hxc0
  have hidentity := hammingNorm_add_residual_identity x.1 c.1
  change hammingNorm x.1 + hammingNorm (x + c).1 =
    hammingNorm c.1 + 2 * hammingNorm (residualMap C c x) at hidentity
  rw [hx] at hidentity
  omega

private theorem binaryRadiusOneHammingBound_of_hammingNorm
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂))
    (hweight : ∀ c : C, c ≠ 0 → 3 ≤ hammingNorm c.1) :
    2 ^ Module.finrank FABL.𝔽₂ C * (Fintype.card ι + 1) ≤
      2 ^ Fintype.card ι := by
  classical
  apply binaryRadiusOneHammingBound C
  intro x y hxy
  let z : C := y - x
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy.symm
  rw [hammingDist_eq_hammingNorm]
  simpa [z, sub_eq_add_neg, add_comm] using hweight z hz

private theorem noBinaryCodeFinrankFiveCardSevenOrEight
    {ι : Type*} [Fintype ι]
    (C : Submodule FABL.𝔽₂ (ι → FABL.𝔽₂))
    (hfinrank : Module.finrank FABL.𝔽₂ C = 5)
    (hcard : Fintype.card ι = 7 ∨ Fintype.card ι = 8)
    (hweight : ∀ c : C, c ≠ 0 → 3 ≤ hammingNorm c.1) : False := by
  classical
  have hbound := binaryRadiusOneHammingBound_of_hammingNorm C hweight
  rcases hcard with hcard | hcard <;>
    rw [hfinrank, hcard] at hbound <;> norm_num at hbound

private noncomputable def supportRestriction (u : BooleanFunction 5) :
    reedMuller 1 5 →ₗ[FABL.𝔽₂] (OneCoordinates u → FABL.𝔽₂) where
  toFun c j := c.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def leaderCode (u : BooleanFunction 5) :
    Submodule FABL.𝔽₂ (OneCoordinates u → FABL.𝔽₂) :=
  LinearMap.range (supportRestriction u)

private noncomputable def reedMullerOne : reedMuller 1 5 :=
  ⟨FABL.affineFunction 1 0, affineFunction_mem_reedMuller_one 1 0⟩

private theorem supportRestriction_reedMullerOne (u : BooleanFunction 5) :
    supportRestriction u reedMullerOne = 1 := by
  funext j
  simp [supportRestriction, reedMullerOne, FABL.affineFunction,
    FABL.f₂DotProduct]

private theorem supportRestriction_hammingNorm_ge_five
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1))
    (c : reedMuller 1 5) (hc : c ≠ 0) :
    5 ≤ hammingNorm (supportRestriction u c) := by
  obtain ⟨b, a, hca⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one c.1 c.2
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hc
      apply Subtype.ext
      rw [hca]
      funext x
      simp [FABL.affineFunction, ha, hb, FABL.f₂DotProduct]
    have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
    have hrestriction : supportRestriction u c = 1 := by
      funext j
      change c.1 j.1 = 1
      rw [hca]
      simp [FABL.affineFunction, ha, hb_one, FABL.f₂DotProduct]
    rw [hrestriction, hammingNorm]
    simp [card_oneCoordinates u, huweight]
  · have hcweight : hammingWeight c.1 = 16 := by
      rw [hca, hammingWeight_affineFunction_of_ne_zero b a ha]
      norm_num
    let d : reedMuller 1 5 := c + reedMullerOne
    have hdrepresentation :
        d.1 = FABL.affineFunction (b + 1) a := by
      funext x
      simp [d, reedMullerOne, hca, FABL.affineFunction,
        FABL.f₂DotProduct]
      abel
    have hdweight : hammingWeight d.1 = 16 := by
      rw [hdrepresentation, hammingWeight_affineFunction_of_ne_zero (b + 1) a ha]
      norm_num
    have hcidentity := hammingNorm_add_restrictOne_identity u c.1
    change hammingWeight (u + c.1) +
        2 * hammingNorm (supportRestriction u c) =
      hammingWeight u + hammingWeight c.1 at hcidentity
    rw [huweight, hcweight] at hcidentity
    have hcleader := hleader c
    have hcle : hammingNorm (supportRestriction u c) ≤ 8 := by omega
    have hdidentity := hammingNorm_add_restrictOne_identity u d.1
    change hammingWeight (u + d.1) +
        2 * hammingNorm (supportRestriction u d) =
      hammingWeight u + hammingWeight d.1 at hdidentity
    rw [huweight, hdweight] at hdidentity
    have hdleader := hleader d
    have hdle : hammingNorm (supportRestriction u d) ≤ 8 := by omega
    have hrestriction :
        supportRestriction u d = supportRestriction u c + 1 := by
      funext j
      simp [supportRestriction, d, reedMullerOne, FABL.affineFunction,
        FABL.f₂DotProduct]
    have hcomplement := hammingNorm_add_one_add (supportRestriction u c)
    have huNorm : hammingNorm u = 13 := huweight
    rw [← hrestriction, card_oneCoordinates u, huNorm] at hcomplement
    omega

private theorem supportRestriction_injective
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1)) :
    Function.Injective (supportRestriction u) := by
  intro c d hcd
  by_contra hne
  have hsub : supportRestriction u (c - d) = 0 := by
    rw [LinearMap.map_sub, hcd, sub_self]
  have hnonzero : c - d ≠ 0 := sub_ne_zero.mpr hne
  have hfive := supportRestriction_hammingNorm_ge_five
    u huweight hleader (c - d) hnonzero
  rw [hsub, hammingNorm_zero] at hfive
  omega

private theorem leaderCode_finrank
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1)) :
    Module.finrank FABL.𝔽₂ (leaderCode u) = 6 := by
  rw [leaderCode, LinearMap.finrank_range_of_inj
    (supportRestriction_injective u huweight hleader), reedMuller_finrank]
  norm_num [Finset.sum_range_succ]

private theorem leaderCode_hammingNorm_ge_five
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1))
    (z : leaderCode u) (hz : z ≠ 0) :
    5 ≤ hammingNorm z.1 := by
  obtain ⟨c, hc⟩ := z.2
  have hcne : c ≠ 0 := by
    intro hzero
    subst c
    apply hz
    apply Subtype.ext
    simpa using hc.symm
  rw [← hc]
  exact supportRestriction_hammingNorm_ge_five u huweight hleader c hcne

private noncomputable def leaderCodeOne (u : BooleanFunction 5) : leaderCode u :=
  ⟨1, reedMullerOne, supportRestriction_reedMullerOne u⟩

private theorem leaderCodeOne_ne_zero
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13) :
    leaderCodeOne u ≠ 0 := by
  intro hzero
  have hpoint := congrFun (congrArg Subtype.val hzero)
  have hcard : 0 < Fintype.card (OneCoordinates u) := by
    have huNorm : hammingNorm u = 13 := huweight
    rw [card_oneCoordinates u, huNorm]
    omega
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp hcard
  have := hpoint j
  simp [leaderCodeOne] at this

private theorem exists_nontrivial_leaderCode
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1)) :
    ∃ z : leaderCode u, z ≠ 0 ∧ z ≠ leaderCodeOne u := by
  classical
  letI : Fintype (leaderCode u) := Fintype.ofFinite (leaderCode u)
  have hcard : Fintype.card (leaderCode u) = 64 := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := FABL.𝔽₂) (V := leaderCode u),
      Nat.card_zmod, leaderCode_finrank u huweight hleader]
    norm_num
  by_contra hexists
  have hsubset :
      (Finset.univ : Finset (leaderCode u)) ⊆ {0, leaderCodeOne u} := by
    intro z _hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hz
    exact hexists ⟨z, (not_or.mp hz).1, (not_or.mp hz).2⟩
  have hcardle := Finset.card_le_card hsubset
  rw [Finset.card_univ, hcard] at hcardle
  have hpair : ({0, leaderCodeOne u} : Finset (leaderCode u)).card ≤ 2 := by
    exact Finset.card_le_two
  omega

private theorem exists_minimum_leaderCodeWord
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1)) :
    ∃ c : leaderCode u,
      c ≠ 0 ∧
      (∀ z : leaderCode u, z ≠ 0 → hammingNorm c.1 ≤ hammingNorm z.1) ∧
      hammingNorm c.1 ≤ 6 := by
  classical
  letI : Fintype (leaderCode u) := Fintype.ofFinite (leaderCode u)
  let nonzeroWords := (Finset.univ : Finset (leaderCode u)).erase 0
  have hnonempty : nonzeroWords.Nonempty := by
    exact ⟨leaderCodeOne u, by
      simp [nonzeroWords, leaderCodeOne_ne_zero u huweight]⟩
  obtain ⟨c, hc, hceq⟩ := Finset.exists_mem_eq_inf' hnonempty
    (fun z : leaderCode u ↦ hammingNorm z.1)
  have hcne : c ≠ 0 := by simpa [nonzeroWords] using hc
  have hcmin : ∀ z : leaderCode u, z ≠ 0 →
      hammingNorm c.1 ≤ hammingNorm z.1 := by
    intro z hz
    have hle := Finset.inf'_le
      (fun w : leaderCode u ↦ hammingNorm w.1)
      (show z ∈ nonzeroWords by simp [nonzeroWords, hz])
    rw [hceq] at hle
    exact hle
  obtain ⟨q, hqzero, hqone⟩ :=
    exists_nontrivial_leaderCode u huweight hleader
  have hqcomp : q + leaderCodeOne u ≠ 0 := by
    intro hzero
    have hneg : q = -(leaderCodeOne u) := add_eq_zero_iff_eq_neg.mp hzero
    rw [neg_eq_self_submodule (leaderCode u) (leaderCodeOne u)] at hneg
    exact hqone hneg
  have hqle := hcmin q hqzero
  have hqcomple := hcmin (q + leaderCodeOne u) hqcomp
  have hqrepresentation :
      (q + leaderCodeOne u).1 = q.1 + 1 := by
    funext j
    simp [leaderCodeOne]
  have hsum := hammingNorm_add_one_add q.1
  have huNorm : hammingNorm u = 13 := huweight
  rw [← hqrepresentation, card_oneCoordinates u, huNorm] at hsum
  refine ⟨c, hcne, hcmin, ?_⟩
  omega

private theorem no_firstOrderCosetLeader_weight_thirteen
    (u : BooleanFunction 5) (huweight : hammingWeight u = 13)
    (hleader : ∀ c : reedMuller 1 5,
      13 ≤ hammingWeight (u + c.1)) : False := by
  let C := leaderCode u
  obtain ⟨c, hc, hcmin, hcle⟩ :=
    exists_minimum_leaderCodeWord u huweight hleader
  have hcge := leaderCode_hammingNorm_ge_five u huweight hleader c hc
  have hresidualFinrank := finrank_residualCode C c hc hcmin
  have hCfinrank := leaderCode_finrank u huweight hleader
  change Module.finrank FABL.𝔽₂ (residualCode C c) =
    Module.finrank FABL.𝔽₂ C - 1 at hresidualFinrank
  rw [hCfinrank] at hresidualFinrank
  norm_num at hresidualFinrank
  have hzeroCard := card_zeroCoordinates c.1
  have hambientCard : Fintype.card (OneCoordinates u) = 13 := by
    have huNorm : hammingNorm u = 13 := huweight
    rw [card_oneCoordinates u, huNorm]
  rw [hambientCard] at hzeroCard
  have hresidualCard :
      Fintype.card (ZeroCoordinates c.1) = 7 ∨
        Fintype.card (ZeroCoordinates c.1) = 8 := by
    omega
  have hresidualWeight :
      ∀ z : residualCode C c, z ≠ 0 → 3 ≤ hammingNorm z.1 :=
    residualCode_hammingNorm_ge_three C c hc hcge hcmin
  exact noBinaryCodeFinrankFiveCardSevenOrEight
    (residualCode C c) hresidualFinrank hresidualCard hresidualWeight

/-- The largest nonlinearity of a five-variable Boolean function is twelve. -/
theorem maximumNonlinearity_five : maximumNonlinearity 5 = 12 := by
  have hlower := quadraticBound_le_maximumNonlinearity_of_odd
    (n := 5) (by decide)
  norm_num at hlower
  obtain ⟨f, hf⟩ := exists_nonlinearity_eq_maximumNonlinearity 5
  have hupper := nonlinearity_cast_le_coveringRadius f
  rw [hf] at hupper
  have hpow : (2 : ℝ) ^ (5 : ℕ) = 32 := by norm_num
  rw [hpow] at hupper
  have hsqrt : 4 < Real.sqrt 32 := by
    calc
      (4 : ℝ) = Real.sqrt 16 := by norm_num
      _ < Real.sqrt 32 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hltReal : (maximumNonlinearity 5 : ℝ) < 14 := by
    linarith
  have hlt : maximumNonlinearity 5 < 14 := by
    exact_mod_cast hltReal
  apply Nat.le_antisymm
  · by_contra hnot
    have hmax : maximumNonlinearity 5 = 13 := by omega
    have hnonlinearity : nonlinearity f = 13 := by omega
    have hhigher : higherOrderNonlinearity 1 f = 13 := by
      rw [← nonlinearity_eq_higherOrderNonlinearity_one]
      exact hnonlinearity
    obtain ⟨g, hg, hfg⟩ :=
      exists_reedMuller_hammingDistance_eq_higherOrderNonlinearity 1 f
    let u : BooleanFunction 5 := f + g
    have huweight : hammingWeight u = 13 := by
      rw [← hammingDistance_eq_hammingWeight_add f g, hfg, hhigher]
    have hleader : ∀ c : reedMuller 1 5,
        13 ≤ hammingWeight (u + c.1) := by
      intro c
      have hminimum := higherOrderNonlinearity_le_hammingDistance
        1 f (g + c.1) ((reedMuller 1 5).add_mem hg c.2)
      rw [hhigher, hammingDistance_eq_hammingWeight_add] at hminimum
      simpa only [u, add_assoc] using hminimum
    exact (no_firstOrderCosetLeader_weight_thirteen u huweight hleader).elim
  · exact hlower

end CryptBoolean
