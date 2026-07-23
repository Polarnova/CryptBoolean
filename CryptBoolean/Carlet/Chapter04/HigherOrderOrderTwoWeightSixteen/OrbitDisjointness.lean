/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.RankSevenPatterns

/-!
# Disjointness of the rank-seven weight-sixteen pattern orbits

The cardinality of the intersection of a finite binary point set with one of
its nontrivial translates is preserved by injective affine maps.  The three
canonical rank-seven patterns have different translation-intersection
profiles, which proves that their affine orbits are pairwise disjoint.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

/-- The number of points of `S` retained by translation through the difference
of two points `x` and `y`. -/
def affineDifferenceOverlapCard
    (S : Finset (FABL.F₂Cube n))
    (x y : FABL.F₂Cube n) : ℕ :=
  (S.filter fun z ↦ z + x + y ∈ S).card

/-- A finite binary point set has a nonzero point difference whose translation
overlap has the prescribed cardinality. -/
abbrev HasAffineDifferenceOverlapCard
    (S : Finset (FABL.F₂Cube n)) (k : ℕ) : Prop :=
  ((S.product S).filter fun p ↦
    p.1 ≠ p.2 ∧ affineDifferenceOverlapCard S p.1 p.2 = k).Nonempty

private theorem sevenVariableAffinePoint_sum_three
    (d : SevenVariableAffineMapData n)
    (x y z : FABL.F₂Cube 7) :
    sevenVariableAffinePoint d (x + y + z) =
      sevenVariableAffinePoint d x + sevenVariableAffinePoint d y +
        sevenVariableAffinePoint d z := by
  simp only [sevenVariableAffinePoint, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]
  have htranslation : d.1 = d.1 + d.1 + d.1 := by
    rw [ZModModule.add_self, zero_add]
  nth_rewrite 1 [htranslation]
  abel

private theorem sum_three_mem_of_sum_three_image_mem
    (S : Finset (FABL.F₂Cube 7))
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (a b c : FABL.F₂Cube 7)
    (hmem : sevenVariableAffinePoint d a +
        sevenVariableAffinePoint d b + sevenVariableAffinePoint d c ∈
      S.image (sevenVariableAffinePoint d)) :
    a + b + c ∈ S := by
  have hinjective := sevenVariableAffinePoint_injective_iff d |>.2 hd
  rw [← sevenVariableAffinePoint_sum_three d a b c] at hmem
  rcases Finset.mem_image.1 hmem with ⟨x, hxS, hx⟩
  simpa only [hinjective hx] using hxS

theorem affineDifferenceOverlapCard_image
    (S : Finset (FABL.F₂Cube 7))
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (x y : FABL.F₂Cube 7) :
    affineDifferenceOverlapCard (S.image (sevenVariableAffinePoint d))
        (sevenVariableAffinePoint d x) (sevenVariableAffinePoint d y) =
      affineDifferenceOverlapCard S x y := by
  classical
  have hinjective := sevenVariableAffinePoint_injective_iff d |>.2 hd
  unfold affineDifferenceOverlapCard
  symm
  apply Finset.card_bij (fun z _hz ↦ sevenVariableAffinePoint d z)
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    refine ⟨Finset.mem_image.2 ⟨z, hz.1, rfl⟩, ?_⟩
    exact Finset.mem_image.2
      ⟨z + x + y, hz.2,
        sevenVariableAffinePoint_sum_three d z x y⟩
  · intro a _ha b _hb hab
    exact hinjective hab
  · intro z hz
    simp only [Finset.mem_filter] at hz
    rcases Finset.mem_image.1 hz.1 with ⟨a, haS, ha⟩
    have hoverlap : a + x + y ∈ S := by
      apply sum_three_mem_of_sum_three_image_mem S d hd a x y
      rw [ha]
      exact hz.2
    refine ⟨a, Finset.mem_filter.2 ⟨haS, hoverlap⟩, ha⟩

theorem hasAffineDifferenceOverlapCard_image_iff
    (S : Finset (FABL.F₂Cube 7))
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (k : ℕ) :
    HasAffineDifferenceOverlapCard
        (S.image (sevenVariableAffinePoint d)) k ↔
      HasAffineDifferenceOverlapCard S k := by
  classical
  have hinjective := sevenVariableAffinePoint_injective_iff d |>.2 hd
  constructor
  · intro h
    change (((S.image (sevenVariableAffinePoint d)).product
      (S.image (sevenVariableAffinePoint d))).filter fun p ↦
        p.1 ≠ p.2 ∧ affineDifferenceOverlapCard
          (S.image (sevenVariableAffinePoint d)) p.1 p.2 = k).Nonempty at h
    rcases h with ⟨p, hp⟩
    rcases Finset.mem_filter.1 hp with ⟨hpProduct, hxy, hoverlap⟩
    rcases Finset.mem_product.1 hpProduct with ⟨hx, hy⟩
    rcases Finset.mem_image.1 hx with ⟨x, hxS, hx⟩
    rcases Finset.mem_image.1 hy with ⟨y, hyS, hy⟩
    have hxy' : x ≠ y := by
      intro h
      apply hxy
      rw [← hx, ← hy, h]
    change ((S.product S).filter fun p ↦
      p.1 ≠ p.2 ∧ affineDifferenceOverlapCard S p.1 p.2 = k).Nonempty
    refine ⟨(x, y), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hxS, hyS⟩, hxy', ?_⟩⟩
    rw [← affineDifferenceOverlapCard_image S d hd x y, hx, hy]
    exact hoverlap
  · intro h
    change ((S.product S).filter fun p ↦
      p.1 ≠ p.2 ∧ affineDifferenceOverlapCard S p.1 p.2 = k).Nonempty at h
    rcases h with ⟨p, hp⟩
    rcases Finset.mem_filter.1 hp with ⟨hpProduct, hxy, hoverlap⟩
    rcases Finset.mem_product.1 hpProduct with ⟨hx, hy⟩
    change (((S.image (sevenVariableAffinePoint d)).product
      (S.image (sevenVariableAffinePoint d))).filter fun p ↦
        p.1 ≠ p.2 ∧ affineDifferenceOverlapCard
          (S.image (sevenVariableAffinePoint d)) p.1 p.2 = k).Nonempty
    refine ⟨(sevenVariableAffinePoint d p.1,
      sevenVariableAffinePoint d p.2), Finset.mem_filter.2
        ⟨Finset.mem_product.2
          ⟨Finset.mem_image.2 ⟨p.1, hx, rfl⟩,
            Finset.mem_image.2 ⟨p.2, hy, rfl⟩⟩,
          hinjective.ne hxy, ?_⟩⟩
    rw [affineDifferenceOverlapCard_image S d hd p.1 p.2]
    exact hoverlap

theorem hasAffineDifferenceOverlapCard_patternImage_iff
    (c : RankSevenWeightSixteenPatternClass)
    (d : SevenVariableAffineMapData n)
    (hd : LinearIndependent FABL.𝔽₂ d.2)
    (k : ℕ) :
    HasAffineDifferenceOverlapCard
        (rankSevenWeightSixteenPatternImage c d) k ↔
      HasAffineDifferenceOverlapCard
        (rankSevenWeightSixteenPattern c) k := by
  exact hasAffineDifferenceOverlapCard_image_iff
    (rankSevenWeightSixteenPattern c) d hd k

private def natXorOverlapCard
    (S : Finset ℕ) (x y : ℕ) : ℕ :=
  (S.filter fun z ↦ z ^^^ x ^^^ y ∈ S).card

private abbrev HasNatXorOverlapCard
    (S : Finset ℕ) (k : ℕ) : Prop :=
  ((S.product S).filter fun p ↦
    p.1 ≠ p.2 ∧ natXorOverlapCard S p.1 p.2 = k).Nonempty

private theorem f₂CubeOfNat_xor (a b : ℕ) :
    f₂CubeOfNat 7 (a ^^^ b) =
      f₂CubeOfNat 7 a + f₂CubeOfNat 7 b := by
  funext i
  simp only [f₂CubeOfNat, Nat.testBit_xor, Pi.add_apply]
  cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;> decide

private theorem f₂CubeOfNat_xor_three (a b c : ℕ) :
    f₂CubeOfNat 7 (a ^^^ b ^^^ c) =
      f₂CubeOfNat 7 a + f₂CubeOfNat 7 b +
        f₂CubeOfNat 7 c := by
  rw [f₂CubeOfNat_xor, f₂CubeOfNat_xor]

private theorem f₂CubeOfNat_injectiveOn_lt_128 :
    Set.InjOn (f₂CubeOfNat 7) {a : ℕ | a < 128} := by
  intro a ha b hb hab
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 7
  · have hcoordinate := congrFun hab ⟨i, hi⟩
    cases hai : a.testBit i <;> cases hbi : b.testBit i <;>
      simp_all [f₂CubeOfNat]
  · have hpow : 2 ^ 7 ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

private theorem rankSevenWeightSixteenPatternIndex_lt_128
    (c : RankSevenWeightSixteenPatternClass)
    (a : ℕ) (ha : a ∈ rankSevenWeightSixteenPatternIndices c) :
    a < 128 := by
  cases c <;> simp [rankSevenWeightSixteenPatternIndices] at ha <;> omega

private theorem affineDifferenceOverlapCard_pattern_eq_nat
    (c : RankSevenWeightSixteenPatternClass)
    (x y : ℕ)
    (hx : x ∈ rankSevenWeightSixteenPatternIndices c)
    (hy : y ∈ rankSevenWeightSixteenPatternIndices c) :
    affineDifferenceOverlapCard (rankSevenWeightSixteenPattern c)
        (f₂CubeOfNat 7 x) (f₂CubeOfNat 7 y) =
      natXorOverlapCard (rankSevenWeightSixteenPatternIndices c) x y := by
  classical
  let S := rankSevenWeightSixteenPatternIndices c
  have hindex (a : ℕ) (ha : a ∈ S) : a < 128 :=
    rankSevenWeightSixteenPatternIndex_lt_128 c a ha
  have hinjective : Set.InjOn (f₂CubeOfNat 7) S := by
    intro a ha b hb hab
    exact f₂CubeOfNat_injectiveOn_lt_128 (hindex a ha) (hindex b hb) hab
  unfold affineDifferenceOverlapCard natXorOverlapCard
  change ((rankSevenWeightSixteenPattern c).filter fun z ↦
      z + f₂CubeOfNat 7 x + f₂CubeOfNat 7 y ∈
        rankSevenWeightSixteenPattern c).card = _
  rw [rankSevenWeightSixteenPattern]
  symm
  apply Finset.card_bij (fun z _hz ↦ f₂CubeOfNat 7 z)
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    refine ⟨Finset.mem_image.2 ⟨z, hz.1, rfl⟩, ?_⟩
    exact Finset.mem_image.2 ⟨z ^^^ x ^^^ y, hz.2,
      f₂CubeOfNat_xor_three z x y⟩
  · intro a ha b hb hab
    exact hinjective (Finset.mem_filter.1 ha).1
      (Finset.mem_filter.1 hb).1 hab
  · intro q hq
    simp only [Finset.mem_filter] at hq
    rcases Finset.mem_image.1 hq.1 with ⟨z, hzS, hz⟩
    rcases Finset.mem_image.1 hq.2 with ⟨w, hwS, hw⟩
    have hwEq : f₂CubeOfNat 7 w = f₂CubeOfNat 7 (z ^^^ x ^^^ y) := by
      rw [f₂CubeOfNat_xor_three, hz]
      exact hw
    have hxLt : x < 128 := hindex x hx
    have hyLt : y < 128 := hindex y hy
    have hzLt : z < 128 := hindex z hzS
    have hzxLt : z ^^^ x < 128 := by
      simpa only [show 128 = 2 ^ 7 by norm_num] using
        Nat.xor_lt_two_pow hzLt hxLt
    have hzxyLt : z ^^^ x ^^^ y < 128 := by
      simpa only [show 128 = 2 ^ 7 by norm_num] using
        Nat.xor_lt_two_pow hzxLt hyLt
    have hwLt : w < 128 := hindex w hwS
    have hwValue : w = z ^^^ x ^^^ y :=
      f₂CubeOfNat_injectiveOn_lt_128 hwLt hzxyLt hwEq
    refine ⟨z, Finset.mem_filter.2 ⟨hzS, ?_⟩, hz⟩
    simpa only [← hwValue] using hwS

private theorem hasAffineDifferenceOverlapCard_pattern_iff_nat
    (c : RankSevenWeightSixteenPatternClass) (k : ℕ) :
    HasAffineDifferenceOverlapCard
        (rankSevenWeightSixteenPattern c) k ↔
      HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices c) k := by
  classical
  let S := rankSevenWeightSixteenPatternIndices c
  constructor
  · intro h
    change (((rankSevenWeightSixteenPattern c).product
      (rankSevenWeightSixteenPattern c)).filter fun p ↦
        p.1 ≠ p.2 ∧ affineDifferenceOverlapCard
          (rankSevenWeightSixteenPattern c) p.1 p.2 = k).Nonempty at h
    rcases h with ⟨p, hp⟩
    rcases Finset.mem_filter.1 hp with ⟨hpProduct, hxy, hoverlap⟩
    rcases Finset.mem_product.1 hpProduct with ⟨hx, hy⟩
    rw [rankSevenWeightSixteenPattern] at hx hy
    rcases Finset.mem_image.1 hx with ⟨x, hxS, hx⟩
    rcases Finset.mem_image.1 hy with ⟨y, hyS, hy⟩
    have hxy' : x ≠ y := by
      intro h
      apply hxy
      rw [← hx, ← hy, h]
    change ((S.product S).filter fun p ↦
      p.1 ≠ p.2 ∧ natXorOverlapCard S p.1 p.2 = k).Nonempty
    refine ⟨(x, y), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hxS, hyS⟩, hxy', ?_⟩⟩
    rw [← affineDifferenceOverlapCard_pattern_eq_nat c x y hxS hyS,
      hx, hy]
    exact hoverlap
  · intro h
    change ((S.product S).filter fun p ↦
      p.1 ≠ p.2 ∧ natXorOverlapCard S p.1 p.2 = k).Nonempty at h
    rcases h with ⟨p, hp⟩
    rcases Finset.mem_filter.1 hp with ⟨hpProduct, hxy, hoverlap⟩
    rcases Finset.mem_product.1 hpProduct with ⟨hx, hy⟩
    have hxy' : f₂CubeOfNat 7 p.1 ≠ f₂CubeOfNat 7 p.2 := by
      intro h
      apply hxy
      exact f₂CubeOfNat_injectiveOn_lt_128
        (rankSevenWeightSixteenPatternIndex_lt_128 c p.1 hx)
        (rankSevenWeightSixteenPatternIndex_lt_128 c p.2 hy) h
    change (((rankSevenWeightSixteenPattern c).product
      (rankSevenWeightSixteenPattern c)).filter fun p ↦
        p.1 ≠ p.2 ∧ affineDifferenceOverlapCard
          (rankSevenWeightSixteenPattern c) p.1 p.2 = k).Nonempty
    refine ⟨(f₂CubeOfNat 7 p.1, f₂CubeOfNat 7 p.2),
      Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_image.2 ⟨p.1, hx, rfl⟩,
          Finset.mem_image.2 ⟨p.2, hy, rfl⟩⟩,
        hxy', ?_⟩⟩
    rw [affineDifferenceOverlapCard_pattern_eq_nat c p.1 p.2 hx hy]
    exact hoverlap

private theorem canonicalNatXorOverlapProfile :
    HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices .d16Plus) 16 ∧
      ¬HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices .twoE8) 16 ∧
      ¬HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices .f16) 16 ∧
      HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices .f16) 4 ∧
      ¬HasNatXorOverlapCard
        (rankSevenWeightSixteenPatternIndices .twoE8) 4 := by
  set_option maxRecDepth 100000 in
    decide

theorem hasAffineDifferenceOverlapCard_sixteen_d16Plus :
    HasAffineDifferenceOverlapCard
      (rankSevenWeightSixteenPattern .d16Plus) 16 := by
  exact (hasAffineDifferenceOverlapCard_pattern_iff_nat .d16Plus 16).2
    canonicalNatXorOverlapProfile.1

theorem not_hasAffineDifferenceOverlapCard_sixteen_twoE8 :
    ¬HasAffineDifferenceOverlapCard
      (rankSevenWeightSixteenPattern .twoE8) 16 := by
  exact fun h ↦ canonicalNatXorOverlapProfile.2.1
    ((hasAffineDifferenceOverlapCard_pattern_iff_nat .twoE8 16).1 h)

theorem not_hasAffineDifferenceOverlapCard_sixteen_f16 :
    ¬HasAffineDifferenceOverlapCard
      (rankSevenWeightSixteenPattern .f16) 16 := by
  exact fun h ↦ canonicalNatXorOverlapProfile.2.2.1
    ((hasAffineDifferenceOverlapCard_pattern_iff_nat .f16 16).1 h)

theorem hasAffineDifferenceOverlapCard_four_f16 :
    HasAffineDifferenceOverlapCard
      (rankSevenWeightSixteenPattern .f16) 4 := by
  exact (hasAffineDifferenceOverlapCard_pattern_iff_nat .f16 4).2
    canonicalNatXorOverlapProfile.2.2.2.1

theorem not_hasAffineDifferenceOverlapCard_four_twoE8 :
    ¬HasAffineDifferenceOverlapCard
      (rankSevenWeightSixteenPattern .twoE8) 4 := by
  exact fun h ↦ canonicalNatXorOverlapProfile.2.2.2.2
    ((hasAffineDifferenceOverlapCard_pattern_iff_nat .twoE8 4).1 h)

/-- An ambient Boolean word belongs to at most one of the three injective
affine rank-seven pattern classes. -/
theorem rankSevenWeightSixteenPatternClass_unique
    {c e : RankSevenWeightSixteenPatternClass}
    {h : BooleanFunction n}
    (hc : IsRankSevenWeightSixteenPatternClass c h)
    (he : IsRankSevenWeightSixteenPatternClass e h) :
    c = e := by
  rcases hc with ⟨d, hd, hwordD⟩
  rcases he with ⟨q, hq, hwordQ⟩
  have himage : rankSevenWeightSixteenPatternImage c d =
      rankSevenWeightSixteenPatternImage e q := by
    have hword : rankSevenWeightSixteenPatternWord c d =
        rankSevenWeightSixteenPatternWord e q := hwordD.symm.trans hwordQ
    have hsupport := congrArg support hword
    simpa only [support_rankSevenWeightSixteenPatternWord] using hsupport
  have hinvariant (k : ℕ) :
      HasAffineDifferenceOverlapCard
          (rankSevenWeightSixteenPattern c) k ↔
        HasAffineDifferenceOverlapCard
          (rankSevenWeightSixteenPattern e) k := by
    rw [← hasAffineDifferenceOverlapCard_patternImage_iff c d hd k,
      himage, hasAffineDifferenceOverlapCard_patternImage_iff e q hq k]
  cases c <;> cases e
  · rfl
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_sixteen_twoE8
        ((hinvariant 16).2
          hasAffineDifferenceOverlapCard_sixteen_d16Plus))
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_four_twoE8
        ((hinvariant 4).2 hasAffineDifferenceOverlapCard_four_f16))
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_sixteen_twoE8
        ((hinvariant 16).1
          hasAffineDifferenceOverlapCard_sixteen_d16Plus))
  · rfl
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_sixteen_f16
        ((hinvariant 16).1
          hasAffineDifferenceOverlapCard_sixteen_d16Plus))
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_four_twoE8
        ((hinvariant 4).1 hasAffineDifferenceOverlapCard_four_f16))
  · exact False.elim
      (not_hasAffineDifferenceOverlapCard_sixteen_f16
        ((hinvariant 16).2
          hasAffineDifferenceOverlapCard_sixteen_d16Plus))
  · rfl

end CryptBoolean
