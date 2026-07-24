/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter03.ReedMullerLowWeightAffineSpan

/-!
# The self-dual code attached to a full-span weight-sixteen word

For a weight-sixteen word orthogonal to quadratic Boolean functions, affine
linear functions evaluated on its support form a self-orthogonal binary code.
When the affine span has dimension seven, adjoining the constant row gives a
binary self-dual code of length sixteen and dimension eight.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- Prepend a zero coordinate to a binary vector. -/
def prependZeroLinearMap (m : ℕ) :
    FABL.F₂Cube m →ₗ[FABL.𝔽₂] FABL.F₂Cube (m + 1) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' c y := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp

@[simp] theorem prependZeroLinearMap_zero_apply
    (y : FABL.F₂Cube m) :
    prependZeroLinearMap m y 0 = 0 := by
  rfl

@[simp] theorem prependZeroLinearMap_succ_apply
    (y : FABL.F₂Cube m) (i : Fin m) :
    prependZeroLinearMap m y i.succ = y i := by
  rfl

theorem prependZeroLinearMap_injective :
    Function.Injective (prependZeroLinearMap m) := by
  intro y z hyz
  funext i
  have hi := congrFun hyz i.succ
  simpa using hi

@[simp] theorem f₂DotProduct_prependZeroLinearMap
    (y z : FABL.F₂Cube m) :
    FABL.f₂DotProduct (prependZeroLinearMap m y)
        (prependZeroLinearMap m z) =
      FABL.f₂DotProduct y z := by
  simp [FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ]

/-- The translated support-difference evaluation code with its deleted
basepoint coordinate restored as zero. -/
noncomputable def extendedSupportDifferenceEvaluation
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    FABL.F₂Cube n →ₗ[FABL.𝔽₂]
      FABL.F₂Cube (((support h).erase p).card + 1) :=
  (prependZeroLinearMap ((support h).erase p).card).comp
    (supportDifferenceEvaluation h p)

/-- The constant-one word on the restored support coordinates. -/
def supportDifferenceConstantWord
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    FABL.F₂Cube (((support h).erase p).card + 1) :=
  1

/-- The support point represented by a restored support coordinate. -/
noncomputable def restoredSupportPoint
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Fin (((support h).erase p).card + 1) → FABL.F₂Cube n :=
  Fin.cases p (fun j ↦ (supportAwayEquiv h p j).1)

@[simp] theorem restoredSupportPoint_zero
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    restoredSupportPoint h p 0 = p := by
  rfl

@[simp] theorem restoredSupportPoint_succ
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (j : Fin ((support h).erase p).card) :
    restoredSupportPoint h p j.succ = (supportAwayEquiv h p j).1 := by
  rfl

/-- Restored support coordinates are pairwise distinct. -/
theorem restoredSupportPoint_injective
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Function.Injective (restoredSupportPoint h p) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
          have hjAway := (supportAwayEquiv h p j).2
          have hjNe : (supportAwayEquiv h p j).1 ≠ p :=
            (Finset.mem_erase.mp hjAway).1
          exact (hjNe hij.symm).elim
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          have hiAway := (supportAwayEquiv h p i).2
          have hiNe : (supportAwayEquiv h p i).1 ≠ p :=
            (Finset.mem_erase.mp hiAway).1
          exact (hiNe hij).elim
      | succ j =>
          have hsub : supportAwayEquiv h p i =
              supportAwayEquiv h p j :=
            Subtype.ext hij
          exact congrArg Fin.succ ((supportAwayEquiv h p).injective hsub)

/-- Evaluation of one translated affine-linear form on the restored support
coordinates. -/
noncomputable def restoredAffineEvaluationWord
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (c : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    FABL.F₂Cube (((support h).erase p).card + 1) :=
  extendedSupportDifferenceEvaluation h p a +
    c • supportDifferenceConstantWord h p

@[simp] theorem restoredAffineEvaluationWord_apply
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (c : FABL.𝔽₂) (a : FABL.F₂Cube n)
    (i : Fin (((support h).erase p).card + 1)) :
    restoredAffineEvaluationWord h p c a i =
      c + FABL.f₂DotProduct a (restoredSupportPoint h p i + p) := by
  induction i using Fin.cases with
  | zero =>
      simp [restoredAffineEvaluationWord,
        extendedSupportDifferenceEvaluation,
        supportDifferenceConstantWord, FABL.f₂DotProduct, dotProduct,
        ZModModule.add_self]
  | succ j =>
      simp [restoredAffineEvaluationWord,
        extendedSupportDifferenceEvaluation,
        supportDifferenceConstantWord,
        supportDifferenceEvaluation_apply, add_comm]

/-- The code generated by translated affine-linear evaluations on the full
support: the translated linear rows and the constant row. -/
noncomputable def augmentedSupportDifferenceCode
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Submodule FABL.𝔽₂
      (FABL.F₂Cube (((support h).erase p).card + 1)) :=
  LinearMap.range (extendedSupportDifferenceEvaluation h p) ⊔
    FABL.𝔽₂ ∙ supportDifferenceConstantWord h p

theorem restoredAffineEvaluationWord_mem_augmentedSupportDifferenceCode
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (c : FABL.𝔽₂) (a : FABL.F₂Cube n) :
    restoredAffineEvaluationWord h p c a ∈
      augmentedSupportDifferenceCode h p := by
  rw [restoredAffineEvaluationWord, augmentedSupportDifferenceCode]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left ⟨a, rfl⟩)
    (Submodule.mem_sup_right
      (Submodule.smul_mem _ c
        (Submodule.mem_span_singleton_self _)))

/-- Distinct restored support coordinates are separated by a generated
affine-evaluation word. -/
theorem exists_restoredAffineEvaluationWord_ne_of_ne
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    {i j : Fin (((support h).erase p).card + 1)} (hij : i ≠ j) :
    ∃ y ∈ augmentedSupportDifferenceCode h p, y i ≠ y j := by
  have hpoint : restoredSupportPoint h p i ≠
      restoredSupportPoint h p j := by
    intro hEq
    exact hij (restoredSupportPoint_injective h p hEq)
  have hfun : ∃ k, restoredSupportPoint h p i k ≠
      restoredSupportPoint h p j k := by
    by_contra h
    push Not at h
    apply hpoint
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hfun
  let a : FABL.F₂Cube n := Pi.single k 1
  refine ⟨restoredAffineEvaluationWord h p 0 a,
    restoredAffineEvaluationWord_mem_augmentedSupportDifferenceCode
      h p 0 a, ?_⟩
  simp only [restoredAffineEvaluationWord_apply, zero_add, a,
    FABL.f₂DotProduct, single_dotProduct, one_mul]
  intro heq
  exact hk (add_right_cancel heq)

theorem range_extendedSupportDifferenceEvaluation_le_perpendicular
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n) :
    LinearMap.range (extendedSupportDifferenceEvaluation h p) ≤
      FABL.perpendicularSubspace
        (LinearMap.range (extendedSupportDifferenceEvaluation h p)) := by
  have hself :=
    range_supportDifferenceEvaluation_le_perpendicular h p hp hdual
  intro y hy
  rw [FABL.mem_perpendicularSubspace_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  rw [extendedSupportDifferenceEvaluation,
    LinearMap.comp_apply, LinearMap.comp_apply,
    f₂DotProduct_prependZeroLinearMap]
  exact (FABL.mem_perpendicularSubspace_iff _ _).1
    (hself ⟨a, rfl⟩)
    (supportDifferenceEvaluation h p b)
    ⟨b, rfl⟩

private theorem binaryScalar_mul_self (b : FABL.𝔽₂) : b * b = b := by
  fin_cases b <;> decide

/-- The nonzero coordinates of a finite binary vector. -/
def binaryVectorSupport (x : FABL.F₂Cube m) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ x i = 1

theorem mem_binaryVectorSupport
    (x : FABL.F₂Cube m) (i : Fin m) :
    i ∈ binaryVectorSupport x ↔ x i = 1 := by
  simp [binaryVectorSupport]

/-- The Hamming weight of a finite binary vector. -/
def binaryVectorWeight (x : FABL.F₂Cube m) : ℕ :=
  (binaryVectorSupport x).card

theorem f₂DotProduct_eq_sum_support
    (x y : FABL.F₂Cube m) :
    FABL.f₂DotProduct x y = ∑ i ∈ binaryVectorSupport x, y i := by
  classical
  rw [FABL.f₂DotProduct, dotProduct, binaryVectorSupport,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hzero : x i = 0
  · simp [hzero]
  · have hone : x i = 1 := Fin.eq_one_of_ne_zero _ hzero
    simp [hone]

theorem f₂DotProduct_self_eq_binaryVectorWeight_cast
    (x : FABL.F₂Cube m) :
    FABL.f₂DotProduct x x = (binaryVectorWeight x : FABL.𝔽₂) := by
  rw [f₂DotProduct_eq_sum_support]
  calc
    (∑ i ∈ binaryVectorSupport x, x i) =
        ∑ _i ∈ binaryVectorSupport x, (1 : FABL.𝔽₂) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (mem_binaryVectorSupport x i).mp hi
    _ = ((binaryVectorSupport x).card : FABL.𝔽₂) := by simp
    _ = (binaryVectorWeight x : FABL.𝔽₂) := rfl

theorem even_binaryVectorWeight_of_f₂DotProduct_self_eq_zero
    (x : FABL.F₂Cube m)
    (hself : FABL.f₂DotProduct x x = 0) :
    Even (binaryVectorWeight x) := by
  rw [f₂DotProduct_self_eq_binaryVectorWeight_cast,
    ZMod.natCast_eq_zero_iff_even] at hself
  exact hself

theorem binaryVectorWeight_pos_of_ne_zero
    (x : FABL.F₂Cube m) (hx : x ≠ 0) :
    0 < binaryVectorWeight x := by
  apply Nat.pos_of_ne_zero
  intro hzero
  apply hx
  funext i
  by_contra hi
  have hiOne : x i = 1 := Fin.eq_one_of_ne_zero _ hi
  have hiSupport : i ∈ binaryVectorSupport x :=
    (mem_binaryVectorSupport x i).mpr hiOne
  have hcard : (binaryVectorSupport x).card = 0 := hzero
  rw [Finset.card_eq_zero.mp hcard] at hiSupport
  simp at hiSupport

@[simp] theorem f₂DotProduct_one_prependZeroLinearMap
    (y : FABL.F₂Cube m) :
    FABL.f₂DotProduct 1 (prependZeroLinearMap m y) =
      FABL.f₂DotProduct y y := by
  simp only [FABL.f₂DotProduct, dotProduct, Fin.sum_univ_succ,
    Pi.one_apply, prependZeroLinearMap_zero_apply,
    prependZeroLinearMap_succ_apply, one_mul, zero_add,
    binaryScalar_mul_self]

theorem supportDifferenceConstantWord_mem_range_perpendicular
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n) :
    supportDifferenceConstantWord h p ∈
      FABL.perpendicularSubspace
        (LinearMap.range (extendedSupportDifferenceEvaluation h p)) := by
  rw [FABL.mem_perpendicularSubspace_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := hy
  rw [supportDifferenceConstantWord,
    extendedSupportDifferenceEvaluation, LinearMap.comp_apply,
    f₂DotProduct_one_prependZeroLinearMap]
  have hself :=
    range_supportDifferenceEvaluation_le_perpendicular h p hp hdual
  exact (FABL.mem_perpendicularSubspace_iff _ _).1
    (hself ⟨a, rfl⟩)
    (supportDifferenceEvaluation h p a)
    ⟨a, rfl⟩

theorem f₂DotProduct_supportDifferenceConstantWord_self
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hweight : hammingWeight h = 16) :
    FABL.f₂DotProduct (supportDifferenceConstantWord h p)
      (supportDifferenceConstantWord h p) = 0 := by
  have hlength : ((support h).erase p).card + 1 = 16 := by
    rw [Finset.card_erase_add_one hp, ← hammingWeight_eq_card_support,
      hweight]
  simp only [FABL.f₂DotProduct, dotProduct,
    supportDifferenceConstantWord, Pi.one_apply, mul_one, sum_const,
    card_univ, hlength, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  decide

/-- The full affine-evaluation code of a weight-sixteen dual word is
self-orthogonal. -/
theorem augmentedSupportDifferenceCode_le_perpendicular
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n)
    (hweight : hammingWeight h = 16) :
    augmentedSupportDifferenceCode h p ≤
      FABL.perpendicularSubspace (augmentedSupportDifferenceCode h p) := by
  intro x hx
  rw [FABL.mem_perpendicularSubspace_iff]
  intro y hy
  rw [augmentedSupportDifferenceCode] at hx hy
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, rfl⟩ := hx₀
  obtain ⟨b, rfl⟩ := hy₀
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
  let ea := extendedSupportDifferenceEvaluation h p a
  let eb := extendedSupportDifferenceEvaluation h p b
  let c := supportDifferenceConstantWord h p
  have hEE : FABL.f₂DotProduct ea eb = 0 := by
    have hself :=
      range_extendedSupportDifferenceEvaluation_le_perpendicular
        h p hp hdual
    exact (FABL.mem_perpendicularSubspace_iff _ _).1
      (hself ⟨a, rfl⟩) eb ⟨b, rfl⟩
  have hCE : FABL.f₂DotProduct c eb = 0 := by
    exact (FABL.mem_perpendicularSubspace_iff _ _).1
      (supportDifferenceConstantWord_mem_range_perpendicular
        h p hp hdual) eb ⟨b, rfl⟩
  have hEC : FABL.f₂DotProduct ea c = 0 := by
    rw [show FABL.f₂DotProduct ea c =
      FABL.f₂DotProduct c ea by exact dotProduct_comm _ _]
    exact (FABL.mem_perpendicularSubspace_iff _ _).1
      (supportDifferenceConstantWord_mem_range_perpendicular
        h p hp hdual) ea ⟨a, rfl⟩
  have hCC : FABL.f₂DotProduct c c = 0 :=
    f₂DotProduct_supportDifferenceConstantWord_self h p hp hweight
  change FABL.f₂DotProduct (ea + α • c) (eb + β • c) = 0
  change ea ⬝ᵥ eb = 0 at hEE
  change c ⬝ᵥ eb = 0 at hCE
  change ea ⬝ᵥ c = 0 at hEC
  change c ⬝ᵥ c = 0 at hCC
  simp only [FABL.f₂DotProduct, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hEE, hCE, hEC, hCC,
    smul_zero, zero_add]

/-- Every nonzero word in the full affine-evaluation code has weight at
least four. -/
theorem four_le_binaryVectorWeight_of_mem_augmentedSupportDifferenceCode
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n)
    (hweight : hammingWeight h = 16)
    (x : FABL.F₂Cube (((support h).erase p).card + 1))
    (hx : x ∈ augmentedSupportDifferenceCode h p) (hxne : x ≠ 0) :
    4 ≤ binaryVectorWeight x := by
  have hselfCode := augmentedSupportDifferenceCode_le_perpendicular
    h p hp hdual hweight
  have hxx : FABL.f₂DotProduct x x = 0 :=
    (FABL.mem_perpendicularSubspace_iff _ _).1 (hselfCode hx) x hx
  have heven := even_binaryVectorWeight_of_f₂DotProduct_self_eq_zero x hxx
  have hpos := binaryVectorWeight_pos_of_ne_zero x hxne
  by_contra hfour
  have hlt : binaryVectorWeight x < 4 := Nat.lt_of_not_ge hfour
  have htwo : binaryVectorWeight x = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hsupportCard : (binaryVectorSupport x).card = 2 := htwo
  obtain ⟨i, j, hij, hsupport⟩ := Finset.card_eq_two.mp hsupportCard
  obtain ⟨y, hy, hyij⟩ :=
    exists_restoredAffineEvaluationWord_ne_of_ne h p hij
  have hxy : FABL.f₂DotProduct x y = 0 :=
    (FABL.mem_perpendicularSubspace_iff _ _).1 (hselfCode hx) y hy
  rw [f₂DotProduct_eq_sum_support, hsupport] at hxy
  have hsum : y i + y j = 0 := by
    simpa only [Finset.sum_insert, Finset.mem_singleton, hij,
      not_false_eq_true, Finset.sum_singleton] using hxy
  have hyEq : y i = y j := by
    have hneg := add_eq_zero_iff_eq_neg.mp hsum
    simpa only [ZMod.neg_eq_self_mod_two] using hneg
  exact hyij hyEq

theorem finrank_range_extendedSupportDifferenceEvaluation
    (h : BooleanFunction n) (p : FABL.F₂Cube n) :
    Module.finrank FABL.𝔽₂
        (LinearMap.range (extendedSupportDifferenceEvaluation h p)) =
      Module.finrank FABL.𝔽₂
        (LinearMap.range (supportDifferenceEvaluation h p)) := by
  have hker :
      LinearMap.ker (extendedSupportDifferenceEvaluation h p) =
        LinearMap.ker (supportDifferenceEvaluation h p) := by
    ext a
    simp only [LinearMap.mem_ker, extendedSupportDifferenceEvaluation,
      LinearMap.comp_apply]
    constructor
    · intro ha
      apply prependZeroLinearMap_injective (m := ((support h).erase p).card)
      simpa using ha
    · intro ha
      rw [ha]
      exact LinearMap.map_zero _
  have hext :=
    (extendedSupportDifferenceEvaluation h p).finrank_range_add_finrank_ker
  have hbase :=
    (supportDifferenceEvaluation h p).finrank_range_add_finrank_ker
  rw [hker] at hext
  omega

/-- In the full affine-span case the augmented code has dimension eight. -/
theorem finrank_augmentedSupportDifferenceCode_eq_eight
    (h : BooleanFunction n) (p : FABL.F₂Cube n)
    (hspan : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) = 7) :
    Module.finrank FABL.𝔽₂
      (augmentedSupportDifferenceCode h p) = 8 := by
  have hconstantNotRange :
      supportDifferenceConstantWord h p ∉
        LinearMap.range (extendedSupportDifferenceEvaluation h p) := by
    rintro ⟨a, ha⟩
    have hzero := congrFun ha 0
    simp only [extendedSupportDifferenceEvaluation, LinearMap.comp_apply,
      prependZeroLinearMap_zero_apply, supportDifferenceConstantWord,
      Pi.one_apply] at hzero
    exact zero_ne_one hzero
  rw [augmentedSupportDifferenceCode,
    Submodule.finrank_sup_span_singleton hconstantNotRange,
    finrank_range_extendedSupportDifferenceEvaluation,
    ← finrank_supportDifferenceSpan_eq_finrank_range, hspan]

/-- A full-span weight-sixteen dual word canonically produces a binary
self-dual code of length sixteen and dimension eight. -/
theorem augmentedSupportDifferenceCode_eq_perpendicular
    (h : BooleanFunction n) (p : FABL.F₂Cube n) (hp : p ∈ support h)
    (hdual : h ∈ reedMullerDual 2 n)
    (hweight : hammingWeight h = 16)
    (hspan : Module.finrank FABL.𝔽₂
      (supportDifferenceSpan h p) = 7) :
    augmentedSupportDifferenceCode h p =
      FABL.perpendicularSubspace (augmentedSupportDifferenceCode h p) := by
  have hle := augmentedSupportDifferenceCode_le_perpendicular
    h p hp hdual hweight
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [FABL.finrank_perpendicularSubspace,
    finrank_augmentedSupportDifferenceCode_eq_eight h p hspan]
  have hlength : ((support h).erase p).card + 1 = 16 := by
    rw [Finset.card_erase_add_one hp, ← hammingWeight_eq_card_support,
      hweight]
  rw [hlength]

end CryptBoolean
