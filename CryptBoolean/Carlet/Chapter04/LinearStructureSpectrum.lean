/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.SpectralSupport
public import CryptBoolean.Carlet.Chapter04.AutocorrelationBounds

/-!
# Carlet Chapter 4 spectral characterization of linear structures

The raw Poisson formula and Wiener--Khintchine identity relate squared Walsh coefficients on a
hyperplane coset to one autocorrelation coefficient. This yields the Walsh-support
characterization of constant derivatives.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

noncomputable local instance linearStructureSpectrumSubmoduleFintype
    (E : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) : Fintype E :=
  Fintype.ofFinite E

/-- The Walsh hyperplane perpendicular to the direction `e`. -/
noncomputable def walshHyperplane (e : FABL.F₂Cube n) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  FABL.perpendicularSubspace (Submodule.span FABL.𝔽₂ {e})

/-- Membership in the Walsh hyperplane is the vanishing dot-product condition. -/
theorem mem_walshHyperplane_iff (e u : FABL.F₂Cube n) :
    u ∈ walshHyperplane e ↔ FABL.f₂DotProduct u e = 0 := by
  rw [walshHyperplane, FABL.mem_perpendicularSubspace_iff]
  constructor
  · intro h
    exact h e (Submodule.mem_span_singleton_self e)
  · intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change dotProduct u (c • e) = 0
    rw [dotProduct_smul]
    change c * FABL.f₂DotProduct u e = 0
    rw [h, mul_zero]

/-- The cardinality of a nondegenerate Walsh hyperplane is `2^(n-1)`. -/
theorem natCard_walshHyperplane (e : FABL.F₂Cube n) (he : e ≠ 0) :
    Nat.card (walshHyperplane e) = 2 ^ (n - 1) := by
  rw [walshHyperplane, FABL.card_submodule_eq_two_pow_finrank,
    FABL.finrank_perpendicularSubspace, finrank_span_singleton he]

private theorem sum_span_singleton
    (e : FABL.F₂Cube n) (he : e ≠ 0) (g : FABL.F₂Cube n → ℝ) :
    ∑ x : Submodule.span FABL.𝔽₂ {e}, g x.1 = g 0 + g e := by
  let φ := LinearEquiv.toSpanNonzeroSingleton FABL.𝔽₂ (FABL.F₂Cube n) e he
  rw [← Fintype.sum_equiv φ.toEquiv
    (fun c : FABL.𝔽₂ ↦ g (φ c).1) (fun x ↦ g x.1) (fun _ ↦ rfl)]
  have huniv : (Finset.univ : Finset FABL.𝔽₂) = {0, 1} := rfl
  rw [huniv]
  simp [φ, LinearEquiv.toSpanNonzeroSingleton_apply]

/-- Carlet's hyperplane Walsh--autocorrelation identity: for `e ≠ 0`, the squared raw
Walsh spectrum on `a + {0,e}ᵖ` has the displayed unnormalized sum. -/
theorem sum_walshTransform_sq_hyperplane_coset
    (f : BooleanFunction n) (e a : FABL.F₂Cube n) (he : e ≠ 0) :
    (∑ u : walshHyperplane e,
        (walshTransform f (a + u.1) : ℝ) ^ 2) =
      (2 : ℝ) ^ (n - 1) *
        ((2 : ℝ) ^ n +
          FABL.vectorWalshCharacter a e * autocorrelation f e) := by
  classical
  let E := walshHyperplane e
  have hpoisson := rawPoissonSummationFormula (autocorrelation f) E a 0
  have hperp : FABL.perpendicularSubspace E =
      Submodule.span FABL.𝔽₂ {e} := by
    simp [E, walshHyperplane,
      FABL.perpendicularSubspace_perpendicularSubspace]
  have hsum :
      (∑ x : FABL.perpendicularSubspace E,
          FABL.vectorWalshCharacter a x.1 * autocorrelation f x.1) =
        (2 : ℝ) ^ n +
          FABL.vectorWalshCharacter a e * autocorrelation f e := by
    rw [hperp]
    simpa [autocorrelation_zero] using
      sum_span_singleton e he
        (fun x ↦ FABL.vectorWalshCharacter a x * autocorrelation f x)
  have hcard : (Nat.card E : ℝ) = (2 : ℝ) ^ (n - 1) := by
    rw [show E = walshHyperplane e from rfl, natCard_walshHyperplane e he]
    norm_num
  simp only [zero_add, FABL.vectorWalshCharacter_zero, AddChar.one_apply,
    one_mul, rawFourierTransform_autocorrelation] at hpoisson
  rw [hcard, hsum] at hpoisson
  simpa using hpoisson

/-- Carlet's raw Walsh support. -/
noncomputable def walshSupport (f : BooleanFunction n) : Finset (FABL.F₂Cube n) :=
  rawFourierSupport (realSignView f)

/-- Membership in Carlet's Walsh support is nonvanishing of the raw integer coefficient. -/
@[simp] theorem mem_walshSupport (f : BooleanFunction n) (u : FABL.F₂Cube n) :
    u ∈ walshSupport f ↔ walshTransform f u ≠ 0 := by
  rw [walshSupport, mem_rawFourierSupport]
  rw [show rawFourierTransform (realSignView f) u =
      (walshTransform f u : ℝ) by
    exact (walshTransform_cast_eq_sum_realSignView_mul_character f u).symm]
  exact_mod_cast (Iff.rfl : walshTransform f u ≠ 0 ↔ walshTransform f u ≠ 0)

private theorem hammingWeight_eq_two_pow_iff_eq_one (g : BooleanFunction n) :
    hammingWeight g = 2 ^ n ↔ g = 1 := by
  rw [hammingWeight_eq_card_support, ← card_f₂Cube n]
  constructor
  · intro hcard
    have hsupport : support g = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by rw [Finset.card_univ, hcard])
    funext x
    exact (mem_support g x).mp (by rw [hsupport]; exact Finset.mem_univ x)
  · rintro rfl
    have hsupport : support (1 : BooleanFunction n) = Finset.univ := by
      ext x
      simp [mem_support]
    rw [hsupport, Finset.card_univ]

private theorem autocorrelation_eq_two_pow_iff_derivative_eq_zero
    (f : BooleanFunction n) (e : FABL.F₂Cube n) :
    autocorrelation f e = (2 : ℝ) ^ n ↔
      FABL.booleanDerivative f e = 0 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight]
  constructor
  · intro h
    have hweight : hammingWeight (FABL.booleanDerivative f e) = 0 := by
      exact_mod_cast (by linarith :
        (hammingWeight (FABL.booleanDerivative f e) : ℝ) = 0)
    exact hammingNorm_eq_zero.mp hweight
  · intro h
    rw [h]
    simp

private theorem autocorrelation_eq_neg_two_pow_iff_derivative_eq_one
    (f : BooleanFunction n) (e : FABL.F₂Cube n) :
    autocorrelation f e = -((2 : ℝ) ^ n) ↔
      FABL.booleanDerivative f e = 1 := by
  rw [autocorrelation_eq_two_pow_sub_two_derivative_weight]
  constructor
  · intro h
    have hweight : hammingWeight (FABL.booleanDerivative f e) = 2 ^ n := by
      exact_mod_cast (by linarith :
        (hammingWeight (FABL.booleanDerivative f e) : ℝ) = (2 : ℝ) ^ n)
    exact (hammingWeight_eq_two_pow_iff_eq_one _).mp hweight
  · intro h
    have hweight := (hammingWeight_eq_two_pow_iff_eq_one
      (FABL.booleanDerivative f e)).mpr h
    rw [hweight]
    push_cast
    ring

private theorem positive_dimension_of_ne_zero
    (e : FABL.F₂Cube n) (he : e ≠ 0) : 0 < n := by
  by_contra hn
  have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  exact he (Subsingleton.elim e 0)

private theorem two_pow_eq_two_mul_two_pow_pred (hn : 0 < n) :
    (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
  calc
    (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by
      congr 1
      omega
    _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
    _ = 2 * (2 : ℝ) ^ (n - 1) := by ring

private theorem walshCoefficient_eq_zero_of_mem_coset_sum_eq_zero
    (f : BooleanFunction n) (e a : FABL.F₂Cube n) (v : walshHyperplane e)
    (hsum : (∑ u : walshHyperplane e,
        (walshTransform f (a + u.1) : ℝ) ^ 2) = 0) :
    walshTransform f (a + v.1) = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun (u : walshHyperplane e) _ ↦ sq_nonneg
      (walshTransform f (a + u.1) : ℝ))).mp hsum
      v (Finset.mem_univ _)
  exact_mod_cast (sq_eq_zero_iff.mp hterm)

/-- Carlet Proposition 15, null-derivative case: for a nonzero direction, the derivative is
zero exactly when the raw Walsh support lies in the perpendicular hyperplane. -/
theorem booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (he : e ≠ 0) :
    FABL.booleanDerivative f e = 0 ↔
      (↑(walshSupport f) : Set (FABL.F₂Cube n)) ⊆
        (walshHyperplane e : Set (FABL.F₂Cube n)) := by
  classical
  constructor
  · intro hderivative u hu
    by_contra huperp
    have hdot : FABL.f₂DotProduct u e = 1 :=
      Fin.eq_one_of_ne_zero _
        (fun hzero ↦ huperp ((mem_walshHyperplane_iff e u).mpr hzero))
    have hcharacter : FABL.vectorWalshCharacter u e = -1 := by
      rw [FABL.vectorWalshCharacter_apply, hdot, FABL.binarySign_one]
    have hsum := sum_walshTransform_sq_hyperplane_coset f e u he
    have hautocorrelation :=
      (autocorrelation_eq_two_pow_iff_derivative_eq_zero f e).mpr hderivative
    rw [hautocorrelation, hcharacter] at hsum
    have hsumzero :
        (∑ v : walshHyperplane e,
          (walshTransform f (u + v.1) : ℝ) ^ 2) = 0 := by
      nlinarith
    exact (mem_walshSupport f u).mp hu
      (by simpa using
        (walshCoefficient_eq_zero_of_mem_coset_sum_eq_zero
          f e u (0 : walshHyperplane e) hsumzero))
  · intro hsupport
    have houtside (u : FABL.F₂Cube n) (hu : u ∉ walshHyperplane e) :
        walshTransform f u = 0 := by
      by_contra hnonzero
      exact hu (hsupport ((mem_walshSupport f u).mpr hnonzero))
    have hsubtype :
        (∑ u : walshHyperplane e,
          (walshTransform f u.1 : ℝ) ^ 2) =
        ∑ u ∈ Finset.univ.filter (fun u : FABL.F₂Cube n ↦
          u ∈ walshHyperplane e), (walshTransform f u : ℝ) ^ 2 := by
      apply Finset.sum_bij (fun u _ ↦ u.1)
      · intro u _
        simp [u.2]
      · intro u _ v _ huv
        exact Subtype.ext huv
      · intro u hu
        have huperp : u ∈ walshHyperplane e := by simpa using hu
        exact ⟨⟨u, huperp⟩, Finset.mem_univ _, rfl⟩
      · intro _ _
        rfl
    have hinside :
        (∑ u : walshHyperplane e,
          (walshTransform f u.1 : ℝ) ^ 2) =
        ∑ u : FABL.F₂Cube n, (walshTransform f u : ℝ) ^ 2 := by
      rw [hsubtype]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u _ hu
      have hunot : u ∉ walshHyperplane e := by simpa using hu
      rw [houtside u hunot]
      norm_num
    have hcoset := sum_walshTransform_sq_hyperplane_coset f e 0 he
    simp only [zero_add, FABL.vectorWalshCharacter_zero, AddChar.one_apply,
      one_mul] at hcoset
    rw [hinside, sum_walshTransform_sq_eq_two_pow_sq] at hcoset
    have hn := positive_dimension_of_ne_zero e he
    have hpow := two_pow_eq_two_mul_two_pow_pred (n := n) hn
    have hpositive : 0 < (2 : ℝ) ^ (n - 1) := by positivity
    apply (autocorrelation_eq_two_pow_iff_derivative_eq_zero f e).mp
    nlinarith

/-- Carlet Proposition 15, one-derivative case: for a nonzero direction, the derivative is
one exactly when the raw Walsh support lies in the complementary hyperplane coset. -/
theorem booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (he : e ≠ 0) :
    FABL.booleanDerivative f e = 1 ↔
      (↑(walshSupport f) : Set (FABL.F₂Cube n)) ⊆
        (walshHyperplane e : Set (FABL.F₂Cube n))ᶜ := by
  classical
  constructor
  · intro hderivative u hu
    change u ∉ walshHyperplane e
    intro huperp
    have hsum := sum_walshTransform_sq_hyperplane_coset f e 0 he
    have hautocorrelation :=
      (autocorrelation_eq_neg_two_pow_iff_derivative_eq_one f e).mpr hderivative
    simp only [zero_add, FABL.vectorWalshCharacter_zero, AddChar.one_apply,
      one_mul, hautocorrelation, add_neg_cancel, mul_zero] at hsum
    have hsum' :
        (∑ w : walshHyperplane e,
          (walshTransform f (0 + w.1) : ℝ) ^ 2) = 0 := by
      simpa using hsum
    let v : walshHyperplane e := ⟨u, huperp⟩
    exact (mem_walshSupport f u).mp hu
      (by simpa [v] using
        (walshCoefficient_eq_zero_of_mem_coset_sum_eq_zero f e 0 v hsum'))
  · intro hsupport
    have hinsideZero (u : walshHyperplane e) : walshTransform f u.1 = 0 := by
      by_contra hnonzero
      have hcompl := hsupport ((mem_walshSupport f u.1).mpr hnonzero)
      exact hcompl u.2
    have hsumzero :
        (∑ u : walshHyperplane e,
          (walshTransform f u.1 : ℝ) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      rw [hinsideZero u]
      norm_num
    have hcoset := sum_walshTransform_sq_hyperplane_coset f e 0 he
    simp only [zero_add, FABL.vectorWalshCharacter_zero, AddChar.one_apply,
      one_mul] at hcoset
    rw [hsumzero] at hcoset
    have hpositive : 0 < (2 : ℝ) ^ (n - 1) := by positivity
    apply (autocorrelation_eq_neg_two_pow_iff_derivative_eq_one f e).mp
    nlinarith

/-- A derivative equal to one pairs the inputs of `f` into opposite-valued translates, so `f`
is balanced. -/
theorem isBalanced_of_booleanDerivative_eq_one
    (f : BooleanFunction n) (e : FABL.F₂Cube n)
    (hderivative : FABL.booleanDerivative f e = 1) : IsBalanced f := by
  have he : e ≠ 0 := by
    intro hezero
    subst e
    have hvalue := congrFun hderivative 0
    simp only [FABL.booleanDerivative, add_zero, Pi.one_apply] at hvalue
    rw [ZModModule.add_self] at hvalue
    exact zero_ne_one hvalue
  have hsupport :=
    (booleanDerivative_eq_one_iff_walshSupport_subset_hyperplane_compl
      f e he).mp hderivative
  apply (isBalanced_iff_walshTransform_zero_eq_zero f).mpr
  by_contra hnonzero
  have hzeroCompl := hsupport ((mem_walshSupport f 0).mpr hnonzero)
  exact hzeroCompl (by simp)

/-- For a non-balanced function, a direction is a linear structure exactly when its derivative
is the null function. -/
theorem isLinearStructure_iff_booleanDerivative_eq_zero_of_not_balanced
    (f : BooleanFunction n) (e : FABL.F₂Cube n) (hf : ¬ IsBalanced f) :
    IsLinearStructure f e ↔ FABL.booleanDerivative f e = 0 := by
  constructor
  · rintro ⟨ε, hε⟩
    by_cases hzero : ε = 0
    · funext x
      simpa [hzero] using hε x
    · have hone : ε = 1 := Fin.eq_one_of_ne_zero ε hzero
      apply False.elim
      apply hf
      apply isBalanced_of_booleanDerivative_eq_one f e
      funext x
      simpa [hone] using hε x
  · intro h
    exact ⟨0, fun x ↦ congrFun h x⟩

/-- The linear span of the raw Walsh support. -/
noncomputable def walshSupportSpan (f : BooleanFunction n) :
    Submodule FABL.𝔽₂ (FABL.F₂Cube n) :=
  Submodule.span FABL.𝔽₂ (↑(walshSupport f) : Set (FABL.F₂Cube n))

/-- Carlet's rank of the raw Walsh support. -/
noncomputable def walshSupportRank (f : BooleanFunction n) : ℕ :=
  Module.finrank FABL.𝔽₂ (walshSupportSpan f)

private theorem walshHyperplane_ne_top
    (e : FABL.F₂Cube n) (he : e ≠ 0) : walshHyperplane e ≠ ⊤ := by
  intro htop
  have hfinrank := congrArg
    (fun S : Submodule FABL.𝔽₂ (FABL.F₂Cube n) ↦
      Module.finrank FABL.𝔽₂ S) htop
  have hn := positive_dimension_of_ne_zero e he
  have : n - 1 = n := by
    rw [walshHyperplane, FABL.finrank_perpendicularSubspace,
      finrank_span_singleton he] at hfinrank
    simpa using hfinrank
  omega

private theorem exists_nonzero_walshHyperplane_of_ne_top
    (S : Submodule FABL.𝔽₂ (FABL.F₂Cube n)) (hS : S ≠ ⊤) :
    ∃ e : FABL.F₂Cube n, e ≠ 0 ∧ S ≤ walshHyperplane e := by
  have hlt : Module.finrank FABL.𝔽₂ S < n := by
    simpa using S.finrank_lt hS
  have hperpPositive :
      0 < Module.finrank FABL.𝔽₂ (FABL.perpendicularSubspace S) := by
    rw [FABL.finrank_perpendicularSubspace]
    omega
  obtain ⟨e, he⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hperpPositive
  refine ⟨e.1, ?_, ?_⟩
  · intro hzero
    exact he (Subtype.ext hzero)
  · intro u hu
    apply (mem_walshHyperplane_iff e.1 u).mpr
    have hdot :=
      (FABL.mem_perpendicularSubspace_iff S e.1).mp e.2 u hu
    simpa [FABL.f₂DotProduct, dotProduct_comm] using hdot

/-- The Walsh support spans the full cube exactly when no nonzero direction has null
derivative. -/
theorem no_nonzero_null_derivative_iff_walshSupportSpan_eq_top
    (f : BooleanFunction n) :
    (∀ e : FABL.F₂Cube n, e ≠ 0 → FABL.booleanDerivative f e ≠ 0) ↔
      walshSupportSpan f = ⊤ := by
  constructor
  · intro hnull
    by_contra hspan
    obtain ⟨e, he, hle⟩ :=
      exists_nonzero_walshHyperplane_of_ne_top (walshSupportSpan f) hspan
    have hsupport :
        (↑(walshSupport f) : Set (FABL.F₂Cube n)) ⊆
          (walshHyperplane e : Set (FABL.F₂Cube n)) := by
      intro u hu
      exact hle (Submodule.subset_span hu)
    exact hnull e he
      ((booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane
        f e he).mpr hsupport)
  · intro hspan e he hderivative
    have hsupport :=
      (booleanDerivative_eq_zero_iff_walshSupport_subset_hyperplane
        f e he).mp hderivative
    have hle : walshSupportSpan f ≤ walshHyperplane e :=
      Submodule.span_le.mpr hsupport
    have htop : walshHyperplane e = ⊤ := by
      apply top_unique
      simpa [hspan] using hle
    exact walshHyperplane_ne_top e he htop

/-- Full Walsh-support rank is equivalent to spanning the binary cube. -/
theorem walshSupportRank_eq_n_iff (f : BooleanFunction n) :
    walshSupportRank f = n ↔ walshSupportSpan f = ⊤ := by
  constructor
  · intro hrank
    apply Submodule.eq_top_of_finrank_eq
    simpa [walshSupportRank] using hrank
  · intro hspan
    rw [walshSupportRank, hspan]
    simp

/-- Carlet's full-rank consequence of Proposition 15: a non-balanced function has no nonzero
linear structure exactly when its Walsh support has rank `n`. -/
theorem no_nonzero_linearStructure_iff_walshSupportRank_eq_n_of_not_balanced
    (f : BooleanFunction n) (hf : ¬ IsBalanced f) :
    (∀ e : FABL.F₂Cube n, e ≠ 0 → ¬ IsLinearStructure f e) ↔
      walshSupportRank f = n := by
  rw [walshSupportRank_eq_n_iff,
    ← no_nonzero_null_derivative_iff_walshSupportSpan_eq_top]
  constructor
  · intro hlinear e he hderivative
    exact hlinear e he
      ((isLinearStructure_iff_booleanDerivative_eq_zero_of_not_balanced
        f e hf).mpr hderivative)
  · intro hnull e he hlinear
    exact hnull e he
      ((isLinearStructure_iff_booleanDerivative_eq_zero_of_not_balanced
        f e hf).mp hlinear)

end CryptBoolean
