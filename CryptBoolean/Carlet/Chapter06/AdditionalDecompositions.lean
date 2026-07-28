/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.QuadraticNormalForm
public import CryptBoolean.Carlet.Chapter06.HyperplaneRestriction
public import CryptBoolean.Carlet.Chapter06.QuadraticBent
public import CryptBoolean.Carlet.Chapter06.SecondOrderCharacterization

/-!
# Additional decompositions of bent functions

Carlet Section 6.4.3: bent restrictions arising from balanced hyperplane
derivatives, and the spectra of restrictions to four codimension-two cosets.
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n : ℕ}

private def standardHyperplaneDirection (u : FABL.F₂Cube n) :
    FABL.F₂Cube (n + 1) :=
  Fin.append u (singletonF₂Cube 0)

private theorem autocorrelation_standardHyperplaneDirection
    (f : BooleanFunction (n + 1)) (u : FABL.F₂Cube n) :
    autocorrelation f (standardHyperplaneDirection u) =
      autocorrelation (firstBlockSlice f (singletonF₂Cube 0)) u +
        autocorrelation (firstBlockSlice f (singletonF₂Cube 1)) u := by
  classical
  rw [autocorrelation]
  calc
    ∑ z : FABL.F₂Cube (n + 1),
        realSignView
          (FABL.booleanDerivative f (standardHyperplaneDirection u)) z =
      ∑ p : FABL.F₂Cube n × FABL.F₂Cube 1,
        realSignView
          (FABL.booleanDerivative f (standardHyperplaneDirection u))
            (Fin.append p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.appendEquiv n 1)
        (fun p ↦ realSignView
          (FABL.booleanDerivative f (standardHyperplaneDirection u))
            (Fin.append p.1 p.2))
        (fun z ↦ realSignView
          (FABL.booleanDerivative f (standardHyperplaneDirection u)) z)
        (fun _ ↦ rfl)).symm
    _ = ∑ y : FABL.F₂Cube 1, ∑ x : FABL.F₂Cube n,
        realSignView (FABL.booleanDerivative (firstBlockSlice f y) u) x := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [realSignView_booleanDerivative, standardHyperplaneDirection]
      rw [← finAppend_add]
      rw [show singletonF₂Cube 0 = 0 by rfl, add_zero]
      simp [realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, firstBlockSlice]
    _ = autocorrelation (firstBlockSlice f (singletonF₂Cube 0)) u +
        autocorrelation (firstBlockSlice f (singletonF₂Cube 1)) u := by
      rw [sum_singletonF₂Cube]
      rfl

private theorem sq_add_sq_two_pow (k : ℕ) (x y : ℤ)
    (h : x ^ 2 + y ^ 2 = (2 : ℤ) ^ (2 * k + 1)) :
    x.natAbs = 2 ^ k ∧ y.natAbs = 2 ^ k := by
  induction k generalizing x y with
  | zero =>
      norm_num at h ⊢
      have hxLower : -1 ≤ x := by nlinarith [sq_nonneg (x + 1)]
      have hxUpper : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
      have hyLower : -1 ≤ y := by nlinarith [sq_nonneg (y + 1)]
      have hyUpper : y ≤ 1 := by nlinarith [sq_nonneg (y - 1)]
      interval_cases x <;> interval_cases y
      all_goals norm_num at h
      all_goals norm_num
  | succ k ih =>
      have hrightEven : Even ((2 : ℤ) ^ (2 * (k + 1) + 1)) := by
        exact Even.pow_of_ne_zero (by decide) (by omega)
      rcases Int.even_or_odd x with hx | hx
      · rcases Int.even_or_odd y with hy | hy
        · obtain ⟨x', rfl⟩ := hx
          obtain ⟨y', rfl⟩ := hy
          have h' : x' ^ 2 + y' ^ 2 = (2 : ℤ) ^ (2 * k + 1) := by
            rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
              pow_add] at h
            norm_num at h ⊢
            nlinarith
          obtain ⟨hx', hy'⟩ := ih x' y' h'
          constructor
          · rw [← two_mul x', Int.natAbs_mul, hx', pow_succ]
            exact Nat.mul_comm _ _
          · rw [← two_mul y', Int.natAbs_mul, hy', pow_succ]
            exact Nat.mul_comm _ _
        · have hleftOdd : Odd (x ^ 2 + y ^ 2) :=
            hx.pow_of_ne_zero (by decide) |>.add_odd hy.pow
          exact (Int.not_odd_iff_even.mpr (h ▸ hrightEven) hleftOdd).elim
      · rcases Int.even_or_odd y with hy | hy
        · have hleftOdd : Odd (x ^ 2 + y ^ 2) :=
            hx.pow.add_even (hy.pow_of_ne_zero (by decide))
          exact (Int.not_odd_iff_even.mpr (h ▸ hrightEven) hleftOdd).elim
        · have hxEight : 8 ∣ x ^ 2 - 1 :=
            Int.eight_dvd_sq_sub_one_of_odd hx
          have hyEight : 8 ∣ y ^ 2 - 1 :=
            Int.eight_dvd_sq_sub_one_of_odd hy
          have hleftEight : 8 ∣ x ^ 2 + y ^ 2 - 2 := by
            rw [show x ^ 2 + y ^ 2 - 2 =
              (x ^ 2 - 1) + (y ^ 2 - 1) by ring]
            exact dvd_add hxEight hyEight
          have hrightEight : 8 ∣ (2 : ℤ) ^ (2 * (k + 1) + 1) := by
            rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add]
            norm_num
          have : 8 ∣ (2 : ℤ) := by
            rw [h] at hleftEight
            simpa using dvd_sub hrightEight hleftEight
          norm_num at this

private theorem isBent_firstBlockSlices_of_balanced_hyperplane_derivatives
    (k : ℕ) (f : BooleanFunction (2 * k + 1))
    (hbalanced : ∀ u : FABL.F₂Cube (2 * k), u ≠ 0 →
      IsBalanced
        (FABL.booleanDerivative f (standardHyperplaneDirection u))) :
    ∀ b : FABL.𝔽₂,
      IsBent (firstBlockSlice f (singletonF₂Cube b)) := by
  classical
  let h₀ := firstBlockSlice f (singletonF₂Cube 0)
  let h₁ := firstBlockSlice f (singletonF₂Cube 1)
  have hsumZero (u : FABL.F₂Cube (2 * k)) (hu : u ≠ 0) :
      autocorrelation h₀ u + autocorrelation h₁ u = 0 := by
    rw [← autocorrelation_standardHyperplaneDirection]
    exact (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero
      f (standardHyperplaneDirection u)).mp (hbalanced u hu)
  have hmagnitudes (a : FABL.F₂Cube (2 * k)) :
      (walshTransform h₀ a).natAbs = 2 ^ k ∧
        (walshTransform h₁ a).natAbs = 2 ^ k := by
    have hsquaresReal :
        (walshTransform h₀ a : ℝ) ^ 2 +
            (walshTransform h₁ a : ℝ) ^ 2 =
          (2 : ℝ) ^ (2 * k + 1) := by
      rw [← rawFourierTransform_autocorrelation,
        ← rawFourierTransform_autocorrelation,
        rawFourierTransform, rawFourierTransform]
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_eq_single 0]
      · have hcharacter : FABL.vectorWalshCharacter a 0 = 1 := by simp
        rw [hcharacter, autocorrelation_zero, autocorrelation_zero,
          mul_one]
        rw [pow_succ]
        ring
      · intro u _hu hu0
        rw [← add_mul, hsumZero u hu0, zero_mul]
      · simp
    have hsquaresInt :
        walshTransform h₀ a ^ 2 + walshTransform h₁ a ^ 2 =
          (2 : ℤ) ^ (2 * k + 1) := by
      exact_mod_cast hsquaresReal
    exact sq_add_sq_two_pow k _ _ hsquaresInt
  have hbent₀ : IsBent h₀ :=
    (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half h₀).2 (by
      intro a
      simpa using (hmagnitudes a).1)
  have hbent₁ : IsBent h₁ :=
    (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half h₁).2 (by
      intro a
      simpa using (hmagnitudes a).2)
  intro b
  fin_cases b
  · exact hbent₀
  · exact hbent₁

private def linearHyperplaneDirection (k : ℕ)
    (L : FABL.F₂Cube (2 * k + 1) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (2 * k + 1))
    (u : FABL.F₂Cube (2 * k)) : FABL.F₂Cube (2 * k + 1) :=
  L (standardHyperplaneDirection u)

/-- If every nonzero derivative in a hyperplane is balanced, both coset
restrictions are bent. -/
theorem isBent_linearHyperplaneRestriction_of_balanced_derivatives
    (k : ℕ) (f : BooleanFunction (2 * k + 1))
    (L : FABL.F₂Cube (2 * k + 1) ≃ₗ[FABL.𝔽₂]
      FABL.F₂Cube (2 * k + 1))
    (hbalanced : ∀ u : FABL.F₂Cube (2 * k), u ≠ 0 →
      IsBalanced
        (FABL.booleanDerivative f
          (L (Fin.append u (singletonF₂Cube 0)))))
    (b : FABL.𝔽₂) :
    IsBent (linearHyperplaneRestriction f L b) := by
  apply isBent_firstBlockSlices_of_balanced_hyperplane_derivatives
    k (f ∘ L) _ b
  intro u hu
  apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero _ _).2
  have hlinear :
      L.toAffineEquiv.linear (standardHyperplaneDirection u) =
        L (standardHyperplaneDirection u) := by
    rfl
  have hauto :
      autocorrelation (f ∘ L) (standardHyperplaneDirection u) =
        autocorrelation f (L (standardHyperplaneDirection u)) := by
    simpa [hlinear] using autocorrelation_comp_affineEquiv
      f L.toAffineEquiv (standardHyperplaneDirection u)
  rw [hauto]
  apply (isBalanced_booleanDerivative_iff_autocorrelation_eq_zero _ _).1
  simpa [linearHyperplaneDirection, standardHyperplaneDirection] using
    hbalanced u hu

private def f₂CubeTwoBasis (i : Fin 2) : FABL.F₂Cube 2 :=
  Pi.single i 1

private theorem f₂CubeTwoBasis_apply (i j : Fin 2) :
    f₂CubeTwoBasis i j = if i = j then 1 else 0 := by
  classical
  simp [f₂CubeTwoBasis, Pi.single_apply, eq_comm]

private theorem secondBooleanDerivative_eq_quadraticPolarKernel
    (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (a e x : FABL.F₂Cube n) :
    secondBooleanDerivative f a e x = quadraticPolarKernel f a e := by
  have hderivativeDegree :
      FABL.functionAlgebraicDegree (FABL.booleanDerivative f e) ≤ 1 :=
    (FABL.functionAlgebraicDegree_booleanDerivative_le f e).trans (by omega)
  obtain ⟨d, u, hu⟩ :=
    FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one
      (FABL.booleanDerivative f e) hderivativeDegree
  rw [secondBooleanDerivative, hu, FABL.booleanDerivative,
    FABL.affineFunction]
  rw [quadraticPolarKernel_comm,
    quadraticPolarKernel_eq_dotProduct_of_derivative_eq_affine
      f e a d u hu]
  simp only [FABL.affineFunction, FABL.f₂DotProduct]
  rw [dotProduct_add]
  abel_nf
  simp [two_smul, ZModModule.add_self]

private theorem f₂CubeTwo_eq_basis_sum (x : FABL.F₂Cube 2) :
    x = x 0 • f₂CubeTwoBasis 0 + x 1 • f₂CubeTwoBasis 1 := by
  simpa [f₂CubeTwoBasis, Fin.sum_univ_two] using
    (pi_eq_sum_univ' x)

private theorem quadraticRadical_eq_bot_iff_basis_cross_eq_one
    (f : BooleanFunction 2)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    quadraticRadical f hdegree = ⊥ ↔
      quadraticPolarKernel f (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 1) = 1 := by
  let e₀ := f₂CubeTwoBasis 0
  let e₁ := f₂CubeTwoBasis 1
  have h₀₀ : quadraticPolarKernel f e₀ e₀ = 0 := by
    simpa [e₀] using quadraticPolar_isAlt f hdegree e₀
  have h₁₁ : quadraticPolarKernel f e₁ e₁ = 0 := by
    simpa [e₁] using quadraticPolar_isAlt f hdegree e₁
  have h₀₀' : quadraticPolarKernel f (f₂CubeTwoBasis 0)
      (f₂CubeTwoBasis 0) = 0 := by
    simpa [e₀] using h₀₀
  have h₁₁' : quadraticPolarKernel f (f₂CubeTwoBasis 1)
      (f₂CubeTwoBasis 1) = 0 := by
    simpa [e₁] using h₁₁
  constructor
  · intro hradical
    have hne : quadraticPolarKernel f (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 1) ≠ 0 := by
      intro hcross
      have hcross' : quadraticPolarKernel f e₀ e₁ = 0 := by
        simpa [e₀, e₁] using hcross
      have he₀ : e₀ ∈ quadraticRadical f hdegree := by
        rw [mem_quadraticRadical_iff]
        intro b
        rw [f₂CubeTwo_eq_basis_sum b,
          quadraticPolarKernel_add_right f hdegree,
          quadraticPolarKernel_smul_right f hdegree,
          quadraticPolarKernel_smul_right f hdegree]
        change b 0 • quadraticPolarKernel f e₀ e₀ +
            b 1 • quadraticPolarKernel f e₀ e₁ = 0
        rw [h₀₀, hcross']
        simp
      rw [hradical] at he₀
      have he₀Zero : e₀ = 0 := by simpa using he₀
      have := congrFun he₀Zero 0
      simp [e₀, f₂CubeTwoBasis] at this
    exact Fin.eq_one_of_ne_zero _ hne
  · intro hcross
    apply le_antisymm
    · intro a ha
      have ha₀ := (mem_quadraticRadical_iff f hdegree a).mp ha e₀
      have ha₁ := (mem_quadraticRadical_iff f hdegree a).mp ha e₁
      have h₁₀ : quadraticPolarKernel f e₁ e₀ = 1 := by
        rw [quadraticPolarKernel_comm, hcross]
      have h₁₀' : quadraticPolarKernel f (f₂CubeTwoBasis 1)
          (f₂CubeTwoBasis 0) = 1 := by
        simpa [e₀, e₁] using h₁₀
      have hvalue₀ : quadraticPolarKernel f a e₀ = a 1 := by
        change quadraticPolarKernel f a (f₂CubeTwoBasis 0) = a 1
        rw [f₂CubeTwo_eq_basis_sum a,
          quadraticPolarKernel_add_left f hdegree,
          quadraticPolarKernel_smul_left f hdegree,
          quadraticPolarKernel_smul_left f hdegree]
        simp only [Pi.add_apply, Pi.smul_apply]
        simp only [f₂CubeTwoBasis_apply]
        rw [h₀₀', h₁₀']
        simp
      have hvalue₁ : quadraticPolarKernel f a e₁ = a 0 := by
        change quadraticPolarKernel f a (f₂CubeTwoBasis 1) = a 0
        rw [f₂CubeTwo_eq_basis_sum a,
          quadraticPolarKernel_add_left f hdegree,
          quadraticPolarKernel_smul_left f hdegree,
          quadraticPolarKernel_smul_left f hdegree]
        simp only [Pi.add_apply, Pi.smul_apply]
        simp only [f₂CubeTwoBasis_apply]
        rw [hcross, h₁₁']
        simp
      rw [hvalue₀] at ha₀
      rw [hvalue₁] at ha₁
      have haZero : a = 0 := by
        funext i
        fin_cases i
        · exact ha₁
        · exact ha₀
      simp [haZero]
    · exact bot_le

private theorem isBent_two_iff_secondBooleanDerivative_basis_eq_one
    (f : BooleanFunction 2) :
    IsBent f ↔
      secondBooleanDerivative f (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 1) = 1 := by
  let hdegree := FABL.functionAlgebraicDegree_le_dimension f
  rw [isBent_iff_quadraticRadical_eq_bot f hdegree,
    quadraticRadical_eq_bot_iff_basis_cross_eq_one f hdegree]
  constructor
  · intro hcross
    funext x
    rw [secondBooleanDerivative_eq_quadraticPolarKernel f hdegree,
      hcross]
    rfl
  · intro hsecond
    have hvalue := congrFun hsecond 0
    simpa [secondBooleanDerivative_eq_quadraticPolarKernel f hdegree]
      using hvalue

/-- The Walsh coefficient of a codimension-two restriction is the two-bit
Walsh coefficient of the corresponding dual slice, with exact raw scaling. -/
theorem four_mul_walshTransform_firstBlockSlice_eq
    (f : BooleanFunction (n + 2)) (hf : IsBent f)
    (a : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    (4 : ℝ) * (walshTransform (firstBlockSlice f y) a : ℝ) =
      (2 : ℝ) ^ ((n + 2) / 2) *
        (walshTransform (secondBlockSlice (bentDual f) a) y : ℝ) := by
  let φ : FABL.F₂Cube 2 → ℝ :=
    fun t ↦ (walshTransform (firstBlockSlice f t) a : ℝ)
  have hambient (t : FABL.F₂Cube 2) :
      rawFourierTransform φ t =
        (2 : ℝ) ^ ((n + 2) / 2) *
          realSignView (secondBlockSlice (bentDual f) a) t := by
    rw [← walshTransform_append_cast_eq_rawFourierTransform_sliceWalsh]
    have hdual := congrArg (fun z : ℤ ↦ (z : ℝ))
      (walshTransform_eq_two_pow_half_mul_bitSignInt_bentDual
        f hf (Fin.append a t))
    have hsign :
        (bitSignInt (bentDual f (Fin.append a t)) : ℝ) =
          realSignView (secondBlockSlice (bentDual f) a) t := by
      rw [bitSignInt_cast]
      simp [secondBlockSlice, realSignView, FABL.realSignEncodedFunction,
        FABL.signEncodedFunction, FABL.signValue_signEncode_eq_binarySign]
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hsign] using hdual
  calc
    (4 : ℝ) * (walshTransform (firstBlockSlice f y) a : ℝ) =
        rawFourierTransform (rawFourierTransform φ) y := by
      rw [rawFourierTransform_involution]
      norm_num [φ]
    _ = rawFourierTransform
        (fun t ↦ (2 : ℝ) ^ ((n + 2) / 2) *
          realSignView (secondBlockSlice (bentDual f) a) t) y := by
      congr 1
      funext t
      exact hambient t
    _ = (2 : ℝ) ^ ((n + 2) / 2) *
        (walshTransform (secondBlockSlice (bentDual f) a) y : ℝ) := by
      exact rawFourierTransform_const_mul_realSignView
        (secondBlockSlice (bentDual f) a) _ y

private theorem two_mul_walshTransform_firstBlockSlice_eq
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (a : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    2 * walshTransform (firstBlockSlice f y) a =
      (2 ^ (n / 2) : ℤ) *
        walshTransform (secondBlockSlice (bentDual f) a) y := by
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hreal := four_mul_walshTransform_firstBlockSlice_eq f hf a y
  have hint :
      (4 : ℤ) * walshTransform (firstBlockSlice f y) a =
        (2 : ℤ) ^ ((n + 2) / 2) *
          walshTransform (secondBlockSlice (bentDual f) a) y := by
    exact_mod_cast hreal
  rw [hhalf, pow_succ] at hint
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  calc
    2 * (2 * walshTransform (firstBlockSlice f y) a) =
        4 * walshTransform (firstBlockSlice f y) a := by ring
    _ = (2 ^ (n / 2) * 2) *
        walshTransform (secondBlockSlice (bentDual f) a) y := hint
    _ = 2 * ((2 ^ (n / 2) : ℤ) *
        walshTransform (secondBlockSlice (bentDual f) a) y) := by ring

private theorem two_mul_natAbs_walshTransform_firstBlockSlice_eq
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (a : FABL.F₂Cube n) (y : FABL.F₂Cube 2) :
    2 * (walshTransform (firstBlockSlice f y) a).natAbs =
      2 ^ (n / 2) *
        (walshTransform (secondBlockSlice (bentDual f) a) y).natAbs := by
  have h := congrArg Int.natAbs
    (two_mul_walshTransform_firstBlockSlice_eq f hf hn a y)
  norm_num [Int.natAbs_mul, Int.natAbs_pow] at h
  exact h

private theorem forall_isBent_firstBlockSlice_iff_secondBlockSlice_bentDual
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n) :
    (∀ y, IsBent (firstBlockSlice f y)) ↔
      ∀ a, IsBent (secondBlockSlice (bentDual f) a) := by
  constructor
  · intro hslices a
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
      (secondBlockSlice (bentDual f) a)).2
    intro y
    have hscale := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn a y
    rw [natAbs_walshTransform_eq_two_pow_half_of_isBent
      (firstBlockSlice f y) (hslices y) a] at hscale
    rw [show 2 * 2 ^ (n / 2) = 2 ^ (n / 2) * 2 by omega] at hscale
    norm_num
    exact (Nat.mul_left_cancel (Nat.two_pow_pos _) hscale).symm
  · intro hdualSlices y
    apply (isBent_iff_forall_natAbs_walshTransform_eq_two_pow_half
      (firstBlockSlice f y)).2
    intro a
    have hscale := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn a y
    rw [natAbs_walshTransform_eq_two_pow_half_of_isBent
      (secondBlockSlice (bentDual f) a) (hdualSlices a) y] at hscale
    norm_num at hscale
    rw [Nat.mul_comm (2 ^ (n / 2)) 2] at hscale
    exact Nat.mul_left_cancel (by omega) hscale

private theorem secondBooleanDerivative_secondBlockSlice
    (f : BooleanFunction (n + 2)) (a : FABL.F₂Cube n)
    (u v y : FABL.F₂Cube 2) :
    secondBooleanDerivative (secondBlockSlice f a) u v y =
      secondBooleanDerivative f (Fin.append 0 u) (Fin.append 0 v)
        (Fin.append a y) := by
  rw [secondBooleanDerivative_apply, secondBooleanDerivative_apply]
  simp only [secondBlockSlice]
  have hyu : Fin.append a y + Fin.append 0 u =
      Fin.append a (y + u) := by
    rw [← finAppend_add]
    simp
  have hyv : Fin.append a y + Fin.append 0 v =
      Fin.append a (y + v) := by
    rw [← finAppend_add]
    simp
  have hyuv : Fin.append a y + Fin.append 0 u + Fin.append 0 v =
      Fin.append a (y + u + v) := by
    calc
      Fin.append a y + Fin.append 0 u + Fin.append 0 v =
          Fin.append a (y + u) + Fin.append 0 v := by rw [hyu]
      _ = Fin.append (a + 0) (y + u + v) := by
        rw [finAppend_add]
      _ = Fin.append a (y + u + v) := by simp
  rw [hyuv, hyu, hyv]

/-- The four codimension-two coordinate restrictions of a bent function are
bent exactly when the dual has constant second derivative one in the two
orthogonal coordinate directions. -/
theorem isBent_firstBlockSlices_iff_bentDual_secondDerivative_eq_one
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n) :
    (∀ y, IsBent (firstBlockSlice f y)) ↔
      secondBooleanDerivative (bentDual f)
        (Fin.append 0 (Pi.single 0 1))
        (Fin.append 0 (Pi.single 1 1)) = 1 := by
  rw [forall_isBent_firstBlockSlice_iff_secondBlockSlice_bentDual
    f hf hn]
  constructor
  · intro hslices
    funext z
    let a := ((Fin.appendEquiv n 2).symm z).1
    let y := ((Fin.appendEquiv n 2).symm z).2
    have hz : Fin.append a y = z :=
      (Fin.appendEquiv n 2).apply_symm_apply z
    rw [← hz]
    change secondBooleanDerivative (bentDual f)
      (Fin.append 0 (f₂CubeTwoBasis 0))
      (Fin.append 0 (f₂CubeTwoBasis 1)) (Fin.append a y) = _
    rw [← secondBooleanDerivative_secondBlockSlice]
    have hsecond :=
      (isBent_two_iff_secondBooleanDerivative_basis_eq_one
        (secondBlockSlice (bentDual f) a)).1 (hslices a)
    simpa [f₂CubeTwoBasis] using congrFun hsecond y
  · intro hsecond a
    apply (isBent_two_iff_secondBooleanDerivative_basis_eq_one
      (secondBlockSlice (bentDual f) a)).2
    funext y
    rw [secondBooleanDerivative_secondBlockSlice]
    have hvalue := congrFun hsecond (Fin.append a y)
    simpa [f₂CubeTwoBasis] using hvalue

private theorem twoVariableWalshMagnitudeProfile (g : BooleanFunction 2) :
    (∀ y, (walshTransform g y).natAbs = 2) ∨
      ∃ u, ∀ y, (walshTransform g y).natAbs = if y = u then 4 else 0 := by
  let hdegree := FABL.functionAlgebraicDegree_le_dimension g
  by_cases hg : IsBent g
  · left
    intro y
    simpa using natAbs_walshTransform_eq_two_pow_half_of_isBent g hg y
  · right
    have hcrossNe : quadraticPolarKernel g (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 1) ≠ 1 := by
      intro hcross
      apply hg
      exact (isBent_iff_quadraticRadical_eq_bot g hdegree).2
        ((quadraticRadical_eq_bot_iff_basis_cross_eq_one
          g hdegree).2 hcross)
    have hcross : quadraticPolarKernel g (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 1) = 0 := by
      by_contra hne
      exact hcrossNe (Fin.eq_one_of_ne_zero _ hne)
    have hdiag₀ : quadraticPolarKernel g (f₂CubeTwoBasis 0)
        (f₂CubeTwoBasis 0) = 0 := by
      simpa using quadraticPolar_isAlt g hdegree (f₂CubeTwoBasis 0)
    have hdiag₁ : quadraticPolarKernel g (f₂CubeTwoBasis 1)
        (f₂CubeTwoBasis 1) = 0 := by
      simpa using quadraticPolar_isAlt g hdegree (f₂CubeTwoBasis 1)
    have hpolar : ∀ x y, quadraticPolarKernel g x y = 0 := by
      intro x y
      have h₀y : quadraticPolarKernel g (f₂CubeTwoBasis 0) y = 0 := by
        rw [f₂CubeTwo_eq_basis_sum y,
          quadraticPolarKernel_add_right g hdegree,
          quadraticPolarKernel_smul_right g hdegree,
          quadraticPolarKernel_smul_right g hdegree,
          hdiag₀, hcross]
        simp
      have h₁y : quadraticPolarKernel g (f₂CubeTwoBasis 1) y = 0 := by
        rw [f₂CubeTwo_eq_basis_sum y,
          quadraticPolarKernel_add_right g hdegree,
          quadraticPolarKernel_smul_right g hdegree,
          quadraticPolarKernel_smul_right g hdegree,
          quadraticPolarKernel_comm g (f₂CubeTwoBasis 1)
            (f₂CubeTwoBasis 0), hcross,
          hdiag₁]
        simp
      rw [f₂CubeTwo_eq_basis_sum x,
        quadraticPolarKernel_add_left g hdegree,
        quadraticPolarKernel_smul_left g hdegree,
        quadraticPolarKernel_smul_left g hdegree, h₀y, h₁y]
      simp
    obtain ⟨c, u, rfl⟩ :=
      exists_affineFunction_of_quadraticPolarKernel_eq_zero g hpolar
    refine ⟨u, fun y ↦ ?_⟩
    rw [walshTransform_affineFunction]
    by_cases hy : y = u
    · subst y
      simp only [if_pos, Int.natAbs_mul, Int.natAbs_pow]
      rw [bitSignInt_eq_if_one]
      split <;> norm_num
    · simp [hy]

private theorem sum_sq_walshTransform_secondBlockSlice_bentDual
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (y : FABL.F₂Cube 2) :
    (∑ a : FABL.F₂Cube n,
        (walshTransform (secondBlockSlice (bentDual f) a) y : ℝ) ^ 2) =
      4 * (2 : ℝ) ^ n := by
  have hhalf : (n + 2) / 2 = n / 2 + 1 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hfactor : ((2 : ℝ) ^ ((n + 2) / 2)) ^ 2 =
      4 * (2 : ℝ) ^ n := by
    rw [hhalf, pow_succ]
    calc
      ((2 : ℝ) ^ (n / 2) * 2) ^ 2 =
          4 * (((2 : ℝ) ^ (n / 2)) ^ 2) := by ring
      _ = 4 * (2 : ℝ) ^ (2 * (n / 2)) := by
        rw [show ((2 : ℝ) ^ (n / 2)) ^ 2 =
          (2 : ℝ) ^ (2 * (n / 2)) by
            rw [mul_comm, pow_mul]]
      _ = 4 * (2 : ℝ) ^ n := by
        congr 2
        rcases hn with ⟨k, hk⟩
        omega
  have hscaled :
      16 * ∑ a : FABL.F₂Cube n,
          (walshTransform (firstBlockSlice f y) a : ℝ) ^ 2 =
        ((2 : ℝ) ^ ((n + 2) / 2)) ^ 2 *
          ∑ a : FABL.F₂Cube n,
            (walshTransform
              (secondBlockSlice (bentDual f) a) y : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    have hpoint :=
      four_mul_walshTransform_firstBlockSlice_eq f hf a y
    calc
      16 * (walshTransform (firstBlockSlice f y) a : ℝ) ^ 2 =
          (4 * (walshTransform (firstBlockSlice f y) a : ℝ)) ^ 2 := by
            ring
      _ = ((2 : ℝ) ^ ((n + 2) / 2) *
          (walshTransform
            (secondBlockSlice (bentDual f) a) y : ℝ)) ^ 2 := by
            rw [hpoint]
      _ = ((2 : ℝ) ^ ((n + 2) / 2)) ^ 2 *
          (walshTransform
            (secondBlockSlice (bentDual f) a) y : ℝ) ^ 2 := by ring
  rw [sum_walshTransform_sq_eq_two_pow_sq, hfactor] at hscaled
  apply mul_left_cancel₀ (by positivity : 4 * (2 : ℝ) ^ n ≠ 0)
  calc
    (4 * (2 : ℝ) ^ n) *
        ∑ a : FABL.F₂Cube n,
          (walshTransform
            (secondBlockSlice (bentDual f) a) y : ℝ) ^ 2 =
      16 * ((2 : ℝ) ^ n) ^ 2 := hscaled.symm
    _ = (4 * (2 : ℝ) ^ n) * (4 * (2 : ℝ) ^ n) := by ring

private theorem intCast_sq_eq_natAbsCast_sq (z : ℤ) :
    (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
  calc
    (z : ℝ) ^ 2 = |(z : ℝ)| ^ 2 := (sq_abs _).symm
    _ = (z.natAbs : ℝ) ^ 2 := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]

private theorem exists_secondBlockSlice_bentDual_walshMagnitude_four
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (a : FABL.F₂Cube n)
    (haffine : ∃ u, ∀ y,
      (walshTransform (secondBlockSlice (bentDual f) a) y).natAbs =
        if y = u then 4 else 0)
    (z : FABL.F₂Cube 2) :
    ∃ b, (walshTransform
      (secondBlockSlice (bentDual f) b) z).natAbs = 4 := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨u, hu⟩ := haffine
  have haZero :
      (walshTransform (secondBlockSlice (bentDual f) a) z).natAbs = 0 := by
    rw [hu]
    by_cases hzu : z = u
    · have hzFour := hu z
      rw [if_pos hzu] at hzFour
      exact (hnone a hzFour).elim
    · rw [if_neg hzu]
  have hstrict :
      (∑ b : FABL.F₂Cube n,
          (walshTransform
            (secondBlockSlice (bentDual f) b) z : ℝ) ^ 2) <
        ∑ _b : FABL.F₂Cube n, (4 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro b _hb
      rcases twoVariableWalshMagnitudeProfile
          (secondBlockSlice (bentDual f) b) with hbent | ⟨v, hv⟩
      · rw [intCast_sq_eq_natAbsCast_sq, hbent]
        norm_num
      · have hbZero :
            (walshTransform
              (secondBlockSlice (bentDual f) b) z).natAbs = 0 := by
          rw [hv]
          by_cases hzv : z = v
          · have hzFour := hv z
            rw [if_pos hzv] at hzFour
            exact (hnone b hzFour).elim
          · rw [if_neg hzv]
        rw [intCast_sq_eq_natAbsCast_sq, hbZero]
        norm_num
    · refine ⟨a, Finset.mem_univ a, ?_⟩
      rw [intCast_sq_eq_natAbsCast_sq, haZero]
      norm_num
  rw [sum_sq_walshTransform_secondBlockSlice_bentDual f hf hn z,
    Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul] at hstrict
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hstrict
  nlinarith

private theorem exists_secondBlockSlice_bentDual_walshMagnitude_zero
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (a : FABL.F₂Cube n)
    (haffine : ∃ u, ∀ y,
      (walshTransform (secondBlockSlice (bentDual f) a) y).natAbs =
        if y = u then 4 else 0)
    (z : FABL.F₂Cube 2) :
    ∃ b, (walshTransform
      (secondBlockSlice (bentDual f) b) z).natAbs = 0 := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨u, hu⟩ := haffine
  have haFour :
      (walshTransform (secondBlockSlice (bentDual f) a) z).natAbs = 4 := by
    rw [hu]
    by_cases hzu : z = u
    · rw [if_pos hzu]
    · have hzZero := hu z
      rw [if_neg hzu] at hzZero
      exact (hnone a hzZero).elim
  have hstrict :
      (∑ _b : FABL.F₂Cube n, (4 : ℝ)) <
        ∑ b : FABL.F₂Cube n,
          (walshTransform
            (secondBlockSlice (bentDual f) b) z : ℝ) ^ 2 := by
    apply Finset.sum_lt_sum
    · intro b _hb
      rcases twoVariableWalshMagnitudeProfile
          (secondBlockSlice (bentDual f) b) with hbent | ⟨v, hv⟩
      · rw [intCast_sq_eq_natAbsCast_sq, hbent]
        norm_num
      · have hbFour :
            (walshTransform
              (secondBlockSlice (bentDual f) b) z).natAbs = 4 := by
          rw [hv]
          by_cases hzv : z = v
          · rw [if_pos hzv]
          · have hzZero := hv z
            rw [if_neg hzv] at hzZero
            exact (hnone b hzZero).elim
        rw [intCast_sq_eq_natAbsCast_sq, hbFour]
        norm_num
    · refine ⟨a, Finset.mem_univ a, ?_⟩
      rw [intCast_sq_eq_natAbsCast_sq, haFour]
      norm_num
  rw [sum_sq_walshTransform_secondBlockSlice_bentDual f hf hn z,
    Finset.sum_const, Finset.card_univ, card_f₂Cube, nsmul_eq_mul] at hstrict
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hstrict
  nlinarith

private theorem exists_secondBlockSlice_bentDual_same_walshMagnitude
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (a : FABL.F₂Cube n) (y z : FABL.F₂Cube 2) :
    ∃ b, (walshTransform
        (secondBlockSlice (bentDual f) a) y).natAbs =
      (walshTransform
        (secondBlockSlice (bentDual f) b) z).natAbs := by
  rcases twoVariableWalshMagnitudeProfile
      (secondBlockSlice (bentDual f) a) with hbent | haffine
  · exact ⟨a, (hbent y).trans (hbent z).symm⟩
  · obtain ⟨u, hu⟩ := haffine
    by_cases hyu : y = u
    · obtain ⟨b, hb⟩ :=
        exists_secondBlockSlice_bentDual_walshMagnitude_four
          f hf hn a ⟨u, hu⟩ z
      refine ⟨b, ?_⟩
      rw [hu, if_pos hyu, hb]
    · obtain ⟨b, hb⟩ :=
        exists_secondBlockSlice_bentDual_walshMagnitude_zero
          f hf hn a ⟨u, hu⟩ z
      refine ⟨b, ?_⟩
      rw [hu, if_neg hyu, hb]

/-- The set of magnitudes occurring in the raw Walsh spectrum. -/
def walshMagnitudeSet (f : BooleanFunction n) : Finset ℕ :=
  Finset.univ.image fun a ↦ (walshTransform f a).natAbs

/-- The four codimension-two coordinate restrictions of a bent function have
the same set of raw Walsh magnitudes. -/
theorem walshMagnitudeSet_firstBlockSlice_eq
    (f : BooleanFunction (n + 2)) (hf : IsBent f) (hn : Even n)
    (y z : FABL.F₂Cube 2) :
    walshMagnitudeSet (firstBlockSlice f y) =
      walshMagnitudeSet (firstBlockSlice f z) := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    rw [walshMagnitudeSet] at hq ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨a, rfl⟩ := hq
    obtain ⟨b, hmagnitude⟩ :=
      exists_secondBlockSlice_bentDual_same_walshMagnitude
        f hf hn a y z
    refine ⟨b, ?_⟩
    have hy := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn a y
    have hz := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn b z
    have htwice :
        2 * (walshTransform (firstBlockSlice f y) a).natAbs =
          2 * (walshTransform (firstBlockSlice f z) b).natAbs := by
      calc
        2 * (walshTransform (firstBlockSlice f y) a).natAbs =
            2 ^ (n / 2) *
              (walshTransform
                (secondBlockSlice (bentDual f) a) y).natAbs := hy
        _ = 2 ^ (n / 2) *
              (walshTransform
                (secondBlockSlice (bentDual f) b) z).natAbs := by
              rw [hmagnitude]
        _ = 2 * (walshTransform (firstBlockSlice f z) b).natAbs := hz.symm
    exact (Nat.mul_left_cancel (by omega) htwice).symm
  · intro q hq
    rw [walshMagnitudeSet] at hq ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq ⊢
    obtain ⟨b, rfl⟩ := hq
    obtain ⟨a, hmagnitude⟩ :=
      exists_secondBlockSlice_bentDual_same_walshMagnitude
        f hf hn b z y
    refine ⟨a, ?_⟩
    have hz := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn b z
    have hy := two_mul_natAbs_walshTransform_firstBlockSlice_eq
      f hf hn a y
    have htwice :
        2 * (walshTransform (firstBlockSlice f z) b).natAbs =
          2 * (walshTransform (firstBlockSlice f y) a).natAbs := by
      calc
        2 * (walshTransform (firstBlockSlice f z) b).natAbs =
            2 ^ (n / 2) *
              (walshTransform
                (secondBlockSlice (bentDual f) b) z).natAbs := hz
        _ = 2 ^ (n / 2) *
              (walshTransform
                (secondBlockSlice (bentDual f) a) y).natAbs := by
              rw [hmagnitude]
        _ = 2 * (walshTransform (firstBlockSlice f y) a).natAbs := hy.symm
    exact (Nat.mul_left_cancel (by omega) htwice).symm

end CryptBoolean
