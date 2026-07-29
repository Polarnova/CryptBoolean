/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter07.DirectSum
public import CryptBoolean.Carlet.Chapter06.HyperplaneRestriction

/-!
# Concatenation of resilient Boolean functions

Carlet Relation (65) and the resulting resiliency and nonlinearity properties
of Siegenthaler's concatenation construction.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n m : ℕ}

/-- Carlet Relation (65): the Walsh transform of the concatenation of `f`
and `g` is the sum or difference of their Walsh transforms according to the
last frequency coordinate. -/
theorem walshTransform_hyperplaneExtension_append
    (f g : BooleanFunction n) (a : FABL.F₂Cube n) (b : FABL.𝔽₂) :
    walshTransform (hyperplaneExtension f g)
        (Fin.append a (singletonF₂Cube b)) =
      walshTransform f a + bitSignInt b * walshTransform g a := by
  rw [walshTransform_append_singletonF₂Cube]
  have hzero :
      firstBlockSlice (hyperplaneExtension f g) (singletonF₂Cube 0) = f := by
    funext x
    simp [firstBlockSlice]
  have hone :
      firstBlockSlice (hyperplaneExtension f g) (singletonF₂Cube 1) = g := by
    funext x
    simp [firstBlockSlice]
  rw [hzero, hone]

/-- Concatenating two `m`-resilient functions preserves `m`-resiliency. -/
theorem isResilient_hyperplaneExtension
    (f g : BooleanFunction n) (hm : m < n)
    (hf : IsResilient m f) (hg : IsResilient m g) :
    IsResilient m (hyperplaneExtension f g) := by
  have hn : 0 < n := by omega
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    m (hyperplaneExtension f g) (by omega) (by omega)]
  intro u hweight
  let p := (Fin.appendEquiv n 1).symm u
  let a : FABL.F₂Cube n := p.1
  let b : FABL.𝔽₂ := p.2 0
  have htail : p.2 = singletonF₂Cube b := by
    funext i
    fin_cases i
    rfl
  have hu : Fin.append a (singletonF₂Cube b) = u := by
    rw [← htail]
    exact (Fin.appendEquiv n 1).apply_symm_apply u
  have haweight : (FABL.f₂Support a).card ≤ m := by
    apply (Nat.le_add_right (FABL.f₂Support a).card _).trans
    rw [← card_f₂Support_append, hu]
    exact hweight
  have hfzero := theorem_3_resilient_iff_walshTransform_eq_zero
    m f hn hm |>.mp hf a haweight
  have hgzero := theorem_3_resilient_iff_walshTransform_eq_zero
    m g hn hm |>.mp hg a haweight
  rw [← hu, walshTransform_hyperplaneExtension_append, hfzero, hgzero]
  simp

/-- If the two spectra also cancel at every frequency of weight `m+1`, their
concatenation is `(m+1)`-resilient. -/
theorem isResilient_succ_hyperplaneExtension_of_walshCancellation
    (f g : BooleanFunction n) (hm : m < n)
    (hf : IsResilient m f) (hg : IsResilient m g)
    (hcancel : ∀ a : FABL.F₂Cube n,
      (FABL.f₂Support a).card = m + 1 →
        walshTransform f a + walshTransform g a = 0) :
    IsResilient (m + 1) (hyperplaneExtension f g) := by
  have hn : 0 < n := by omega
  have hfWalsh := theorem_3_resilient_iff_walshTransform_eq_zero
    m f hn hm |>.mp hf
  have hgWalsh := theorem_3_resilient_iff_walshTransform_eq_zero
    m g hn hm |>.mp hg
  rw [theorem_3_resilient_iff_walshTransform_eq_zero
    (m + 1) (hyperplaneExtension f g) (by omega) (by omega)]
  intro u hweight
  let p := (Fin.appendEquiv n 1).symm u
  let a : FABL.F₂Cube n := p.1
  let b : FABL.𝔽₂ := p.2 0
  have htail : p.2 = singletonF₂Cube b := by
    funext i
    fin_cases i
    rfl
  have hu : Fin.append a (singletonF₂Cube b) = u := by
    rw [← htail]
    exact (Fin.appendEquiv n 1).apply_symm_apply u
  have hweightAppend :
      (FABL.f₂Support a).card +
          (FABL.f₂Support (singletonF₂Cube b)).card ≤ m + 1 := by
    rw [← card_f₂Support_append, hu]
    exact hweight
  rw [← hu, walshTransform_hyperplaneExtension_append]
  by_cases hb : b = 0
  · have hsign : bitSignInt b = 1 := by
      simp [bitSignInt_eq_if_one, hb]
    rw [hsign, one_mul]
    have haweight : (FABL.f₂Support a).card ≤ m + 1 := by
      have htailWeight :
          (FABL.f₂Support (singletonF₂Cube b)).card = 0 := by
        rw [hb]
        simp [singletonF₂Cube, FABL.f₂Support]
      omega
    by_cases ham : (FABL.f₂Support a).card ≤ m
    · rw [hfWalsh a ham, hgWalsh a ham]
      simp
    · exact hcancel a (by omega)
  · have hbOne : b = 1 := Fin.eq_one_of_ne_zero b hb
    have haweight : (FABL.f₂Support a).card ≤ m := by
      have htailWeight :
          (FABL.f₂Support (singletonF₂Cube b)).card = 1 := by
        rw [hbOne]
        simp [singletonF₂Cube, FABL.f₂Support]
      omega
    rw [hfWalsh a haweight, hgWalsh a haweight]
    simp

/-- The nonlinearity of a concatenation is at least the sum of the
nonlinearities of its two restrictions. -/
theorem nonlinearity_add_le_hyperplaneExtension
    (f g : BooleanFunction n) :
    nonlinearity f + nonlinearity g ≤
      nonlinearity (hyperplaneExtension f g) := by
  let h := hyperplaneExtension f g
  have hmax : maxWalshMagnitude h ≤
      maxWalshMagnitude f + maxWalshMagnitude g := by
    unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro u _hu
    let p := (Fin.appendEquiv n 1).symm u
    let a : FABL.F₂Cube n := p.1
    let b : FABL.𝔽₂ := p.2 0
    have htail : p.2 = singletonF₂Cube b := by
      funext i
      fin_cases i
      rfl
    have hu : Fin.append a (singletonF₂Cube b) = u := by
      rw [← htail]
      exact (Fin.appendEquiv n 1).apply_symm_apply u
    rw [← hu, walshTransform_hyperplaneExtension_append]
    calc
      (walshTransform f a + bitSignInt b * walshTransform g a).natAbs ≤
          (walshTransform f a).natAbs +
            (bitSignInt b * walshTransform g a).natAbs :=
        Int.natAbs_add_le _ _
      _ = (walshTransform f a).natAbs +
          (walshTransform g a).natAbs := by
        rw [Int.natAbs_mul, natAbs_bitSignInt, one_mul]
      _ ≤ maxWalshMagnitude f + maxWalshMagnitude g :=
        Nat.add_le_add
          (walshTransform_natAbs_le_maxWalshMagnitude f a)
          (walshTransform_natAbs_le_maxWalshMagnitude g a)
  have hh := two_mul_nonlinearity_add_maxWalshMagnitude h
  have hf := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hg := two_mul_nonlinearity_add_maxWalshMagnitude g
  have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [pow_succ]
    omega
  dsimp [h] at hh hmax ⊢
  omega

/-- Disjoint Walsh supports make the maximum Walsh magnitude of a
concatenation the larger of the two restriction magnitudes. -/
theorem maxWalshMagnitude_hyperplaneExtension_of_disjointWalshSupport
    (f g : BooleanFunction n)
    (hdisjoint : ∀ a : FABL.F₂Cube n,
      walshTransform f a = 0 ∨ walshTransform g a = 0) :
    maxWalshMagnitude (hyperplaneExtension f g) =
      max (maxWalshMagnitude f) (maxWalshMagnitude g) := by
  apply le_antisymm
  · unfold maxWalshMagnitude
    apply Finset.sup'_le
    intro u _hu
    let p := (Fin.appendEquiv n 1).symm u
    let a : FABL.F₂Cube n := p.1
    let b : FABL.𝔽₂ := p.2 0
    have htail : p.2 = singletonF₂Cube b := by
      funext i
      fin_cases i
      rfl
    have hu : Fin.append a (singletonF₂Cube b) = u := by
      rw [← htail]
      exact (Fin.appendEquiv n 1).apply_symm_apply u
    rw [← hu, walshTransform_hyperplaneExtension_append]
    rcases hdisjoint a with hfzero | hgzero
    · rw [hfzero, zero_add, Int.natAbs_mul,
        natAbs_bitSignInt, one_mul]
      exact (walshTransform_natAbs_le_maxWalshMagnitude g a).trans
        (Nat.le_max_right _ _)
    · rw [hgzero, mul_zero, add_zero]
      exact (walshTransform_natAbs_le_maxWalshMagnitude f a).trans
        (Nat.le_max_left _ _)
  · rw [Nat.max_le]
    constructor
    · unfold maxWalshMagnitude
      apply Finset.sup'_le
      intro a _ha
      by_cases hfzero : walshTransform f a = 0
      · simp [hfzero]
      · have hgzero := (hdisjoint a).resolve_left hfzero
        calc
          (walshTransform f a).natAbs =
              (walshTransform (hyperplaneExtension f g)
                (Fin.append a (singletonF₂Cube 0))).natAbs := by
            rw [walshTransform_hyperplaneExtension_append, hgzero,
              mul_zero, add_zero]
          _ ≤ maxWalshMagnitude (hyperplaneExtension f g) :=
            walshTransform_natAbs_le_maxWalshMagnitude _ _
    · unfold maxWalshMagnitude
      apply Finset.sup'_le
      intro a _ha
      by_cases hgzero : walshTransform g a = 0
      · simp [hgzero]
      · have hfzero := (hdisjoint a).resolve_right hgzero
        calc
          (walshTransform g a).natAbs =
              (walshTransform (hyperplaneExtension f g)
                (Fin.append a (singletonF₂Cube 0))).natAbs := by
            rw [walshTransform_hyperplaneExtension_append, hfzero, zero_add,
              Int.natAbs_mul, natAbs_bitSignInt, one_mul]
          _ ≤ maxWalshMagnitude (hyperplaneExtension f g) :=
            walshTransform_natAbs_le_maxWalshMagnitude _ _

/-- With disjoint Walsh supports, Carlet's concatenation has the exact
nonlinearity `2^(n-1) + min(nl(f), nl(g))`. -/
theorem nonlinearity_hyperplaneExtension_of_disjointWalshSupport
    (f g : BooleanFunction n) (hn : 0 < n)
    (hdisjoint : ∀ a : FABL.F₂Cube n,
      walshTransform f a = 0 ∨ walshTransform g a = 0) :
    nonlinearity (hyperplaneExtension f g) =
      2 ^ (n - 1) + min (nonlinearity f) (nonlinearity g) := by
  have hh := two_mul_nonlinearity_add_maxWalshMagnitude
    (hyperplaneExtension f g)
  have hf := two_mul_nonlinearity_add_maxWalshMagnitude f
  have hg := two_mul_nonlinearity_add_maxWalshMagnitude g
  rw [maxWalshMagnitude_hyperplaneExtension_of_disjointWalshSupport
    f g hdisjoint] at hh
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hsucc : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hsucc, pow_succ]
    omega
  have hpowSucc : 2 ^ (n + 1) = 2 * 2 ^ n := by
    rw [pow_succ]
    omega
  rcases le_total (nonlinearity f) (nonlinearity g) with hfg | hgf
  · have hMagnitude : maxWalshMagnitude g ≤ maxWalshMagnitude f := by
      omega
    rw [Nat.max_eq_left hMagnitude] at hh
    rw [Nat.min_eq_left hfg]
    omega
  · have hMagnitude : maxWalshMagnitude f ≤ maxWalshMagnitude g := by
      omega
    rw [Nat.max_eq_right hMagnitude] at hh
    rw [Nat.min_eq_right hgf]
    omega

end CryptBoolean
