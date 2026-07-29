/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter05.QuadraticValues
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection

/-!
# Quadratic affine normal forms
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- A Boolean function with identically zero quadratic polar kernel is affine. -/
theorem exists_affineFunction_of_quadraticPolarKernel_eq_zero
    {n : ℕ} (f : BooleanFunction n)
    (hpolar : ∀ x y, quadraticPolarKernel f x y = 0) :
    ∃ c : FABL.𝔽₂, ∃ a : FABL.F₂Cube n,
      f = FABL.affineFunction c a := by
  let c := f 0
  let L : FABL.F₂Cube n → FABL.𝔽₂ := fun x ↦ f x + c
  have hlinear : FABL.IsF₂Linear L := by
    intro x y
    have hp := hpolar x y
    rw [quadraticPolarKernel_eq] at hp
    change f (x + y) + c = (f x + c) + (f y + c)
    have htwo : c + c = 0 := ZModModule.add_self c
    rw [show f (x + y) + c = f x + f y by
      apply eq_of_sub_eq_zero
      rw [sub_eq_add_neg, ZModModule.neg_eq_self]
      calc
        f (x + y) + c + (f x + f y) =
            f (x + y) + f x + f y + c := by abel
        _ = 0 := hp]
    calc
      f x + f y = (f x + f y) + (c + c) := by rw [htwo, add_zero]
      _ = (f x + c) + (f y + c) := by abel
  obtain ⟨a, ha⟩ :=
    (FABL.isF₂Linear_iff_exists_dotProduct L).mp hlinear
  refine ⟨c, a, funext fun x ↦ ?_⟩
  have hx := ha x
  change f x + c = FABL.f₂DotProduct a x at hx
  have hc : c + c = 0 := ZModModule.add_self c
  calc
    f x = (f x + c) + c := by rw [add_assoc, hc, add_zero]
    _ = FABL.f₂DotProduct a x + c := by rw [hx]
    _ = c + FABL.f₂DotProduct a x := add_comm _ _
    _ = FABL.affineFunction c a x := rfl

/-- Splits an initial block of Boolean-cube coordinates from the remaining block. -/
def quadraticNormalFormSplitLinearEquiv (m p : ℕ) :
    FABL.F₂Cube (m + p) ≃ₗ[FABL.𝔽₂]
      (FABL.F₂Cube m × FABL.F₂Cube p) where
  __ := (Fin.appendEquiv m p).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext i <;> rfl

private theorem affineFunction_quadraticNormalFormSplitLinearEquiv_symm
    (m p : ℕ) (c : FABL.𝔽₂)
    (a₁ : FABL.F₂Cube m) (a₂ : FABL.F₂Cube p)
    (x₁ : FABL.F₂Cube m) (x₂ : FABL.F₂Cube p) :
    FABL.affineFunction c
        ((quadraticNormalFormSplitLinearEquiv m p).symm (a₁, a₂))
        ((quadraticNormalFormSplitLinearEquiv m p).symm (x₁, x₂)) =
      FABL.affineFunction c a₁ x₁ + FABL.f₂DotProduct a₂ x₂ := by
  change c + FABL.f₂DotProduct (Fin.append a₁ a₂) (Fin.append x₁ x₂) = _
  rw [FABL.f₂DotProduct_append]
  simp only [FABL.affineFunction]
  ring

/-- The dimension of `Q_l` with `r` unused coordinates. -/
@[reducible] def quadraticNormalFormDimension : ℕ → ℕ → ℕ
  | 0, r => r
  | l + 1, r => 2 + quadraticNormalFormDimension l r

/-- The normal form `Q_l` with `r` unused coordinates has dimension `2*l+r`. -/
theorem quadraticNormalFormDimension_eq (l r : ℕ) :
    quadraticNormalFormDimension l r = 2 * l + r := by
  induction l with
  | zero => simp [quadraticNormalFormDimension]
  | succ l ih => simp only [quadraticNormalFormDimension, ih]; omega

/-- Carlet's `Q_l = x_1x_2 + ⋯ + x_(2l-1)x_(2l)`, with `r` unused coordinates. -/
def quadraticNormalForm :
    (l r : ℕ) → FABL.F₂Cube (quadraticNormalFormDimension l r) → FABL.𝔽₂
  | 0, _ => fun _ => 0
  | l + 1, r => fun x =>
      let z := quadraticNormalFormSplitLinearEquiv 2
        (quadraticNormalFormDimension l r) x
      z.1 0 * z.1 1 + quadraticNormalForm l r z.2

private def pairedAlternatingForm :
    (l r : ℕ) → FABL.F₂Cube (quadraticNormalFormDimension l r) →
      FABL.F₂Cube (quadraticNormalFormDimension l r) → FABL.𝔽₂
  | 0, _ => fun _ _ => 0
  | l + 1, r => fun x y =>
      let zx := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x
      let zy := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) y
      zx.1 0 * zy.1 1 + zx.1 1 * zy.1 0 +
        pairedAlternatingForm l r zx.2 zy.2

@[simp] private theorem quadraticNormalForm_zero (l r : ℕ) :
    quadraticNormalForm l r 0 = 0 := by
  induction l with
  | zero => rfl
  | succ l ih =>
      let z := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
        (0 : FABL.F₂Cube (quadraticNormalFormDimension (l + 1) r))
      change z.1 0 * z.1 1 + quadraticNormalForm l r z.2 = 0
      have hz : z = 0 := by
        dsimp [z]
        exact map_zero _
      rw [hz]
      simp [ih]

private theorem quadraticNormalForm_polar
    (l r : ℕ) (x y : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
    quadraticNormalForm l r (x + y) +
        quadraticNormalForm l r x +
        quadraticNormalForm l r y +
        quadraticNormalForm l r 0 =
      pairedAlternatingForm l r x y := by
  induction l with
  | zero => simp [quadraticNormalForm, pairedAlternatingForm]
  | succ l ih =>
      rw [quadraticNormalForm_zero]
      simp only [quadraticNormalForm, pairedAlternatingForm]
      rw [show quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) (x + y) =
          quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x +
            quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) y by
            exact map_add _ x y]
      rw [← ih
        (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x).2
        (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) y).2]
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      have htwo : (2 : FABL.𝔽₂) = 0 := ZMod.natCast_self 2
      ring_nf
      simp [htwo]

private theorem exists_paired_alternating_decomposition
    {V : Type*} [AddCommGroup V] [Module FABL.𝔽₂ V]
    [FiniteDimensional FABL.𝔽₂ V]
    (B : LinearMap.BilinForm FABL.𝔽₂ V)
    (hSymm : B.IsSymm) (hAlt : B.IsAlt) :
    ∃ l r : ℕ,
      Module.finrank FABL.𝔽₂ V = quadraticNormalFormDimension l r ∧
        ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ₗ[FABL.𝔽₂] V,
          ∀ x y, B (e x) (e y) = pairedAlternatingForm l r x y := by
  classical
  by_cases hzero : B = 0
  · let b := Module.finBasis FABL.𝔽₂ V
    refine ⟨0, Module.finrank FABL.𝔽₂ V, rfl, b.equivFun.symm, ?_⟩
    intro x y
    simp [hzero, pairedAlternatingForm]
  · obtain ⟨u, hu⟩ : ∃ u : V, B u ≠ 0 := by
      by_contra h
      push Not at h
      apply hzero
      ext x y
      exact DFunLike.congr_fun (h x) y
    obtain ⟨v, huvNe⟩ : ∃ v : V, B u v ≠ 0 := by
      by_contra h
      push Not at h
      apply hu
      ext y
      exact h y
    have huv : B u v = 1 := Fin.eq_one_of_ne_zero _ huvNe
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      simp at huv
    have hv0 : v ≠ 0 := by
      intro h
      subst v
      simp at huv
    have huvDistinct : u ≠ v := by
      intro h
      subst v
      rw [hAlt.self_eq_zero] at huv
      exact zero_ne_one huv
    have hscalar : ∀ a : FABL.𝔽₂, a • u ≠ v := by
      intro a ha
      have h := congrArg (fun z : V => B u z) ha
      simp only [map_smul, smul_eq_mul, hAlt.self_eq_zero, mul_zero] at h
      rw [huv] at h
      exact zero_ne_one h
    have hIndependent : LinearIndepOn FABL.𝔽₂ id ({u, v} : Set V) :=
      linearIndepOn_id_pair hu0 hscalar
    let H : Submodule FABL.𝔽₂ V := Submodule.span FABL.𝔽₂ {u, v}
    let W : Submodule FABL.𝔽₂ V := B.orthogonal H
    have huH : u ∈ H := Submodule.subset_span (by simp)
    have hvH : v ∈ H := Submodule.subset_span (by simp)
    have hdisjoint : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro z hzH hzW
      obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair.mp hzH)
      have hbu := hzW u huH
      have hav := hzW v hvH
      have hvu : B v u = 1 := by
        calc
          B v u = B u v := (hSymm.eq u v).symm
          _ = 1 := huv
      have hb : b = 0 := by
        simpa [map_add, map_smul, hAlt.self_eq_zero, huv] using hbu
      have ha : a = 0 := by
        simpa [map_add, map_smul, hAlt.self_eq_zero, hvu, hb] using hav
      simp [ha, hb]
    have hCompl : IsCompl H W :=
      (B.isCompl_orthogonal_iff_disjoint hAlt.isRefl).mpr hdisjoint
    have hHrank : Module.finrank FABL.𝔽₂ H = 2 := by
      change Module.finrank FABL.𝔽₂ (Submodule.span FABL.𝔽₂ {u, v}) = 2
      rw [finrank_span_set_eq_card hIndependent]
      simp [huvDistinct]
    have hRanks := Submodule.finrank_add_eq_of_isCompl hCompl
    have hWlt : Module.finrank FABL.𝔽₂ W < Module.finrank FABL.𝔽₂ V := by
      rw [hHrank] at hRanks
      omega
    let BW : LinearMap.BilinForm FABL.𝔽₂ W := B.restrict W
    have hBWSymm : BW.IsSymm := by
      constructor
      intro x y
      exact hSymm.eq x.1 y.1
    have hBWAlt : BW.IsAlt := by
      intro w
      exact hAlt.self_eq_zero w.1
    obtain ⟨l, r, hWdim, eW, heW⟩ :=
      exists_paired_alternating_decomposition BW hBWSymm hBWAlt
    let pairH : Fin 2 → H := ![⟨u, huH⟩, ⟨v, hvH⟩]
    have hPairAmbient : LinearIndependent FABL.𝔽₂ ![u, v] :=
      (LinearIndependent.pair_iff' hu0).mpr hscalar
    have hPairH : LinearIndependent FABL.𝔽₂ pairH := by
      apply LinearIndependent.of_comp H.subtype
      have hcomp : H.subtype ∘ pairH = ![u, v] := by
        funext i
        fin_cases i <;> rfl
      rw [hcomp]
      exact hPairAmbient
    let bH : Module.Basis (Fin 2) FABL.𝔽₂ H :=
      basisOfLinearIndependentOfCardEqFinrank' pairH hPairH (by simp [hHrank])
    let eH : FABL.F₂Cube 2 ≃ₗ[FABL.𝔽₂] H := bH.equivFun.symm
    have heH (x : FABL.F₂Cube 2) :
        (eH x : H) = x 0 • (⟨u, huH⟩ : H) + x 1 • (⟨v, hvH⟩ : H) := by
      have hsum := bH.sum_equivFun (eH x)
      rw [bH.equivFun.apply_symm_apply] at hsum
      rw [Fin.sum_univ_two] at hsum
      simp [eH, bH, pairH] at hsum ⊢
    have hHform (x y : FABL.F₂Cube 2) :
        B (eH x).1 (eH y).1 =
          x 0 * y 1 + x 1 * y 0 := by
      rw [heH x, heH y]
      change B (x 0 • u + x 1 • v) (y 0 • u + y 1 • v) = _
      have hvu : B v u = 1 := by
        calc
          B v u = B u v := (hSymm.eq u v).symm
          _ = 1 := huv
      simp [map_add, map_smul, hAlt.self_eq_zero, huv, hvu]
      ring
    let split := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
    let e : FABL.F₂Cube (quadraticNormalFormDimension (l + 1) r) ≃ₗ[FABL.𝔽₂] V :=
      split.trans ((eH.prodCongr eW).trans (H.prodEquivOfIsCompl W hCompl))
    have heForm (x y : FABL.F₂Cube (quadraticNormalFormDimension (l + 1) r)) :
        B (e x) (e y) = pairedAlternatingForm (l + 1) r x y := by
      let sx := split x
      let sy := split y
      have hxW : ((eW sx.2).1 : V) ∈ W := (eW sx.2).2
      have hyW : ((eW sy.2).1 : V) ∈ W := (eW sy.2).2
      have hxOrth : ∀ h ∈ H, B h (eW sx.2).1 = 0 := hxW
      have hyOrth : ∀ h ∈ H, B h (eW sy.2).1 = 0 := hyW
      have hxOrthSymm : B (eW sx.2).1 (eH sy.1).1 = 0 := by
        rw [← hSymm.eq]
        exact hxOrth (eH sy.1).1 (eH sy.1).2
      change B ((eH sx.1).1 + (eW sx.2).1)
          ((eH sy.1).1 + (eW sy.2).1) = _
      calc
        B ((eH sx.1).1 + (eW sx.2).1)
            ((eH sy.1).1 + (eW sy.2).1) =
          B (eH sx.1).1 (eH sy.1).1 +
            B (eH sx.1).1 (eW sy.2).1 +
            B (eW sx.2).1 (eH sy.1).1 +
            B (eW sx.2).1 (eW sy.2).1 := by
              simp only [map_add, LinearMap.add_apply]
              abel
        _ = B (eH sx.1).1 (eH sy.1).1 +
            B (eW sx.2).1 (eW sy.2).1 := by
              rw [hyOrth (eH sx.1).1 (eH sx.1).2, hxOrthSymm]
              simp
        _ = _ := by
          rw [hHform]
          have hWform := heW sx.2 sy.2
          change B (eW sx.2).1 (eW sy.2).1 = _ at hWform
          rw [hWform]
          simp [pairedAlternatingForm, sx, sy, split]
    refine ⟨l + 1, r, ?_, e, heForm⟩
    rw [quadraticNormalFormDimension]
    rw [← hWdim, ← hRanks, hHrank]
  termination_by Module.finrank FABL.𝔽₂ V
  decreasing_by exact hWlt

private theorem exists_paired_quadratic_affine_decomposition
    {n : ℕ} (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2) :
    ∃ l r : ℕ,
      n = quadraticNormalFormDimension l r ∧
        ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube n,
          ∃ c : FABL.𝔽₂, ∃ a : FABL.F₂Cube (quadraticNormalFormDimension l r),
            ∀ x, f (e x) =
              quadraticNormalForm l r x + FABL.affineFunction c a x := by
  classical
  obtain ⟨l, r, hdim, e, he⟩ :=
    exists_paired_alternating_decomposition
      (quadraticPolar f hdegree)
      (quadraticPolar_isSymm f hdegree)
      (quadraticPolar_isAlt f hdegree)
  let h : BooleanFunction (quadraticNormalFormDimension l r) :=
    fun x => f (e x) + quadraticNormalForm l r x
  have hpolar (x y : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
      h (x + y) + h x + h y + h 0 = 0 := by
    have hfpolar := he x y
    rw [quadraticPolar_apply, quadraticPolarKernel_eq] at hfpolar
    rw [← e.map_add x y] at hfpolar
    have hqpolar := quadraticNormalForm_polar l r x y
    let fp : FABL.𝔽₂ := f (e (x + y)) + f (e x) + f (e y) + f 0
    let qp : FABL.𝔽₂ :=
      quadraticNormalForm l r (x + y) +
        quadraticNormalForm l r x +
        quadraticNormalForm l r y +
        quadraticNormalForm l r 0
    have hfp : fp = pairedAlternatingForm l r x y := by
      simpa [fp] using hfpolar
    have hqp : qp = pairedAlternatingForm l r x y := by
      simpa [qp] using hqpolar
    dsimp only [h]
    calc
      (f (e (x + y)) + quadraticNormalForm l r (x + y)) +
            (f (e x) + quadraticNormalForm l r x) +
          (f (e y) + quadraticNormalForm l r y) +
        (f (e 0) + quadraticNormalForm l r 0) = fp + qp := by
          dsimp only [fp, qp]
          rw [e.map_zero]
          abel
      _ = 0 := by rw [hfp, hqp, ZModModule.add_self]
  have hpolarKernel : ∀ x y, quadraticPolarKernel h x y = 0 := by
    intro x y
    rw [quadraticPolarKernel_eq]
    exact hpolar x y
  obtain ⟨c, a, ha⟩ :=
    exists_affineFunction_of_quadraticPolarKernel_eq_zero h hpolarKernel
  refine ⟨l, r, ?_, e, c, a, ?_⟩
  · simpa only [Module.finrank_pi, Fintype.card_fin] using hdim
  · intro x
    have hh := congrFun ha x
    calc
      f (e x) = quadraticNormalForm l r x + h x := by
        dsimp only [h]
        have hq := ZModModule.add_self (quadraticNormalForm l r x)
        calc
          f (e x) = f (e x) + 0 := (add_zero _).symm
          _ = f (e x) +
              (quadraticNormalForm l r x +
                quadraticNormalForm l r x) := by rw [hq]
          _ = quadraticNormalForm l r x +
              (f (e x) + quadraticNormalForm l r x) := by abel
      _ = quadraticNormalForm l r x +
          FABL.affineFunction c a x := by rw [hh]

/-- A nonzero binary dot-product functional can be made the first coordinate
by a linear change of variables. -/
theorem exists_dotProduct_normalizing_linearEquiv
    {r : ℕ} (a : FABL.F₂Cube r) (ha : a ≠ 0) :
    ∃ hr : 0 < r,
      ∃ e : FABL.F₂Cube r ≃ₗ[FABL.𝔽₂] FABL.F₂Cube r,
        ∀ x, FABL.f₂DotProduct a (e x) = x ⟨0, hr⟩ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext j
    exact h j
  have haj : a j = 1 := Fin.eq_one_of_ne_zero _ hj
  have hr : 0 < r := Nat.zero_lt_of_lt j.2
  let φ : Module.Dual FABL.𝔽₂ (FABL.F₂Cube r) :=
    (dotProductEquiv FABL.𝔽₂ (Fin r)) a
  let v : FABL.F₂Cube r := Pi.single j 1
  have hφv : φ v = 1 := by
    rw [show φ v = FABL.f₂DotProduct a v by
      exact dotProductEquiv_apply_apply FABL.𝔽₂ (Fin r) a v]
    simp [FABL.f₂DotProduct, v, dotProduct_single, haj]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv, map_zero] at hφv
    exact zero_ne_one hφv
  have hsurjective : Function.Surjective φ := by
    intro c
    refine ⟨c • v, ?_⟩
    rw [map_smul, hφv, smul_eq_mul, mul_one]
  have hrange : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr hsurjective
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hkerRank : Module.finrank FABL.𝔽₂ (LinearMap.ker φ) = k := by
    have hrank := LinearMap.finrank_range_add_finrank_ker φ
    have hRangeRank : Module.finrank FABL.𝔽₂ (LinearMap.range φ) = 1 := by
      rw [hrange]
      simp
    have hDomainRank : Module.finrank FABL.𝔽₂ (FABL.F₂Cube (k + 1)) = k + 1 := by
      simp
    rw [hRangeRank, hDomainRank] at hrank
    omega
  let bK := Module.finBasis FABL.𝔽₂ (LinearMap.ker φ)
  rw [hkerRank] at bK
  have hli : ∀ (c : FABL.𝔽₂), ∀ x ∈ LinearMap.ker φ,
      c • v + x = 0 → c = 0 := by
    intro c x hx hsum
    have h := congrArg φ hsum
    rw [map_add, map_smul, hφv, LinearMap.mem_ker.mp hx,
      map_zero, smul_eq_mul, mul_one, add_zero] at h
    exact h
  have hsp : ∀ z : FABL.F₂Cube (k + 1),
      ∃ c : FABL.𝔽₂, z + c • v ∈ LinearMap.ker φ := by
    intro z
    refine ⟨φ z, ?_⟩
    rw [LinearMap.mem_ker, map_add, map_smul, hφv, smul_eq_mul,
      mul_one, ZModModule.add_self]
  let b : Module.Basis (Fin (k + 1)) FABL.𝔽₂ (FABL.F₂Cube (k + 1)) :=
    Module.Basis.mkFinCons v bK hli hsp
  have hφcoord : φ = b.coord 0 := by
    apply b.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hb0 : b 0 = v := by
        simp [b, Module.Basis.coe_mkFinCons]
      rw [hb0, hφv]
      rw [Module.Basis.coord_apply, ← hb0, b.repr_self_apply]
      simp
    · have hbsucc : b (Fin.succ j) = (bK j).1 := by
        simp [b, Module.Basis.coe_mkFinCons]
      rw [hbsucc, LinearMap.mem_ker.mp (bK j).2]
      rw [Module.Basis.coord_apply, ← hbsucc, b.repr_self_apply]
      simp
  let e : FABL.F₂Cube (k + 1) ≃ₗ[FABL.𝔽₂] FABL.F₂Cube (k + 1) :=
    b.equivFun.symm
  refine ⟨by omega, e, ?_⟩
  intro x
  rw [show FABL.f₂DotProduct a (e x) = φ (e x) by
    exact (dotProductEquiv_apply_apply FABL.𝔽₂ (Fin (k + 1)) a (e x)).symm]
  rw [hφcoord]
  rw [Module.Basis.coord_apply]
  change b.equivFun (e x) 0 = x 0
  rw [b.equivFun.apply_symm_apply]

/-- The coordinate `x_(2l+1)` immediately following the paired variables of `Q_l`. -/
def quadraticNormalFormFirstFreeCoordinate :
    (l r : ℕ) → 0 < r → FABL.F₂Cube (quadraticNormalFormDimension l r) → FABL.𝔽₂
  | 0, _, hr, x => x ⟨0, hr⟩
  | l + 1, r, hr, x =>
      quadraticNormalFormFirstFreeCoordinate l r hr
        (quadraticNormalFormSplitLinearEquiv 2
          (quadraticNormalFormDimension l r) x).2

private def liftPairedAffineEquiv
    (l r : ℕ) (t : FABL.F₂Cube 2)
    (e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
      FABL.F₂Cube (quadraticNormalFormDimension l r)) :
    FABL.F₂Cube (2 + quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
      FABL.F₂Cube (2 + quadraticNormalFormDimension l r) :=
  (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)).toAffineEquiv |>.trans
    ((AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube 2) t).prodCongr e) |>.trans
      (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)).symm.toAffineEquiv

private theorem quadraticNormalFormSplitLinearEquiv_liftPairedAffineEquiv
    (l r : ℕ) (t : FABL.F₂Cube 2)
    (e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
      FABL.F₂Cube (quadraticNormalFormDimension l r))
    (x : FABL.F₂Cube (2 + quadraticNormalFormDimension l r)) :
    quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
        (liftPairedAffineEquiv l r t e x) =
      (t + (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x).1,
        e (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x).2) := by
  change quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
      ((quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)).symm
        (t + (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x).1,
          e (quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r) x).2)) = _
  rw [LinearEquiv.apply_symm_apply]

private theorem liftPairedAffineEquiv_normalization_step
    (l r : ℕ) (c : FABL.𝔽₂)
    (a : FABL.F₂Cube (2 + quadraticNormalFormDimension l r))
    (e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
      FABL.F₂Cube (quadraticNormalFormDimension l r))
    (x : FABL.F₂Cube (2 + quadraticNormalFormDimension l r)) :
    let s := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
    let za := s a
    let t : FABL.F₂Cube 2 := ![za.1 1, za.1 0]
    let c' : FABL.𝔽₂ := c + za.1 0 * za.1 1
    quadraticNormalForm (l + 1) r
          (liftPairedAffineEquiv l r t e x) +
        FABL.affineFunction c a (liftPairedAffineEquiv l r t e x) =
      (s x).1 0 * (s x).1 1 +
        (quadraticNormalForm l r (e (s x).2) +
          FABL.affineFunction c' za.2 (e (s x).2)) := by
  dsimp only
  let s := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
  let za := s a
  let t : FABL.F₂Cube 2 := ![za.1 1, za.1 0]
  let c' : FABL.𝔽₂ := c + za.1 0 * za.1 1
  have hs := quadraticNormalFormSplitLinearEquiv_liftPairedAffineEquiv l r t e x
  let z := s x
  have hEx : liftPairedAffineEquiv l r t e x =
      s.symm (t + z.1, e z.2) := by
    apply s.injective
    rw [s.apply_symm_apply]
    exact hs
  rw [hEx]
  simp only [quadraticNormalForm]
  rw [show quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
        (s.symm (t + z.1, e z.2)) = (t + z.1, e z.2) by
      change s (s.symm (t + z.1, e z.2)) = _
      exact s.apply_symm_apply (t + z.1, e z.2)]
  rw [show quadraticNormalFormSplitLinearEquiv 2
      (quadraticNormalFormDimension l r) x = z by rfl]
  have ha : a = s.symm za := (s.symm_apply_apply a).symm
  have hsa : s a = za := rfl
  have hsza : quadraticNormalFormSplitLinearEquiv 2
      (quadraticNormalFormDimension l r) (s.symm za) = za := by
    change s (s.symm za) = za
    exact s.apply_symm_apply za
  rw [ha, affineFunction_quadraticNormalFormSplitLinearEquiv_symm]
  rw [hsa, hsza]
  dsimp only [t, c']
  simp only [FABL.affineFunction, FABL.f₂DotProduct, dotProduct,
    Fin.sum_univ_two, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have htwo : (2 : FABL.𝔽₂) = 0 := ZMod.natCast_self 2
  have hthree : (3 : FABL.𝔽₂) = 1 := by
    calc
      (3 : FABL.𝔽₂) = 2 + 1 := by ring
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add _
  ring_nf
  simp [htwo, hthree]

private theorem exists_paired_quadratic_normalization
    (l r : ℕ) (c : FABL.𝔽₂)
    (a : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
    (∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
        FABL.F₂Cube (quadraticNormalFormDimension l r),
      ∀ x, quadraticNormalForm l r (e x) +
          FABL.affineFunction c a (e x) =
        quadraticNormalForm l r x) ∨
    (∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
        FABL.F₂Cube (quadraticNormalFormDimension l r),
      ∀ x, quadraticNormalForm l r (e x) +
          FABL.affineFunction c a (e x) =
        quadraticNormalForm l r x + 1) ∨
    (∃ hr : 0 < r,
      ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
        FABL.F₂Cube (quadraticNormalFormDimension l r),
      ∀ x, quadraticNormalForm l r (e x) +
          FABL.affineFunction c a (e x) =
        quadraticNormalForm l r x +
          quadraticNormalFormFirstFreeCoordinate l r hr x) := by
  induction l generalizing c with
  | zero =>
      simp only [quadraticNormalFormDimension]
      change FABL.F₂Cube r at a
      by_cases ha : a = 0
      · subst a
        fin_cases c
        · left
          refine ⟨AffineEquiv.refl FABL.𝔽₂ (FABL.F₂Cube r), ?_⟩
          intro x
          change FABL.F₂Cube r at x
          simp [quadraticNormalForm, FABL.affineFunction,
            FABL.f₂DotProduct, dotProduct]
          rfl
        · right
          left
          refine ⟨AffineEquiv.refl FABL.𝔽₂ (FABL.F₂Cube r), ?_⟩
          intro x
          change FABL.F₂Cube r at x
          simp [quadraticNormalForm, FABL.affineFunction,
            FABL.f₂DotProduct, dotProduct]
          rfl
      · obtain ⟨hr, e, he⟩ := exists_dotProduct_normalizing_linearEquiv a ha
        right
        right
        let t : FABL.F₂Cube r := Pi.single ⟨0, hr⟩ c
        let E : FABL.F₂Cube r ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube r :=
          (AffineEquiv.constVAdd FABL.𝔽₂ (FABL.F₂Cube r) t).trans
            e.toAffineEquiv
        refine ⟨hr, E, ?_⟩
        intro x
        change FABL.F₂Cube r at x
        simp only [quadraticNormalForm, quadraticNormalFormFirstFreeCoordinate,
          zero_add]
        change c + FABL.f₂DotProduct a (E x) = x ⟨0, hr⟩
        rw [show E x = e (t + x) by rfl]
        rw [he]
        change c + (c + x ⟨0, hr⟩) = x ⟨0, hr⟩
        rw [← add_assoc, ZModModule.add_self, zero_add]
  | succ l ih =>
      simp only [quadraticNormalFormDimension] at ⊢
      change FABL.F₂Cube (2 + quadraticNormalFormDimension l r) at a
      let s := quadraticNormalFormSplitLinearEquiv 2 (quadraticNormalFormDimension l r)
      let za := s a
      let t : FABL.F₂Cube 2 := ![za.1 1, za.1 0]
      let c' : FABL.𝔽₂ := c + za.1 0 * za.1 1
      rcases ih c' za.2 with hzero | hone | hrad
      · obtain ⟨e, he⟩ := hzero
        left
        refine ⟨liftPairedAffineEquiv l r t e, ?_⟩
        intro x
        rw [liftPairedAffineEquiv_normalization_step l r c a e x]
        rw [he]
        simp only [quadraticNormalForm]
      · obtain ⟨e, he⟩ := hone
        right
        left
        refine ⟨liftPairedAffineEquiv l r t e, ?_⟩
        intro x
        rw [liftPairedAffineEquiv_normalization_step l r c a e x]
        rw [he]
        simp only [quadraticNormalForm]
        abel
      · obtain ⟨hr, e, he⟩ := hrad
        right
        right
        refine ⟨hr, liftPairedAffineEquiv l r t e, ?_⟩
        intro x
        rw [liftPairedAffineEquiv_normalization_step l r c a e x]
        rw [he]
        simp only [quadraticNormalForm, quadraticNormalFormFirstFreeCoordinate]
        abel

private def pairedHeadQuadratic : BooleanFunction 2 :=
  fun x => x 0 * x 1

private theorem pairedHeadQuadratic_eq_innerProductModTwoBit :
    pairedHeadQuadratic =
      (FABL.innerProductModTwoBit : BooleanFunction (1 + 1)) := by
  funext x
  rw [FABL.innerProductModTwoBit_eq_sum_anfMonomial]
  simp [pairedHeadQuadratic, FABL.anfMonomial]

private theorem quadraticNormalForm_succ
    (l r : ℕ) :
    quadraticNormalForm (l + 1) r =
      booleanDirectSum pairedHeadQuadratic
        (quadraticNormalForm l r) := by
  rfl

private theorem walshTransform_quadraticNormalForm_zero
    (l r : ℕ) :
    walshTransform (quadraticNormalForm l r) 0 = 2 ^ (l + r) := by
  induction l with
  | zero =>
      rw [show quadraticNormalForm 0 r =
          (FABL.affineFunction 0 0 : BooleanFunction r) by
        funext x
        simp [quadraticNormalForm, FABL.affineFunction,
          FABL.f₂DotProduct, dotProduct]]
      rw [walshTransform_affineFunction]
      simp [bitSignInt]
  | succ l ih =>
      rw [quadraticNormalForm_succ]
      have hzero : (0 : FABL.F₂Cube (2 + quadraticNormalFormDimension l r)) =
          Fin.append (0 : FABL.F₂Cube 2)
            (0 : FABL.F₂Cube (quadraticNormalFormDimension l r)) := by
        funext i
        refine Fin.addCases (m := 2) (n := quadraticNormalFormDimension l r) ?_ ?_ i
        · intro j
          simp
        · intro j
          simp
      rw [hzero, walshTransform_booleanDirectSum_append,
        pairedHeadQuadratic_eq_innerProductModTwoBit,
        walshTransform_innerProductModTwoBit_zero, ih]
      push_cast
      rw [pow_add]
      rw [show l + 1 + r = (l + r) + 1 by omega, pow_succ]
      rw [← pow_add]
      ring

private theorem hammingWeight_comp_affineEquiv
    {n : ℕ} (f : BooleanFunction n)
    (e : FABL.F₂Cube n ≃ᵃ[FABL.𝔽₂] FABL.F₂Cube n) :
    hammingWeight (f ∘ e) = hammingWeight f := by
  have h := hammingDistance_comp_affineEquiv f 0 e
  rw [hammingDistance_eq_hammingWeight_add,
    hammingDistance_eq_hammingWeight_add] at h
  simpa using h

private theorem hammingWeight_quadraticNormalForm_lt
    (l r : ℕ) (hl : 0 < l) :
    hammingWeight (quadraticNormalForm l r) <
      2 ^ (quadraticNormalFormDimension l r - 1) := by
  have hwalsh := walshTransform_zero_eq_two_pow_sub_two_weight
    (quadraticNormalForm l r)
  rw [walshTransform_quadraticNormalForm_zero] at hwalsh
  have hdim : 0 < quadraticNormalFormDimension l r := by
    rw [quadraticNormalFormDimension_eq]
    omega
  have hdimPow : (2 : ℤ) ^ quadraticNormalFormDimension l r =
      2 * (2 : ℤ) ^ (quadraticNormalFormDimension l r - 1) := by
    calc
      (2 : ℤ) ^ quadraticNormalFormDimension l r =
          2 ^ ((quadraticNormalFormDimension l r - 1) + 1) := by congr 1; omega
      _ = 2 ^ (quadraticNormalFormDimension l r - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (quadraticNormalFormDimension l r - 1) := by ring
  have hpositive : (0 : ℤ) < 2 ^ (l + r) := pow_pos (by omega) _
  rw [hdimPow] at hwalsh
  have hint : (hammingWeight (quadraticNormalForm l r) : ℤ) <
      (2 : ℤ) ^ (quadraticNormalFormDimension l r - 1) := by omega
  exact_mod_cast hint

private theorem hammingWeight_quadraticNormalForm_add_one_gt
    (l r : ℕ) (hl : 0 < l) :
    2 ^ (quadraticNormalFormDimension l r - 1) <
      hammingWeight (fun x ↦ quadraticNormalForm l r x + 1) := by
  rw [show (fun x ↦ quadraticNormalForm l r x + 1) =
      quadraticNormalForm l r + FABL.affineFunction 1 0 by
    funext x
    simp [FABL.affineFunction, FABL.f₂DotProduct, dotProduct]]
  rw [hammingWeight_add_constant_one]
  have hlower := hammingWeight_quadraticNormalForm_lt l r hl
  have hdim : 0 < quadraticNormalFormDimension l r := by
    rw [quadraticNormalFormDimension_eq]
    omega
  have hdimPow : 2 ^ quadraticNormalFormDimension l r =
      2 * 2 ^ (quadraticNormalFormDimension l r - 1) := by
    calc
      2 ^ quadraticNormalFormDimension l r =
          2 ^ ((quadraticNormalFormDimension l r - 1) + 1) := by congr 1; omega
      _ = 2 ^ (quadraticNormalFormDimension l r - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (quadraticNormalFormDimension l r - 1) := Nat.mul_comm _ _
  rw [hdimPow]
  omega

private theorem isBalanced_quadraticNormalForm_add_firstRadical
    (l r : ℕ) (hr : 0 < r) :
    IsBalanced (fun x ↦ quadraticNormalForm l r x +
      quadraticNormalFormFirstFreeCoordinate l r hr x) := by
  induction l with
  | zero =>
      let a : FABL.F₂Cube r := Pi.single ⟨0, hr⟩ 1
      have ha : a ≠ 0 := by
        intro hzero
        have h := congrFun hzero ⟨0, hr⟩
        simp [a] at h
      rw [show (fun x ↦ quadraticNormalForm 0 r x +
          quadraticNormalFormFirstFreeCoordinate 0 r hr x) =
          FABL.affineFunction 0 a by
        funext x
        simp [quadraticNormalForm, quadraticNormalFormFirstFreeCoordinate,
          FABL.affineFunction, FABL.f₂DotProduct, a]]
      exact isBalanced_affineFunction_of_ne_zero 0 a ha
  | succ l ih =>
      apply (isBalanced_iff_walshTransform_zero_eq_zero _).mpr
      rw [show (fun x ↦ quadraticNormalForm (l + 1) r x +
          quadraticNormalFormFirstFreeCoordinate (l + 1) r hr x) =
          booleanDirectSum pairedHeadQuadratic
            (fun y ↦ quadraticNormalForm l r y +
              quadraticNormalFormFirstFreeCoordinate l r hr y) by
        funext x
        simp only [quadraticNormalForm, quadraticNormalFormFirstFreeCoordinate,
          booleanDirectSum, pairedHeadQuadratic]
        abel]
      have hzero : (0 : FABL.F₂Cube (2 + quadraticNormalFormDimension l r)) =
          Fin.append (0 : FABL.F₂Cube 2)
            (0 : FABL.F₂Cube (quadraticNormalFormDimension l r)) := by
        funext i
        refine Fin.addCases (m := 2) (n := quadraticNormalFormDimension l r) ?_ ?_ i
        · intro j
          simp
        · intro j
          simp
      rw [hzero, walshTransform_booleanDirectSum_append,
        (isBalanced_iff_walshTransform_zero_eq_zero _).mp ih, mul_zero]

/-- Carlet's quadratic affine normal form, split by balancedness and weight. -/
theorem quadratic_affine_normal_form
    {n : ℕ} (f : BooleanFunction n)
    (hdegree : FABL.functionAlgebraicDegree f ≤ 2)
    (hnonaffine : ¬ ∃ c a, f = FABL.affineFunction c a) :
    (IsBalanced f →
      ∃ l r : ℕ, 1 ≤ l ∧ l ≤ (n - 1) / 2 ∧
        n = 2 * l + r ∧ ∃ hr : 0 < r,
          ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
              FABL.F₂Cube n,
            ∀ x, f (e x) = quadraticNormalForm l r x +
              quadraticNormalFormFirstFreeCoordinate l r hr x) ∧
    (hammingWeight f < 2 ^ (n - 1) →
      ∃ l r : ℕ, 1 ≤ l ∧ l ≤ n / 2 ∧ n = 2 * l + r ∧
        ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
            FABL.F₂Cube n,
          ∀ x, f (e x) = quadraticNormalForm l r x) ∧
    (2 ^ (n - 1) < hammingWeight f →
      ∃ l r : ℕ, 1 ≤ l ∧ l ≤ n / 2 ∧ n = 2 * l + r ∧
        ∃ e : FABL.F₂Cube (quadraticNormalFormDimension l r) ≃ᵃ[FABL.𝔽₂]
            FABL.F₂Cube n,
          ∀ x, f (e x) = quadraticNormalForm l r x + 1) := by
  obtain ⟨l, r, hdim, e, c, a, hdecomposition⟩ :=
    exists_paired_quadratic_affine_decomposition f hdegree
  subst n
  have hl : 0 < l := by
    by_contra hnotPositive
    have hlzero : l = 0 := Nat.eq_zero_of_not_pos hnotPositive
    subst l
    have hcomp : f ∘ e.toAffineEquiv = FABL.affineFunction c a := by
      funext x
      simpa [quadraticNormalForm] using hdecomposition x
    have hfdegree : FABL.functionAlgebraicDegree f ≤ 1 := by
      rw [← FABL.functionAlgebraicDegree_comp_affineEquiv f e.toAffineEquiv,
        hcomp]
      exact FABL.functionAlgebraicDegree_affineFunction_le_one c a
    obtain ⟨c', a', haffine⟩ :=
      FABL.exists_affineFunction_of_functionAlgebraicDegree_le_one f hfdegree
    exact hnonaffine ⟨c', a', haffine⟩
  have hdimension : quadraticNormalFormDimension l r = 2 * l + r :=
    quadraticNormalFormDimension_eq l r
  have hn : 0 < quadraticNormalFormDimension l r := by
    rw [hdimension]
    omega
  rcases exists_paired_quadratic_normalization l r c a with
      hnormal | hnormal | hnormal
  · obtain ⟨A, hA⟩ := hnormal
    let E := A.trans e.toAffineEquiv
    have hform (x : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
        f (E x) = quadraticNormalForm l r x := by
      change f (e (A x)) = _
      rw [hdecomposition]
      exact hA x
    have hweight : hammingWeight (quadraticNormalForm l r) =
        hammingWeight f := by
      calc
        hammingWeight (quadraticNormalForm l r) =
            hammingWeight (f ∘ E) := by
              apply congrArg hammingWeight
              funext x
              exact (hform x).symm
        _ = hammingWeight f := hammingWeight_comp_affineEquiv f E
    have hlower := hammingWeight_quadraticNormalForm_lt l r hl
    refine ⟨?_, ?_, ?_⟩
    · intro hbalanced
      have hcenter := hammingWeight_eq_two_pow_pred_of_isBalanced f hn hbalanced
      rw [hweight, hcenter] at hlower
      omega
    · intro _hbelow
      refine ⟨l, r, by omega, ?_, hdimension, E, hform⟩
      rw [hdimension]
      omega
    · intro habove
      rw [hweight] at hlower
      omega
  · obtain ⟨A, hA⟩ := hnormal
    let E := A.trans e.toAffineEquiv
    have hform (x : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
        f (E x) = quadraticNormalForm l r x + 1 := by
      change f (e (A x)) = _
      rw [hdecomposition]
      exact hA x
    let g : BooleanFunction (quadraticNormalFormDimension l r) :=
      fun x ↦ quadraticNormalForm l r x + 1
    have hweight : hammingWeight g = hammingWeight f := by
      calc
        hammingWeight g = hammingWeight (f ∘ E) := by
          apply congrArg hammingWeight
          funext x
          exact (hform x).symm
        _ = hammingWeight f := hammingWeight_comp_affineEquiv f E
    have hupper := hammingWeight_quadraticNormalForm_add_one_gt l r hl
    change 2 ^ (quadraticNormalFormDimension l r - 1) < hammingWeight g at hupper
    refine ⟨?_, ?_, ?_⟩
    · intro hbalanced
      have hcenter := hammingWeight_eq_two_pow_pred_of_isBalanced f hn hbalanced
      rw [hweight, hcenter] at hupper
      omega
    · intro hbelow
      rw [hweight] at hupper
      omega
    · intro _habove
      refine ⟨l, r, by omega, ?_, hdimension, E, hform⟩
      rw [hdimension]
      omega
  · obtain ⟨hr, A, hA⟩ := hnormal
    let E := A.trans e.toAffineEquiv
    let g : BooleanFunction (quadraticNormalFormDimension l r) :=
      fun x ↦ quadraticNormalForm l r x +
        quadraticNormalFormFirstFreeCoordinate l r hr x
    have hform (x : FABL.F₂Cube (quadraticNormalFormDimension l r)) :
        f (E x) = g x := by
      change f (e (A x)) = _
      rw [hdecomposition]
      exact hA x
    have hweight : hammingWeight g = hammingWeight f := by
      calc
        hammingWeight g = hammingWeight (f ∘ E) := by
          apply congrArg hammingWeight
          funext x
          exact (hform x).symm
        _ = hammingWeight f := hammingWeight_comp_affineEquiv f E
    have hgbalanced : IsBalanced g :=
      isBalanced_quadraticNormalForm_add_firstRadical l r hr
    have hfbalanced : IsBalanced f := by
      unfold IsBalanced at hgbalanced ⊢
      rw [← hweight]
      exact hgbalanced
    have hcenter := hammingWeight_eq_two_pow_pred_of_isBalanced f hn hfbalanced
    refine ⟨?_, ?_, ?_⟩
    · intro _hbalanced
      refine ⟨l, r, by omega, ?_, hdimension, hr, E, ?_⟩
      · rw [hdimension]
        omega
      · intro x
        exact hform x
    · intro hbelow
      omega
    · intro habove
      omega

end CryptBoolean
