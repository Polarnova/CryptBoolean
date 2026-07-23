/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.LinearStructureNormalForm
public import CryptBoolean.Carlet.Chapter04.Nonlinearity
public import FABL.Chapter06.Constructions.BentFunctions

/-!
# Nonlinearity bounds from linear structures

Carlet Proposition 14 separates the linear-kernel coordinates. Their affine contribution cancels
against a matching affine approximant, so every mismatch on the complementary cube has exactly one
copy for each point of the linear-kernel cube. Relation (36) then gives Carlet's refined bound.
-/

open Finset
open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {m k : ℕ}

private def separatedLinearFunction
    (g : BooleanFunction m) (ε : FABL.F₂Cube k) : BooleanFunction (m + k) :=
  fun z ↦
    let p := (Fin.appendEquiv m k).symm z
    g p.1 + FABL.f₂DotProduct ε p.2

@[simp] private theorem separatedLinearFunction_append
    (g : BooleanFunction m) (ε : FABL.F₂Cube k)
    (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
    separatedLinearFunction g ε (Fin.append x y) =
      g x + FABL.f₂DotProduct ε y := by
  simp [separatedLinearFunction]

private theorem separatedLinearFunction_ne_affineFunction_append_iff
    (g : BooleanFunction m) (ε : FABL.F₂Cube k)
    (c : FABL.𝔽₂) (a : FABL.F₂Cube m)
    (x : FABL.F₂Cube m) (y : FABL.F₂Cube k) :
    separatedLinearFunction g ε (Fin.append x y) ≠
        FABL.affineFunction c (Fin.append a ε) (Fin.append x y) ↔
      g x ≠ FABL.affineFunction c a x := by
  rw [separatedLinearFunction_append]
  simp only [FABL.affineFunction, FABL.f₂DotProduct_append]
  constructor
  · intro hne heq
    apply hne
    rw [heq]
    abel
  · intro hne heq
    apply hne
    apply add_right_cancel (b := FABL.f₂DotProduct ε y)
    simpa only [add_assoc] using heq

private theorem hammingDistance_separatedLinearFunction_affineFunction
    (g : BooleanFunction m) (ε : FABL.F₂Cube k)
    (c : FABL.𝔽₂) (a : FABL.F₂Cube m) :
    hammingDistance (separatedLinearFunction g ε)
        (FABL.affineFunction c (Fin.append a ε)) =
      2 ^ k * hammingDistance g (FABL.affineFunction c a) := by
  classical
  unfold hammingDistance hammingDist
  calc
    #((Finset.univ : Finset (FABL.F₂Cube (m + k))).filter fun z ↦
        separatedLinearFunction g ε z ≠
          FABL.affineFunction c (Fin.append a ε) z) =
        #(((Finset.univ : Finset (FABL.F₂Cube m)).filter fun x ↦
            g x ≠ FABL.affineFunction c a x) ×ˢ
          (Finset.univ : Finset (FABL.F₂Cube k))) := by
      apply Finset.card_bij
        (fun z _hz ↦ (Fin.appendEquiv m k).symm z)
      · intro z hz
        let p := (Fin.appendEquiv m k).symm z
        have hz' : z = Fin.append p.1 p.2 :=
          ((Fin.appendEquiv m k).apply_symm_apply z).symm
        have hmismatch := (Finset.mem_filter.mp hz).2
        rw [hz'] at hmismatch
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
        exact (separatedLinearFunction_ne_affineFunction_append_iff
          g ε c a p.1 p.2).1 hmismatch
      · intro z _hz w _hw hzw
        exact (Fin.appendEquiv m k).symm.injective hzw
      · intro p hp
        refine ⟨Fin.append p.1 p.2, ?_, ?_⟩
        · have hp' := Finset.mem_product.mp hp
          have hmismatch := (Finset.mem_filter.mp hp'.1).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          exact (separatedLinearFunction_ne_affineFunction_append_iff
            g ε c a p.1 p.2).2 hmismatch
        · exact (Fin.appendEquiv m k).symm_apply_apply p
    _ = #((Finset.univ : Finset (FABL.F₂Cube m)).filter fun x ↦
          g x ≠ FABL.affineFunction c a x) *
        #(Finset.univ : Finset (FABL.F₂Cube k)) := Finset.card_product _ _
    _ = 2 ^ k *
        #((Finset.univ : Finset (FABL.F₂Cube m)).filter fun x ↦
          g x ≠ FABL.affineFunction c a x) := by
      rw [Finset.card_univ, card_f₂Cube]
      exact Nat.mul_comm _ _

private theorem nonlinearity_separatedLinearFunction_le
    (g : BooleanFunction m) (ε : FABL.F₂Cube k) :
    nonlinearity (separatedLinearFunction g ε) ≤
      2 ^ k * nonlinearity g := by
  classical
  unfold nonlinearity
  obtain ⟨p, _hp, hmin⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube m)))
    Finset.univ_nonempty
    (fun q ↦ hammingDistance g (FABL.affineFunction q.1 q.2))
  calc
    (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube (m + k))).inf'
        Finset.univ_nonempty
        (fun q ↦ hammingDistance (separatedLinearFunction g ε)
          (FABL.affineFunction q.1 q.2)) ≤
        hammingDistance (separatedLinearFunction g ε)
          (FABL.affineFunction p.1 (Fin.append p.2 ε)) :=
      Finset.inf'_le _ (Finset.mem_univ (p.1, Fin.append p.2 ε))
    _ = 2 ^ k * hammingDistance g (FABL.affineFunction p.1 p.2) :=
      hammingDistance_separatedLinearFunction_affineFunction g ε p.1 p.2
    _ = 2 ^ k *
        (Finset.univ : Finset (FABL.𝔽₂ × FABL.F₂Cube m)).inf'
          Finset.univ_nonempty
          (fun q ↦ hammingDistance g (FABL.affineFunction q.1 q.2)) := by
      rw [hmin.symm]

private theorem two_pow_mul_relation_36_eq (m k : ℕ) :
    (2 : ℝ) ^ k *
        ((2 : ℝ) ^ ((m : ℝ) - 1) -
          (2 : ℝ) ^ ((m : ℝ) / 2 - 1)) =
      (2 : ℝ) ^ (((m + k : ℕ) : ℝ) - 1) -
        (2 : ℝ) ^ ((((m + k : ℕ) : ℝ) + (k : ℝ) - 2) / 2) := by
  rw [← Real.rpow_natCast, mul_sub,
    ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
  push_cast
  congr 1 <;> ring_nf

private theorem nonlinearity_cast_le_of_finrank_linearKernel_ge
    (f : BooleanFunction (m + k))
    (hk : k ≤ Module.finrank FABL.𝔽₂ (linearKernel f)) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ (((m + k : ℕ) : ℝ) - 1) -
        (2 : ℝ) ^ ((((m + k : ℕ) : ℝ) + (k : ℝ) - 2) / 2) := by
  obtain ⟨L, g, ε, hnormal⟩ :=
    (finrank_linearKernel_ge_iff_hasSeparatedLinearStructureNormalForm f).mp hk
  have hcomp : f ∘ L = separatedLinearFunction g ε := by
    funext z
    let p := (Fin.appendEquiv m k).symm z
    have hz : z = Fin.append p.1 p.2 :=
      ((Fin.appendEquiv m k).apply_symm_apply z).symm
    rw [hz]
    simpa [Function.comp_apply] using hnormal p.1 p.2
  have hinvariant : nonlinearity (f ∘ L) = nonlinearity f := by
    simpa using nonlinearity_comp_affineEquiv f L.toAffineEquiv
  have hnlNat : nonlinearity f ≤ 2 ^ k * nonlinearity g := by
    rw [← hinvariant, hcomp]
    exact nonlinearity_separatedLinearFunction_le g ε
  have hnlReal :
      (nonlinearity f : ℝ) ≤ (2 : ℝ) ^ k * (nonlinearity g : ℝ) := by
    exact_mod_cast hnlNat
  calc
    (nonlinearity f : ℝ) ≤
        (2 : ℝ) ^ k * (nonlinearity g : ℝ) := hnlReal
    _ ≤ (2 : ℝ) ^ k *
        ((2 : ℝ) ^ ((m : ℝ) - 1) -
          (2 : ℝ) ^ ((m : ℝ) / 2 - 1)) :=
      mul_le_mul_of_nonneg_left (nonlinearity_cast_le_relation_36 g) (by positivity)
    _ = (2 : ℝ) ^ (((m + k : ℕ) : ℝ) - 1) -
        (2 : ℝ) ^ ((((m + k : ℕ) : ℝ) + (k : ℝ) - 2) / 2) :=
      two_pow_mul_relation_36_eq m k

/-- If the linear kernel has dimension `k`, Carlet Relation (36) improves to
`nl(f) ≤ 2^(n-1) - 2^((n+k-2)/2)` for `n = m + k`. -/
theorem nonlinearity_cast_le_of_finrank_linearKernel_eq
    (f : BooleanFunction (m + k))
    (hker : Module.finrank FABL.𝔽₂ (linearKernel f) = k) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ (((m + k : ℕ) : ℝ) - 1) -
        (2 : ℝ) ^ ((((m + k : ℕ) : ℝ) + (k : ℝ) - 2) / 2) := by
  apply nonlinearity_cast_le_of_finrank_linearKernel_ge f
  omega

/-- A nonzero linear structure gives Carlet's bound
`nl(f) ≤ 2^(n-1) - 2^((n-1)/2)` in dimension `n = m + 1`. -/
theorem nonlinearity_cast_le_of_exists_nonzero_linearStructure
    (f : BooleanFunction (m + 1))
    (hstructure : ∃ e : FABL.F₂Cube (m + 1), e ≠ 0 ∧ IsLinearStructure f e) :
    (nonlinearity f : ℝ) ≤
      (2 : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1) -
        (2 : ℝ) ^ ((((m + 1 : ℕ) : ℝ) - 1) / 2) := by
  have hk : 1 ≤ Module.finrank FABL.𝔽₂ (linearKernel f) := by
    rw [Submodule.one_le_finrank_iff, Submodule.ne_bot_iff]
    obtain ⟨e, he, hlinear⟩ := hstructure
    exact ⟨e, hlinear, he⟩
  have hbound :=
    nonlinearity_cast_le_of_finrank_linearKernel_ge (m := m) (k := 1) f hk
  push_cast at hbound ⊢
  ring_nf at hbound ⊢
  exact hbound

end CryptBoolean
