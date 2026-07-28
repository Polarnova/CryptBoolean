/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.OtherComplexity

/-!
# Carlet Definition 4: normal and weakly normal Boolean functions
-/

open scoped BooleanCube

@[expose] public section

namespace CryptBoolean

variable {n k : ℕ}

/-- A Boolean function is `k`-normal when it is constant on a `k`-dimensional affine flat. -/
def IsKNormal (f : BooleanFunction n) (k : ℕ) : Prop :=
  ∃ H : Submodule FABL.𝔽₂ (FABL.F₂Cube n), ∃ a : FABL.F₂Cube n,
    Module.finrank FABL.𝔽₂ H = k ∧ IsConstantOnAffineFlat f H a

/-- A Boolean function is `k`-weakly normal when it is affine on a `k`-dimensional affine flat. -/
def IsKWeaklyNormal (f : BooleanFunction n) (k : ℕ) : Prop :=
  ∃ H : Submodule FABL.𝔽₂ (FABL.F₂Cube n), ∃ a : FABL.F₂Cube n,
    Module.finrank FABL.𝔽₂ H = k ∧ IsAffineOnAffineFlat f H a

/-- Every `k`-normal Boolean function is `k`-weakly normal. -/
theorem IsKNormal.isKWeaklyNormal {f : BooleanFunction n} (h : IsKNormal f k) :
    IsKWeaklyNormal f k := by
  obtain ⟨H, a, hdim, hconstant⟩ := h
  exact ⟨H, a, hdim, hconstant.isAffineOnAffineFlat⟩

/-- A `k`-normal flat witnesses that `k` is bounded by Carlet's normality parameter. -/
theorem IsKNormal.le_normality {f : BooleanFunction n} (h : IsKNormal f k) :
    k ≤ normality f := by
  classical
  obtain ⟨H, a, hdim, hconstant⟩ := h
  rw [normality, ← hdim]
  have hp : (H, a) ∈
      ((Finset.univ : Finset
        (Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n)).filter
        (fun p ↦ IsConstantOnAffineFlat f p.1 p.2)) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ (H, a), hconstant⟩
  exact Finset.le_sup
    (f := fun p ↦ Module.finrank FABL.𝔽₂ p.1) hp

/-- A `k`-weakly-normal flat witnesses that `k` is bounded by weak normality. -/
theorem IsKWeaklyNormal.le_weakNormality {f : BooleanFunction n}
    (h : IsKWeaklyNormal f k) : k ≤ weakNormality f := by
  classical
  obtain ⟨H, a, hdim, haffine⟩ := h
  rw [weakNormality, ← hdim]
  have hp : (H, a) ∈
      ((Finset.univ : Finset
        (Submodule FABL.𝔽₂ (FABL.F₂Cube n) × FABL.F₂Cube n)).filter
        (fun p ↦ IsAffineOnAffineFlat f p.1 p.2)) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ (H, a), haffine⟩
  exact Finset.le_sup
    (f := fun p ↦ Module.finrank FABL.𝔽₂ p.1) hp

end CryptBoolean
