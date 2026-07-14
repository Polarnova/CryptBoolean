/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter02.NumericalNormalForm
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Carlet Chapter 2 finite-field representations

The binary Galois field, its absolute trace, trace representations of Boolean
functions, and the unique bounded-degree univariate representation. These
declarations reuse Mathlib's finite-field trace and Lagrange interpolation APIs.
-/

open Finset Polynomial
open scoped BigOperators

@[expose] public section

namespace CryptBoolean

/-- Mathlib's canonical field with `2^n` elements. -/
abbrev BinaryGaloisField (n : ℕ) := GaloisField 2 n

/-- A scalar Boolean function represented on the binary Galois field. -/
abbrev FieldBooleanFunction (n : ℕ) := BinaryGaloisField n → FABL.𝔽₂

/-- The absolute trace from `GF(2^n)` to `GF(2)`. -/
noncomputable def absoluteTrace (n : ℕ) : BinaryGaloisField n →ₗ[FABL.𝔽₂] FABL.𝔽₂ :=
  Algebra.trace FABL.𝔽₂ (BinaryGaloisField n)

/-- Mathlib's finite-field trace formula specializes to the absolute binary trace. -/
theorem algebraMap_absoluteTrace_eq_sum_frobenius {n : ℕ} (hn : n ≠ 0)
    (x : BinaryGaloisField n) :
    algebraMap FABL.𝔽₂ (BinaryGaloisField n) (absoluteTrace n x) =
      ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
  have h := FiniteField.algebraMap_trace_eq_sum_pow
    FABL.𝔽₂ (BinaryGaloisField n) x
  rw [GaloisField.finrank 2 hn, Nat.card_eq_fintype_card, ZMod.card] at h
  simpa [absoluteTrace] using h

/-- Nondegeneracy of the finite-field trace supplies an element of absolute trace one. -/
theorem exists_absoluteTrace_eq_one (n : ℕ) :
    ∃ traceOne : BinaryGaloisField n, absoluteTrace n traceOne = 1 := by
  simpa [absoluteTrace] using
    (Algebra.trace_surjective FABL.𝔽₂ (BinaryGaloisField n) (1 : FABL.𝔽₂))

/-- The absolute trace onto the binary prime field is surjective. -/
theorem absoluteTrace_surjective (n : ℕ) :
    Function.Surjective (absoluteTrace n) := by
  simpa [absoluteTrace] using
    (Algebra.trace_surjective FABL.𝔽₂ (BinaryGaloisField n))

/-- A field-valued lift selected by a trace-one element. -/
noncomputable def traceLift {n : ℕ} (traceOne : BinaryGaloisField n)
    (f : FieldBooleanFunction n) :
    BinaryGaloisField n → BinaryGaloisField n :=
  fun x ↦ if f x = 0 then 0 else traceOne

/-- Every field-domain Boolean function is an absolute trace of a field-valued function. -/
theorem absoluteTrace_traceLift {n : ℕ} (traceOne : BinaryGaloisField n)
    (htraceOne : absoluteTrace n traceOne = 1) (f : FieldBooleanFunction n)
    (x : BinaryGaloisField n) :
    absoluteTrace n (traceLift traceOne f x) = f x := by
  by_cases hfx : f x = 0
  · simp [traceLift, hfx]
  · have hfx_one : f x = 1 := Fin.eq_one_of_ne_zero (f x) hfx
    simp [traceLift, hfx_one, htraceOne]

/-- The canonical Lagrange polynomial representing a function on `GF(2^n)`. -/
noncomputable def univariateRepresentation {n : ℕ}
    (F : BinaryGaloisField n → BinaryGaloisField n) :
    (BinaryGaloisField n)[X] := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  classical
  exact Lagrange.interpolate Finset.univ id F

/-- The univariate representation evaluates to the original function. -/
theorem eval_univariateRepresentation {n : ℕ}
    (F : BinaryGaloisField n → BinaryGaloisField n) (x : BinaryGaloisField n) :
    (univariateRepresentation F).eval x = F x := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  classical
  exact Lagrange.eval_interpolate_at_node F (Set.injOn_id _) (Finset.mem_univ x)

/-- The canonical univariate representation has degree strictly below the field cardinality. -/
theorem degree_univariateRepresentation_lt_card {n : ℕ}
    (F : BinaryGaloisField n → BinaryGaloisField n) :
    (univariateRepresentation F).degree < Nat.card (BinaryGaloisField n) := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  classical
  rw [Nat.card_eq_fintype_card]
  exact Lagrange.degree_interpolate_lt F (Set.injOn_id _)

/-- Carlet's unique univariate representation below degree `2^n`. -/
theorem existsUnique_univariateRepresentation {n : ℕ}
    (F : BinaryGaloisField n → BinaryGaloisField n) :
    ∃! P : (BinaryGaloisField n)[X],
      P.degree < Nat.card (BinaryGaloisField n) ∧ ∀ x, P.eval x = F x := by
  letI := Fintype.ofFinite (BinaryGaloisField n)
  classical
  refine ⟨univariateRepresentation F,
    ⟨degree_univariateRepresentation_lt_card F, eval_univariateRepresentation F⟩, ?_⟩
  intro P hP
  rw [Nat.card_eq_fintype_card] at hP
  calc
    P = Lagrange.interpolate Finset.univ id (fun x ↦ P.eval x) :=
      Lagrange.eq_interpolate (Set.injOn_id _) hP.1
    _ = Lagrange.interpolate Finset.univ id F := by
      apply Lagrange.interpolate_eq_of_values_eq_on
      intro x _
      exact hP.2 x
    _ = univariateRepresentation F := rfl

end CryptBoolean
