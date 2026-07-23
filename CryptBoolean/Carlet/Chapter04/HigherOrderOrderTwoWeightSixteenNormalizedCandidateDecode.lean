/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenNormalizedCandidates

/-!
# Decode normalized weight-sixteen affine certificates

The generated affine code is row-major.  Its low seven bits store a source
origin, and the following seven chunks store the rows of a linear map.  The
corresponding `SevenVariableAffineMapData` therefore uses the image of the
source origin as translation and the transpose of those rows as directions.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace CryptBoolean

/-- Interpret one affine-code bit as an element of the binary field. -/
def normalizedCandidateAffineBit
    (candidate : NormalizedWeightSixteenCandidate) (index : ℕ) : FABL.𝔽₂ :=
  if candidate.affineCode.getLsbD index then 1 else 0

/-- The source origin encoded in the low seven bits. -/
def normalizedCandidateSourceOrigin
    (candidate : NormalizedWeightSixteenCandidate) : FABL.F₂Cube 7 :=
  fun i ↦ normalizedCandidateAffineBit candidate i

/-- The `j`th output row of the encoded linear map. -/
def normalizedCandidateAffineRow
    (candidate : NormalizedWeightSixteenCandidate) (j : Fin 7) :
    FABL.F₂Cube 7 :=
  fun i ↦ normalizedCandidateAffineBit candidate (7 * (j + 1) + i)

/-- Row evaluation of the encoded linear map. -/
def normalizedCandidateLinearPoint
    (candidate : NormalizedWeightSixteenCandidate) (x : FABL.F₂Cube 7) :
    FABL.F₂Cube 7 :=
  fun j ↦ ∑ i : Fin 7, normalizedCandidateAffineRow candidate j i * x i

/-- Decode the row-major affine certificate into the column-oriented data used
by `sevenVariableAffinePoint`. -/
def normalizedCandidateAffineMapData
    (candidate : NormalizedWeightSixteenCandidate) :
    SevenVariableAffineMapData 7 :=
  (normalizedCandidateLinearPoint candidate
      (normalizedCandidateSourceOrigin candidate),
    fun i j ↦ normalizedCandidateAffineRow candidate j i)

/-- Decoding transposes the stored rows and maps the source origin before using
it as the affine translation. -/
theorem sevenVariableAffinePoint_normalizedCandidateAffineMapData
    (candidate : NormalizedWeightSixteenCandidate) (x : FABL.F₂Cube 7) :
    sevenVariableAffinePoint (normalizedCandidateAffineMapData candidate) x =
      normalizedCandidateLinearPoint candidate
        (x + normalizedCandidateSourceOrigin candidate) := by
  funext j
  simp only [sevenVariableAffinePoint, normalizedCandidateAffineMapData,
    normalizedCandidateLinearPoint, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hcomm :
      (∑ i : Fin 7, x i * normalizedCandidateAffineRow candidate j i) =
        ∑ i : Fin 7, normalizedCandidateAffineRow candidate j i * x i := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  rw [hcomm]
  exact add_comm _ _

end CryptBoolean
