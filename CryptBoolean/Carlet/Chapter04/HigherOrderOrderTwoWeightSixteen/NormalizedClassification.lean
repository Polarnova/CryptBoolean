/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.NormalizedClassifier
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.CandidateDecode

/-!
# Complete normalized rank-seven pattern classifier

The nonidentity columns of a normalized support form a strictly increasing
orthogonal sequence of odd nonunit vectors in `𝔽₂⁸`.  At each step the finite
search retains only the later columns orthogonal to the chosen column.  A
generic extension lemma proves that every sequence satisfying the systematic
constraints follows one branch of this search.

The final finite equality is divided by the first column.  Its 120 independent
shards are elaborated asynchronously and combined into one kernel-checked
coverage theorem; the mathematical argument itself is shared by every shard.
-/

@[expose] public section

namespace CryptBoolean

open Lean Parser.Term

/-- The odd nonunit eight-bit columns available to a normalized systematic
code. -/
private def systematicWeightSixteenColumns : List (BitVec 8) :=
  (List.range 256).map (BitVec.ofNat 8) |>.filter
    isSystematicWeightSixteenNonunitOddColumn

/-- Later columns that remain orthogonal to the selected column. -/
private def systematicWeightSixteenSuccessors
    (available : List (BitVec 8)) (column : BitVec 8) : List (BitVec 8) :=
  available.filter fun next =>
    column.ult next &&
      areSystematicWeightSixteenColumnsOrthogonal column next

/-- Increasing orthogonal completions of a partial systematic code. -/
private def systematicWeightSixteenCompletions :
    Nat → List (BitVec 8) → List (BitVec 8) → List (List (BitVec 8))
  | 0, chosen, _available => [chosen]
  | remaining + 1, chosen, available =>
      available.flatMap fun column =>
        systematicWeightSixteenCompletions remaining (chosen ++ [column])
          (systematicWeightSixteenSuccessors available column)

/-- Pack an eight-column search leaf into its little-endian 64-bit code. -/
private def packSystematicWeightSixteenColumnList :
    List (BitVec 8) → BitVec 64
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      c7 ++ (c6 ++ (c5 ++ (c4 ++ (c3 ++ (c2 ++ (c1 ++ c0))))))
  | _ => 0

/-- The eight ordered columns extracted from a packed systematic code. -/
private def systematicWeightSixteenColumnsOfCode
    (code : BitVec 64) : List (BitVec 8) :=
  [systematicWeightSixteenColumn code 0,
    systematicWeightSixteenColumn code 1,
    systematicWeightSixteenColumn code 2,
    systematicWeightSixteenColumn code 3,
    systematicWeightSixteenColumn code 4,
    systematicWeightSixteenColumn code 5,
    systematicWeightSixteenColumn code 6,
    systematicWeightSixteenColumn code 7]

/-- A column sequence follows the filtered completion search. -/
private def IsSystematicWeightSixteenExtension :
    List (BitVec 8) → List (BitVec 8) → Prop
  | _, [] => True
  | available, column :: remaining =>
      column ∈ available ∧
        IsSystematicWeightSixteenExtension
          (systematicWeightSixteenSuccessors available column) remaining

private theorem mem_systematicWeightSixteenColumns (column : BitVec 8) :
    column ∈ systematicWeightSixteenColumns ↔
      isSystematicWeightSixteenNonunitOddColumn column = true := by
  rw [systematicWeightSixteenColumns, List.mem_filter]
  simp only [and_iff_right_iff_imp]
  intro _hcolumn
  apply List.mem_map.mpr
  refine ⟨column.toNat, List.mem_range.mpr ?_, ?_⟩
  · simpa using column.isLt
  · simp

private theorem mem_systematicWeightSixteenSuccessors_iff
    (available : List (BitVec 8)) (column next : BitVec 8) :
    next ∈ systematicWeightSixteenSuccessors available column ↔
      next ∈ available ∧ column.ult next = true ∧
        areSystematicWeightSixteenColumnsOrthogonal column next = true := by
  simp [systematicWeightSixteenSuccessors, Bool.and_eq_true]

private theorem bitVec_ult_trans {a b c : BitVec 8}
    (hab : a.ult b = true) (hbc : b.ult c = true) :
    a.ult c = true := by
  simp only [BitVec.ult_eq_decide_lt, decide_eq_true_eq] at *
  exact BitVec.lt_trans hab hbc

private theorem systematicWeightSixteenExtension_of_constraints
    (code : BitVec 64)
    (hconstraints : SystematicWeightSixteenConstraints code = true) :
    IsSystematicWeightSixteenExtension systematicWeightSixteenColumns
      (systematicWeightSixteenColumnsOfCode code) := by
  simp only [SystematicWeightSixteenConstraints,
    Bool.and_eq_true] at hconstraints
  simp only [systematicWeightSixteenColumnsOfCode,
    IsSystematicWeightSixteenExtension,
    mem_systematicWeightSixteenColumns,
    mem_systematicWeightSixteenSuccessors_iff]
  aesop (add safe forward bitVec_ult_trans)

private theorem append_mem_systematicWeightSixteenCompletions_of_extension
    {chosen remaining available : List (BitVec 8)}
    (h : IsSystematicWeightSixteenExtension available remaining) :
    chosen ++ remaining ∈
      systematicWeightSixteenCompletions remaining.length chosen available := by
  induction remaining generalizing chosen available with
  | nil => simp [systematicWeightSixteenCompletions]
  | cons column remaining ih =>
      rw [List.length_cons, systematicWeightSixteenCompletions,
        List.mem_flatMap]
      refine ⟨column, h.1, ?_⟩
      have hmem := ih (chosen := chosen ++ [column])
        (available := systematicWeightSixteenSuccessors available column) h.2
      simpa only [List.append_assoc, List.singleton_append] using hmem

private theorem pack_systematicWeightSixteenColumnsOfCode
    (code : BitVec 64) :
    packSystematicWeightSixteenColumnList
        (systematicWeightSixteenColumnsOfCode code) = code := by
  simp only [packSystematicWeightSixteenColumnList,
    systematicWeightSixteenColumnsOfCode]
  unfold systematicWeightSixteenColumn
  repeat' rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
    (by norm_num)]
  exact BitVec.extractLsb'_eq_self

/-- Boolean coverage of every leaf in the finite completion search. -/
private def systematicWeightSixteenGeneratedCoverage : Bool :=
  (systematicWeightSixteenCompletions 8 []
      systematicWeightSixteenColumns).all fun columns =>
    isGeneratedSystematicWeightSixteenCode
      (packSystematicWeightSixteenColumnList columns)

/-- Coverage of the completion shard selected by its first column. -/
private def systematicWeightSixteenFirstShardCoverage
    (column : BitVec 8) : Bool :=
  (systematicWeightSixteenCompletions 7 [column]
      (systematicWeightSixteenSuccessors
        systematicWeightSixteenColumns column)).all fun columns =>
    isGeneratedSystematicWeightSixteenCode
      (packSystematicWeightSixteenColumnList columns)

private theorem systematicWeightSixteenGeneratedCoverage_eq_shards :
    systematicWeightSixteenGeneratedCoverage =
      systematicWeightSixteenColumns.all
        systematicWeightSixteenFirstShardCoverage := by
  rw [systematicWeightSixteenGeneratedCoverage,
    systematicWeightSixteenCompletions, List.all_flatMap]
  rfl

private meta def systematicWeightSixteenColumnValues : List Nat :=
  (List.range 256).filter fun value =>
    let weight := (List.range 8).foldl
      (fun count bit => if value.testBit bit then count + 1 else count) 0
    weight % 2 == 1 && weight != 1

local syntax "systematic_weight_sixteen_completion_certificates" : command

local macro_rules
  | `(command| systematic_weight_sixteen_completion_certificates) => do
      let values := systematicWeightSixteenColumnValues
      unless values.length == 120 do
        Lean.Macro.throwError
          "the normalized completion search must have 120 first-column shards"
      let generated ← values.toArray.mapIdxM fun index value => do
        let proofName := Lean.mkIdent <|
          Name.mkSimple s!"systematicWeightSixteenFirstShard_{index}"
        let valueTerm : TSyntax `term :=
          ⟨Syntax.mkNumLit (toString value)⟩
        let proofLemma ←
          `(Parser.Tactic.simpLemma| $proofName:term)
        let declaration ← `(command|
          set_option Elab.async true in
          set_option linter.style.maxHeartbeats false in
          set_option maxRecDepth 1000000 in
          set_option maxHeartbeats 20000000 in
          private theorem $proofName :
              systematicWeightSixteenFirstShardCoverage $valueTerm = true := by
            rfl)
        pure (valueTerm, proofLemma, declaration)
      let valueTerms := generated.map fun item => item.1
      let proofLemmas := generated.map fun item => item.2.1
      let declarations := generated.map fun item => item.2.2
      let columnsDeclaration ← `(command|
        private theorem systematicWeightSixteenColumns_eq_literal :
            systematicWeightSixteenColumns = [$[$valueTerms],*] := by
          rfl)
      let aggregate ← `(command|
        private theorem systematicWeightSixteenGeneratedCoverage_true :
            systematicWeightSixteenGeneratedCoverage = true := by
          rw [systematicWeightSixteenGeneratedCoverage_eq_shards,
            systematicWeightSixteenColumns_eq_literal]
          simp only [List.all_cons, $proofLemmas,*, List.all_nil])
      return Lean.mkNullNode <|
        declarations.map (·.raw) ++ #[columnsDeclaration.raw, aggregate.raw]

systematic_weight_sixteen_completion_certificates

/-- Every systematic orthonormal-column code occurs in the generated finite
family of normalized rank-seven weight-sixteen supports. -/
theorem systematicWeightSixteen_generated_of_constraints
    (code : BitVec 64)
    (hconstraints : SystematicWeightSixteenConstraints code = true) :
    isGeneratedSystematicWeightSixteenCode code = true := by
  have hextension :=
    systematicWeightSixteenExtension_of_constraints code hconstraints
  have hmember :=
    append_mem_systematicWeightSixteenCompletions_of_extension
      (chosen := []) hextension
  simp only [systematicWeightSixteenColumnsOfCode, List.nil_append,
    List.length_cons, List.length_nil] at hmember
  have hgenerated :=
    (List.all_eq_true.mp systematicWeightSixteenGeneratedCoverage_true)
      _ hmember
  rwa [pack_systematicWeightSixteenColumnsOfCode] at hgenerated

/-- Every systematic orthonormal-column code carries an explicit generated
canonical-class and affine-map certificate. -/
theorem exists_normalizedWeightSixteenCandidate_of_constraints
    (code : BitVec 64)
    (hconstraints : SystematicWeightSixteenConstraints code = true) :
    ∃ tree candidate,
      normalizedWeightSixteenCandidateBucket (code.extractLsb' 0 16) =
          some tree ∧
        NormalizedWeightSixteenCandidateTree.Member candidate tree ∧
        candidate.systematicCode = code :=
  exists_normalizedWeightSixteenCandidate_of_generated code
    (systematicWeightSixteen_generated_of_constraints code hconstraints)

end CryptBoolean
