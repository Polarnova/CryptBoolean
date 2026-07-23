/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenNormalizedClassifier
public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteenNormalizedCandidateDecode
public meta import Std.Tactic.BVDecide.Reflect

/-!
# Complete normalized rank-seven pattern classifier

A systematic code is indexed by its first two ordered nonunit odd columns.
For each admissible prefix, the corresponding finite candidate tree contains
every code satisfying the systematic orthonormality constraints.  The union of
these prefix cases yields the normalized rank-seven classification.
-/

@[expose] public section

namespace CryptBoolean

open Lean Parser.Term

syntax normalizedWeightSixteenClassificationRow :=
  "|" term "," ident "," ident

local syntax (name := normalizedWeightSixteenClassificationCommand)
  "normalized_weight_sixteen_classification" ident "where"
    normalizedWeightSixteenClassificationRow* : command

local macro_rules
  | `(command| normalized_weight_sixteen_classification
      $dispatcherName:ident where
      $[$rows:normalizedWeightSixteenClassificationRow]*) => do
    let generated ← rows.mapM fun row => do
      let `(normalizedWeightSixteenClassificationRow|
        | $bucketPrefix:term, $tree:ident, $proofName:ident) := row
        | Lean.Macro.throwUnsupported
      let declaration ←
        `(command|
          set_option Elab.async true in
          /-- Every systematic code with the selected prefix and satisfying
          the orthonormality constraints belongs to its candidate tree. -/
          theorem $proofName
              (code : BitVec 64)
              (hprefix :
                code.extractLsb' 0 16 = BitVec.ofNat 16 $bucketPrefix)
              (hconstraints :
                SystematicWeightSixteenConstraints code = true) :
              ($tree).containsSystematicCode code = true := by
            unfold SystematicWeightSixteenConstraints
              systematicWeightSixteenColumn at hconstraints
            unfold isSystematicWeightSixteenNonunitOddColumn at hconstraints
            unfold areSystematicWeightSixteenColumnsOrthogonal at hconstraints
            unfold $tree
            simp only [
              NormalizedWeightSixteenCandidateTree.containsSystematicCode]
            weightSixteenFiniteCertificate)
      let branch ←
        `(tactic|
          (
            have hprefix :
                code.extractLsb' 0 16 =
                  BitVec.ofNat 16 $bucketPrefix := by
              simpa only [beq_iff_eq] using hprefixes
            unfold isGeneratedSystematicWeightSixteenCode
            rw [hprefix]
            exact $proofName code hprefix hconstraints
          ))
      pure (declaration, branch)
    let declarations := generated.map Prod.fst
    let branches := generated.map Prod.snd
    let focusedBranches ← branches.mapM fun branch =>
      `(tactic| focus $branch:tactic)
    let dispatcherDeclaration ← `(command|
      /-- Every systematic orthonormal-column code occurs in the generated
      finite family of normalized rank-seven weight-sixteen supports. -/
      theorem $dispatcherName
          (code : BitVec 64)
          (hconstraints :
            SystematicWeightSixteenConstraints code = true) :
          isGeneratedSystematicWeightSixteenCode code = true := by
        have hprefixes :=
          systematicWeightSixteen_prefix_allowed code hconstraints
        unfold IsSystematicWeightSixteenPrefixAllowed at hprefixes
        simp only [Bool.or_eq_true] at hprefixes
        repeat' (apply Or.elim hprefixes <;> intro hprefixes)
        $focusedBranches:tactic*)
    return Lean.mkNullNode <|
      declarations.map (·.raw) ++ #[dispatcherDeclaration.raw]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
normalized_weight_sixteen_classification
  systematicWeightSixteen_generated_of_constraints where
  | 2823, normalizedWeightSixteenCandidateBucket_0b07, systematicWeightSixteen_bucket_0b07_complete
  | 3335, normalizedWeightSixteenCandidateBucket_0d07, systematicWeightSixteen_bucket_0d07_complete
  | 3339, normalizedWeightSixteenCandidateBucket_0d0b, systematicWeightSixteen_bucket_0d0b_complete
  | 3591, normalizedWeightSixteenCandidateBucket_0e07, systematicWeightSixteen_bucket_0e07_complete
  | 3595, normalizedWeightSixteenCandidateBucket_0e0b, systematicWeightSixteen_bucket_0e0b_complete
  | 3597, normalizedWeightSixteenCandidateBucket_0e0d, systematicWeightSixteen_bucket_0e0d_complete
  | 4871, normalizedWeightSixteenCandidateBucket_1307, systematicWeightSixteen_bucket_1307_complete
  | 4875, normalizedWeightSixteenCandidateBucket_130b, systematicWeightSixteen_bucket_130b_complete
  | 5383, normalizedWeightSixteenCandidateBucket_1507, systematicWeightSixteen_bucket_1507_complete
  | 5389, normalizedWeightSixteenCandidateBucket_150d, systematicWeightSixteen_bucket_150d_complete
  | 5395, normalizedWeightSixteenCandidateBucket_1513, systematicWeightSixteen_bucket_1513_complete
  | 5639, normalizedWeightSixteenCandidateBucket_1607, systematicWeightSixteen_bucket_1607_complete
  | 5646, normalizedWeightSixteenCandidateBucket_160e, systematicWeightSixteen_bucket_160e_complete
  | 5651, normalizedWeightSixteenCandidateBucket_1613, systematicWeightSixteen_bucket_1613_complete
  | 5653, normalizedWeightSixteenCandidateBucket_1615, systematicWeightSixteen_bucket_1615_complete
  | 6411, normalizedWeightSixteenCandidateBucket_190b, systematicWeightSixteen_bucket_190b_complete
  | 6413, normalizedWeightSixteenCandidateBucket_190d, systematicWeightSixteen_bucket_190d_complete
  | 6419, normalizedWeightSixteenCandidateBucket_1913, systematicWeightSixteen_bucket_1913_complete
  | 6421, normalizedWeightSixteenCandidateBucket_1915, systematicWeightSixteen_bucket_1915_complete
  | 6667, normalizedWeightSixteenCandidateBucket_1a0b, systematicWeightSixteen_bucket_1a0b_complete
  | 6670, normalizedWeightSixteenCandidateBucket_1a0e, systematicWeightSixteen_bucket_1a0e_complete
  | 6675, normalizedWeightSixteenCandidateBucket_1a13, systematicWeightSixteen_bucket_1a13_complete
  | 6678, normalizedWeightSixteenCandidateBucket_1a16, systematicWeightSixteen_bucket_1a16_complete
  | 6681, normalizedWeightSixteenCandidateBucket_1a19, systematicWeightSixteen_bucket_1a19_complete
  | 7181, normalizedWeightSixteenCandidateBucket_1c0d, systematicWeightSixteen_bucket_1c0d_complete
  | 7182, normalizedWeightSixteenCandidateBucket_1c0e, systematicWeightSixteen_bucket_1c0e_complete
  | 7189, normalizedWeightSixteenCandidateBucket_1c15, systematicWeightSixteen_bucket_1c15_complete
  | 7190, normalizedWeightSixteenCandidateBucket_1c16, systematicWeightSixteen_bucket_1c16_complete
  | 7193, normalizedWeightSixteenCandidateBucket_1c19, systematicWeightSixteen_bucket_1c19_complete
  | 7194, normalizedWeightSixteenCandidateBucket_1c1a, systematicWeightSixteen_bucket_1c1a_complete
  | 8967, normalizedWeightSixteenCandidateBucket_2307, systematicWeightSixteen_bucket_2307_complete
  | 8971, normalizedWeightSixteenCandidateBucket_230b, systematicWeightSixteen_bucket_230b_complete
  | 8979, normalizedWeightSixteenCandidateBucket_2313, systematicWeightSixteen_bucket_2313_complete
  | 8988, normalizedWeightSixteenCandidateBucket_231c, systematicWeightSixteen_bucket_231c_complete
  | 8991, normalizedWeightSixteenCandidateBucket_231f, systematicWeightSixteen_bucket_231f_complete
  | 9479, normalizedWeightSixteenCandidateBucket_2507, systematicWeightSixteen_bucket_2507_complete
  | 9485, normalizedWeightSixteenCandidateBucket_250d, systematicWeightSixteen_bucket_250d_complete
  | 9493, normalizedWeightSixteenCandidateBucket_2515, systematicWeightSixteen_bucket_2515_complete
  | 9498, normalizedWeightSixteenCandidateBucket_251a, systematicWeightSixteen_bucket_251a_complete
  | 9503, normalizedWeightSixteenCandidateBucket_251f, systematicWeightSixteen_bucket_251f_complete
  | 9507, normalizedWeightSixteenCandidateBucket_2523, systematicWeightSixteen_bucket_2523_complete
  | 9735, normalizedWeightSixteenCandidateBucket_2607, systematicWeightSixteen_bucket_2607_complete
  | 9742, normalizedWeightSixteenCandidateBucket_260e, systematicWeightSixteen_bucket_260e_complete
  | 9750, normalizedWeightSixteenCandidateBucket_2616, systematicWeightSixteen_bucket_2616_complete
  | 9753, normalizedWeightSixteenCandidateBucket_2619, systematicWeightSixteen_bucket_2619_complete
  | 9759, normalizedWeightSixteenCandidateBucket_261f, systematicWeightSixteen_bucket_261f_complete
  | 9763, normalizedWeightSixteenCandidateBucket_2623, systematicWeightSixteen_bucket_2623_complete
  | 9765, normalizedWeightSixteenCandidateBucket_2625, systematicWeightSixteen_bucket_2625_complete
  | 10507, normalizedWeightSixteenCandidateBucket_290b, systematicWeightSixteen_bucket_290b_complete
  | 10509, normalizedWeightSixteenCandidateBucket_290d, systematicWeightSixteen_bucket_290d_complete
  | 10518, normalizedWeightSixteenCandidateBucket_2916, systematicWeightSixteen_bucket_2916_complete
  | 10521, normalizedWeightSixteenCandidateBucket_2919, systematicWeightSixteen_bucket_2919_complete
  | 10527, normalizedWeightSixteenCandidateBucket_291f, systematicWeightSixteen_bucket_291f_complete
  | 10531, normalizedWeightSixteenCandidateBucket_2923, systematicWeightSixteen_bucket_2923_complete
  | 10533, normalizedWeightSixteenCandidateBucket_2925, systematicWeightSixteen_bucket_2925_complete
  | 10763, normalizedWeightSixteenCandidateBucket_2a0b, systematicWeightSixteen_bucket_2a0b_complete
  | 10766, normalizedWeightSixteenCandidateBucket_2a0e, systematicWeightSixteen_bucket_2a0e_complete
  | 10773, normalizedWeightSixteenCandidateBucket_2a15, systematicWeightSixteen_bucket_2a15_complete
  | 10778, normalizedWeightSixteenCandidateBucket_2a1a, systematicWeightSixteen_bucket_2a1a_complete
  | 10783, normalizedWeightSixteenCandidateBucket_2a1f, systematicWeightSixteen_bucket_2a1f_complete
  | 10787, normalizedWeightSixteenCandidateBucket_2a23, systematicWeightSixteen_bucket_2a23_complete
  | 10790, normalizedWeightSixteenCandidateBucket_2a26, systematicWeightSixteen_bucket_2a26_complete
  | 10793, normalizedWeightSixteenCandidateBucket_2a29, systematicWeightSixteen_bucket_2a29_complete
  | 11277, normalizedWeightSixteenCandidateBucket_2c0d, systematicWeightSixteen_bucket_2c0d_complete
  | 11278, normalizedWeightSixteenCandidateBucket_2c0e, systematicWeightSixteen_bucket_2c0e_complete
  | 11283, normalizedWeightSixteenCandidateBucket_2c13, systematicWeightSixteen_bucket_2c13_complete
  | 11292, normalizedWeightSixteenCandidateBucket_2c1c, systematicWeightSixteen_bucket_2c1c_complete
  | 11295, normalizedWeightSixteenCandidateBucket_2c1f, systematicWeightSixteen_bucket_2c1f_complete
  | 11301, normalizedWeightSixteenCandidateBucket_2c25, systematicWeightSixteen_bucket_2c25_complete
  | 11302, normalizedWeightSixteenCandidateBucket_2c26, systematicWeightSixteen_bucket_2c26_complete
  | 11305, normalizedWeightSixteenCandidateBucket_2c29, systematicWeightSixteen_bucket_2c29_complete
  | 11306, normalizedWeightSixteenCandidateBucket_2c2a, systematicWeightSixteen_bucket_2c2a_complete
  | 12051, normalizedWeightSixteenCandidateBucket_2f13, systematicWeightSixteen_bucket_2f13_complete
  | 12053, normalizedWeightSixteenCandidateBucket_2f15, systematicWeightSixteen_bucket_2f15_complete
  | 12054, normalizedWeightSixteenCandidateBucket_2f16, systematicWeightSixteen_bucket_2f16_complete
  | 12057, normalizedWeightSixteenCandidateBucket_2f19, systematicWeightSixteen_bucket_2f19_complete
  | 12058, normalizedWeightSixteenCandidateBucket_2f1a, systematicWeightSixteen_bucket_2f1a_complete
  | 12060, normalizedWeightSixteenCandidateBucket_2f1c, systematicWeightSixteen_bucket_2f1c_complete
  | 12063, normalizedWeightSixteenCandidateBucket_2f1f, systematicWeightSixteen_bucket_2f1f_complete
  | 12558, normalizedWeightSixteenCandidateBucket_310e, systematicWeightSixteen_bucket_310e_complete
  | 12563, normalizedWeightSixteenCandidateBucket_3113, systematicWeightSixteen_bucket_3113_complete
  | 12565, normalizedWeightSixteenCandidateBucket_3115, systematicWeightSixteen_bucket_3115_complete
  | 12569, normalizedWeightSixteenCandidateBucket_3119, systematicWeightSixteen_bucket_3119_complete
  | 12575, normalizedWeightSixteenCandidateBucket_311f, systematicWeightSixteen_bucket_311f_complete
  | 12579, normalizedWeightSixteenCandidateBucket_3123, systematicWeightSixteen_bucket_3123_complete
  | 12581, normalizedWeightSixteenCandidateBucket_3125, systematicWeightSixteen_bucket_3125_complete
  | 12585, normalizedWeightSixteenCandidateBucket_3129, systematicWeightSixteen_bucket_3129_complete
  | 12591, normalizedWeightSixteenCandidateBucket_312f, systematicWeightSixteen_bucket_312f_complete
  | 12813, normalizedWeightSixteenCandidateBucket_320d, systematicWeightSixteen_bucket_320d_complete
  | 12819, normalizedWeightSixteenCandidateBucket_3213, systematicWeightSixteen_bucket_3213_complete
  | 12822, normalizedWeightSixteenCandidateBucket_3216, systematicWeightSixteen_bucket_3216_complete
  | 12826, normalizedWeightSixteenCandidateBucket_321a, systematicWeightSixteen_bucket_321a_complete
  | 12831, normalizedWeightSixteenCandidateBucket_321f, systematicWeightSixteen_bucket_321f_complete
  | 12835, normalizedWeightSixteenCandidateBucket_3223, systematicWeightSixteen_bucket_3223_complete
  | 12838, normalizedWeightSixteenCandidateBucket_3226, systematicWeightSixteen_bucket_3226_complete
  | 12842, normalizedWeightSixteenCandidateBucket_322a, systematicWeightSixteen_bucket_322a_complete
  | 12847, normalizedWeightSixteenCandidateBucket_322f, systematicWeightSixteen_bucket_322f_complete
  | 12849, normalizedWeightSixteenCandidateBucket_3231, systematicWeightSixteen_bucket_3231_complete
  | 13323, normalizedWeightSixteenCandidateBucket_340b, systematicWeightSixteen_bucket_340b_complete
  | 13333, normalizedWeightSixteenCandidateBucket_3415, systematicWeightSixteen_bucket_3415_complete
  | 13334, normalizedWeightSixteenCandidateBucket_3416, systematicWeightSixteen_bucket_3416_complete
  | 13340, normalizedWeightSixteenCandidateBucket_341c, systematicWeightSixteen_bucket_341c_complete
  | 13343, normalizedWeightSixteenCandidateBucket_341f, systematicWeightSixteen_bucket_341f_complete
  | 13349, normalizedWeightSixteenCandidateBucket_3425, systematicWeightSixteen_bucket_3425_complete
  | 13350, normalizedWeightSixteenCandidateBucket_3426, systematicWeightSixteen_bucket_3426_complete
  | 13356, normalizedWeightSixteenCandidateBucket_342c, systematicWeightSixteen_bucket_342c_complete
  | 13359, normalizedWeightSixteenCandidateBucket_342f, systematicWeightSixteen_bucket_342f_complete
  | 13361, normalizedWeightSixteenCandidateBucket_3431, systematicWeightSixteen_bucket_3431_complete
  | 13362, normalizedWeightSixteenCandidateBucket_3432, systematicWeightSixteen_bucket_3432_complete
  | 14091, normalizedWeightSixteenCandidateBucket_370b, systematicWeightSixteen_bucket_370b_complete
  | 14093, normalizedWeightSixteenCandidateBucket_370d, systematicWeightSixteen_bucket_370d_complete
  | 14094, normalizedWeightSixteenCandidateBucket_370e, systematicWeightSixteen_bucket_370e_complete
  | 14105, normalizedWeightSixteenCandidateBucket_3719, systematicWeightSixteen_bucket_3719_complete
  | 14106, normalizedWeightSixteenCandidateBucket_371a, systematicWeightSixteen_bucket_371a_complete
  | 14108, normalizedWeightSixteenCandidateBucket_371c, systematicWeightSixteen_bucket_371c_complete
  | 14111, normalizedWeightSixteenCandidateBucket_371f, systematicWeightSixteen_bucket_371f_complete
  | 14121, normalizedWeightSixteenCandidateBucket_3729, systematicWeightSixteen_bucket_3729_complete
  | 14122, normalizedWeightSixteenCandidateBucket_372a, systematicWeightSixteen_bucket_372a_complete
  | 14124, normalizedWeightSixteenCandidateBucket_372c, systematicWeightSixteen_bucket_372c_complete
  | 14127, normalizedWeightSixteenCandidateBucket_372f, systematicWeightSixteen_bucket_372f_complete
  | 14343, normalizedWeightSixteenCandidateBucket_3807, systematicWeightSixteen_bucket_3807_complete
  | 14361, normalizedWeightSixteenCandidateBucket_3819, systematicWeightSixteen_bucket_3819_complete
  | 14362, normalizedWeightSixteenCandidateBucket_381a, systematicWeightSixteen_bucket_381a_complete
  | 14364, normalizedWeightSixteenCandidateBucket_381c, systematicWeightSixteen_bucket_381c_complete
  | 14367, normalizedWeightSixteenCandidateBucket_381f, systematicWeightSixteen_bucket_381f_complete
  | 14377, normalizedWeightSixteenCandidateBucket_3829, systematicWeightSixteen_bucket_3829_complete
  | 14378, normalizedWeightSixteenCandidateBucket_382a, systematicWeightSixteen_bucket_382a_complete
  | 14380, normalizedWeightSixteenCandidateBucket_382c, systematicWeightSixteen_bucket_382c_complete
  | 14383, normalizedWeightSixteenCandidateBucket_382f, systematicWeightSixteen_bucket_382f_complete
  | 14385, normalizedWeightSixteenCandidateBucket_3831, systematicWeightSixteen_bucket_3831_complete
  | 14386, normalizedWeightSixteenCandidateBucket_3832, systematicWeightSixteen_bucket_3832_complete
  | 14388, normalizedWeightSixteenCandidateBucket_3834, systematicWeightSixteen_bucket_3834_complete
  | 14391, normalizedWeightSixteenCandidateBucket_3837, systematicWeightSixteen_bucket_3837_complete
  | 15111, normalizedWeightSixteenCandidateBucket_3b07, systematicWeightSixteen_bucket_3b07_complete
  | 15117, normalizedWeightSixteenCandidateBucket_3b0d, systematicWeightSixteen_bucket_3b0d_complete
  | 15118, normalizedWeightSixteenCandidateBucket_3b0e, systematicWeightSixteen_bucket_3b0e_complete
  | 15125, normalizedWeightSixteenCandidateBucket_3b15, systematicWeightSixteen_bucket_3b15_complete
  | 15126, normalizedWeightSixteenCandidateBucket_3b16, systematicWeightSixteen_bucket_3b16_complete
  | 15132, normalizedWeightSixteenCandidateBucket_3b1c, systematicWeightSixteen_bucket_3b1c_complete
  | 15135, normalizedWeightSixteenCandidateBucket_3b1f, systematicWeightSixteen_bucket_3b1f_complete
  | 15141, normalizedWeightSixteenCandidateBucket_3b25, systematicWeightSixteen_bucket_3b25_complete
  | 15142, normalizedWeightSixteenCandidateBucket_3b26, systematicWeightSixteen_bucket_3b26_complete
  | 15148, normalizedWeightSixteenCandidateBucket_3b2c, systematicWeightSixteen_bucket_3b2c_complete
  | 15151, normalizedWeightSixteenCandidateBucket_3b2f, systematicWeightSixteen_bucket_3b2f_complete
  | 15156, normalizedWeightSixteenCandidateBucket_3b34, systematicWeightSixteen_bucket_3b34_complete
  | 15159, normalizedWeightSixteenCandidateBucket_3b37, systematicWeightSixteen_bucket_3b37_complete
  | 15623, normalizedWeightSixteenCandidateBucket_3d07, systematicWeightSixteen_bucket_3d07_complete
  | 15627, normalizedWeightSixteenCandidateBucket_3d0b, systematicWeightSixteen_bucket_3d0b_complete
  | 15630, normalizedWeightSixteenCandidateBucket_3d0e, systematicWeightSixteen_bucket_3d0e_complete
  | 15635, normalizedWeightSixteenCandidateBucket_3d13, systematicWeightSixteen_bucket_3d13_complete
  | 15638, normalizedWeightSixteenCandidateBucket_3d16, systematicWeightSixteen_bucket_3d16_complete
  | 15642, normalizedWeightSixteenCandidateBucket_3d1a, systematicWeightSixteen_bucket_3d1a_complete
  | 15647, normalizedWeightSixteenCandidateBucket_3d1f, systematicWeightSixteen_bucket_3d1f_complete
  | 15651, normalizedWeightSixteenCandidateBucket_3d23, systematicWeightSixteen_bucket_3d23_complete
  | 15654, normalizedWeightSixteenCandidateBucket_3d26, systematicWeightSixteen_bucket_3d26_complete
  | 15658, normalizedWeightSixteenCandidateBucket_3d2a, systematicWeightSixteen_bucket_3d2a_complete
  | 15663, normalizedWeightSixteenCandidateBucket_3d2f, systematicWeightSixteen_bucket_3d2f_complete
  | 15666, normalizedWeightSixteenCandidateBucket_3d32, systematicWeightSixteen_bucket_3d32_complete
  | 15671, normalizedWeightSixteenCandidateBucket_3d37, systematicWeightSixteen_bucket_3d37_complete
  | 15675, normalizedWeightSixteenCandidateBucket_3d3b, systematicWeightSixteen_bucket_3d3b_complete
  | 15879, normalizedWeightSixteenCandidateBucket_3e07, systematicWeightSixteen_bucket_3e07_complete
  | 15883, normalizedWeightSixteenCandidateBucket_3e0b, systematicWeightSixteen_bucket_3e0b_complete
  | 15885, normalizedWeightSixteenCandidateBucket_3e0d, systematicWeightSixteen_bucket_3e0d_complete
  | 15891, normalizedWeightSixteenCandidateBucket_3e13, systematicWeightSixteen_bucket_3e13_complete
  | 15893, normalizedWeightSixteenCandidateBucket_3e15, systematicWeightSixteen_bucket_3e15_complete
  | 15897, normalizedWeightSixteenCandidateBucket_3e19, systematicWeightSixteen_bucket_3e19_complete
  | 15903, normalizedWeightSixteenCandidateBucket_3e1f, systematicWeightSixteen_bucket_3e1f_complete
  | 15907, normalizedWeightSixteenCandidateBucket_3e23, systematicWeightSixteen_bucket_3e23_complete
  | 15909, normalizedWeightSixteenCandidateBucket_3e25, systematicWeightSixteen_bucket_3e25_complete
  | 15913, normalizedWeightSixteenCandidateBucket_3e29, systematicWeightSixteen_bucket_3e29_complete
  | 15919, normalizedWeightSixteenCandidateBucket_3e2f, systematicWeightSixteen_bucket_3e2f_complete
  | 15921, normalizedWeightSixteenCandidateBucket_3e31, systematicWeightSixteen_bucket_3e31_complete
  | 15927, normalizedWeightSixteenCandidateBucket_3e37, systematicWeightSixteen_bucket_3e37_complete
  | 15931, normalizedWeightSixteenCandidateBucket_3e3b, systematicWeightSixteen_bucket_3e3b_complete
  | 15933, normalizedWeightSixteenCandidateBucket_3e3d, systematicWeightSixteen_bucket_3e3d_complete
  | 17731, normalizedWeightSixteenCandidateBucket_4543, systematicWeightSixteen_bucket_4543_complete
  | 17987, normalizedWeightSixteenCandidateBucket_4643, systematicWeightSixteen_bucket_4643_complete
  | 17989, normalizedWeightSixteenCandidateBucket_4645, systematicWeightSixteen_bucket_4645_complete
  | 18755, normalizedWeightSixteenCandidateBucket_4943, systematicWeightSixteen_bucket_4943_complete
  | 18757, normalizedWeightSixteenCandidateBucket_4945, systematicWeightSixteen_bucket_4945_complete
  | 19011, normalizedWeightSixteenCandidateBucket_4a43, systematicWeightSixteen_bucket_4a43_complete
  | 19014, normalizedWeightSixteenCandidateBucket_4a46, systematicWeightSixteen_bucket_4a46_complete
  | 19017, normalizedWeightSixteenCandidateBucket_4a49, systematicWeightSixteen_bucket_4a49_complete
  | 19525, normalizedWeightSixteenCandidateBucket_4c45, systematicWeightSixteen_bucket_4c45_complete
  | 19526, normalizedWeightSixteenCandidateBucket_4c46, systematicWeightSixteen_bucket_4c46_complete
  | 19529, normalizedWeightSixteenCandidateBucket_4c49, systematicWeightSixteen_bucket_4c49_complete
  | 19530, normalizedWeightSixteenCandidateBucket_4c4a, systematicWeightSixteen_bucket_4c4a_complete
  | 20803, normalizedWeightSixteenCandidateBucket_5143, systematicWeightSixteen_bucket_5143_complete
  | 20805, normalizedWeightSixteenCandidateBucket_5145, systematicWeightSixteen_bucket_5145_complete
  | 20809, normalizedWeightSixteenCandidateBucket_5149, systematicWeightSixteen_bucket_5149_complete
  | 20815, normalizedWeightSixteenCandidateBucket_514f, systematicWeightSixteen_bucket_514f_complete
  | 21059, normalizedWeightSixteenCandidateBucket_5243, systematicWeightSixteen_bucket_5243_complete
  | 21062, normalizedWeightSixteenCandidateBucket_5246, systematicWeightSixteen_bucket_5246_complete
  | 21066, normalizedWeightSixteenCandidateBucket_524a, systematicWeightSixteen_bucket_524a_complete
  | 21071, normalizedWeightSixteenCandidateBucket_524f, systematicWeightSixteen_bucket_524f_complete
  | 21073, normalizedWeightSixteenCandidateBucket_5251, systematicWeightSixteen_bucket_5251_complete
  | 21573, normalizedWeightSixteenCandidateBucket_5445, systematicWeightSixteen_bucket_5445_complete
  | 21574, normalizedWeightSixteenCandidateBucket_5446, systematicWeightSixteen_bucket_5446_complete
  | 21580, normalizedWeightSixteenCandidateBucket_544c, systematicWeightSixteen_bucket_544c_complete
  | 21583, normalizedWeightSixteenCandidateBucket_544f, systematicWeightSixteen_bucket_544f_complete
  | 21585, normalizedWeightSixteenCandidateBucket_5451, systematicWeightSixteen_bucket_5451_complete
  | 21586, normalizedWeightSixteenCandidateBucket_5452, systematicWeightSixteen_bucket_5452_complete
  | 22345, normalizedWeightSixteenCandidateBucket_5749, systematicWeightSixteen_bucket_5749_complete
  | 22346, normalizedWeightSixteenCandidateBucket_574a, systematicWeightSixteen_bucket_574a_complete
  | 22348, normalizedWeightSixteenCandidateBucket_574c, systematicWeightSixteen_bucket_574c_complete
  | 22351, normalizedWeightSixteenCandidateBucket_574f, systematicWeightSixteen_bucket_574f_complete
  | 22601, normalizedWeightSixteenCandidateBucket_5849, systematicWeightSixteen_bucket_5849_complete
  | 22602, normalizedWeightSixteenCandidateBucket_584a, systematicWeightSixteen_bucket_584a_complete
  | 22604, normalizedWeightSixteenCandidateBucket_584c, systematicWeightSixteen_bucket_584c_complete
  | 22607, normalizedWeightSixteenCandidateBucket_584f, systematicWeightSixteen_bucket_584f_complete
  | 22609, normalizedWeightSixteenCandidateBucket_5851, systematicWeightSixteen_bucket_5851_complete
  | 22610, normalizedWeightSixteenCandidateBucket_5852, systematicWeightSixteen_bucket_5852_complete
  | 22612, normalizedWeightSixteenCandidateBucket_5854, systematicWeightSixteen_bucket_5854_complete
  | 22615, normalizedWeightSixteenCandidateBucket_5857, systematicWeightSixteen_bucket_5857_complete
  | 23365, normalizedWeightSixteenCandidateBucket_5b45, systematicWeightSixteen_bucket_5b45_complete
  | 23366, normalizedWeightSixteenCandidateBucket_5b46, systematicWeightSixteen_bucket_5b46_complete
  | 23372, normalizedWeightSixteenCandidateBucket_5b4c, systematicWeightSixteen_bucket_5b4c_complete
  | 23375, normalizedWeightSixteenCandidateBucket_5b4f, systematicWeightSixteen_bucket_5b4f_complete
  | 23380, normalizedWeightSixteenCandidateBucket_5b54, systematicWeightSixteen_bucket_5b54_complete
  | 23383, normalizedWeightSixteenCandidateBucket_5b57, systematicWeightSixteen_bucket_5b57_complete
  | 23875, normalizedWeightSixteenCandidateBucket_5d43, systematicWeightSixteen_bucket_5d43_complete
  | 23878, normalizedWeightSixteenCandidateBucket_5d46, systematicWeightSixteen_bucket_5d46_complete
  | 23882, normalizedWeightSixteenCandidateBucket_5d4a, systematicWeightSixteen_bucket_5d4a_complete
  | 23887, normalizedWeightSixteenCandidateBucket_5d4f, systematicWeightSixteen_bucket_5d4f_complete
  | 23890, normalizedWeightSixteenCandidateBucket_5d52, systematicWeightSixteen_bucket_5d52_complete
  | 23895, normalizedWeightSixteenCandidateBucket_5d57, systematicWeightSixteen_bucket_5d57_complete
  | 23899, normalizedWeightSixteenCandidateBucket_5d5b, systematicWeightSixteen_bucket_5d5b_complete
  | 24131, normalizedWeightSixteenCandidateBucket_5e43, systematicWeightSixteen_bucket_5e43_complete
  | 24133, normalizedWeightSixteenCandidateBucket_5e45, systematicWeightSixteen_bucket_5e45_complete
  | 24137, normalizedWeightSixteenCandidateBucket_5e49, systematicWeightSixteen_bucket_5e49_complete
  | 24143, normalizedWeightSixteenCandidateBucket_5e4f, systematicWeightSixteen_bucket_5e4f_complete
  | 24145, normalizedWeightSixteenCandidateBucket_5e51, systematicWeightSixteen_bucket_5e51_complete
  | 24151, normalizedWeightSixteenCandidateBucket_5e57, systematicWeightSixteen_bucket_5e57_complete
  | 24155, normalizedWeightSixteenCandidateBucket_5e5b, systematicWeightSixteen_bucket_5e5b_complete
  | 24157, normalizedWeightSixteenCandidateBucket_5e5d, systematicWeightSixteen_bucket_5e5d_complete
  | 25185, normalizedWeightSixteenCandidateBucket_6261, systematicWeightSixteen_bucket_6261_complete
  | 25697, normalizedWeightSixteenCandidateBucket_6461, systematicWeightSixteen_bucket_6461_complete
  | 25698, normalizedWeightSixteenCandidateBucket_6462, systematicWeightSixteen_bucket_6462_complete
  | 26721, normalizedWeightSixteenCandidateBucket_6861, systematicWeightSixteen_bucket_6861_complete
  | 26722, normalizedWeightSixteenCandidateBucket_6862, systematicWeightSixteen_bucket_6862_complete
  | 26724, normalizedWeightSixteenCandidateBucket_6864, systematicWeightSixteen_bucket_6864_complete
  | 26727, normalizedWeightSixteenCandidateBucket_6867, systematicWeightSixteen_bucket_6867_complete
  | 27492, normalizedWeightSixteenCandidateBucket_6b64, systematicWeightSixteen_bucket_6b64_complete
  | 27495, normalizedWeightSixteenCandidateBucket_6b67, systematicWeightSixteen_bucket_6b67_complete
  | 28002, normalizedWeightSixteenCandidateBucket_6d62, systematicWeightSixteen_bucket_6d62_complete
  | 28007, normalizedWeightSixteenCandidateBucket_6d67, systematicWeightSixteen_bucket_6d67_complete
  | 28011, normalizedWeightSixteenCandidateBucket_6d6b, systematicWeightSixteen_bucket_6d6b_complete
  | 28257, normalizedWeightSixteenCandidateBucket_6e61, systematicWeightSixteen_bucket_6e61_complete
  | 28263, normalizedWeightSixteenCandidateBucket_6e67, systematicWeightSixteen_bucket_6e67_complete
  | 28267, normalizedWeightSixteenCandidateBucket_6e6b, systematicWeightSixteen_bucket_6e6b_complete
  | 28269, normalizedWeightSixteenCandidateBucket_6e6d, systematicWeightSixteen_bucket_6e6d_complete
  | 30067, normalizedWeightSixteenCandidateBucket_7573, systematicWeightSixteen_bucket_7573_complete
  | 30323, normalizedWeightSixteenCandidateBucket_7673, systematicWeightSixteen_bucket_7673_complete
  | 30325, normalizedWeightSixteenCandidateBucket_7675, systematicWeightSixteen_bucket_7675_complete
  | 31353, normalizedWeightSixteenCandidateBucket_7a79, systematicWeightSixteen_bucket_7a79_complete
  | 33663, normalizedWeightSixteenCandidateBucket_837f, systematicWeightSixteen_bucket_837f_complete
  | 34175, normalizedWeightSixteenCandidateBucket_857f, systematicWeightSixteen_bucket_857f_complete
  | 34431, normalizedWeightSixteenCandidateBucket_867f, systematicWeightSixteen_bucket_867f_complete
  | 35199, normalizedWeightSixteenCandidateBucket_897f, systematicWeightSixteen_bucket_897f_complete
  | 35455, normalizedWeightSixteenCandidateBucket_8a7f, systematicWeightSixteen_bucket_8a7f_complete
  | 35967, normalizedWeightSixteenCandidateBucket_8c7f, systematicWeightSixteen_bucket_8c7f_complete
  | 36735, normalizedWeightSixteenCandidateBucket_8f7f, systematicWeightSixteen_bucket_8f7f_complete
  | 37247, normalizedWeightSixteenCandidateBucket_917f, systematicWeightSixteen_bucket_917f_complete
  | 37503, normalizedWeightSixteenCandidateBucket_927f, systematicWeightSixteen_bucket_927f_complete
  | 38015, normalizedWeightSixteenCandidateBucket_947f, systematicWeightSixteen_bucket_947f_complete
  | 38783, normalizedWeightSixteenCandidateBucket_977f, systematicWeightSixteen_bucket_977f_complete
  | 39807, normalizedWeightSixteenCandidateBucket_9b7f, systematicWeightSixteen_bucket_9b7f_complete
  | 40319, normalizedWeightSixteenCandidateBucket_9d7f, systematicWeightSixteen_bucket_9d7f_complete
  | 41343, normalizedWeightSixteenCandidateBucket_a17f, systematicWeightSixteen_bucket_a17f_complete
  | 41599, normalizedWeightSixteenCandidateBucket_a27f, systematicWeightSixteen_bucket_a27f_complete
  | 42111, normalizedWeightSixteenCandidateBucket_a47f, systematicWeightSixteen_bucket_a47f_complete
  | 42879, normalizedWeightSixteenCandidateBucket_a77f, systematicWeightSixteen_bucket_a77f_complete
  | 43903, normalizedWeightSixteenCandidateBucket_ab7f, systematicWeightSixteen_bucket_ab7f_complete
  | 44415, normalizedWeightSixteenCandidateBucket_ad7f, systematicWeightSixteen_bucket_ad7f_complete
  | 45951, normalizedWeightSixteenCandidateBucket_b37f, systematicWeightSixteen_bucket_b37f_complete
  | 46463, normalizedWeightSixteenCandidateBucket_b57f, systematicWeightSixteen_bucket_b57f_complete
  | 47487, normalizedWeightSixteenCandidateBucket_b97f, systematicWeightSixteen_bucket_b97f_complete
  | 49023, normalizedWeightSixteenCandidateBucket_bf7f, systematicWeightSixteen_bucket_bf7f_complete

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
