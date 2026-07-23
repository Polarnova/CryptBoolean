/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import CryptBoolean.Carlet.Chapter04.HigherOrderOrderTwoWeightSixteen.CandidateSoundness

/-!
# Compact soundness certificates for normalized weight-sixteen candidates

Each table row names one generated candidate bucket and its independent
kernel-checked compact-mask certificate. The table command emits ordinary
top-level theorem commands before assembling their source-facing soundness
theorem.
-/

@[expose] public section

namespace CryptBoolean

syntax normalizedWeightSixteenCertificateRow :=
  "|" term "," ident "," ident

local syntax (name := normalizedWeightSixteenCertificatesCommand)
  "normalized_weight_sixteen_certificates" ident "where"
    normalizedWeightSixteenCertificateRow* : command

local macro_rules
  | `(command| normalized_weight_sixteen_certificates
      $soundnessName:ident where
      $[$rows:normalizedWeightSixteenCertificateRow]*) => do
    let generated ← rows.mapM fun row => do
      let `(normalizedWeightSixteenCertificateRow|
        | $bucketPrefix:term, $tree:ident, $proofName:ident) := row
        | Lean.Macro.throwUnsupported
      let declaration ←
        `(command| compact_mask_soundness $proofName for $tree)
      let branch ← `(tactic|
        (
          have hprefix :
              code.extractLsb' 0 16 =
                BitVec.ofNat 16 $bucketPrefix := by
            simpa only [beq_iff_eq] using hprefixes
          unfold normalizedWeightSixteenCandidateBucket at hbucket
          rw [hprefix] at hbucket
          cases hbucket
          exact ⟨candidate, hcode,
            NormalizedWeightSixteenCandidateTree.All.of_member
              $proofName hmember⟩
        ))
      pure (declaration, branch)
    let declarations := generated.map Prod.fst
    let branches := generated.map Prod.snd
    let focusedBranches ← branches.mapM fun branch =>
      `(tactic| focus $branch:tactic)
    let soundness ← `(command|
      set_option Elab.async true in
      set_option linter.style.maxHeartbeats false in
      set_option maxHeartbeats 20000000 in
      /-- Every systematic orthonormal-column code has a generated candidate
      with a valid compact mask certificate. -/
      theorem $soundnessName :
          HasNormalizedWeightSixteenCompactCandidateSoundness := by
        intro code hconstraints
        obtain ⟨tree, candidate, hbucket, hmember, hcode⟩ :=
          exists_normalizedWeightSixteenCandidate_of_constraints
            code hconstraints
        have hprefixes :=
          systematicWeightSixteen_prefix_allowed code hconstraints
        unfold IsSystematicWeightSixteenPrefixAllowed at hprefixes
        simp only [Bool.or_eq_true] at hprefixes
        repeat' (apply Or.elim hprefixes <;> intro hprefixes)
        $focusedBranches:tactic*)
    return Lean.mkNullNode <|
      declarations.map (·.raw) ++
        #[soundness.raw]

normalized_weight_sixteen_certificates
  normalizedWeightSixteenCompactCandidateSoundness where
  | 2823, normalizedWeightSixteenCandidateBucket_0b07, normalizedWeightSixteenCandidateBucket_0b07_compact
  | 3335, normalizedWeightSixteenCandidateBucket_0d07, normalizedWeightSixteenCandidateBucket_0d07_compact
  | 3339, normalizedWeightSixteenCandidateBucket_0d0b, normalizedWeightSixteenCandidateBucket_0d0b_compact
  | 3591, normalizedWeightSixteenCandidateBucket_0e07, normalizedWeightSixteenCandidateBucket_0e07_compact
  | 3595, normalizedWeightSixteenCandidateBucket_0e0b, normalizedWeightSixteenCandidateBucket_0e0b_compact
  | 3597, normalizedWeightSixteenCandidateBucket_0e0d, normalizedWeightSixteenCandidateBucket_0e0d_compact
  | 4871, normalizedWeightSixteenCandidateBucket_1307, normalizedWeightSixteenCandidateBucket_1307_compact
  | 4875, normalizedWeightSixteenCandidateBucket_130b, normalizedWeightSixteenCandidateBucket_130b_compact
  | 5383, normalizedWeightSixteenCandidateBucket_1507, normalizedWeightSixteenCandidateBucket_1507_compact
  | 5389, normalizedWeightSixteenCandidateBucket_150d, normalizedWeightSixteenCandidateBucket_150d_compact
  | 5395, normalizedWeightSixteenCandidateBucket_1513, normalizedWeightSixteenCandidateBucket_1513_compact
  | 5639, normalizedWeightSixteenCandidateBucket_1607, normalizedWeightSixteenCandidateBucket_1607_compact
  | 5646, normalizedWeightSixteenCandidateBucket_160e, normalizedWeightSixteenCandidateBucket_160e_compact
  | 5651, normalizedWeightSixteenCandidateBucket_1613, normalizedWeightSixteenCandidateBucket_1613_compact
  | 5653, normalizedWeightSixteenCandidateBucket_1615, normalizedWeightSixteenCandidateBucket_1615_compact
  | 6411, normalizedWeightSixteenCandidateBucket_190b, normalizedWeightSixteenCandidateBucket_190b_compact
  | 6413, normalizedWeightSixteenCandidateBucket_190d, normalizedWeightSixteenCandidateBucket_190d_compact
  | 6419, normalizedWeightSixteenCandidateBucket_1913, normalizedWeightSixteenCandidateBucket_1913_compact
  | 6421, normalizedWeightSixteenCandidateBucket_1915, normalizedWeightSixteenCandidateBucket_1915_compact
  | 6667, normalizedWeightSixteenCandidateBucket_1a0b, normalizedWeightSixteenCandidateBucket_1a0b_compact
  | 6670, normalizedWeightSixteenCandidateBucket_1a0e, normalizedWeightSixteenCandidateBucket_1a0e_compact
  | 6675, normalizedWeightSixteenCandidateBucket_1a13, normalizedWeightSixteenCandidateBucket_1a13_compact
  | 6678, normalizedWeightSixteenCandidateBucket_1a16, normalizedWeightSixteenCandidateBucket_1a16_compact
  | 6681, normalizedWeightSixteenCandidateBucket_1a19, normalizedWeightSixteenCandidateBucket_1a19_compact
  | 7181, normalizedWeightSixteenCandidateBucket_1c0d, normalizedWeightSixteenCandidateBucket_1c0d_compact
  | 7182, normalizedWeightSixteenCandidateBucket_1c0e, normalizedWeightSixteenCandidateBucket_1c0e_compact
  | 7189, normalizedWeightSixteenCandidateBucket_1c15, normalizedWeightSixteenCandidateBucket_1c15_compact
  | 7190, normalizedWeightSixteenCandidateBucket_1c16, normalizedWeightSixteenCandidateBucket_1c16_compact
  | 7193, normalizedWeightSixteenCandidateBucket_1c19, normalizedWeightSixteenCandidateBucket_1c19_compact
  | 7194, normalizedWeightSixteenCandidateBucket_1c1a, normalizedWeightSixteenCandidateBucket_1c1a_compact
  | 8967, normalizedWeightSixteenCandidateBucket_2307, normalizedWeightSixteenCandidateBucket_2307_compact
  | 8971, normalizedWeightSixteenCandidateBucket_230b, normalizedWeightSixteenCandidateBucket_230b_compact
  | 8979, normalizedWeightSixteenCandidateBucket_2313, normalizedWeightSixteenCandidateBucket_2313_compact
  | 8988, normalizedWeightSixteenCandidateBucket_231c, normalizedWeightSixteenCandidateBucket_231c_compact
  | 8991, normalizedWeightSixteenCandidateBucket_231f, normalizedWeightSixteenCandidateBucket_231f_compact
  | 9479, normalizedWeightSixteenCandidateBucket_2507, normalizedWeightSixteenCandidateBucket_2507_compact
  | 9485, normalizedWeightSixteenCandidateBucket_250d, normalizedWeightSixteenCandidateBucket_250d_compact
  | 9493, normalizedWeightSixteenCandidateBucket_2515, normalizedWeightSixteenCandidateBucket_2515_compact
  | 9498, normalizedWeightSixteenCandidateBucket_251a, normalizedWeightSixteenCandidateBucket_251a_compact
  | 9503, normalizedWeightSixteenCandidateBucket_251f, normalizedWeightSixteenCandidateBucket_251f_compact
  | 9507, normalizedWeightSixteenCandidateBucket_2523, normalizedWeightSixteenCandidateBucket_2523_compact
  | 9735, normalizedWeightSixteenCandidateBucket_2607, normalizedWeightSixteenCandidateBucket_2607_compact
  | 9742, normalizedWeightSixteenCandidateBucket_260e, normalizedWeightSixteenCandidateBucket_260e_compact
  | 9750, normalizedWeightSixteenCandidateBucket_2616, normalizedWeightSixteenCandidateBucket_2616_compact
  | 9753, normalizedWeightSixteenCandidateBucket_2619, normalizedWeightSixteenCandidateBucket_2619_compact
  | 9759, normalizedWeightSixteenCandidateBucket_261f, normalizedWeightSixteenCandidateBucket_261f_compact
  | 9763, normalizedWeightSixteenCandidateBucket_2623, normalizedWeightSixteenCandidateBucket_2623_compact
  | 9765, normalizedWeightSixteenCandidateBucket_2625, normalizedWeightSixteenCandidateBucket_2625_compact
  | 10507, normalizedWeightSixteenCandidateBucket_290b, normalizedWeightSixteenCandidateBucket_290b_compact
  | 10509, normalizedWeightSixteenCandidateBucket_290d, normalizedWeightSixteenCandidateBucket_290d_compact
  | 10518, normalizedWeightSixteenCandidateBucket_2916, normalizedWeightSixteenCandidateBucket_2916_compact
  | 10521, normalizedWeightSixteenCandidateBucket_2919, normalizedWeightSixteenCandidateBucket_2919_compact
  | 10527, normalizedWeightSixteenCandidateBucket_291f, normalizedWeightSixteenCandidateBucket_291f_compact
  | 10531, normalizedWeightSixteenCandidateBucket_2923, normalizedWeightSixteenCandidateBucket_2923_compact
  | 10533, normalizedWeightSixteenCandidateBucket_2925, normalizedWeightSixteenCandidateBucket_2925_compact
  | 10763, normalizedWeightSixteenCandidateBucket_2a0b, normalizedWeightSixteenCandidateBucket_2a0b_compact
  | 10766, normalizedWeightSixteenCandidateBucket_2a0e, normalizedWeightSixteenCandidateBucket_2a0e_compact
  | 10773, normalizedWeightSixteenCandidateBucket_2a15, normalizedWeightSixteenCandidateBucket_2a15_compact
  | 10778, normalizedWeightSixteenCandidateBucket_2a1a, normalizedWeightSixteenCandidateBucket_2a1a_compact
  | 10783, normalizedWeightSixteenCandidateBucket_2a1f, normalizedWeightSixteenCandidateBucket_2a1f_compact
  | 10787, normalizedWeightSixteenCandidateBucket_2a23, normalizedWeightSixteenCandidateBucket_2a23_compact
  | 10790, normalizedWeightSixteenCandidateBucket_2a26, normalizedWeightSixteenCandidateBucket_2a26_compact
  | 10793, normalizedWeightSixteenCandidateBucket_2a29, normalizedWeightSixteenCandidateBucket_2a29_compact
  | 11277, normalizedWeightSixteenCandidateBucket_2c0d, normalizedWeightSixteenCandidateBucket_2c0d_compact
  | 11278, normalizedWeightSixteenCandidateBucket_2c0e, normalizedWeightSixteenCandidateBucket_2c0e_compact
  | 11283, normalizedWeightSixteenCandidateBucket_2c13, normalizedWeightSixteenCandidateBucket_2c13_compact
  | 11292, normalizedWeightSixteenCandidateBucket_2c1c, normalizedWeightSixteenCandidateBucket_2c1c_compact
  | 11295, normalizedWeightSixteenCandidateBucket_2c1f, normalizedWeightSixteenCandidateBucket_2c1f_compact
  | 11301, normalizedWeightSixteenCandidateBucket_2c25, normalizedWeightSixteenCandidateBucket_2c25_compact
  | 11302, normalizedWeightSixteenCandidateBucket_2c26, normalizedWeightSixteenCandidateBucket_2c26_compact
  | 11305, normalizedWeightSixteenCandidateBucket_2c29, normalizedWeightSixteenCandidateBucket_2c29_compact
  | 11306, normalizedWeightSixteenCandidateBucket_2c2a, normalizedWeightSixteenCandidateBucket_2c2a_compact
  | 12051, normalizedWeightSixteenCandidateBucket_2f13, normalizedWeightSixteenCandidateBucket_2f13_compact
  | 12053, normalizedWeightSixteenCandidateBucket_2f15, normalizedWeightSixteenCandidateBucket_2f15_compact
  | 12054, normalizedWeightSixteenCandidateBucket_2f16, normalizedWeightSixteenCandidateBucket_2f16_compact
  | 12057, normalizedWeightSixteenCandidateBucket_2f19, normalizedWeightSixteenCandidateBucket_2f19_compact
  | 12058, normalizedWeightSixteenCandidateBucket_2f1a, normalizedWeightSixteenCandidateBucket_2f1a_compact
  | 12060, normalizedWeightSixteenCandidateBucket_2f1c, normalizedWeightSixteenCandidateBucket_2f1c_compact
  | 12063, normalizedWeightSixteenCandidateBucket_2f1f, normalizedWeightSixteenCandidateBucket_2f1f_compact
  | 12558, normalizedWeightSixteenCandidateBucket_310e, normalizedWeightSixteenCandidateBucket_310e_compact
  | 12563, normalizedWeightSixteenCandidateBucket_3113, normalizedWeightSixteenCandidateBucket_3113_compact
  | 12565, normalizedWeightSixteenCandidateBucket_3115, normalizedWeightSixteenCandidateBucket_3115_compact
  | 12569, normalizedWeightSixteenCandidateBucket_3119, normalizedWeightSixteenCandidateBucket_3119_compact
  | 12575, normalizedWeightSixteenCandidateBucket_311f, normalizedWeightSixteenCandidateBucket_311f_compact
  | 12579, normalizedWeightSixteenCandidateBucket_3123, normalizedWeightSixteenCandidateBucket_3123_compact
  | 12581, normalizedWeightSixteenCandidateBucket_3125, normalizedWeightSixteenCandidateBucket_3125_compact
  | 12585, normalizedWeightSixteenCandidateBucket_3129, normalizedWeightSixteenCandidateBucket_3129_compact
  | 12591, normalizedWeightSixteenCandidateBucket_312f, normalizedWeightSixteenCandidateBucket_312f_compact
  | 12813, normalizedWeightSixteenCandidateBucket_320d, normalizedWeightSixteenCandidateBucket_320d_compact
  | 12819, normalizedWeightSixteenCandidateBucket_3213, normalizedWeightSixteenCandidateBucket_3213_compact
  | 12822, normalizedWeightSixteenCandidateBucket_3216, normalizedWeightSixteenCandidateBucket_3216_compact
  | 12826, normalizedWeightSixteenCandidateBucket_321a, normalizedWeightSixteenCandidateBucket_321a_compact
  | 12831, normalizedWeightSixteenCandidateBucket_321f, normalizedWeightSixteenCandidateBucket_321f_compact
  | 12835, normalizedWeightSixteenCandidateBucket_3223, normalizedWeightSixteenCandidateBucket_3223_compact
  | 12838, normalizedWeightSixteenCandidateBucket_3226, normalizedWeightSixteenCandidateBucket_3226_compact
  | 12842, normalizedWeightSixteenCandidateBucket_322a, normalizedWeightSixteenCandidateBucket_322a_compact
  | 12847, normalizedWeightSixteenCandidateBucket_322f, normalizedWeightSixteenCandidateBucket_322f_compact
  | 12849, normalizedWeightSixteenCandidateBucket_3231, normalizedWeightSixteenCandidateBucket_3231_compact
  | 13323, normalizedWeightSixteenCandidateBucket_340b, normalizedWeightSixteenCandidateBucket_340b_compact
  | 13333, normalizedWeightSixteenCandidateBucket_3415, normalizedWeightSixteenCandidateBucket_3415_compact
  | 13334, normalizedWeightSixteenCandidateBucket_3416, normalizedWeightSixteenCandidateBucket_3416_compact
  | 13340, normalizedWeightSixteenCandidateBucket_341c, normalizedWeightSixteenCandidateBucket_341c_compact
  | 13343, normalizedWeightSixteenCandidateBucket_341f, normalizedWeightSixteenCandidateBucket_341f_compact
  | 13349, normalizedWeightSixteenCandidateBucket_3425, normalizedWeightSixteenCandidateBucket_3425_compact
  | 13350, normalizedWeightSixteenCandidateBucket_3426, normalizedWeightSixteenCandidateBucket_3426_compact
  | 13356, normalizedWeightSixteenCandidateBucket_342c, normalizedWeightSixteenCandidateBucket_342c_compact
  | 13359, normalizedWeightSixteenCandidateBucket_342f, normalizedWeightSixteenCandidateBucket_342f_compact
  | 13361, normalizedWeightSixteenCandidateBucket_3431, normalizedWeightSixteenCandidateBucket_3431_compact
  | 13362, normalizedWeightSixteenCandidateBucket_3432, normalizedWeightSixteenCandidateBucket_3432_compact
  | 14091, normalizedWeightSixteenCandidateBucket_370b, normalizedWeightSixteenCandidateBucket_370b_compact
  | 14093, normalizedWeightSixteenCandidateBucket_370d, normalizedWeightSixteenCandidateBucket_370d_compact
  | 14094, normalizedWeightSixteenCandidateBucket_370e, normalizedWeightSixteenCandidateBucket_370e_compact
  | 14105, normalizedWeightSixteenCandidateBucket_3719, normalizedWeightSixteenCandidateBucket_3719_compact
  | 14106, normalizedWeightSixteenCandidateBucket_371a, normalizedWeightSixteenCandidateBucket_371a_compact
  | 14108, normalizedWeightSixteenCandidateBucket_371c, normalizedWeightSixteenCandidateBucket_371c_compact
  | 14111, normalizedWeightSixteenCandidateBucket_371f, normalizedWeightSixteenCandidateBucket_371f_compact
  | 14121, normalizedWeightSixteenCandidateBucket_3729, normalizedWeightSixteenCandidateBucket_3729_compact
  | 14122, normalizedWeightSixteenCandidateBucket_372a, normalizedWeightSixteenCandidateBucket_372a_compact
  | 14124, normalizedWeightSixteenCandidateBucket_372c, normalizedWeightSixteenCandidateBucket_372c_compact
  | 14127, normalizedWeightSixteenCandidateBucket_372f, normalizedWeightSixteenCandidateBucket_372f_compact
  | 14343, normalizedWeightSixteenCandidateBucket_3807, normalizedWeightSixteenCandidateBucket_3807_compact
  | 14361, normalizedWeightSixteenCandidateBucket_3819, normalizedWeightSixteenCandidateBucket_3819_compact
  | 14362, normalizedWeightSixteenCandidateBucket_381a, normalizedWeightSixteenCandidateBucket_381a_compact
  | 14364, normalizedWeightSixteenCandidateBucket_381c, normalizedWeightSixteenCandidateBucket_381c_compact
  | 14367, normalizedWeightSixteenCandidateBucket_381f, normalizedWeightSixteenCandidateBucket_381f_compact
  | 14377, normalizedWeightSixteenCandidateBucket_3829, normalizedWeightSixteenCandidateBucket_3829_compact
  | 14378, normalizedWeightSixteenCandidateBucket_382a, normalizedWeightSixteenCandidateBucket_382a_compact
  | 14380, normalizedWeightSixteenCandidateBucket_382c, normalizedWeightSixteenCandidateBucket_382c_compact
  | 14383, normalizedWeightSixteenCandidateBucket_382f, normalizedWeightSixteenCandidateBucket_382f_compact
  | 14385, normalizedWeightSixteenCandidateBucket_3831, normalizedWeightSixteenCandidateBucket_3831_compact
  | 14386, normalizedWeightSixteenCandidateBucket_3832, normalizedWeightSixteenCandidateBucket_3832_compact
  | 14388, normalizedWeightSixteenCandidateBucket_3834, normalizedWeightSixteenCandidateBucket_3834_compact
  | 14391, normalizedWeightSixteenCandidateBucket_3837, normalizedWeightSixteenCandidateBucket_3837_compact
  | 15111, normalizedWeightSixteenCandidateBucket_3b07, normalizedWeightSixteenCandidateBucket_3b07_compact
  | 15117, normalizedWeightSixteenCandidateBucket_3b0d, normalizedWeightSixteenCandidateBucket_3b0d_compact
  | 15118, normalizedWeightSixteenCandidateBucket_3b0e, normalizedWeightSixteenCandidateBucket_3b0e_compact
  | 15125, normalizedWeightSixteenCandidateBucket_3b15, normalizedWeightSixteenCandidateBucket_3b15_compact
  | 15126, normalizedWeightSixteenCandidateBucket_3b16, normalizedWeightSixteenCandidateBucket_3b16_compact
  | 15132, normalizedWeightSixteenCandidateBucket_3b1c, normalizedWeightSixteenCandidateBucket_3b1c_compact
  | 15135, normalizedWeightSixteenCandidateBucket_3b1f, normalizedWeightSixteenCandidateBucket_3b1f_compact
  | 15141, normalizedWeightSixteenCandidateBucket_3b25, normalizedWeightSixteenCandidateBucket_3b25_compact
  | 15142, normalizedWeightSixteenCandidateBucket_3b26, normalizedWeightSixteenCandidateBucket_3b26_compact
  | 15148, normalizedWeightSixteenCandidateBucket_3b2c, normalizedWeightSixteenCandidateBucket_3b2c_compact
  | 15151, normalizedWeightSixteenCandidateBucket_3b2f, normalizedWeightSixteenCandidateBucket_3b2f_compact
  | 15156, normalizedWeightSixteenCandidateBucket_3b34, normalizedWeightSixteenCandidateBucket_3b34_compact
  | 15159, normalizedWeightSixteenCandidateBucket_3b37, normalizedWeightSixteenCandidateBucket_3b37_compact
  | 15623, normalizedWeightSixteenCandidateBucket_3d07, normalizedWeightSixteenCandidateBucket_3d07_compact
  | 15627, normalizedWeightSixteenCandidateBucket_3d0b, normalizedWeightSixteenCandidateBucket_3d0b_compact
  | 15630, normalizedWeightSixteenCandidateBucket_3d0e, normalizedWeightSixteenCandidateBucket_3d0e_compact
  | 15635, normalizedWeightSixteenCandidateBucket_3d13, normalizedWeightSixteenCandidateBucket_3d13_compact
  | 15638, normalizedWeightSixteenCandidateBucket_3d16, normalizedWeightSixteenCandidateBucket_3d16_compact
  | 15642, normalizedWeightSixteenCandidateBucket_3d1a, normalizedWeightSixteenCandidateBucket_3d1a_compact
  | 15647, normalizedWeightSixteenCandidateBucket_3d1f, normalizedWeightSixteenCandidateBucket_3d1f_compact
  | 15651, normalizedWeightSixteenCandidateBucket_3d23, normalizedWeightSixteenCandidateBucket_3d23_compact
  | 15654, normalizedWeightSixteenCandidateBucket_3d26, normalizedWeightSixteenCandidateBucket_3d26_compact
  | 15658, normalizedWeightSixteenCandidateBucket_3d2a, normalizedWeightSixteenCandidateBucket_3d2a_compact
  | 15663, normalizedWeightSixteenCandidateBucket_3d2f, normalizedWeightSixteenCandidateBucket_3d2f_compact
  | 15666, normalizedWeightSixteenCandidateBucket_3d32, normalizedWeightSixteenCandidateBucket_3d32_compact
  | 15671, normalizedWeightSixteenCandidateBucket_3d37, normalizedWeightSixteenCandidateBucket_3d37_compact
  | 15675, normalizedWeightSixteenCandidateBucket_3d3b, normalizedWeightSixteenCandidateBucket_3d3b_compact
  | 15879, normalizedWeightSixteenCandidateBucket_3e07, normalizedWeightSixteenCandidateBucket_3e07_compact
  | 15883, normalizedWeightSixteenCandidateBucket_3e0b, normalizedWeightSixteenCandidateBucket_3e0b_compact
  | 15885, normalizedWeightSixteenCandidateBucket_3e0d, normalizedWeightSixteenCandidateBucket_3e0d_compact
  | 15891, normalizedWeightSixteenCandidateBucket_3e13, normalizedWeightSixteenCandidateBucket_3e13_compact
  | 15893, normalizedWeightSixteenCandidateBucket_3e15, normalizedWeightSixteenCandidateBucket_3e15_compact
  | 15897, normalizedWeightSixteenCandidateBucket_3e19, normalizedWeightSixteenCandidateBucket_3e19_compact
  | 15903, normalizedWeightSixteenCandidateBucket_3e1f, normalizedWeightSixteenCandidateBucket_3e1f_compact
  | 15907, normalizedWeightSixteenCandidateBucket_3e23, normalizedWeightSixteenCandidateBucket_3e23_compact
  | 15909, normalizedWeightSixteenCandidateBucket_3e25, normalizedWeightSixteenCandidateBucket_3e25_compact
  | 15913, normalizedWeightSixteenCandidateBucket_3e29, normalizedWeightSixteenCandidateBucket_3e29_compact
  | 15919, normalizedWeightSixteenCandidateBucket_3e2f, normalizedWeightSixteenCandidateBucket_3e2f_compact
  | 15921, normalizedWeightSixteenCandidateBucket_3e31, normalizedWeightSixteenCandidateBucket_3e31_compact
  | 15927, normalizedWeightSixteenCandidateBucket_3e37, normalizedWeightSixteenCandidateBucket_3e37_compact
  | 15931, normalizedWeightSixteenCandidateBucket_3e3b, normalizedWeightSixteenCandidateBucket_3e3b_compact
  | 15933, normalizedWeightSixteenCandidateBucket_3e3d, normalizedWeightSixteenCandidateBucket_3e3d_compact
  | 17731, normalizedWeightSixteenCandidateBucket_4543, normalizedWeightSixteenCandidateBucket_4543_compact
  | 17987, normalizedWeightSixteenCandidateBucket_4643, normalizedWeightSixteenCandidateBucket_4643_compact
  | 17989, normalizedWeightSixteenCandidateBucket_4645, normalizedWeightSixteenCandidateBucket_4645_compact
  | 18755, normalizedWeightSixteenCandidateBucket_4943, normalizedWeightSixteenCandidateBucket_4943_compact
  | 18757, normalizedWeightSixteenCandidateBucket_4945, normalizedWeightSixteenCandidateBucket_4945_compact
  | 19011, normalizedWeightSixteenCandidateBucket_4a43, normalizedWeightSixteenCandidateBucket_4a43_compact
  | 19014, normalizedWeightSixteenCandidateBucket_4a46, normalizedWeightSixteenCandidateBucket_4a46_compact
  | 19017, normalizedWeightSixteenCandidateBucket_4a49, normalizedWeightSixteenCandidateBucket_4a49_compact
  | 19525, normalizedWeightSixteenCandidateBucket_4c45, normalizedWeightSixteenCandidateBucket_4c45_compact
  | 19526, normalizedWeightSixteenCandidateBucket_4c46, normalizedWeightSixteenCandidateBucket_4c46_compact
  | 19529, normalizedWeightSixteenCandidateBucket_4c49, normalizedWeightSixteenCandidateBucket_4c49_compact
  | 19530, normalizedWeightSixteenCandidateBucket_4c4a, normalizedWeightSixteenCandidateBucket_4c4a_compact
  | 20803, normalizedWeightSixteenCandidateBucket_5143, normalizedWeightSixteenCandidateBucket_5143_compact
  | 20805, normalizedWeightSixteenCandidateBucket_5145, normalizedWeightSixteenCandidateBucket_5145_compact
  | 20809, normalizedWeightSixteenCandidateBucket_5149, normalizedWeightSixteenCandidateBucket_5149_compact
  | 20815, normalizedWeightSixteenCandidateBucket_514f, normalizedWeightSixteenCandidateBucket_514f_compact
  | 21059, normalizedWeightSixteenCandidateBucket_5243, normalizedWeightSixteenCandidateBucket_5243_compact
  | 21062, normalizedWeightSixteenCandidateBucket_5246, normalizedWeightSixteenCandidateBucket_5246_compact
  | 21066, normalizedWeightSixteenCandidateBucket_524a, normalizedWeightSixteenCandidateBucket_524a_compact
  | 21071, normalizedWeightSixteenCandidateBucket_524f, normalizedWeightSixteenCandidateBucket_524f_compact
  | 21073, normalizedWeightSixteenCandidateBucket_5251, normalizedWeightSixteenCandidateBucket_5251_compact
  | 21573, normalizedWeightSixteenCandidateBucket_5445, normalizedWeightSixteenCandidateBucket_5445_compact
  | 21574, normalizedWeightSixteenCandidateBucket_5446, normalizedWeightSixteenCandidateBucket_5446_compact
  | 21580, normalizedWeightSixteenCandidateBucket_544c, normalizedWeightSixteenCandidateBucket_544c_compact
  | 21583, normalizedWeightSixteenCandidateBucket_544f, normalizedWeightSixteenCandidateBucket_544f_compact
  | 21585, normalizedWeightSixteenCandidateBucket_5451, normalizedWeightSixteenCandidateBucket_5451_compact
  | 21586, normalizedWeightSixteenCandidateBucket_5452, normalizedWeightSixteenCandidateBucket_5452_compact
  | 22345, normalizedWeightSixteenCandidateBucket_5749, normalizedWeightSixteenCandidateBucket_5749_compact
  | 22346, normalizedWeightSixteenCandidateBucket_574a, normalizedWeightSixteenCandidateBucket_574a_compact
  | 22348, normalizedWeightSixteenCandidateBucket_574c, normalizedWeightSixteenCandidateBucket_574c_compact
  | 22351, normalizedWeightSixteenCandidateBucket_574f, normalizedWeightSixteenCandidateBucket_574f_compact
  | 22601, normalizedWeightSixteenCandidateBucket_5849, normalizedWeightSixteenCandidateBucket_5849_compact
  | 22602, normalizedWeightSixteenCandidateBucket_584a, normalizedWeightSixteenCandidateBucket_584a_compact
  | 22604, normalizedWeightSixteenCandidateBucket_584c, normalizedWeightSixteenCandidateBucket_584c_compact
  | 22607, normalizedWeightSixteenCandidateBucket_584f, normalizedWeightSixteenCandidateBucket_584f_compact
  | 22609, normalizedWeightSixteenCandidateBucket_5851, normalizedWeightSixteenCandidateBucket_5851_compact
  | 22610, normalizedWeightSixteenCandidateBucket_5852, normalizedWeightSixteenCandidateBucket_5852_compact
  | 22612, normalizedWeightSixteenCandidateBucket_5854, normalizedWeightSixteenCandidateBucket_5854_compact
  | 22615, normalizedWeightSixteenCandidateBucket_5857, normalizedWeightSixteenCandidateBucket_5857_compact
  | 23365, normalizedWeightSixteenCandidateBucket_5b45, normalizedWeightSixteenCandidateBucket_5b45_compact
  | 23366, normalizedWeightSixteenCandidateBucket_5b46, normalizedWeightSixteenCandidateBucket_5b46_compact
  | 23372, normalizedWeightSixteenCandidateBucket_5b4c, normalizedWeightSixteenCandidateBucket_5b4c_compact
  | 23375, normalizedWeightSixteenCandidateBucket_5b4f, normalizedWeightSixteenCandidateBucket_5b4f_compact
  | 23380, normalizedWeightSixteenCandidateBucket_5b54, normalizedWeightSixteenCandidateBucket_5b54_compact
  | 23383, normalizedWeightSixteenCandidateBucket_5b57, normalizedWeightSixteenCandidateBucket_5b57_compact
  | 23875, normalizedWeightSixteenCandidateBucket_5d43, normalizedWeightSixteenCandidateBucket_5d43_compact
  | 23878, normalizedWeightSixteenCandidateBucket_5d46, normalizedWeightSixteenCandidateBucket_5d46_compact
  | 23882, normalizedWeightSixteenCandidateBucket_5d4a, normalizedWeightSixteenCandidateBucket_5d4a_compact
  | 23887, normalizedWeightSixteenCandidateBucket_5d4f, normalizedWeightSixteenCandidateBucket_5d4f_compact
  | 23890, normalizedWeightSixteenCandidateBucket_5d52, normalizedWeightSixteenCandidateBucket_5d52_compact
  | 23895, normalizedWeightSixteenCandidateBucket_5d57, normalizedWeightSixteenCandidateBucket_5d57_compact
  | 23899, normalizedWeightSixteenCandidateBucket_5d5b, normalizedWeightSixteenCandidateBucket_5d5b_compact
  | 24131, normalizedWeightSixteenCandidateBucket_5e43, normalizedWeightSixteenCandidateBucket_5e43_compact
  | 24133, normalizedWeightSixteenCandidateBucket_5e45, normalizedWeightSixteenCandidateBucket_5e45_compact
  | 24137, normalizedWeightSixteenCandidateBucket_5e49, normalizedWeightSixteenCandidateBucket_5e49_compact
  | 24143, normalizedWeightSixteenCandidateBucket_5e4f, normalizedWeightSixteenCandidateBucket_5e4f_compact
  | 24145, normalizedWeightSixteenCandidateBucket_5e51, normalizedWeightSixteenCandidateBucket_5e51_compact
  | 24151, normalizedWeightSixteenCandidateBucket_5e57, normalizedWeightSixteenCandidateBucket_5e57_compact
  | 24155, normalizedWeightSixteenCandidateBucket_5e5b, normalizedWeightSixteenCandidateBucket_5e5b_compact
  | 24157, normalizedWeightSixteenCandidateBucket_5e5d, normalizedWeightSixteenCandidateBucket_5e5d_compact
  | 25185, normalizedWeightSixteenCandidateBucket_6261, normalizedWeightSixteenCandidateBucket_6261_compact
  | 25697, normalizedWeightSixteenCandidateBucket_6461, normalizedWeightSixteenCandidateBucket_6461_compact
  | 25698, normalizedWeightSixteenCandidateBucket_6462, normalizedWeightSixteenCandidateBucket_6462_compact
  | 26721, normalizedWeightSixteenCandidateBucket_6861, normalizedWeightSixteenCandidateBucket_6861_compact
  | 26722, normalizedWeightSixteenCandidateBucket_6862, normalizedWeightSixteenCandidateBucket_6862_compact
  | 26724, normalizedWeightSixteenCandidateBucket_6864, normalizedWeightSixteenCandidateBucket_6864_compact
  | 26727, normalizedWeightSixteenCandidateBucket_6867, normalizedWeightSixteenCandidateBucket_6867_compact
  | 27492, normalizedWeightSixteenCandidateBucket_6b64, normalizedWeightSixteenCandidateBucket_6b64_compact
  | 27495, normalizedWeightSixteenCandidateBucket_6b67, normalizedWeightSixteenCandidateBucket_6b67_compact
  | 28002, normalizedWeightSixteenCandidateBucket_6d62, normalizedWeightSixteenCandidateBucket_6d62_compact
  | 28007, normalizedWeightSixteenCandidateBucket_6d67, normalizedWeightSixteenCandidateBucket_6d67_compact
  | 28011, normalizedWeightSixteenCandidateBucket_6d6b, normalizedWeightSixteenCandidateBucket_6d6b_compact
  | 28257, normalizedWeightSixteenCandidateBucket_6e61, normalizedWeightSixteenCandidateBucket_6e61_compact
  | 28263, normalizedWeightSixteenCandidateBucket_6e67, normalizedWeightSixteenCandidateBucket_6e67_compact
  | 28267, normalizedWeightSixteenCandidateBucket_6e6b, normalizedWeightSixteenCandidateBucket_6e6b_compact
  | 28269, normalizedWeightSixteenCandidateBucket_6e6d, normalizedWeightSixteenCandidateBucket_6e6d_compact
  | 30067, normalizedWeightSixteenCandidateBucket_7573, normalizedWeightSixteenCandidateBucket_7573_compact
  | 30323, normalizedWeightSixteenCandidateBucket_7673, normalizedWeightSixteenCandidateBucket_7673_compact
  | 30325, normalizedWeightSixteenCandidateBucket_7675, normalizedWeightSixteenCandidateBucket_7675_compact
  | 31353, normalizedWeightSixteenCandidateBucket_7a79, normalizedWeightSixteenCandidateBucket_7a79_compact
  | 33663, normalizedWeightSixteenCandidateBucket_837f, normalizedWeightSixteenCandidateBucket_837f_compact
  | 34175, normalizedWeightSixteenCandidateBucket_857f, normalizedWeightSixteenCandidateBucket_857f_compact
  | 34431, normalizedWeightSixteenCandidateBucket_867f, normalizedWeightSixteenCandidateBucket_867f_compact
  | 35199, normalizedWeightSixteenCandidateBucket_897f, normalizedWeightSixteenCandidateBucket_897f_compact
  | 35455, normalizedWeightSixteenCandidateBucket_8a7f, normalizedWeightSixteenCandidateBucket_8a7f_compact
  | 35967, normalizedWeightSixteenCandidateBucket_8c7f, normalizedWeightSixteenCandidateBucket_8c7f_compact
  | 36735, normalizedWeightSixteenCandidateBucket_8f7f, normalizedWeightSixteenCandidateBucket_8f7f_compact
  | 37247, normalizedWeightSixteenCandidateBucket_917f, normalizedWeightSixteenCandidateBucket_917f_compact
  | 37503, normalizedWeightSixteenCandidateBucket_927f, normalizedWeightSixteenCandidateBucket_927f_compact
  | 38015, normalizedWeightSixteenCandidateBucket_947f, normalizedWeightSixteenCandidateBucket_947f_compact
  | 38783, normalizedWeightSixteenCandidateBucket_977f, normalizedWeightSixteenCandidateBucket_977f_compact
  | 39807, normalizedWeightSixteenCandidateBucket_9b7f, normalizedWeightSixteenCandidateBucket_9b7f_compact
  | 40319, normalizedWeightSixteenCandidateBucket_9d7f, normalizedWeightSixteenCandidateBucket_9d7f_compact
  | 41343, normalizedWeightSixteenCandidateBucket_a17f, normalizedWeightSixteenCandidateBucket_a17f_compact
  | 41599, normalizedWeightSixteenCandidateBucket_a27f, normalizedWeightSixteenCandidateBucket_a27f_compact
  | 42111, normalizedWeightSixteenCandidateBucket_a47f, normalizedWeightSixteenCandidateBucket_a47f_compact
  | 42879, normalizedWeightSixteenCandidateBucket_a77f, normalizedWeightSixteenCandidateBucket_a77f_compact
  | 43903, normalizedWeightSixteenCandidateBucket_ab7f, normalizedWeightSixteenCandidateBucket_ab7f_compact
  | 44415, normalizedWeightSixteenCandidateBucket_ad7f, normalizedWeightSixteenCandidateBucket_ad7f_compact
  | 45951, normalizedWeightSixteenCandidateBucket_b37f, normalizedWeightSixteenCandidateBucket_b37f_compact
  | 46463, normalizedWeightSixteenCandidateBucket_b57f, normalizedWeightSixteenCandidateBucket_b57f_compact
  | 47487, normalizedWeightSixteenCandidateBucket_b97f, normalizedWeightSixteenCandidateBucket_b97f_compact
  | 49023, normalizedWeightSixteenCandidateBucket_bf7f, normalizedWeightSixteenCandidateBucket_bf7f_compact

end CryptBoolean
