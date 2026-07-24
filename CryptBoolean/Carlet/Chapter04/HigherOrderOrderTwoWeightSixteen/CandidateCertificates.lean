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
  "|" term "," ident

local syntax (name := normalizedWeightSixteenCertificatesCommand)
  "normalized_weight_sixteen_certificates" ident "where"
    normalizedWeightSixteenCertificateRow* : command

set_option linter.style.maxHeartbeats false in
local macro_rules
  | `(command| normalized_weight_sixteen_certificates
      $soundnessName:ident where
      $[$rows:normalizedWeightSixteenCertificateRow]*) => do
    let generated ← rows.mapM fun row => do
      let `(normalizedWeightSixteenCertificateRow|
        | $bucketPrefix:term, $tree:ident) := row
        | Lean.Macro.throwUnsupported
      let proofName := Lean.mkIdent <| tree.getId.appendAfter "_compact"
      let declaration ←
        `(command| compact_mask_soundness $proofName for $tree)
      pure (declaration, bucketPrefix, proofName)
    let declarations := generated.map fun item => item.1
    let dispatchCases := generated.map fun item => (item.2.1, item.2.2)
    let rec dispatcherProof
        (fuel : Nat)
        (current : Array (Lean.TSyntax `term × Lean.TSyntax `ident)) :
        Lean.MacroM (Lean.TSyntax `tactic) := do
      if current.isEmpty then
        `(tactic| cases hbucket)
      else
        match fuel with
        | 0 =>
            Lean.Macro.throwError
              "certificate dispatch exhausted its structural bound"
        | fuel + 1 =>
            let midpoint := current.size / 2
            let some (bucketPrefix, proofName) := current[midpoint]?
              | Lean.Macro.throwError
                  "certificate dispatch midpoint is out of bounds"
            let left ← dispatcherProof fuel (current.extract 0 midpoint)
            let right ←
              dispatcherProof fuel
                (current.extract (midpoint + 1) current.size)
            `(tactic| (
              by_cases hlt : codePrefix.toNat < $bucketPrefix
              · rw [if_pos hlt] at hbucket
                $left:tactic
              · rw [if_neg hlt] at hbucket
                by_cases heq : codePrefix.toNat = $bucketPrefix
                · rw [if_pos heq] at hbucket
                  cases hbucket
                  exact $proofName
                · rw [if_neg heq] at hbucket
                  $right:tactic))
    let dispatch ← dispatcherProof dispatchCases.size dispatchCases
    let bucketSoundnessName :=
      Lean.mkIdent <| soundnessName.getId.appendAfter "_of_bucket"
    let bucketSoundness ← `(command|
      set_option Elab.async true in
      /-- A generated bucket carries the compact-mask certificate associated
      with every one of its candidate leaves. -/
      private theorem $bucketSoundnessName
          {codePrefix : BitVec 16}
          {tree : NormalizedWeightSixteenCandidateTree}
          (hbucket :
            normalizedWeightSixteenCandidateBucket codePrefix = some tree) :
          tree.All
            NormalizedWeightSixteenCandidate.IsCompactMaskSound := by
        unfold normalizedWeightSixteenCandidateBucket at hbucket
        $dispatch:tactic)
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
        exact ⟨candidate, hcode,
          NormalizedWeightSixteenCandidateTree.All.of_member
            ($bucketSoundnessName hbucket) hmember⟩)
    return Lean.mkNullNode <|
      declarations.map (·.raw) ++
        #[bucketSoundness.raw, soundness.raw]

normalized_weight_sixteen_certificates
  normalizedWeightSixteenCompactCandidateSoundness where
  | 2823, normalizedWeightSixteenCandidateBucket_0b07
  | 3335, normalizedWeightSixteenCandidateBucket_0d07
  | 3339, normalizedWeightSixteenCandidateBucket_0d0b
  | 3591, normalizedWeightSixteenCandidateBucket_0e07
  | 3595, normalizedWeightSixteenCandidateBucket_0e0b
  | 3597, normalizedWeightSixteenCandidateBucket_0e0d
  | 4871, normalizedWeightSixteenCandidateBucket_1307
  | 4875, normalizedWeightSixteenCandidateBucket_130b
  | 5383, normalizedWeightSixteenCandidateBucket_1507
  | 5389, normalizedWeightSixteenCandidateBucket_150d
  | 5395, normalizedWeightSixteenCandidateBucket_1513
  | 5639, normalizedWeightSixteenCandidateBucket_1607
  | 5646, normalizedWeightSixteenCandidateBucket_160e
  | 5651, normalizedWeightSixteenCandidateBucket_1613
  | 5653, normalizedWeightSixteenCandidateBucket_1615
  | 6411, normalizedWeightSixteenCandidateBucket_190b
  | 6413, normalizedWeightSixteenCandidateBucket_190d
  | 6419, normalizedWeightSixteenCandidateBucket_1913
  | 6421, normalizedWeightSixteenCandidateBucket_1915
  | 6667, normalizedWeightSixteenCandidateBucket_1a0b
  | 6670, normalizedWeightSixteenCandidateBucket_1a0e
  | 6675, normalizedWeightSixteenCandidateBucket_1a13
  | 6678, normalizedWeightSixteenCandidateBucket_1a16
  | 6681, normalizedWeightSixteenCandidateBucket_1a19
  | 7181, normalizedWeightSixteenCandidateBucket_1c0d
  | 7182, normalizedWeightSixteenCandidateBucket_1c0e
  | 7189, normalizedWeightSixteenCandidateBucket_1c15
  | 7190, normalizedWeightSixteenCandidateBucket_1c16
  | 7193, normalizedWeightSixteenCandidateBucket_1c19
  | 7194, normalizedWeightSixteenCandidateBucket_1c1a
  | 8967, normalizedWeightSixteenCandidateBucket_2307
  | 8971, normalizedWeightSixteenCandidateBucket_230b
  | 8979, normalizedWeightSixteenCandidateBucket_2313
  | 8988, normalizedWeightSixteenCandidateBucket_231c
  | 8991, normalizedWeightSixteenCandidateBucket_231f
  | 9479, normalizedWeightSixteenCandidateBucket_2507
  | 9485, normalizedWeightSixteenCandidateBucket_250d
  | 9493, normalizedWeightSixteenCandidateBucket_2515
  | 9498, normalizedWeightSixteenCandidateBucket_251a
  | 9503, normalizedWeightSixteenCandidateBucket_251f
  | 9507, normalizedWeightSixteenCandidateBucket_2523
  | 9735, normalizedWeightSixteenCandidateBucket_2607
  | 9742, normalizedWeightSixteenCandidateBucket_260e
  | 9750, normalizedWeightSixteenCandidateBucket_2616
  | 9753, normalizedWeightSixteenCandidateBucket_2619
  | 9759, normalizedWeightSixteenCandidateBucket_261f
  | 9763, normalizedWeightSixteenCandidateBucket_2623
  | 9765, normalizedWeightSixteenCandidateBucket_2625
  | 10507, normalizedWeightSixteenCandidateBucket_290b
  | 10509, normalizedWeightSixteenCandidateBucket_290d
  | 10518, normalizedWeightSixteenCandidateBucket_2916
  | 10521, normalizedWeightSixteenCandidateBucket_2919
  | 10527, normalizedWeightSixteenCandidateBucket_291f
  | 10531, normalizedWeightSixteenCandidateBucket_2923
  | 10533, normalizedWeightSixteenCandidateBucket_2925
  | 10763, normalizedWeightSixteenCandidateBucket_2a0b
  | 10766, normalizedWeightSixteenCandidateBucket_2a0e
  | 10773, normalizedWeightSixteenCandidateBucket_2a15
  | 10778, normalizedWeightSixteenCandidateBucket_2a1a
  | 10783, normalizedWeightSixteenCandidateBucket_2a1f
  | 10787, normalizedWeightSixteenCandidateBucket_2a23
  | 10790, normalizedWeightSixteenCandidateBucket_2a26
  | 10793, normalizedWeightSixteenCandidateBucket_2a29
  | 11277, normalizedWeightSixteenCandidateBucket_2c0d
  | 11278, normalizedWeightSixteenCandidateBucket_2c0e
  | 11283, normalizedWeightSixteenCandidateBucket_2c13
  | 11292, normalizedWeightSixteenCandidateBucket_2c1c
  | 11295, normalizedWeightSixteenCandidateBucket_2c1f
  | 11301, normalizedWeightSixteenCandidateBucket_2c25
  | 11302, normalizedWeightSixteenCandidateBucket_2c26
  | 11305, normalizedWeightSixteenCandidateBucket_2c29
  | 11306, normalizedWeightSixteenCandidateBucket_2c2a
  | 12051, normalizedWeightSixteenCandidateBucket_2f13
  | 12053, normalizedWeightSixteenCandidateBucket_2f15
  | 12054, normalizedWeightSixteenCandidateBucket_2f16
  | 12057, normalizedWeightSixteenCandidateBucket_2f19
  | 12058, normalizedWeightSixteenCandidateBucket_2f1a
  | 12060, normalizedWeightSixteenCandidateBucket_2f1c
  | 12063, normalizedWeightSixteenCandidateBucket_2f1f
  | 12558, normalizedWeightSixteenCandidateBucket_310e
  | 12563, normalizedWeightSixteenCandidateBucket_3113
  | 12565, normalizedWeightSixteenCandidateBucket_3115
  | 12569, normalizedWeightSixteenCandidateBucket_3119
  | 12575, normalizedWeightSixteenCandidateBucket_311f
  | 12579, normalizedWeightSixteenCandidateBucket_3123
  | 12581, normalizedWeightSixteenCandidateBucket_3125
  | 12585, normalizedWeightSixteenCandidateBucket_3129
  | 12591, normalizedWeightSixteenCandidateBucket_312f
  | 12813, normalizedWeightSixteenCandidateBucket_320d
  | 12819, normalizedWeightSixteenCandidateBucket_3213
  | 12822, normalizedWeightSixteenCandidateBucket_3216
  | 12826, normalizedWeightSixteenCandidateBucket_321a
  | 12831, normalizedWeightSixteenCandidateBucket_321f
  | 12835, normalizedWeightSixteenCandidateBucket_3223
  | 12838, normalizedWeightSixteenCandidateBucket_3226
  | 12842, normalizedWeightSixteenCandidateBucket_322a
  | 12847, normalizedWeightSixteenCandidateBucket_322f
  | 12849, normalizedWeightSixteenCandidateBucket_3231
  | 13323, normalizedWeightSixteenCandidateBucket_340b
  | 13333, normalizedWeightSixteenCandidateBucket_3415
  | 13334, normalizedWeightSixteenCandidateBucket_3416
  | 13340, normalizedWeightSixteenCandidateBucket_341c
  | 13343, normalizedWeightSixteenCandidateBucket_341f
  | 13349, normalizedWeightSixteenCandidateBucket_3425
  | 13350, normalizedWeightSixteenCandidateBucket_3426
  | 13356, normalizedWeightSixteenCandidateBucket_342c
  | 13359, normalizedWeightSixteenCandidateBucket_342f
  | 13361, normalizedWeightSixteenCandidateBucket_3431
  | 13362, normalizedWeightSixteenCandidateBucket_3432
  | 14091, normalizedWeightSixteenCandidateBucket_370b
  | 14093, normalizedWeightSixteenCandidateBucket_370d
  | 14094, normalizedWeightSixteenCandidateBucket_370e
  | 14105, normalizedWeightSixteenCandidateBucket_3719
  | 14106, normalizedWeightSixteenCandidateBucket_371a
  | 14108, normalizedWeightSixteenCandidateBucket_371c
  | 14111, normalizedWeightSixteenCandidateBucket_371f
  | 14121, normalizedWeightSixteenCandidateBucket_3729
  | 14122, normalizedWeightSixteenCandidateBucket_372a
  | 14124, normalizedWeightSixteenCandidateBucket_372c
  | 14127, normalizedWeightSixteenCandidateBucket_372f
  | 14343, normalizedWeightSixteenCandidateBucket_3807
  | 14361, normalizedWeightSixteenCandidateBucket_3819
  | 14362, normalizedWeightSixteenCandidateBucket_381a
  | 14364, normalizedWeightSixteenCandidateBucket_381c
  | 14367, normalizedWeightSixteenCandidateBucket_381f
  | 14377, normalizedWeightSixteenCandidateBucket_3829
  | 14378, normalizedWeightSixteenCandidateBucket_382a
  | 14380, normalizedWeightSixteenCandidateBucket_382c
  | 14383, normalizedWeightSixteenCandidateBucket_382f
  | 14385, normalizedWeightSixteenCandidateBucket_3831
  | 14386, normalizedWeightSixteenCandidateBucket_3832
  | 14388, normalizedWeightSixteenCandidateBucket_3834
  | 14391, normalizedWeightSixteenCandidateBucket_3837
  | 15111, normalizedWeightSixteenCandidateBucket_3b07
  | 15117, normalizedWeightSixteenCandidateBucket_3b0d
  | 15118, normalizedWeightSixteenCandidateBucket_3b0e
  | 15125, normalizedWeightSixteenCandidateBucket_3b15
  | 15126, normalizedWeightSixteenCandidateBucket_3b16
  | 15132, normalizedWeightSixteenCandidateBucket_3b1c
  | 15135, normalizedWeightSixteenCandidateBucket_3b1f
  | 15141, normalizedWeightSixteenCandidateBucket_3b25
  | 15142, normalizedWeightSixteenCandidateBucket_3b26
  | 15148, normalizedWeightSixteenCandidateBucket_3b2c
  | 15151, normalizedWeightSixteenCandidateBucket_3b2f
  | 15156, normalizedWeightSixteenCandidateBucket_3b34
  | 15159, normalizedWeightSixteenCandidateBucket_3b37
  | 15623, normalizedWeightSixteenCandidateBucket_3d07
  | 15627, normalizedWeightSixteenCandidateBucket_3d0b
  | 15630, normalizedWeightSixteenCandidateBucket_3d0e
  | 15635, normalizedWeightSixteenCandidateBucket_3d13
  | 15638, normalizedWeightSixteenCandidateBucket_3d16
  | 15642, normalizedWeightSixteenCandidateBucket_3d1a
  | 15647, normalizedWeightSixteenCandidateBucket_3d1f
  | 15651, normalizedWeightSixteenCandidateBucket_3d23
  | 15654, normalizedWeightSixteenCandidateBucket_3d26
  | 15658, normalizedWeightSixteenCandidateBucket_3d2a
  | 15663, normalizedWeightSixteenCandidateBucket_3d2f
  | 15666, normalizedWeightSixteenCandidateBucket_3d32
  | 15671, normalizedWeightSixteenCandidateBucket_3d37
  | 15675, normalizedWeightSixteenCandidateBucket_3d3b
  | 15879, normalizedWeightSixteenCandidateBucket_3e07
  | 15883, normalizedWeightSixteenCandidateBucket_3e0b
  | 15885, normalizedWeightSixteenCandidateBucket_3e0d
  | 15891, normalizedWeightSixteenCandidateBucket_3e13
  | 15893, normalizedWeightSixteenCandidateBucket_3e15
  | 15897, normalizedWeightSixteenCandidateBucket_3e19
  | 15903, normalizedWeightSixteenCandidateBucket_3e1f
  | 15907, normalizedWeightSixteenCandidateBucket_3e23
  | 15909, normalizedWeightSixteenCandidateBucket_3e25
  | 15913, normalizedWeightSixteenCandidateBucket_3e29
  | 15919, normalizedWeightSixteenCandidateBucket_3e2f
  | 15921, normalizedWeightSixteenCandidateBucket_3e31
  | 15927, normalizedWeightSixteenCandidateBucket_3e37
  | 15931, normalizedWeightSixteenCandidateBucket_3e3b
  | 15933, normalizedWeightSixteenCandidateBucket_3e3d
  | 17731, normalizedWeightSixteenCandidateBucket_4543
  | 17987, normalizedWeightSixteenCandidateBucket_4643
  | 17989, normalizedWeightSixteenCandidateBucket_4645
  | 18755, normalizedWeightSixteenCandidateBucket_4943
  | 18757, normalizedWeightSixteenCandidateBucket_4945
  | 19011, normalizedWeightSixteenCandidateBucket_4a43
  | 19014, normalizedWeightSixteenCandidateBucket_4a46
  | 19017, normalizedWeightSixteenCandidateBucket_4a49
  | 19525, normalizedWeightSixteenCandidateBucket_4c45
  | 19526, normalizedWeightSixteenCandidateBucket_4c46
  | 19529, normalizedWeightSixteenCandidateBucket_4c49
  | 19530, normalizedWeightSixteenCandidateBucket_4c4a
  | 20803, normalizedWeightSixteenCandidateBucket_5143
  | 20805, normalizedWeightSixteenCandidateBucket_5145
  | 20809, normalizedWeightSixteenCandidateBucket_5149
  | 20815, normalizedWeightSixteenCandidateBucket_514f
  | 21059, normalizedWeightSixteenCandidateBucket_5243
  | 21062, normalizedWeightSixteenCandidateBucket_5246
  | 21066, normalizedWeightSixteenCandidateBucket_524a
  | 21071, normalizedWeightSixteenCandidateBucket_524f
  | 21073, normalizedWeightSixteenCandidateBucket_5251
  | 21573, normalizedWeightSixteenCandidateBucket_5445
  | 21574, normalizedWeightSixteenCandidateBucket_5446
  | 21580, normalizedWeightSixteenCandidateBucket_544c
  | 21583, normalizedWeightSixteenCandidateBucket_544f
  | 21585, normalizedWeightSixteenCandidateBucket_5451
  | 21586, normalizedWeightSixteenCandidateBucket_5452
  | 22345, normalizedWeightSixteenCandidateBucket_5749
  | 22346, normalizedWeightSixteenCandidateBucket_574a
  | 22348, normalizedWeightSixteenCandidateBucket_574c
  | 22351, normalizedWeightSixteenCandidateBucket_574f
  | 22601, normalizedWeightSixteenCandidateBucket_5849
  | 22602, normalizedWeightSixteenCandidateBucket_584a
  | 22604, normalizedWeightSixteenCandidateBucket_584c
  | 22607, normalizedWeightSixteenCandidateBucket_584f
  | 22609, normalizedWeightSixteenCandidateBucket_5851
  | 22610, normalizedWeightSixteenCandidateBucket_5852
  | 22612, normalizedWeightSixteenCandidateBucket_5854
  | 22615, normalizedWeightSixteenCandidateBucket_5857
  | 23365, normalizedWeightSixteenCandidateBucket_5b45
  | 23366, normalizedWeightSixteenCandidateBucket_5b46
  | 23372, normalizedWeightSixteenCandidateBucket_5b4c
  | 23375, normalizedWeightSixteenCandidateBucket_5b4f
  | 23380, normalizedWeightSixteenCandidateBucket_5b54
  | 23383, normalizedWeightSixteenCandidateBucket_5b57
  | 23875, normalizedWeightSixteenCandidateBucket_5d43
  | 23878, normalizedWeightSixteenCandidateBucket_5d46
  | 23882, normalizedWeightSixteenCandidateBucket_5d4a
  | 23887, normalizedWeightSixteenCandidateBucket_5d4f
  | 23890, normalizedWeightSixteenCandidateBucket_5d52
  | 23895, normalizedWeightSixteenCandidateBucket_5d57
  | 23899, normalizedWeightSixteenCandidateBucket_5d5b
  | 24131, normalizedWeightSixteenCandidateBucket_5e43
  | 24133, normalizedWeightSixteenCandidateBucket_5e45
  | 24137, normalizedWeightSixteenCandidateBucket_5e49
  | 24143, normalizedWeightSixteenCandidateBucket_5e4f
  | 24145, normalizedWeightSixteenCandidateBucket_5e51
  | 24151, normalizedWeightSixteenCandidateBucket_5e57
  | 24155, normalizedWeightSixteenCandidateBucket_5e5b
  | 24157, normalizedWeightSixteenCandidateBucket_5e5d
  | 25185, normalizedWeightSixteenCandidateBucket_6261
  | 25697, normalizedWeightSixteenCandidateBucket_6461
  | 25698, normalizedWeightSixteenCandidateBucket_6462
  | 26721, normalizedWeightSixteenCandidateBucket_6861
  | 26722, normalizedWeightSixteenCandidateBucket_6862
  | 26724, normalizedWeightSixteenCandidateBucket_6864
  | 26727, normalizedWeightSixteenCandidateBucket_6867
  | 27492, normalizedWeightSixteenCandidateBucket_6b64
  | 27495, normalizedWeightSixteenCandidateBucket_6b67
  | 28002, normalizedWeightSixteenCandidateBucket_6d62
  | 28007, normalizedWeightSixteenCandidateBucket_6d67
  | 28011, normalizedWeightSixteenCandidateBucket_6d6b
  | 28257, normalizedWeightSixteenCandidateBucket_6e61
  | 28263, normalizedWeightSixteenCandidateBucket_6e67
  | 28267, normalizedWeightSixteenCandidateBucket_6e6b
  | 28269, normalizedWeightSixteenCandidateBucket_6e6d
  | 30067, normalizedWeightSixteenCandidateBucket_7573
  | 30323, normalizedWeightSixteenCandidateBucket_7673
  | 30325, normalizedWeightSixteenCandidateBucket_7675
  | 31353, normalizedWeightSixteenCandidateBucket_7a79
  | 33663, normalizedWeightSixteenCandidateBucket_837f
  | 34175, normalizedWeightSixteenCandidateBucket_857f
  | 34431, normalizedWeightSixteenCandidateBucket_867f
  | 35199, normalizedWeightSixteenCandidateBucket_897f
  | 35455, normalizedWeightSixteenCandidateBucket_8a7f
  | 35967, normalizedWeightSixteenCandidateBucket_8c7f
  | 36735, normalizedWeightSixteenCandidateBucket_8f7f
  | 37247, normalizedWeightSixteenCandidateBucket_917f
  | 37503, normalizedWeightSixteenCandidateBucket_927f
  | 38015, normalizedWeightSixteenCandidateBucket_947f
  | 38783, normalizedWeightSixteenCandidateBucket_977f
  | 39807, normalizedWeightSixteenCandidateBucket_9b7f
  | 40319, normalizedWeightSixteenCandidateBucket_9d7f
  | 41343, normalizedWeightSixteenCandidateBucket_a17f
  | 41599, normalizedWeightSixteenCandidateBucket_a27f
  | 42111, normalizedWeightSixteenCandidateBucket_a47f
  | 42879, normalizedWeightSixteenCandidateBucket_a77f
  | 43903, normalizedWeightSixteenCandidateBucket_ab7f
  | 44415, normalizedWeightSixteenCandidateBucket_ad7f
  | 45951, normalizedWeightSixteenCandidateBucket_b37f
  | 46463, normalizedWeightSixteenCandidateBucket_b57f
  | 47487, normalizedWeightSixteenCandidateBucket_b97f
  | 49023, normalizedWeightSixteenCandidateBucket_bf7f

end CryptBoolean
