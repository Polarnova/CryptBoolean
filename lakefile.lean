import Lake

open Lake DSL System

require FABL from git "https://github.com/Polarnova/FABL.git" @ "v0.5.6"

package CryptBooleanFunction where
  precompileModules := false
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]

input_file normalizedWeightSixteenCandidateGenerator where
  path := "scripts/generate_normalized_weight_sixteen_candidates.py"
  text := true

input_file rankSevenWeightSixteenPatterns where
  path :=
    "CryptBoolean/Carlet/Chapter04/HigherOrderOrderTwoWeightSixteen/RankSevenPatterns.lean"
  text := true

/-- Reconstruct the generated finite certificate table before Lean scans its imports. -/
target normalizedWeightSixteenCandidates pkg : FilePath := do
  let generator ← normalizedWeightSixteenCandidateGenerator.fetch
  let patterns ← rankSevenWeightSixteenPatterns.fetch
  let inputs := generator.zipWith (sync := true)
    (fun generatorPath patternsPath => (generatorPath, patternsPath)) patterns
  let output := pkg.dir /
    "CryptBoolean/Carlet/Chapter04/HigherOrderOrderTwoWeightSixteen/NormalizedCandidates.lean"
  inputs.mapM fun (generatorPath, _patternsPath) => do
    let traceFile := pkg.buildDir / "normalized-weight-sixteen-candidates.trace"
    buildUnlessUpToDate output (← getTrace) traceFile do
      proc {
        cmd := if Platform.isWindows then "python" else "python3"
        args := #[generatorPath.toString, "--lean-output", output.toString,
          "--timeout-seconds", "60"]
        cwd := some pkg.dir
      } (quiet := true)
    return output

@[default_target]
lean_lib CryptBoolean where
  needs := #[normalizedWeightSixteenCandidates]
