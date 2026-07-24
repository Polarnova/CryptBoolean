import Lake

open Lake DSL

require FABL from git "https://github.com/Polarnova/FABL.git" @ "v0.5.6"

package CryptBooleanFunction where
  version := v!"0.3.0"
  description := "Cryptographic Boolean Functions in Lean"
  keywords := #["mathematics", "boolean-functions", "cryptography", "formalization"]
  license := "Apache-2.0"
  releaseRepo := "https://github.com/Polarnova/CryptBoolean"
  buildArchive := s!"CryptBoolean-{System.Platform.target}.tar.gz"
  preferReleaseBuild := true
  precompileModules := false
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]

@[default_target]
lean_lib CryptBoolean where
