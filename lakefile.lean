import Lake

open Lake DSL

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

@[default_target]
lean_lib CryptBoolean where
