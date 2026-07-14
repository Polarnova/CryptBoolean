import Lake

open Lake DSL

require FABL from git "https://github.com/Polarnova/FABL.git" @ "34334a1b0c8dd806c076444a0875caf29ba5e248"

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
