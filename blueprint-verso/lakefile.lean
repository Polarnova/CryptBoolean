import Lake

open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.30.0"
require CryptBoolean from ".."

package CryptBooleanBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib CryptBooleanBlueprint where

lean_exe «blueprint-gen» where
  root := `CryptBooleanBlueprintMain
