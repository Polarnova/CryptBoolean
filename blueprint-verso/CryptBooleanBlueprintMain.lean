/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import BlueprintSite
import VersoBlueprint.PreviewManifest
import CryptBooleanBlueprint.Blueprint

def main (args : List String) : IO UInt32 := do
  let profile ← BlueprintSite.readProfile
  let cryptBooleanRevision ←
    BlueprintSite.sourceRevision "CRYPTBOOLEAN_SOURCE_REVISION" "main"
  let fablRevision ← BlueprintSite.sourceRevision "FABL_SOURCE_REVISION" "main"
  let mathlibRevision ← BlueprintSite.sourceRevision "MATHLIB_SOURCE_REVISION" "v4.32.0"
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CryptBooleanBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := BlueprintSite.renderConfig profile #[
      .github "CryptBoolean/" "Polarnova/CryptBoolean" cryptBooleanRevision,
      .github "FABL/" "Polarnova/FABL" fablRevision,
      .github "Mathlib/" "leanprover-community/mathlib4" mathlibRevision
    ])
