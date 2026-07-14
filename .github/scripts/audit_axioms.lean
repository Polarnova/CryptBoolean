import CryptBoolean
import Mathlib.Util.AssertNoSorry

open Lean Elab Command

/-- Reject public `CryptBoolean` declarations that depend on nonstandard axioms. -/
elab "#audit_crypt_boolean" : command => do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    if (`CryptBoolean).isPrefixOf name then names.push name else names
  let allowed := NameSet.ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut offenders := #[]
  let mut unexpected := #[]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    if axioms.contains ``sorryAx then
      offenders := offenders.push name
    for ax in axioms do
      unless allowed.contains ax do
        unexpected := unexpected.push (name, ax)
  unless offenders.isEmpty do
    throwError "sorryAx found in public declarations: {offenders.toList}"
  unless unexpected.isEmpty do
    throwError "nonstandard axioms found in public declarations: {unexpected.toList}"
  logInfo m!"axiom audit ok: {declarations.size} CryptBoolean declarations"

#audit_crypt_boolean
