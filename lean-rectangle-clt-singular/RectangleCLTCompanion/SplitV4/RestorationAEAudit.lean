import RectangleCLTCompanion.SplitV4.RestorationAE
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_signed_relative_ae_zero
#print axioms RectangleCLT.Companion.SplitV4.restoration_signed_relative_ae_zero

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationAE" then
          names := names.push n
  unless names.size > 0 do
    throwError "No a.e. restoration declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in a.e. restoration closure"
  logInfo m!"Audited all {names.size} a.e. restoration theorem declarations."
