import RectangleCLTCompanion.SplitV4.RestorationConditionalTransport
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationThirdExpectation_conditional_transport
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationFourthExpectation_conditional_transport
#print axioms RectangleCLT.Companion.SplitV4.restorationThirdExpectation_conditional_transport
#print axioms RectangleCLT.Companion.SplitV4.restorationFourthExpectation_conditional_transport

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalTransport" then
          names := names.push n
  unless names.size > 0 do
    throwError "No restoration conditional transport declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in restoration conditional transport closure"
  logInfo m!"Audited all {names.size} restoration conditional transport theorem declarations."
