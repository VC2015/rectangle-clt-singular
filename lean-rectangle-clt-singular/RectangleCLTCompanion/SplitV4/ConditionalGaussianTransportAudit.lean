import RectangleCLTCompanion.SplitV4.ConditionalGaussianTransport
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.indep_sup_of_conditionalEventIndependence
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_data_gaussian_test_transport
#print axioms RectangleCLT.Companion.SplitV4.indep_sup_of_conditionalEventIndependence
#print axioms RectangleCLT.Companion.SplitV4.independent_data_gaussian_test_transport

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.ConditionalGaussianTransport" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional Gaussian transport declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional Gaussian transport closure"
  logInfo m!"Audited all {names.size} conditional Gaussian transport theorem declarations."
