import RectangleCLTCompanion.SplitV4.RestorationConditionalAveraging
import Lean.Util.CollectAxioms

/-! Audit of genuine conditional averaging at the common base in B.2.
The B.4 averaged matrix estimate is an explicit analytic input here. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedSelectorMatrixEstimate_ae_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_trace_conditionalMatrixAverage_eq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_restoration_matrix_order_bound
#print axioms RectangleCLT.Companion.SplitV4.averagedSelectorMatrixEstimate_ae_bound
#print axioms RectangleCLT.Companion.SplitV4.integral_trace_conditionalMatrixAverage_eq
#print axioms RectangleCLT.Companion.SplitV4.conditional_restoration_matrix_order_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalAveraging" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional restoration averaging declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional restoration averaging closure"
  logInfo m!"Audited all {names.size} conditional restoration averaging theorem declarations."
