import RectangleCLTCompanion.SplitV4.RestorationConditionalSeries
import Lean.Util.CollectAxioms

/-! Conditional restoration series-order audit. Actual expected orders
are summable with the sharp matrix bound; the translated expectation/Stein
identification remains a separate analytic step. -/

#print RectangleCLT.Companion.SplitV4.conditionalRestorationTraceOrderIntegral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_restoration_order_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_restoration_expected_series_bound
#print axioms RectangleCLT.Companion.SplitV4.conditional_translated_restoration_order_bound
#print axioms RectangleCLT.Companion.SplitV4.conditional_restoration_expected_series_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalSeries" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional restoration series declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional restoration series closure"
  logInfo m!"Audited all {names.size} conditional restoration series theorem declarations."
