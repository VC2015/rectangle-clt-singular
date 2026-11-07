import RectangleCLTCompanion.SplitV4.LogisticGammaTrace
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.gammaAdjustedThreshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_logistic_power_trace_le_of_L1_budget
#print axioms RectangleCLT.Companion.SplitV4.averaged_logistic_power_trace_le_of_L1_budget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if #["RectangleCLTCompanion.SplitV4.GaussianThresholdCommonShift",
          "RectangleCLTCompanion.SplitV4.AveragedDerivativeBound",
          "RectangleCLTCompanion.SplitV4.LogisticGammaTrace"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in signed Gamma trace closure"
  logInfo m!"Audited {names.size} common-shift, compact-L1 averaging and signed Gamma trace theorem declarations; only the permitted three axioms."
  logInfo "Actual Gaussian score weights stay signed. The displayed intermediate uniform L1 hard derivative budget is the only quantitative input; it is not a final matrix estimate premise."
