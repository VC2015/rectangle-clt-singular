import RectangleCLTCompanion.SplitV4.TimeWeights
import Lean.Util.CollectAxioms

/-! Strict audit of the time integrals and the endpoint-limit justifications.
The scalar weights alone do not certify the stochastic comparison argument. -/

#print RectangleCLT.Companion.SplitV4.gaussianTimeWeight
#print RectangleCLT.Companion.SplitV4.pairedTimeWeight
#print RectangleCLT.Companion.SplitV4.fourthTimeWeight
#check RectangleCLT.Companion.SplitV4.intervalIntegrable_gaussianTimeWeight
#check RectangleCLT.Companion.SplitV4.intervalIntegrable_pairedTimeWeight
#check RectangleCLT.Companion.SplitV4.intervalIntegrable_fourthTimeWeight
#check RectangleCLT.Companion.SplitV4.gaussianTimePrimitive_endpoint_limits
#check RectangleCLT.Companion.SplitV4.pairedTimePrimitive_endpoint_limits
#check RectangleCLT.Companion.SplitV4.fourthTimePrimitive_endpoint_limits
#check RectangleCLT.Companion.SplitV4.integral_gaussianTimeWeight
#check RectangleCLT.Companion.SplitV4.integral_pairedTimeWeight
#check RectangleCLT.Companion.SplitV4.integral_fourthTimeWeight
#check RectangleCLT.Companion.SplitV4.truncated_gaussianTimeWeight_tendsto
#check RectangleCLT.Companion.SplitV4.truncated_pairedTimeWeight_tendsto
#check RectangleCLT.Companion.SplitV4.truncated_fourthTimeWeight_tendsto
#print axioms RectangleCLT.Companion.SplitV4.integral_gaussianTimeWeight
#print axioms RectangleCLT.Companion.SplitV4.integral_pairedTimeWeight
#print axioms RectangleCLT.Companion.SplitV4.integral_fourthTimeWeight

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.TimeWeights then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in split-V4 time-integral dependency closure"
  logInfo m!"Audited {names.size} split-V4 time-integral theorem declarations; only propext, Classical.choice and Quot.sound."
