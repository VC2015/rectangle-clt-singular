import RectangleCLTCompanion.SplitV4.Printed.CovariancePotential
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightPotential_hessian_ge_identity
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_isProbability
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_integral_potential_density
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_of_potential_hessian
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianWeightProbabilityLaw_variance_le_via_printed_potential

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.CovariancePotential" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed CovariancePotential closure"
  logInfo m!"Audited {names.size} printed CovariancePotential theorem declarations; only the permitted three axioms."
