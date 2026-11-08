import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_tail_envelope
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_negative_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_positive_region
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_far_positive
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumDensity_derivative_small_dimension
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound
#print axioms RectangleCLT.Companion.SplitV4.Printed.normalMaximumCDF_second_derivative_global_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed global Gaussian maximum smoothness declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed Gaussian maximum smoothness closure"
  logInfo m!"Audited all {names.size} printed Gaussian maximum smoothness theorem declarations; only the three permitted axioms."
