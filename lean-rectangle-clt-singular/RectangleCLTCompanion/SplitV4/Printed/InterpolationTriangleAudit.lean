import RectangleCLTCompanion.SplitV4.Printed.InterpolationTriangle
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.weighted_triangle_integral_swap
#print axioms RectangleCLT.Companion.SplitV4.Printed.signed_hessian_fourth_kernel_expectation
#print axioms RectangleCLT.Companion.SplitV4.Printed.genericRowOperator_fourth_from_signed_hessian

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed.InterpolationTriangle" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed triangular interpolation transition"
  logInfo m!"Audited {names.size} triangular interpolation theorem declarations; only the permitted three axioms."
