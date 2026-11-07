import RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction
import Lean.Util.CollectAxioms

#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_integral_shift_pos_of_mass
#print axioms RectangleCLT.Companion.SplitV4.Printed.concaveOn_log_gaussian_convolution_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_cgf_sub_quadratic_eq_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussianTilt_directional_variance_le_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_weightCovariance_contraction_nonnegative
#print axioms RectangleCLT.Companion.SplitV4.Printed.nonnegativeLogConcave_indicator
#print axioms RectangleCLT.Companion.SplitV4.Printed.gaussian_convex_indicator_covariance_contraction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed nonnegative covariance closure"
  logInfo m!"Audited {names.size} printed nonnegative covariance theorem declarations; only the permitted three axioms."
