import RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound
import RectangleCLTCompanion.SplitV4.NuclearTraceDual
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.logisticMatrixConstant
#print RectangleCLT.Companion.SplitV4.logisticGaussianScore
#print RectangleCLT.Companion.SplitV4.PolyhedralBaseConcentration
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_matrix_estimate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_matrix_estimate_rectangle
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_trace_mul_le_nuclear_of_quadratic
#print axioms RectangleCLT.Companion.SplitV4.logistic_matrix_estimate
#print axioms RectangleCLT.Companion.SplitV4.logistic_matrix_estimate_rectangle
#print axioms RectangleCLT.Companion.SplitV4.abs_trace_mul_le_nuclear_of_quadratic

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.GaussianThresholdCommonShift",
    "RectangleCLTCompanion.SplitV4.AveragedDerivativeBound",
    "RectangleCLTCompanion.SplitV4.LogisticGammaTrace",
    "RectangleCLTCompanion.SplitV4.LogisticMatrixBound",
    "RectangleCLTCompanion.SplitV4.LogisticMatrixIntegrability",
    "RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound",
    "RectangleCLTCompanion.SplitV4.NuclearTraceDual"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in full logistic matrix closure"
  logInfo m!"Audited {names.size} actual common-shift, signed Gamma, nuclear matrix and regularization theorem declarations; only the permitted three axioms."
  logInfo "The terminal native Gaussian matrix estimate uses only the actual uniform concentrated-base law, positive C0, h≥δ and δ√L≤σ. Repeated normals and singular Gram matrices are permitted; no final trace or matrix estimate is assumed."
