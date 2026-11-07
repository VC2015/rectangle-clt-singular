import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
import RectangleCLTCompanion.SplitV4.LogisticMatrixLimits
import RectangleCLTCompanion.SplitV4.LogisticPaddingLimits
import Lean.Util.CollectAxioms

/-! Strict audit of the B.4 nuclear-norm reduction, actual signed Gamma
mixture, concentration pullbacks, and padded-normal limit infrastructure.
The whole B.4 quantitative theorem still requires the separate hard-threshold
derivative bound and its application through the Gamma mixture.
-/

#print RectangleCLT.Companion.SplitV4.symmetricTraceUnitBall
#print RectangleCLT.Companion.SplitV4.symmetricNuclearNorm
#print RectangleCLT.Companion.SplitV4.logisticNullWeight
#print RectangleCLT.Companion.SplitV4.logisticFaceWeight
#print RectangleCLT.Companion.SplitV4.logisticTupleWeight
#print RectangleCLT.Companion.SplitV4.logisticGaussianScore
#print RectangleCLT.Companion.SplitV4.PolyhedralBaseConcentration
#print RectangleCLT.Companion.SplitV4.logisticPaddedNormals
#print RectangleCLT.Companion.SplitV4.logisticPaddedBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.symmetricNuclearNorm_eq_sum_abs_eigenvalues
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticMatrixEstimate_of_transition_and_signed_trace
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gammaMixture_integral_signed_test
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.PolyhedralBaseConcentration.reindex
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logisticPaddedBase_transitionMassBound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.weightedScore_entry_tendsto_of_bounded_weights

#print axioms RectangleCLT.Companion.SplitV4.symmetricNuclearNorm_eq_sum_abs_eigenvalues
#print axioms RectangleCLT.Companion.SplitV4.symmetricNuclearNorm_upperLeft_le
#print axioms RectangleCLT.Companion.SplitV4.logisticMatrixEstimate_of_transition_and_signed_trace
#print axioms RectangleCLT.Companion.SplitV4.gammaMixture_integral_signed_test
#print axioms RectangleCLT.Companion.SplitV4.PolyhedralBaseConcentration.reindex
#print axioms RectangleCLT.Companion.SplitV4.PolyhedralBaseConcentration.transitionMassBound
#print axioms RectangleCLT.Companion.SplitV4.logisticPaddedNormals_linearIndependent
#print axioms RectangleCLT.Companion.SplitV4.logisticPaddedNormals_joint_projection_tendsto
#print axioms RectangleCLT.Companion.SplitV4.integral_nonnegative_limit_le_uniform_bound
#print axioms RectangleCLT.Companion.SplitV4.weightedScore_firstGaussianBlock
#print axioms RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_entry_tendsto
#print axioms RectangleCLT.Companion.SplitV4.logisticPaddedScore_upperLeft_nuclear_sum_tendsto

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.SymmetricNuclearNorm",
    "RectangleCLTCompanion.SplitV4.ConcentratedBasePullback",
    "RectangleCLTCompanion.SplitV4.LogisticNormalRegularization",
    "RectangleCLTCompanion.SplitV4.LogisticMatrixLimits",
    "RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate",
    "RectangleCLTCompanion.SplitV4.LogisticPaddingLimits"]
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
      throwError "Unexpected axiom {ax} in logistic matrix infrastructure closure"
  logInfo m!"Audited {names.size} logistic matrix infrastructure theorem declarations; only the permitted three axioms."
  logInfo "Actual nuclear norm equals the eigenvalue absolute sum; selector contraction, signed Gamma reconstruction, duplicate/subsystem concentration pullback, and padded geometry are proved. The signed B5 trace budget remains explicit in the quantitative closure theorem."
