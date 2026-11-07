import RectangleCLTCompanion.SplitV4.AveragedThresholdBound
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdGeometryConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdGeometryConstant_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianAdaptiveOuterEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_gaussianAdaptiveOuterEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdsFromBase_one_zero

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.mem_gaussianAdaptiveOuterEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_gaussianThreshold_facet_term_le_mass

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.abs_gaussianThreshold_pair_term_le_mass

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_gaussianThresholdDerivative_for_averaging

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_abs_le_radius_moment

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_gaussianThresholdDerivative_base_succ

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_gaussianThresholdDerivative_base

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedThresholdConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedThresholdConstant_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_succ

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.mono_log

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedThresholdPaperConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedThresholdPaperConstant_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_of_log_le_two

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.threshold_dimensionLog_faces_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_rectangle_bound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.thresholdGeometryConstant,
    ``RectangleCLT.Companion.SplitV4.thresholdGeometryConstant_pos,
    ``RectangleCLT.Companion.SplitV4.gaussianAdaptiveOuterEvent,
    ``RectangleCLT.Companion.SplitV4.measurableSet_gaussianAdaptiveOuterEvent,
    ``RectangleCLT.Companion.SplitV4.thresholdsFromBase_one_zero,
    ``RectangleCLT.Companion.SplitV4.mem_gaussianAdaptiveOuterEvent,
    ``RectangleCLT.Companion.SplitV4.abs_gaussianThreshold_facet_term_le_mass,
    ``RectangleCLT.Companion.SplitV4.abs_gaussianThreshold_pair_term_le_mass,
    ``RectangleCLT.Companion.SplitV4.continuous_gaussianThresholdDerivative_for_averaging,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_abs_le_radius_moment,
    ``RectangleCLT.Companion.SplitV4.integrable_gaussianThresholdDerivative_base_succ,
    ``RectangleCLT.Companion.SplitV4.integrable_gaussianThresholdDerivative_base,
    ``RectangleCLT.Companion.SplitV4.averagedThresholdConstant,
    ``RectangleCLT.Companion.SplitV4.averagedThresholdConstant_pos,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_succ,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound,
    ``RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.mono_log,
    ``RectangleCLT.Companion.SplitV4.averagedThresholdPaperConstant,
    ``RectangleCLT.Companion.SplitV4.averagedThresholdPaperConstant_pos,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_of_log_le_two,
    ``RectangleCLT.Companion.SplitV4.threshold_dimensionLog_faces_le,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_rectangle_bound]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in full averaged Gaussian threshold derivative bound"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited full actual B.5: adaptive Gaussian threshold derivative layer bound, genuine arbitrary-base integrability, concentrated-base expectation bound, and original L=log(ep) rectangle normalization with universal constant."
