import RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairBisector

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairDifference

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairFirstLevel

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairSecondLevel

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_gaussianPairSectionPoint

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_gaussianPairBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_gaussianPairEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalPair_eq_withDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalPair_integral_density

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalPair_integrable_density_iff

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normalPair_integral_dominates_translated_fiber

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdRidge_fiber_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairBisector_abs_le_radius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint_comp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint_add_parameters

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent_section

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianPairEvent_weighted_mass

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPair_coefficient_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_le_weighted_pair_event

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.thresholdPairBisector,
    ``RectangleCLT.Companion.SplitV4.thresholdPairDifference,
    ``RectangleCLT.Companion.SplitV4.thresholdPairFirstLevel,
    ``RectangleCLT.Companion.SplitV4.thresholdPairSecondLevel,
    ``RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint,
    ``RectangleCLT.Companion.SplitV4.gaussianPairBase,
    ``RectangleCLT.Companion.SplitV4.measurable_gaussianPairSectionPoint,
    ``RectangleCLT.Companion.SplitV4.measurable_gaussianPairBase,
    ``RectangleCLT.Companion.SplitV4.gaussianPairEvent,
    ``RectangleCLT.Companion.SplitV4.measurableSet_gaussianPairEvent,
    ``RectangleCLT.Companion.SplitV4.normalPair_eq_withDensity,
    ``RectangleCLT.Companion.SplitV4.normalPair_integral_density,
    ``RectangleCLT.Companion.SplitV4.normalPair_integrable_density_iff,
    ``RectangleCLT.Companion.SplitV4.normalPair_integral_dominates_translated_fiber,
    ``RectangleCLT.Companion.SplitV4.thresholdRidge_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.thresholdPairBisector_abs_le_radius,
    ``RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint_comp,
    ``RectangleCLT.Companion.SplitV4.gaussianPairSectionPoint_add_parameters,
    ``RectangleCLT.Companion.SplitV4.gaussianPairEvent_section,
    ``RectangleCLT.Companion.SplitV4.gaussianPairEvent_weighted_mass,
    ``RectangleCLT.Companion.SplitV4.thresholdPair_coefficient_identity,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdMixed_le_weighted_pair_event]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual Gaussian ridge tube data or integration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual pair data, true 2D Gaussian density, weighted normal fibers, genuine ambient pair-event mass, exact angle cancellation and actual mixed-derivative-to-pair-event comparison."
