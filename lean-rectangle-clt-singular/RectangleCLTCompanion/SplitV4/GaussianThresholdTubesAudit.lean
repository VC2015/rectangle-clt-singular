import RectangleCLTCompanion.SplitV4.GaussianThresholdTubes
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianNormalSectionMap

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_gaussianNormalSectionMap

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianNormalSectionMap_measurePreserving

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_gaussianNormalSectionMap_iff

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_gaussianNormalSectionMap

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.euclideanThresholdRadius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_euclideanThresholdRadius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.euclideanThresholdRadius_ge_one

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.euclideanThresholdRadius_add_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdEuclideanNormal_unit

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdFacet_fiber_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdSectionProbability_eq_strict

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianSectionPoint_comp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianSectionPoint_add_parameter

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.normal_integral_dominates_translated_fiber

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_gaussianFacetEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianFacetEvent_section

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_le_weighted_facet_event

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.gaussianNormalSectionMap,
    ``RectangleCLT.Companion.SplitV4.measurable_gaussianNormalSectionMap,
    ``RectangleCLT.Companion.SplitV4.gaussianNormalSectionMap_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.integrable_gaussianNormalSectionMap_iff,
    ``RectangleCLT.Companion.SplitV4.integral_gaussianNormalSectionMap,
    ``RectangleCLT.Companion.SplitV4.euclideanThresholdRadius,
    ``RectangleCLT.Companion.SplitV4.continuous_euclideanThresholdRadius,
    ``RectangleCLT.Companion.SplitV4.euclideanThresholdRadius_ge_one,
    ``RectangleCLT.Companion.SplitV4.euclideanThresholdRadius_add_le,
    ``RectangleCLT.Companion.SplitV4.thresholdEuclideanNormal_unit,
    ``RectangleCLT.Companion.SplitV4.thresholdFacet_fiber_lower,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdSectionProbability_eq_strict,
    ``RectangleCLT.Companion.SplitV4.gaussianSectionPoint_comp,
    ``RectangleCLT.Companion.SplitV4.gaussianSectionPoint_add_parameter,
    ``RectangleCLT.Companion.SplitV4.normal_integral_dominates_translated_fiber,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetBase,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetEvent,
    ``RectangleCLT.Companion.SplitV4.measurableSet_gaussianFacetEvent,
    ``RectangleCLT.Companion.SplitV4.gaussianFacetEvent_section,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdFirst_le_weighted_facet_event]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual Gaussian threshold tube transport"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual section Gaussian pushforward, unbounded integral/integrability transport, true normal-density fiber bounds, strict-face section probabilities and the actual one-face derivative-to-tube mass comparison."
