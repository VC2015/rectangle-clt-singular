import RectangleCLTCompanion.SplitV4.AveragedThreshold
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairSpan

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairSpan_finrank_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_ge_one

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_thresholdProjectionRadius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_thresholdProjectionRadius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPairSpan_projection_norm_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_add_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_abs_inner_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_face_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdPolyhedron

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_thresholdDot

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_thresholdPolyhedron

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdOuterLayer

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_thresholdOuterLayer

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.outerLayer_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.thresholdsFromBase

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptiveThresholdEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurableSet_adaptiveThresholdEvent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptiveThresholdEvent_section

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.adaptive_section_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.concentratedBase_adaptiveLayer_average

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.concentratedBase_gaussian_adaptiveLayer_average

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptiveOutwardTube

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptiveOutwardTube_disjoint

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptive_displacement_le_reciprocal_radius

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptive_radius_at_endpoint_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptiveOutwardTube_subset_outerLayer

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ridgeRectangle_mem_adaptiveOutwardTube

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptive_facet_gaussian_integral_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.adaptive_ridge_gaussian_integral_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdCDF

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdFirst

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdMixed

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdTrace

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.thresholdPairSpan,
    ``RectangleCLT.Companion.SplitV4.thresholdPairSpan_finrank_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_ge_one,
    ``RectangleCLT.Companion.SplitV4.measurable_thresholdProjectionRadius,
    ``RectangleCLT.Companion.SplitV4.continuous_thresholdProjectionRadius,
    ``RectangleCLT.Companion.SplitV4.thresholdPairSpan_projection_norm_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_add_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_abs_inner_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_face_le,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
    ``RectangleCLT.Companion.SplitV4.thresholdPolyhedron,
    ``RectangleCLT.Companion.SplitV4.measurable_thresholdDot,
    ``RectangleCLT.Companion.SplitV4.measurableSet_thresholdPolyhedron,
    ``RectangleCLT.Companion.SplitV4.thresholdOuterLayer,
    ``RectangleCLT.Companion.SplitV4.measurableSet_thresholdOuterLayer,
    ``RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase,
    ``RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.outerLayer_le,
    ``RectangleCLT.Companion.SplitV4.thresholdsFromBase,
    ``RectangleCLT.Companion.SplitV4.adaptiveThresholdEvent,
    ``RectangleCLT.Companion.SplitV4.measurableSet_adaptiveThresholdEvent,
    ``RectangleCLT.Companion.SplitV4.adaptiveThresholdEvent_section,
    ``RectangleCLT.Companion.SplitV4.ConcentratedThresholdBase.adaptive_section_le,
    ``RectangleCLT.Companion.SplitV4.concentratedBase_adaptiveLayer_average,
    ``RectangleCLT.Companion.SplitV4.concentratedBase_gaussian_adaptiveLayer_average,
    ``RectangleCLT.Companion.SplitV4.adaptiveOutwardTube,
    ``RectangleCLT.Companion.SplitV4.adaptiveOutwardTube_disjoint,
    ``RectangleCLT.Companion.SplitV4.adaptive_displacement_le_reciprocal_radius,
    ``RectangleCLT.Companion.SplitV4.adaptive_radius_at_endpoint_lower,
    ``RectangleCLT.Companion.SplitV4.adaptiveOutwardTube_subset_outerLayer,
    ``RectangleCLT.Companion.SplitV4.ridgeRectangle_mem_adaptiveOutwardTube,
    ``RectangleCLT.Companion.SplitV4.adaptive_facet_gaussian_integral_lower,
    ``RectangleCLT.Companion.SplitV4.adaptive_ridge_gaussian_integral_lower,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdCDF,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdFirst,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdMixed,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdTrace,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual Gaussian threshold geometry or averaging"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual pair-span Gaussian radius/moments, concentrated-base adaptive-layer averaging, disjoint outward geometry and weighted normal-fiber integrals. The full threshold-derivative layer comparison remains a separate endpoint."
