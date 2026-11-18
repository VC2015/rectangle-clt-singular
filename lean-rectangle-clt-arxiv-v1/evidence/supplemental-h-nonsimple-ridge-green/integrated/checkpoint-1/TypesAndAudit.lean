import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenMass
import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenFacetPoint
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option pp.all true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.actualFacet_localFiniteThresholdRegularity,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_of_actualFacets,
    ``RectangleCLTArxivV1.exists_actual_facet_radial_green,
    ``RectangleCLTArxivV1.actualFacetOutwardConormal,
    ``RectangleCLTArxivV1.actualFacetSignedSupportDistance,
    ``RectangleCLTArxivV1.actualFacetGaussianBoundaryMass,
    ``RectangleCLTArxivV1.actualFacet_normal_ne_zero,
    ``RectangleCLTArxivV1.actualFacet_scale_pos,
    ``RectangleCLTArxivV1.actualFacetOutwardConormal_unit,
    ``RectangleCLTArxivV1.actualFacetGaussianBoundaryMass_nonneg,
    ``RectangleCLTArxivV1.actualFacet_finiteThresholdFirst_eq_boundaryMass_div,
    ``RectangleCLTArxivV1.actualFacet_threshold_mul_first_eq_signedDistance_mul_boundaryMass,
    ``RectangleCLTArxivV1.gaussianFiniteThreshold_radialTrace_eq_actualBoundary,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_has_nonzero_active_of_no_strictInterior,
    ``RectangleCLTArxivV1.ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_measure_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdCDF_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.integral_gaussianFiniteThreshold_indicator_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdRadialTrace_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.hardGaussianPairSectionProbability_zero_of_no_strictResidualInterior,
    ``RectangleCLTArxivV1.hardGaussianPairSignedSection_zero_of_no_strictResidualInterior,
    ``RectangleCLTArxivV1.thresholdPair_frame_levels_of_support,
    ``RectangleCLTArxivV1.actualFacet_pairResidual_nonzero_or_level,
    ``RectangleCLTArxivV1.actualFacet_pair_support_nonparallel,
    ``RectangleCLTArxivV1.HasStrictRetainedInterior,
    ``RectangleCLTArxivV1.exists_actual_retained_facet_presentation,
    ``RectangleCLTArxivV1.selected_retained_threshold_event_eq,
    ``RectangleCLTArxivV1.hardPairResidual_strictInterior_of_section_witness,
    ``RectangleCLTArxivV1.gaussianPairSectionPoint_eq_self_of_levels,
    ``RectangleCLTArxivV1.hardPairResidual_strictInterior_of_affine_witness,
    ``RectangleCLTArxivV1.hardPairResidual_support_level,
    ``RectangleCLTArxivV1.hardPairResidual_unitConormal_support_level,
    ``RectangleCLTArxivV1.exists_hardGaussianPairSection_Green_actualFacets,
    ``RectangleCLTArxivV1.hardGaussianPairSection_Green_of_actual_presentation,
    ``RectangleCLTArxivV1.exists_hardGaussianPairSection_Green_normalized,
    ``RectangleCLTArxivV1.HasStrictRidgeInterior,
    ``RectangleCLTArxivV1.hasStrictRidgeInterior_iff_residual,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.normals,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.levels,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.signedDistance,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.boundaryMass,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal_unit,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.boundaryMass_nonneg,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.signedDistance_eq_support,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.native_Green,
    ``RectangleCLTArxivV1.actualFacet_exists_ridgeFacetPresentation,
    ``RectangleCLTArxivV1.actualFacet_nativeRidgeTerms_zero_of_no_strictInterior,
    ``RectangleCLTArxivV1.actualFacet_exists_strict_support_point,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.exists_strict_support_point,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.exists_original_boundary_point,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.outwardConormal_orthogonal,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.normal_eq_scale_conormal,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.selected_support_on_section,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.section_event_iff_retained,
    ``RectangleCLTArxivV1.gaussianPairBase_mem_full_event_iff_residual,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.section_event_iff_original,
    ``RectangleCLTArxivV1.ActualRidgeFacetPresentation.normalDensity_mul_boundaryMass_eq_frameMass]
  let env ← getEnv
  let (_, st) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless (st.axioms.filter fun n => !allowed.contains n).isEmpty do
    throwError "Unexpected axiom: {st.axioms}"
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := (ci.type.getUsedConstants ++ (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])).toList.eraseDups.toArray
    let pdeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" || s.startsWith "Kane" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining" || s.startsWith "_private.Kane"
    graph := graph.push <| Json.mkObj [("name", toJson target.toString), ("direct_project_dependencies", toJson (pdeps.map Name.toString))]
    queue := pdeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [("name", toJson target.toString), ("expanded_type", toJson ty), ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [("axiom_union", toJson (st.axioms.map Name.toString)), ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
