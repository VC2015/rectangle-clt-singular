import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.fourthTransportRadius,
    ``RectangleCLTArxivV1.continuous_fourthTransportRadius,
    ``RectangleCLTArxivV1.fourthFacetEvent,
    ``RectangleCLTArxivV1.fourthPairEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthFacetEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthPairEvent,
    ``RectangleCLTArxivV1.fourthFacetEvent_section,
    ``RectangleCLTArxivV1.gaussianThresholdSectionProbability_eq_strict_of_slack,
    ``RectangleCLTArxivV1.fourthFacet_fiber_coefficient_bound,
    ``RectangleCLTArxivV1.hard_facet_coefficient_le_fourth_event,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint,
    ``RectangleCLTArxivV1.fourthRidge_fiber_coefficient_bound,
    ``RectangleCLTArxivV1.fourthPairEvent_section,
    ``RectangleCLTArxivV1.hard_ridge_coefficient_le_fourth_event_strict,
    ``RectangleCLTArxivV1.gaussianPairBase_ae_no_boundary_of_slack,
    ``RectangleCLTArxivV1.gaussianPairBase_probability_le_eq_lt_of_slack,
    ``RectangleCLTArxivV1.hardGaussianRidgeDensity_eq_strict_of_slack,
    ``RectangleCLTArxivV1.hard_ridge_density_coefficient_le_fourth_event,
    ``RectangleCLTArxivV1.fourthFacetEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthPairEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthStratumEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthStratumEvent,
    ``RectangleCLTArxivV1.fourthStratumEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthStratumEvent_shared_point,
    ``RectangleCLTArxivV1.fourthOuterLayer,
    ``RectangleCLTArxivV1.measurableSet_fourthOuterLayer,
    ``RectangleCLTArxivV1.fourthStratumEvent_mem_outerLayer,
    ``RectangleCLTArxivV1.fourthStratumEvent_indicator_sum_le,
    ``RectangleCLTArxivV1.fourthStratumEvent_integral_sum_le,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_sum_le,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius,
    ``RectangleCLTArxivV1.continuous_fourthThreeFaceRadius,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_ge_one,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_add_le,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_fourth_integrable,
    ``RectangleCLTArxivV1.supplementalHRadius_abs_inner_small_span_le,
    ``RectangleCLTArxivV1.supplementalHRadius_face_abs_le,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_norm_le_threeFaceRadius,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_sum_le_threeFaceRadius,
    ``RectangleCLTArxivV1.fourthOuterLayer_shift_threshold,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_affine_sum_le,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_supporting_levels,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_coefficient_identity,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_off_diagonal,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_threeFace_tube,
    ``RectangleCLTArxivV1.residualThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.measurableSet_all_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_affine_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_threshold_ae_base_residualThresholdRegularity,
    ``RectangleCLTArxivV1.measurable_thresholdSignedSection_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianWeightedFacetIntegral,
    ``RectangleCLTArxivV1.fourthTransport_measurableSet_gaussianOutwardVariableTube,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_base_tube_bound,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedFacetIntegral_concentrated_base,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral,
    ``RectangleCLTArxivV1.hardGaussianFacetIntegral,
    ``RectangleCLTArxivV1.hardGaussianFacetIntegral_eq_signedSection,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_pairing_of_slack,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_eq_ridgeDensity,
    ``RectangleCLTArxivV1.hardFacetResidualDensity_zero_of_parallel_slack,
    ``RectangleCLTArxivV1.concentrated_base_threeFace_weighted_outward_tube,
    ``RectangleCLTArxivV1.ResidualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_residualThresholdRegularity,
    ``RectangleCLTArxivV1.supplementalHRadius,
    ``RectangleCLTArxivV1.supplementalHRadius_moment_le]
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then
      continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    let deps := deps.toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining"
    graph := graph.push <| Json.mkObj [
      ("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let axioms ← Lean.collectAxioms target
      let forbidden := axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
      unless forbidden.isEmpty do
        throwError "Unexpected axioms in {target}: {forbidden}"
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Independent actual H1 facet transport review; volume-AE thresholds only, not J_e or full all-threshold H1"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
