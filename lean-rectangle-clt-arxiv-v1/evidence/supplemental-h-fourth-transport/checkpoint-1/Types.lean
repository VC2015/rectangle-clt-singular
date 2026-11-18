import RectangleCLTArxivV1.SupplementalHFourthTransportData
import RectangleCLTArxivV1.SupplementalHFourthTransportFacet
import RectangleCLTArxivV1.SupplementalHFourthTransportRidge
import RectangleCLTArxivV1.SupplementalHFourthTransportSlack
import RectangleCLTArxivV1.SupplementalHFourthTransportGeometry
import RectangleCLTArxivV1.SupplementalHFourthTransportSum
import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.fourthTransportRadius,
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
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_affine_sum_le]
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
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Genuine generic-radius fourth-weight facet/ridge Gaussian transport, local affine slack, disjoint outward-tube finite sum, and actual three-face radius"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
