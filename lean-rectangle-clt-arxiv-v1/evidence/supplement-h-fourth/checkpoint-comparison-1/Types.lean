import RectangleCLTArxivV1.GapMain
import RectangleCLTArxivV1.HFourthOriginalBound
import RectangleCLTArxivV1.HFourthSeededScales
import RectangleCLTArxivV1.HFourthPhysicalMatrixTransport
import RectangleCLTArxivV1.HFourthPairIndexTransport
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.GapNormalizedMatrixEstimates,
    ``RectangleCLTArxivV1.positiveGapComparisonConstant,
    ``RectangleCLTArxivV1.positiveGapComparisonConstant_pos,
    ``RectangleCLTArxivV1.positiveGap_normalized_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGap_normalized_remainder_majorant_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGap_normalized_time_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapSmoothComparisonConstant,
    ``RectangleCLTArxivV1.positiveGapSmoothComparisonConstant_pos,
    ``RectangleCLTArxivV1.positiveGap_smooth_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapBandwidthConstant,
    ``RectangleCLTArxivV1.positiveGapBandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGapBoundaryConstant,
    ``RectangleCLTArxivV1.positiveGapBoundaryConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGap_boundary_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapCoreConstant,
    ``RectangleCLTArxivV1.positiveGapCoreConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGap_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_original_expectation_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_seed_scale_range,
    ``RectangleCLTArxivV1.hFourth_normalized_seed_scale_range,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore_eq_selectorScore,
    ``RectangleCLTArxivV1.measurable_hFourthCubicGaussianScore_nuclear,
    ``RectangleCLTArxivV1.hFourth_cubic_matrix_sum_physical_transport,
    ``RectangleCLTArxivV1.hFourth_pair_matrix_sum_physical_transport,
    ``RectangleCLTArxivV1.hFourth_pair_nuclear_integral_add_comm,
    ``RectangleCLTArxivV1.hFourth_pair_supplier_of_angle_weighted_front]
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
    ("scope", toJson "Explicit-intermediate H fourth derivative assembly from cubic/pair matrix suppliers, and scalar gap integration/optimization"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
