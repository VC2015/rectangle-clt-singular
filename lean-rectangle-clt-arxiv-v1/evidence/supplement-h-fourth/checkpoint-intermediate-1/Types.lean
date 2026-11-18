import RectangleCLTArxivV1.HFourthFromSuppliers
import RectangleCLTArxivV1.GapComparison
import RectangleCLTArxivV1.GapOptimization
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.positiveGapGain,
    ``RectangleCLTArxivV1.one_le_positiveGapGain,
    ``RectangleCLTArxivV1.positiveGapGain_det_le,
    ``RectangleCLTArxivV1.positiveGap_seed_ratio,
    ``RectangleCLTArxivV1.positiveGap_integral_minimum,
    ``RectangleCLTArxivV1.positiveGap_integrated_remainder_bound,
    ``RectangleCLTArxivV1.positiveGapBandwidth,
    ``RectangleCLTArxivV1.positiveGapRate,
    ``RectangleCLTArxivV1.positiveGapBandwidth_admissible,
    ``RectangleCLTArxivV1.positiveGapBandwidth_pos,
    ``RectangleCLTArxivV1.positiveGapBandwidth_total_cost,
    ``RectangleCLTArxivV1.positiveGap_large_bandwidth_rate,
    ``RectangleCLTArxivV1.positiveGap_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.positiveGapRate_le_coefficient,
    ``RectangleCLTArxivV1.positiveGap_trivial_large_envelope,
    ``RectangleCLTArxivV1.positiveGapMajorant,
    ``RectangleCLTArxivV1.positiveGapMajorant_nonneg,
    ``RectangleCLTArxivV1.positiveGapMajorant_continuousOn,
    ``RectangleCLTArxivV1.positiveGap_integral_majorant_bound,
    ``RectangleCLTArxivV1.positiveGap_time_increment_bound,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore_integrable_entry,
    ``RectangleCLTArxivV1.stronglyMeasurable_hFourthCubicGaussianScore_entry,
    ``RectangleCLTArxivV1.abs_hFourthCubicGaussianScore_entry_le,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore_isHermitian,
    ``RectangleCLTArxivV1.hFourth_integrable_nuclear_of_entry_bounds,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore_nuclear_integrable,
    ``RectangleCLTArxivV1.hFourth_conditional_matrix_sum_bound,
    ``RectangleCLTArxivV1.hFourthCubicRestorationOrder,
    ``RectangleCLTArxivV1.hFourth_cubic_restoration_order_bound,
    ``RectangleCLTArxivV1.hFourth_cubic_restoration_series_bound,
    ``RectangleCLTArxivV1.hFourth_sum_singleton_tuples,
    ``RectangleCLTArxivV1.hFourth_trace_rankOneSum_mul,
    ``RectangleCLTArxivV1.hFourth_trace_cubicScore_eq_integral,
    ``RectangleCLTArxivV1.hFourth_integrable_fixed_cubicScore_weight,
    ``RectangleCLTArxivV1.hFourth_fixed_cubic_restoration_order,
    ``RectangleCLTArxivV1.hFourth_cubic_series_interchange,
    ``RectangleCLTArxivV1.hFourth_cubic_array_series_interchange,
    ``RectangleCLTArxivV1.hFourth_cubic_series_term_eq_order,
    ``RectangleCLTArxivV1.hFourth_cubic_hasSum_expected_orders,
    ``RectangleCLTArxivV1.hFourth_conditional_translated_cubic_bound,
    ``RectangleCLTArxivV1.hFourth_conditional_translated_cubic_bound_numeric,
    ``RectangleCLTArxivV1.hFourthPairRestorationOrder,
    ``RectangleCLTArxivV1.hFourth_pair_restoration_order_bound,
    ``RectangleCLTArxivV1.hFourth_conditional_translated_pair_bound,
    ``RectangleCLTArxivV1.hFourth_conditional_translated_pair_bound_numeric,
    ``RectangleCLTArxivV1.hFourth_sum_pair_tuples,
    ``RectangleCLTArxivV1.hFourth_gaussian_outer_sum_eq_product,
    ``RectangleCLTArxivV1.hFourth_expectation_eq_single_pair_products,
    ``RectangleCLTArxivV1.hFourth_pair_supplier_of_angle_weighted,
    ``RectangleCLTArxivV1.hFourth_expectation_bound_of_matrix_suppliers]
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
