import RectangleCLTArxivV1.SupplementalGCapMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.dimensionCapComparisonConstant_pos,
    ``RectangleCLTArxivV1.dimensionCap_time_gain_ge_one,
    ``RectangleCLTArxivV1.dimensionCap_smooth_comparison,
    ``RectangleCLTArxivV1.dimensionCapBandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.dimensionCapBoundaryConstant_ge_one,
    ``RectangleCLTArxivV1.dimensionCapBoundaryCLT,
    ``RectangleCLTArxivV1.dimensionCapCoreConstant_ge_one,
    ``RectangleCLTArxivV1.dimensionCapCLT,
    ``RectangleCLTArxivV1.dimensionCapUniversalConstant_pos,
    ``RectangleCLTArxivV1.proposition_G1_dimension_log_cap,
    ``RectangleCLTArxivV1.capMinimumMajorant_nonneg,
    ``RectangleCLTArxivV1.capMinimumMajorant_continuousOn,
    ``RectangleCLTArxivV1.cap_abs_le_split_min,
    ``RectangleCLTArxivV1.cap_integral_majorant_bound,
    ``RectangleCLTArxivV1.cap_time_increment_le,
    ``RectangleCLTArxivV1.one_le_dimensionCapGain,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_admissible,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_pos,
    ``RectangleCLTArxivV1.dimensionCap_time_log_le,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_total_cost,
    ``RectangleCLTArxivV1.dimensionCap_large_bandwidth_rate,
    ``RectangleCLTArxivV1.dimensionCap_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.dimensionCapRate_le_coefficient,
    ``RectangleCLTArxivV1.dimensionCap_trivial_large_envelope,
    ``RectangleCLTArxivV1.cap_inv_sqrt_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_inv_mul_sqrt_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_integral_inv_sqrt,
    ``RectangleCLTArxivV1.cap_integral_inv_mul_sqrt,
    ``RectangleCLTArxivV1.cap_const_inv_continuousOn,
    ``RectangleCLTArxivV1.cap_const_inv_sqrt_continuousOn,
    ``RectangleCLTArxivV1.cap_const_inv_mul_sqrt_continuousOn,
    ``RectangleCLTArxivV1.cap_integral_const_inv,
    ``RectangleCLTArxivV1.cap_integral_const_inv_sqrt,
    ``RectangleCLTArxivV1.cap_integral_const_inv_mul_sqrt,
    ``RectangleCLTArxivV1.cap_integral_single_minimum,
    ``RectangleCLTArxivV1.cap_integral_pair_minimum_crossing,
    ``RectangleCLTArxivV1.cap_integral_pair_minimum,
    ``RectangleCLTArxivV1.cap_seed_single_ratio,
    ``RectangleCLTArxivV1.cap_seed_pair_ratio,
    ``RectangleCLTArxivV1.cap_single_ratio_log_le,
    ``RectangleCLTArxivV1.cap_pair_ratio_log_le,
    ``RectangleCLTArxivV1.cap_integrated_remainder_dimension_bound,
    ``RectangleCLTArxivV1.cap_integrated_remainder_direct_bound,
    ``RectangleCLTArxivV1.cap_integrated_remainder_min_bound,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_gaussian,
    ``RectangleCLTArxivV1.bounded_sum_expected_maximum,
    ``RectangleCLTArxivV1.direct_initialization_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.rectangleDistance_le_smoothingDiscrepancy_intrinsic,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound]
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
    ("scope", toJson "Independent G1 review: full generic cap FTC/integration/optimization and actual final Proposition G.1 types and dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.proposition_G1_dimension_log_cap).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_normalizedSeeded_time_comparison_bound do
    throwError "Missing actual G1 route cap_normalizedSeeded_time_comparison_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound do
    throwError "Missing actual G1 route cap_seededFourthRemainder_bounded_integral_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_integral_majorant_bound do
    throwError "Missing actual G1 route cap_integral_majorant_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_time_increment_le do
    throwError "Missing actual G1 route cap_time_increment_le"
  unless deps.visited.contains ``RectangleCLTArxivV1.direct_initialization_intrinsic_of_envelope do
    throwError "Missing actual G1 route direct_initialization_intrinsic_of_envelope"
  unless deps.visited.contains ``RectangleCLTArxivV1.rectangleDistance_le_smoothingDiscrepancy_intrinsic do
    throwError "Missing actual G1 route rectangleDistance_le_smoothingDiscrepancy_intrinsic"
  unless deps.visited.contains ``RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic do
    throwError "Missing actual G1 route integral_smallerEnvelope_directSlepian_intrinsic"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase do
    throwError "Missing actual G1 route intrinsicRectangleConcentration_seededSplitBase"
  unless deps.visited.contains ``RectangleCLTArxivV1.dimensionCapBandwidth_total_cost do
    throwError "Missing actual G1 route dimensionCapBandwidth_total_cost"
  unless deps.visited.contains ``RectangleCLTArxivV1.dimensionCap_large_bandwidth_rate do
    throwError "Missing actual G1 route dimensionCap_large_bandwidth_rate"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_gaussian do
    throwError "Missing actual G1 route intrinsicBoundaryCoefficient_le_gaussian"
  unless deps.visited.contains ``RectangleCLTArxivV1.bounded_sum_expected_maximum do
    throwError "Missing actual G1 route bounded_sum_expected_maximum"
  if deps.visited.contains ``RectangleCLTArxivV1.intrinsicBoundaryCLT then
    throwError "Used old uncapped CLT intrinsicBoundaryCLT"
  logInfo "PASS actual cap, supplied concentration/envelope, optimized bandwidth and noncircular C2 width route"
