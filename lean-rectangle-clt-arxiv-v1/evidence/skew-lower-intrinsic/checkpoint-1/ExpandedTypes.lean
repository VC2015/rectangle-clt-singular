import RectangleCLTArxivV1.SkewLowerIntrinsic
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_sqrt_two_log,
    ``RectangleCLTArxivV1.independentAbsGaussianMean_ge_positiveMean,
    ``RectangleCLTArxivV1.sqrt_two_log_two_mul_div_tendsto,
    ``RectangleCLTArxivV1.tendsto_independentAbsGaussianMean_div_sqrt_two_log,
    ``RectangleCLTArxivV1.skewIntrinsicRate_eq_gaussianWidth,
    ``RectangleCLTArxivV1.skewIntrinsicRate_pos,
    ``RectangleCLTArxivV1.skewIntrinsicRate_div_old_tendsto,
    ``RectangleCLTArxivV1.old_skew_rate_tendsto_zero_of_intrinsic,
    ``RectangleCLTArxivV1.skew_intrinsic_distance_liminf,
    ``RectangleCLTArxivV1.skew_intrinsic_construction_properties,
    ``RectangleCLTArxivV1.theorem_3_intrinsic_canonical,
    ``RectangleCLTArxivV1.lowerNormalizedRows_sum_eq_raw_normalized,
    ``RectangleCLTArxivV1.theorem_3_intrinsic,
    ``RectangleCLTArxivV1.theorem_3_intrinsic_positive_dimensions,
    ``RectangleCLT.Companion.lowerConstructionProperties,
    ``RectangleCLT.Companion.lowerRawRows_attains_envelope,
    ``RectangleCLT.Companion.lowerRawRows_independent_coordinates,
    ``RectangleCLT.Companion.lowerRawRows_covariance,
    ``RectangleCLT.Companion.lowerTwoPointLaw_third_ge,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_eventual_lower_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability]
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
    ("scope", toJson "Theorem3 actual skewed observations and exact intrinsic Gaussian width"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
