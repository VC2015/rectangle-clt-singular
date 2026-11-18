import RectangleCLTArxivV1.DerivativesIntrinsic
import RectangleCLTArxivV1.DirectIntrinsicEnvelope
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.thresholdLogistic,
    ``RectangleCLTArxivV1.thresholdEnvelope,
    ``RectangleCLTArxivV1.exp_one_le_four,
    ``RectangleCLTArxivV1.thresholdLogistic_pos,
    ``RectangleCLTArxivV1.thresholdLogistic_le_one,
    ``RectangleCLTArxivV1.thresholdEnvelope_pos,
    ``RectangleCLTArxivV1.hasDerivAt_thresholdLogistic,
    ``RectangleCLTArxivV1.hasDerivAt_log_thresholdEnvelope,
    ``RectangleCLTArxivV1.abs_log_thresholdEnvelope_derivative,
    ``RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval,
    ``RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference,
    ``RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed,
    ``RectangleCLTArxivV1.integral_logisticEnvelope_le_of_layer_bound_printed,
    ``RectangleCLTArxivV1.integral_logisticEnvelope_intrinsic,
    ``RectangleCLTArxivV1.averaged_translated_derivative_intrinsic,
    ``RectangleCLTArxivV1.intrinsicDerivative_inverse_power_eq_rpow,
    ``RectangleCLTArxivV1.smallerEnvelope_scaled_bounded_intrinsic_maximum,
    ``RectangleCLTArxivV1.smallerEnvelope_scaled_gaussian_intrinsic_maximum,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic]
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
    ("scope", toJson "Lemma A.1 literal threshold integration and direct intrinsic envelope proof endpoints"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
