import RectangleCLTArxivV1.SupplementalHCubicWeights
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.entropy_term_le_reference,
    ``RectangleCLTArxivV1.entropy_term_nonneg,
    ``RectangleCLTArxivV1.integrable_entropy_term,
    ``RectangleCLTArxivV1.entropy_term_common_factor,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_fixed_scale,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_log_ratio,
    ``RectangleCLTArxivV1.sum_face_tuples_cons,
    ``RectangleCLTArxivV1.sum_face_probability_products,
    ``RectangleCLTArxivV1.sum_selector_first_weight,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight,
    ``RectangleCLTArxivV1.sum_selector_first_weight_le,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight_le,
    ``RectangleCLTArxivV1.selector_extra_factors_binomial,
    ``RectangleCLTArxivV1.supplementalHSelectorMass,
    ``RectangleCLTArxivV1.supplementalHSelectorProjection,
    ``RectangleCLTArxivV1.supplementalHSelectorEntropy,
    ``RectangleCLTArxivV1.supplementalHSelectorRadialTrace,
    ``RectangleCLTArxivV1.supplementalH_selector_projected_reduction,
    ``RectangleCLTArxivV1.supplementalH_sum_weighted_selector_reduction,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_nonneg,
    ``RectangleCLTArxivV1.supplementalH_nonnegative_logConcave_mul,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_logConcave,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_logConcave,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_sub,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_add]
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
    ("scope", toJson "Actual arbitrary-length selector matrix reductions, cubic positive-factor log-concavity and outer entropy; quantitative H1 surfaces remain separate"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
