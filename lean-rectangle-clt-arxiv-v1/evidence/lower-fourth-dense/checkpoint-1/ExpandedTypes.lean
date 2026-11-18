import RectangleCLTArxivV1.LowerFourthParameters
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.lowerDenseAmplitude_width_identity,
    ``RectangleCLTArxivV1.tendsto_lowerDense_raw_width_scale,
    ``RectangleCLTArxivV1.lowerDenseAmplitude_moment_identity,
    ``RectangleCLTArxivV1.tendsto_lowerDense_theta,
    ``RectangleCLTArxivV1.eventually_lowerDenseAmplitude_ge_one,
    ``RectangleCLTArxivV1.lowerFamily_polynomialEnvelope_of_factor,
    ``RectangleCLTArxivV1.lowerFamily_polynomialFourth_of_moments,
    ``RectangleCLTArxivV1.eventually_lowerDense_envelope,
    ``RectangleCLTArxivV1.tendsto_lowerDense_fourth_factor,
    ``RectangleCLTArxivV1.eventually_lowerDense_fourth,
    ``RectangleCLTArxivV1.lowerDense_actual_rate_le_twelve_raw,
    ``RectangleCLTArxivV1.theorem_7_polynomial_envelope_lower,
    ``RectangleCLTArxivV1.theorem_7_fixed_envelope_fourth_lower,
    ``RectangleCLTArxivV1.exists_lowerDense_upper_constant,
    ``RectangleCLTArxivV1.lowerDense_four_rate,
    ``RectangleCLTArxivV1.tendsto_lowerFourth_dense_rate,
    ``RectangleCLTArxivV1.eventually_lowerFourth_fourth_factor,
    ``RectangleCLTArxivV1.eventually_lowerFourth_coordinate_fourth,
    ``RectangleCLTArxivV1.eventually_lowerFourth_membership,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_lower,
    ``RectangleCLTArxivV1.lowerFamily_normalizedObservationSum_eq,
    ``RectangleCLTArxivV1.fourthWidthRate_fixed_budget_identity,
    ``RectangleCLTArxivV1.exists_lowerFourth_upper_constant,
    ``RectangleCLTArxivV1.theorem_5_fourth_moment_two_sided]
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
    ("scope", toJson "Actual width-sensitive fixed-fourth and dense lower constructions"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
