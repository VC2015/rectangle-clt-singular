import RectangleCLTArxivV1.EnvelopeExpectedMaximum
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.expectedMaximum_negative_budget_obstruction,
    ``RectangleCLTArxivV1.coordinate_sq_integrable_of_envelope_moment,
    ``RectangleCLTArxivV1.integrable_norm_sum_of_envelope_moment,
    ``RectangleCLTArxivV1.expected_maximum_under_envelope_moment,
    ``RectangleCLTArxivV1.lemma_E1_expected_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_maximum_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_le_exp_moment_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail,
    ``RectangleCLT.Companion.SplitV4.sumVector_ae_zero_of_envelope_budget_zero]
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
    ("scope", toJson "Lemma E.1 qualified nonnegative envelope budget; literal Bernstein/layercake route"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
