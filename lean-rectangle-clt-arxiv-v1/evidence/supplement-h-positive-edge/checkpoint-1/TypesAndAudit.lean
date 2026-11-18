import RectangleCLTArxivV1.SupplementalHPositiveEdgeSum
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.positiveRidge_fiber_of_kernel,
    ``RectangleCLTArxivV1.positiveRidge_angle_second_fiber,
    ``RectangleCLTArxivV1.positiveRidge_angle_normSq_fourth_fiber,
    ``RectangleCLTArxivV1.positiveRidge_coefficient_le_event_strict,
    ``RectangleCLTArxivV1.positiveRidge_coefficient_le_event,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient,
    ``RectangleCLTArxivV1.fourthStratumEvent_integral_sum_le_power,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_sum_of_fibers,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_second_bound,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_fourth_bound,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_second_threeFace_bound,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_fourth_threeFace_bound]
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
    ("scope", toJson "Actual positive edge second/fourth radius fibers and disjoint Gaussian transport"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
