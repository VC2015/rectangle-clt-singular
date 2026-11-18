import RectangleCLTArxivV1.SupplementalGCapOptimization
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.dimensionCapGain,
    ``RectangleCLTArxivV1.dimensionCapBandwidth,
    ``RectangleCLTArxivV1.dimensionCapRate,
    ``RectangleCLTArxivV1.one_le_dimensionCapGain,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_admissible,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_pos,
    ``RectangleCLTArxivV1.dimensionCap_time_log_le,
    ``RectangleCLTArxivV1.dimensionCapBandwidth_total_cost,
    ``RectangleCLTArxivV1.dimensionCap_large_bandwidth_rate,
    ``RectangleCLTArxivV1.dimensionCap_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.dimensionCapRate_le_coefficient,
    ``RectangleCLTArxivV1.dimensionCap_trivial_large_envelope]
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
    ("scope", toJson "Actual small-angle pair copy expectation and normalized remainder"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
