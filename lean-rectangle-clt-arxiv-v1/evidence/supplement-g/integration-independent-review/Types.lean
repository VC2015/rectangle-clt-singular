import RectangleCLTArxivV1.SupplementalGCapIntegration
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_inv_sqrt_intervalIntegrable,
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
    ``RectangleCLTArxivV1.cap_integrated_remainder_min_bound]
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
