import RectangleCLTArxivV1.HFourthSeededRemainder
import RectangleCLTArxivV1.HFourthSeededPhysicalBase
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.hFourth_gap_or_parallel,
    ``RectangleCLTArxivV1.hFourth_copy_pair_zero_outside_gap,
    ``RectangleCLTArxivV1.hFourth_seeded_pattern_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.HFourthSeededMatrixEstimates,
    ``RectangleCLTArxivV1.hFourth_seeded_remainder_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_seeded_remainder_late_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourthRetainedSupportCoordinates,
    ``RectangleCLTArxivV1.hFourthPhysicalSeededBase,
    ``RectangleCLTArxivV1.hFourthRetainedSupportCoordinates_continuous,
    ``RectangleCLTArxivV1.hFourthPhysicalSeededBase_continuous,
    ``RectangleCLTArxivV1.hFourth_retained_support_reconstruct,
    ``RectangleCLTArxivV1.hFourth_seeded_base_eq_physical]
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
