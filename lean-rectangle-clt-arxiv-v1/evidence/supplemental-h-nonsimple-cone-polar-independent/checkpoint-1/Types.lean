import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCone
import RectangleCLTArxivV1.SupplementalHNonsimpleFacePolarLine
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.zero_mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.generator_mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_innerDual,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_coefficient_bound,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_isClosed,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_bipolar,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_mem_iff_polar,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_no_cancellation,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_isClosed,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff_polar,
    ``RectangleCLTArxivV1.nonsimple_polar_positive_endpoint,
    ``RectangleCLTArxivV1.nonsimple_polar_negative_endpoint,
    ``RectangleCLTArxivV1.nonsimple_polar_line_split,
    ``RectangleCLTArxivV1.nonsimple_polar_line_vector_decomposition,
    ``RectangleCLTArxivV1.nonsimple_zero_sum_slopes_both_signs,
    ``RectangleCLTArxivV1.nonsimple_polar_inner_slopes_both_signs,
    ``RectangleCLTArxivV1.nonsimple_polar_inner_line_split]
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
    ("scope", toJson "Actual finite generated cone support-face, native chart angular identification and arbitrary-edge polygon balance under explicit geometric halfspace completeness"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
