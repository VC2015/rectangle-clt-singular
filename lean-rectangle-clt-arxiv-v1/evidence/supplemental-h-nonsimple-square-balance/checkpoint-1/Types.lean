import RectangleCLTArxivV1.SupplementalHNonsimpleSquareBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleSquareEdgeLeft, ``RectangleCLTArxivV1.nonsimpleSquareEdgeRight, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale_pos, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale_sq, ``RectangleCLTArxivV1.nonsimpleSquareRawConormals, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_unit, ``RectangleCLTArxivV1.nonsimpleSquareEdge_distinct, ``RectangleCLTArxivV1.nonsimpleSquareEdge_pair_injective, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_inner, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_zero, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_strict, ``RectangleCLTArxivV1.nonsimpleSquareEdge_sum_ne_zero, ``RectangleCLTArxivV1.nonsimpleSquareEdge_sub_ne_zero, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects_nonneg, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects_zero, ``RectangleCLTArxivV1.nonsimpleSquare_polar_third_nonpos, ``RectangleCLTArxivV1.nonsimpleSquare_polar_third_zero, ``RectangleCLTArxivV1.nonsimpleSquare_polar_zero_pair_is_edge, ``RectangleCLTArxivV1.nonsimpleSquare_polar_edge_multiple, ``RectangleCLTArxivV1.nonsimpleSquare_nonzero_polar_incident_coverage, ``RectangleCLTArxivV1.nonsimpleSquare_normal_span_eq_top, ``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance, ``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance_norm_le]
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
    if (#[``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance,
        ``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance_norm_le]).contains target then
      if ci.type.isForall then
        throwError "Final concrete square balance unexpectedly has a parameter or supplier hypothesis: {target}"
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
    ("scope", toJson "Actual nonsimple square-cone four-edge spherical balance: all incidence and polar-ray coverage inputs discharged"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
