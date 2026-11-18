import RectangleCLTArxivV1.SupplementalHSphericalPolygonPolar
import RectangleCLTArxivV1.SupplementalHSphericalPolygonDual
import RectangleCLTArxivV1.SupplementalHSphericalPolygonConormal
import RectangleCLTArxivV1.SupplementalHSphericalPolygonIncidence
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.sphericalPolygon_exists_orthogonal_pair,
    ``RectangleCLTArxivV1.sphericalPolygon_polar_linear_nonneg_of_one_zero,
    ``RectangleCLTArxivV1.sphericalPolygon_polar_linear_nonneg_of_two_zero,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_eq_nonsimple,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_nonneg_polar,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_supporting_pairs,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_mem_iff_incident_halfspaces,
    ``RectangleCLTArxivV1.sphericalPolygon_vector_eq_coordinate_normal,
    ``RectangleCLTArxivV1.sphericalPolygon_unit_conormal_positive,
    ``RectangleCLTArxivV1.sphericalPolygon_conormal_nonneg_smul,
    ``RectangleCLTArxivV1.sphericalPolygon_unit_conormal_unique,
    ``RectangleCLTArxivV1.sphericalPolygon_conormal_nonneg_smul_of_three,
    ``RectangleCLTArxivV1.sphericalPolygon_incident_ridge_balance,
    ``RectangleCLTArxivV1.sphericalPolygon_incident_ridge_balance_norm_le]
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
