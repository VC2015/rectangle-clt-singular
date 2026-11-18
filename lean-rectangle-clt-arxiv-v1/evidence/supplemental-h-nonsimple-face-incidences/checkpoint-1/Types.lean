import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCofaces
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceConormal
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCoverage
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceTubes
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimple_exactStratum_move_to_active_subset, ``RectangleCLTArxivV1.nonsimple_supporting_pair_has_actual_stratum, ``RectangleCLTArxivV1.nonsimple_pair_normalSpace_rank, ``RectangleCLTArxivV1.nonsimple_supporting_pair_has_actual_ridge, ``RectangleCLTArxivV1.NonsimpleRidgeAt, ``RectangleCLTArxivV1.nonsimpleRidgeAtFintype, ``RectangleCLTArxivV1.nonsimpleIncidentDirection, ``RectangleCLTArxivV1.nonsimpleIncidentProjection, ``RectangleCLTArxivV1.nonsimpleIncidentConormal, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_mem, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_inner, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_zero_on_ridge, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_strict_on_other, ``RectangleCLTArxivV1.nonsimpleRidgeAt_exists_other_active, ``RectangleCLTArxivV1.nonsimpleIncidentProjection_ne_zero, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_unit, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_mem, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_zero_on_ridge, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_strict_on_other, ``RectangleCLTArxivV1.nonsimpleIncidentConormal_nonneg, ``RectangleCLTArxivV1.nonsimple_nonzero_polar_covered_by_actual_incidence, ``RectangleCLTArxivV1.NonsimpleCodimThreeFace, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_disjoint, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_indicator_sum_le, ``RectangleCLTArxivV1.nonsimpleFaceNormalEvent_integral_sum_le]
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
    ("scope", toJson "Independent checked new nonsimple coface construction, canonical conormal, actual polar-ray incidence coverage and generic normal tubes"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
