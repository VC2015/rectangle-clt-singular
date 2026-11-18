import RectangleCLTArxivV1.SupplementalHSphericalPolygonSupport
import RectangleCLTArxivV1.SupplementalHSphericalPolygonChart
import RectangleCLTArxivV1.SupplementalHSphericalPolygonBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_generator_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_add_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_smul_mem,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_linear_nonneg,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_zero_face_coefficients,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_zero_face_eq_wedge,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_map,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_norm,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_inner,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_on_plane,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_eq_positivePlanarWedge,
    ``RectangleCLTArxivV1.sphericalPolygonFacetCoordinates_nonparallel,
    ``RectangleCLTArxivV1.sphericalPolygonFacetChart_angular_area,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_dot,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_unit,
    ``RectangleCLTArxivV1.sphericalPolygon_nonparallel_of_strict_facets,
    ``RectangleCLTArxivV1.sphericalPolygon_distinct_endpoint_pair,
    ``RectangleCLTArxivV1.sphericalPolygon_strict_facets_of_incidence,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_nonparallel,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_facet_angular_area,
    ``RectangleCLTArxivV1.sphericalPolygonGeneratedCone_eq_halfspaces,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_facet_angle,
    ``RectangleCLTArxivV1.sphericalPolygonOutwardNormals_inward,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_balance,
    ``RectangleCLTArxivV1.sphericalPolygon_generated_balance_norm_le]
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
