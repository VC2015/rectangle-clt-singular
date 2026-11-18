import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartProduct
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv,
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv_apply,
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv_gaussian_preserving,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_measurable,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_append,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_gaussian_map,
    ``RectangleCLTArxivV1.nonsimpleChartDensity_append,
    ``RectangleCLTArxivV1.nonsimpleChartDensity_rotation,
    ``RectangleCLTArxivV1.nonsimpleChart_gaussian_map_of_rotated_prefix,
    ``RectangleCLTArxivV1.nonsimpleFrameSection_measurable,
    ``RectangleCLTArxivV1.nonsimpleFrameSection_chart_gaussian_map,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_density,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_tangentChart_integral,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_density_integrable,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_supporting_level,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_measurable,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_isometry,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_covers_closedFace,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_active_level,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_mem_closedFace_iff,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_closedFace_chart_integral,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_surface_integral]
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
