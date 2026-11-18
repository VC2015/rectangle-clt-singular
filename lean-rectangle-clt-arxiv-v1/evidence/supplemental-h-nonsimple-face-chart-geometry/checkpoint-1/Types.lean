import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleFaceChartBasis_exists, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis_normal, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis_normal_coordinate, ``RectangleCLTArxivV1.nonsimpleFaceChart, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart, ``RectangleCLTArxivV1.nonsimpleFaceChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFaceChart_range, ``RectangleCLTArxivV1.nonsimple_vectorNormSq_append, ``RectangleCLTArxivV1.nonsimpleFaceChart_normSq, ``RectangleCLTArxivV1.nonsimpleFaceChart_normalSum_eq_rotation, ``RectangleCLTArxivV1.nonsimpleFaceChart_rotated_inner, ``RectangleCLTArxivV1.nonsimpleFaceChart_rotated_section, ``RectangleCLTArxivV1.nonsimpleFaceChart_measurable, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanAppend, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanAppend_normSq, ``RectangleCLTArxivV1.nonsimpleFaceTangentAppend, ``RectangleCLTArxivV1.nonsimpleFaceChartTangentIsometry, ``RectangleCLTArxivV1.nonsimpleFaceChartAffineIsometry, ``RectangleCLTArxivV1.nonsimpleFaceChartAffineIsometry_apply, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_isometry, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_range, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_normSq, ``RectangleCLTArxivV1.nonsimpleFaceChart_gaussianKernel]
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
    ("scope", toJson "Actual orthonormal-extension three-normal chart geometry, affine isometry, exact hyperplane range, norm/kernel factorization and physical rotated-section identity"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
