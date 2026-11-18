import RectangleCLTArxivV1.SupplementalHNonsimpleFiniteFrameChartGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_exists, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_normal, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_normal_coordinate, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_range, ``RectangleCLTArxivV1.nonsimpleFiniteFrame_vectorNormSq_append, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normalSum_eq_rotation, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_rotated_inner, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_rotated_section, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_measurable, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanAppend, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanAppend_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameTangentAppend, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartTangentIsometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartAffineIsometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartAffineIsometry_apply, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_isometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_range, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_gaussianKernel]
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
    ("scope", toJson "Actual orthonormal-extension finite-normal chart geometry, affine isometry, exact hyperplane range, norm/kernel factorization and physical rotated-section identity"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
