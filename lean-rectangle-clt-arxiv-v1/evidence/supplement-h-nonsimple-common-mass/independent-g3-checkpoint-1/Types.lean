import RectangleCLTArxivV1.SupplementalHNonsimpleFaceMass
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceFrame
import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass
import RectangleCLTArxivV1.SupplementalHNonsimpleGreenSum
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_inner_of_mem_span,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_supporting_level,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_union_supporting,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_univ_eq_sdiff_supporting,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_nonneg,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_frame_independent,
    ``RectangleCLTArxivV1.nonsimpleFaceGaussianMass_point_independent,
    ``RectangleCLTArxivV1.nonsimpleFaceBasis,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame_orthonormal,
    ``RectangleCLTArxivV1.nonsimpleFaceFrame_span,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_mem,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_levels,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_eq_frameProjection,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_unique,
    ``RectangleCLTArxivV1.nonsimpleFaceNormalPoint_eq_of_closedFace,
    ``RectangleCLTArxivV1.nonsimpleNativeNormals,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_nonneg,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_actualFaceMass,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_sdiff_eq_actualFaceMass,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_at_closedFacePoint,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs_pair,
    ``RectangleCLTArxivV1.nonsimpleOrderedFacetPairs_card,
    ``RectangleCLTArxivV1.half_ordered_pair_sum_eq_actual_ridge_sum,
    ``RectangleCLTArxivV1.nonsimple_signed_incidence_grouping]
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
