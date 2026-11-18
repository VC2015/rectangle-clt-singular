import RectangleCLTArxivV1.SupplementalHNonsimpleExample
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleSquareScale, ``RectangleCLTArxivV1.nonsimpleSquareScale_pos, ``RectangleCLTArxivV1.nonsimpleSquareScale_sq, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals, ``RectangleCLTArxivV1.nonsimpleSquareNormals, ``RectangleCLTArxivV1.nonsimpleSquareDefect, ``RectangleCLTArxivV1.nonsimpleSquareNormals_dot, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals_normSq, ``RectangleCLTArxivV1.nonsimpleSquareNormals_unit, ``RectangleCLTArxivV1.nonsimpleSquare_four_normal_relation, ``RectangleCLTArxivV1.nonsimpleSquareCone, ``RectangleCLTArxivV1.nonsimpleSquareCone_eq_thresholdEvent, ``RectangleCLTArxivV1.nonsimpleSquare_strictInterior, ``RectangleCLTArxivV1.nonsimpleSquareDeletionWitness, ``RectangleCLTArxivV1.nonsimpleSquare_irredundant, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanRawNormals, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals_inner, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals_unit, ``RectangleCLTArxivV1.nonsimpleSquare_euclidean_strictInterior, ``RectangleCLTArxivV1.nonsimpleSquare_euclidean_irredundant, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals_mem_normalSpace, ``RectangleCLTArxivV1.nonsimpleSquare_normalSpace_eq_top, ``RectangleCLTArxivV1.nonsimpleSquare_normal_rank_three, ``RectangleCLTArxivV1.nonsimpleSquare_origin_exactStratum, ``RectangleCLTArxivV1.nonsimpleSquare_exactStratum_eq_singleton, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex_card, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex_is_nonsimple]
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
    ("scope", toJson "Constructed nonsimple square cone: actual four-facet geometry, normal rank three and native face index"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
