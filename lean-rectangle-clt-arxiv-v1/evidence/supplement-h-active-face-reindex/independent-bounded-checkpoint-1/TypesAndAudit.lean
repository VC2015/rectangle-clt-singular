import RectangleCLTArxivV1.SupplementalHActiveFaceReindex
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.activeFaceIndex,
    ``RectangleCLTArxivV1.activeFaceIndex_mem,
    ``RectangleCLTArxivV1.activeFaceIndex_injective,
    ``RectangleCLTArxivV1.mem_faces_iff_activeFaceIndex,
    ``RectangleCLTArxivV1.activeFace_card_le,
    ``RectangleCLTArxivV1.activeFaceNormals_eq_selectorFaceNormal,
    ``RectangleCLTArxivV1.activeFaceProjection_mulVec,
    ``RectangleCLTArxivV1.activeFace_nullWeight,
    ``RectangleCLTArxivV1.activeFace_piWeight,
    ``RectangleCLTArxivV1.activeFace_thetaWeight,
    ``RectangleCLTArxivV1.activeFace_selectorWeight_physical,
    ``RectangleCLTArxivV1.sum_activeFace_values,
    ``RectangleCLTArxivV1.sum_activeFace_first_weight_physical,
    ``RectangleCLTArxivV1.sum_active_selectorWeight_physical,
    ``RectangleCLTArxivV1.selectorWeight_zero_of_faces_empty]
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
      let axioms ← Lean.collectAxioms target
      let forbidden := axioms.filter fun n => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains n
      unless forbidden.isEmpty do
        throwError "Unexpected axioms in {target}: {forbidden}"
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Exact active physical face enumeration and weighted tuple sums"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
