import RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.capBoundedIntegratedRemainderConstant_pos,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_majorant,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_integral_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound,
    ``RectangleCLTArxivV1.cap_integral_majorant_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase,
    ``RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope]
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
    ("scope", toJson "Literal actual bounded R4 integral with dimension cap: full types and dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
