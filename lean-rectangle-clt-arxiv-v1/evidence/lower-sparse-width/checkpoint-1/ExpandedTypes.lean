import RectangleCLTArxivV1.LowerSparseWidthLimits
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.lowerSparseKhat_factor,
    ``RectangleCLTArxivV1.lowerSparse_logKhat_sub_bound,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_eq,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_factor,
    ``RectangleCLTArxivV1.lowerSparseCoordinateWidth_fourth,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_pos,
    ``RectangleCLTArxivV1.lowerSparse_cube_div_le_coordinateWidth_fourth,
    ``RectangleCLTArxivV1.lowerSparseRawWidth_le_intrinsicRate,
    ``RectangleCLTArxivV1.lowerSparseIntrinsicRate_le_raw,
    ``RectangleCLTArxivV1.eventually_lowerSparse_logKhat_sub_bound,
    ``RectangleCLTArxivV1.tendsto_lowerSparseKhat,
    ``RectangleCLTArxivV1.eventually_lowerSparseLog_bounds,
    ``RectangleCLTArxivV1.tendsto_lowerSparseLog_div_rareLog,
    ``RectangleCLTArxivV1.tendsto_lowerSparseCoordinateWidth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEll_cube_div,
    ``RectangleCLTArxivV1.tendsto_lowerSparseTheta,
    ``RectangleCLTArxivV1.tendsto_lowerSparseVariance,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEffectiveAmplitude,
    ``RectangleCLTArxivV1.tendsto_lowerSparseRawWidth]
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
    ("scope", toJson "Actual sparse width-sensitive numerical calibration under the stated regime"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
