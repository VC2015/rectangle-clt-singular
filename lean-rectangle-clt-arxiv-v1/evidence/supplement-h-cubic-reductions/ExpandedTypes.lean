import RectangleCLTArxivV1.SupplementalHQuantitativeEntropy
import RectangleCLTArxivV1.SupplementalHCubicMatrix
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_entropy_cardinality_budget,
    ``RectangleCLTArxivV1.supplementalH_integral_entropy_cardinality_bound,
    ``RectangleCLTArxivV1.supplementalHCubicSelectorScore,
    ``RectangleCLTArxivV1.supplementalH_cross_nuclear_le,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_decomposition,
    ``RectangleCLTArxivV1.supplementalHCubicMeanEnergy,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_nuclear_reduction]
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
    ("scope", toJson "Actual cubic Hermite positive-score decomposition and nuclear reduction, plus quantitative common-scale outer entropy; H1 geometric and final summed propositions remain open"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
