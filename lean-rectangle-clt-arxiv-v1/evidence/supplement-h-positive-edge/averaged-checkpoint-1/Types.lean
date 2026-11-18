import RectangleCLTArxivV1.SupplementalHPositiveEdgeAveraged
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.continuous_fourthRidgeNormalPoint_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianRidgeDensity,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_nonneg,
    ``RectangleCLTArxivV1.measurable_positiveEdgeTubeCoefficient_threshold,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_abs_le,
    ``RectangleCLTArxivV1.positiveEdge_outer_affine_integral_eq,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_second_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_fourth_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeTubeCoefficient_second_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeTubeCoefficient_fourth_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeLeadingTerm_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdge_pairSectionProbability_eq,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_norm_sq_eq,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_sub_eq_ridgeLeading,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_eq_hardGaussianRidgeLeadingIntegral,
    ``RectangleCLTArxivV1.ae_hardGaussianRidgeLeadingIntegral_concentrated_base]
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
    ("scope", toJson "Explicit-intermediate H fourth derivative assembly from cubic/pair matrix suppliers, and scalar gap integration/optimization"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
