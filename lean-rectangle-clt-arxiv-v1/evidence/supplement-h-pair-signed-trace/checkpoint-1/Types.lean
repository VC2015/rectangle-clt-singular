import RectangleCLTArxivV1.SupplementalHPairPowerTrace
import RectangleCLTArxivV1.SupplementalHPairTraceRestoration
import RectangleCLTArxivV1.SupplementalHPairPhysicalTrace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.supplementalHPairTraceConstant,
    ``RectangleCLTArxivV1.supplementalHPairTraceConstant_nonneg,
    ``RectangleCLTArxivV1.supplementalHSoftPairPowerTrace,
    ``RectangleCLTArxivV1.supplementalH_softPairPowerTrace_concentrated_base,
    ``RectangleCLTArxivV1.supplementalHSoftPairTrace,
    ``RectangleCLTArxivV1.supplementalHSoftPairTrace_eq_binomial,
    ``RectangleCLTArxivV1.supplementalH_softPairTrace_concentrated_base,
    ``RectangleCLTArxivV1.sum_activeFace_pair_weight_physical,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalTrace,
    ``RectangleCLTArxivV1.integrable_gaussian_pair_radial_selector_physical,
    ``RectangleCLTArxivV1.supplementalHPairPhysicalTrace_eq_softTrace,
    ``RectangleCLTArxivV1.intrinsicRectangleConcentration_pairPhysicalTrace]
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
    ("scope", toJson "Actual Gamma averaged positive mass, normal-square and complete native ridge surface budgets"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
