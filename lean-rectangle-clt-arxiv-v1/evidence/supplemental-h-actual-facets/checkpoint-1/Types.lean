import RectangleCLTArxivV1.SupplementalHActualFacetGeometry
import RectangleCLTArxivV1.SupplementalHActualFacetRegularity
import RectangleCLTArxivV1.SupplementalHActualFacetSelection
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.HasStrictFacetInterior,
    ``RectangleCLTArxivV1.HasIrredundantFacetWitnesses,
    ``RectangleCLTArxivV1.actualFacet_pair_affine_inconsistent,
    ``RectangleCLTArxivV1.actualFacet_triple_affine_inconsistent,
    ``RectangleCLTArxivV1.actualFacet_pair_residual_slack,
    ``RectangleCLTArxivV1.actualFacet_triple_residual_slack,
    ``RectangleCLTArxivV1.actualFacet_residualThresholdRegularity,
    ``RectangleCLTArxivV1.actualFacet_abs_weightedFacetIntegral_le_threeFace_tube,
    ``RectangleCLTArxivV1.FacetPresentationEquivalent,
    ``RectangleCLTArxivV1.exists_irredundant_facet_subfamily,
    ``RectangleCLTArxivV1.exists_actual_facet_presentation,
    ``RectangleCLTArxivV1.exists_actual_facet_weightedIntegral_bound]
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
    ("scope", toJson "Actual facet finite redundancy removal and genuine pointwise residual pair/triple slack to the actual weighted facet tube estimate"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
