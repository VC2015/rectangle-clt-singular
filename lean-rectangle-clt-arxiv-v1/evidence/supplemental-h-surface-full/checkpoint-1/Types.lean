import RectangleCLTArxivV1.SupplementalHSurfaceFatou
import RectangleCLTArxivV1.SupplementalHActualRidgeEstimates
import RectangleCLTArxivV1.SupplementalHSurfaceEmpty
import RectangleCLTArxivV1.SupplementalHSurfaceMain
import RectangleCLTArxivV1.SupplementalHSurfaceFullDimensional
import RectangleCLTArxivV1.SupplementalHSurfaceFinal
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.integrable_abs_bound_of_ae_parameter_continuity,
    ``RectangleCLTArxivV1.actualFacet_weightedRidgeIntegral_concentrated_base,
    ``RectangleCLTArxivV1.exists_fixed_actualFacet_surface_concentrated_base_bound,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_zero_of_empty,
    ``RectangleCLTArxivV1.hardGaussianSignedRidgeTerm_zero_of_empty,
    ``RectangleCLTArxivV1.hardGaussianWeightedRidgeIntegral_zero_of_empty,
    ``RectangleCLTArxivV1.gaussianFiniteThresholdEvent_affine_empty,
    ``RectangleCLTArxivV1.hardGaussianSurfaceIntegrals_zero_empty_presentation,
    ``RectangleCLTArxivV1.exists_fixed_surface_bound_of_empty_or_strictInterior,
    ``RectangleCLTArxivV1.hasStrictFacetInterior_of_nonempty_interior,
    ``RectangleCLTArxivV1.HasStrictFacetInterior.nonempty_interior,
    ``RectangleCLTArxivV1.exists_fixed_surface_bound_of_empty_or_fullDimensional]
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
    ("scope", toJson "Actual all-threshold empty-or-full-dimensional H1 native surface expectations; fixed exact facet selection, nonsimple allowed, arbitrary singular base, genuine continuity/Fatou/subsystem concentration"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
