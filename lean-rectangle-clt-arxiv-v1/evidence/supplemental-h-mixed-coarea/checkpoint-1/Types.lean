import RectangleCLTArxivV1.SupplementalHMixedCoareaIntegral
import RectangleCLTArxivV1.SupplementalHMixedCoareaRegularity
import RectangleCLTArxivV1.SupplementalHMixedCoareaDerivative
import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.measurable_gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.integrable_gaussianFiniteWeightedSection,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedThreshold_update_eq_section_integral,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianFiniteWeightedThreshold_update,
    ``RectangleCLTArxivV1.gaussianFacetScore,
    ``RectangleCLTArxivV1.measurable_gaussianFacetScore,
    ``RectangleCLTArxivV1.integrable_gaussianFacetScore,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_score_eq,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteWeightedSection_score_of_slack,
    ``RectangleCLTArxivV1.MixedGaussianSectionSlack,
    ``RectangleCLTArxivV1.hasDerivAt_thresholdSignedSection_update_conditional_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianSignedFacetDensity_update_of_slack,
    ``RectangleCLTArxivV1.ResidualThresholdRegularity.mixedGaussianSectionSlack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_gaussianSignedFacetDensity_update,
    ``RectangleCLTArxivV1.abs_hardGaussianPairSignedSection_le,
    ``RectangleCLTArxivV1.gaussianMixedSectionDensityBudget,
    ``RectangleCLTArxivV1.gaussianMixedSectionDensityBudget_nonneg,
    ``RectangleCLTArxivV1.gaussianPDFReal_pair_sq_add_dimension_le,
    ``RectangleCLTArxivV1.thresholdSignedSection_update_eq_weightedThreshold,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_facetScore_eq_pairSignedSection,
    ``RectangleCLTArxivV1.gaussianSignedFacetDensity_update_eq_section_integral,
    ``RectangleCLTArxivV1.gaussianSignedFacetDensity_update_increment_bound,
    ``RectangleCLTArxivV1.lipschitzWith_gaussianSignedFacetDensity_update]
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
    ("scope", toJson "Actual local signed mixed coarea under selected double-residual slack and global uniform mixed signed-density Lipschitz, no full family independence"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
