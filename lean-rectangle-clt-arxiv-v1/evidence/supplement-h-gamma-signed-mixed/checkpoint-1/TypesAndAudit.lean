import RectangleCLTArxivV1.SupplementalHGammaRidgeTrace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.measurable_gaussianThresholdTrace_threshold,
    ``RectangleCLTArxivV1.integrable_thresholdSignedSection_of_unit,
    ``RectangleCLTArxivV1.hasDerivAt_gaussianThresholdTrace_update_of_slack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_gaussianThresholdTrace_update,
    ``RectangleCLTArxivV1.gaussianSignedFaceDensityBudget,
    ``RectangleCLTArxivV1.gaussianSignedFaceDensityBudget_nonneg,
    ``RectangleCLTArxivV1.norm_gaussianSignedFace_section_density_le,
    ``RectangleCLTArxivV1.gaussianThresholdTrace_update_increment_bound,
    ``RectangleCLTArxivV1.lipschitzWith_gaussianThresholdTrace_update,
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_gamma_signedFace_offset,
    ``RectangleCLTArxivV1.supplementalH_signedFace_soft_coarea,
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_gamma_threshold_average,
    ``RectangleCLTArxivV1.supplementalHSignedMixedKernel,
    ``RectangleCLTArxivV1.measurable_supplementalHSignedMixedKernel,
    ``RectangleCLTArxivV1.supplementalH_hasDerivAt_gamma_signedMixed_offset,
    ``RectangleCLTArxivV1.supplementalH_signedMixed_soft_coarea,
    ``RectangleCLTArxivV1.supplementalH_angle_zero_of_parallel,
    ``RectangleCLTArxivV1.supplementalH_angle_mul_signedMixedKernel,
    ``RectangleCLTArxivV1.norm_hardGaussianSignedRidgeTerm_le,
    ``RectangleCLTArxivV1.integrable_gamma_signedRidgeTerm,
    ``RectangleCLTArxivV1.supplementalH_signedMixed_angle_soft_coarea,
    ``RectangleCLTArxivV1.integrable_gaussian_logistic_power_pair,
    ``RectangleCLTArxivV1.supplementalH_signedRidge_soft_sum_coarea_scaled,
    ``RectangleCLTArxivV1.supplementalH_signedRidge_soft_sum_coarea]
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
    ("scope", toJson "Actual signed Gamma mixed coarea and native ridge trace"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
