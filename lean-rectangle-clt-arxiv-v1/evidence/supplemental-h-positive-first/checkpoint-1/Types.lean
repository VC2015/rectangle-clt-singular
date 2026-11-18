import RectangleCLTArxivV1.SupplementalHWeightedGammaPrimitive
import RectangleCLTArxivV1.PositiveFirstCoarea
import RectangleCLTArxivV1.PositiveFirstCoareaBounds
import RectangleCLTArxivV1.PositiveFirstCoareaDerivative
import RectangleCLTArxivV1.PositiveGammaFirstCoarea
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.measurable_gaussianFiniteWeightedThreshold,
    ``RectangleCLTArxivV1.abs_gaussianFiniteWeightedThreshold_le,
    ``RectangleCLTArxivV1.weighted_logistic_power_eq_gamma_weighted_threshold,
    ``RectangleCLTArxivV1.positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.measurable_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.integrable_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.integral_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.positiveGaussianPlaneTest_eq_actual_projection,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_planeTest_eq,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteWeightedSection_planeTest_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_positivePlaneThreshold_update_of_slack,
    ``RectangleCLTArxivV1.norm_positivePlaneThreshold_le_two,
    ``RectangleCLTArxivV1.norm_positiveMassThreshold_le_one,
    ``RectangleCLTArxivV1.norm_positivePlaneFirstSection_density_le,
    ``RectangleCLTArxivV1.norm_positiveMassFirstSection_density_le,
    ``RectangleCLTArxivV1.lipschitzWith_weightedThreshold_update_of_section_bound,
    ``RectangleCLTArxivV1.lipschitzWith_positivePlaneThreshold_update,
    ``RectangleCLTArxivV1.lipschitzWith_positiveMassThreshold_update,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMassThreshold_update_of_slack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_positiveMassThreshold_update,
    ``RectangleCLTArxivV1.ae_hasDerivAt_positivePlaneThreshold_update,
    ``RectangleCLTArxivV1.weighted_first_soft_coarea_of_hard_derivative,
    ``RectangleCLTArxivV1.positiveMass_soft_first_coarea,
    ``RectangleCLTArxivV1.positivePlane_soft_first_coarea]
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
    ("scope", toJson "Actual first positive mass and pair-plane Gaussian coarea and Gamma identity, genuine integrable test preserved, global primitive bounds and first-coordinate Lipschitz, arbitrary dependent unit families"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
