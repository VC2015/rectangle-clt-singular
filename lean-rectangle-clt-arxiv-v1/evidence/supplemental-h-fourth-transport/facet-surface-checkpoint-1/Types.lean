import RectangleCLTArxivV1.SupplementalHFourthTransportFacetSum
import RectangleCLTArxivV1.SupplementalHFourthTransportRegularity
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.fourthRidgeNormalPoint_supporting_levels,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_coefficient_identity,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_off_diagonal,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_threeFace_tube,
    ``RectangleCLTArxivV1.residualThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.measurableSet_all_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_affine_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_threshold_ae_base_residualThresholdRegularity,
    ``RectangleCLTArxivV1.measurable_thresholdSignedSection_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianWeightedFacetIntegral,
    ``RectangleCLTArxivV1.fourthTransport_measurableSet_gaussianOutwardVariableTube,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_base_tube_bound,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedFacetIntegral_concentrated_base]
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
    ("scope", toJson "Actual signed weighted facet J_f surface functional, genuine affine AE threshold/base regularity, and concentrated-base expectation estimate"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
