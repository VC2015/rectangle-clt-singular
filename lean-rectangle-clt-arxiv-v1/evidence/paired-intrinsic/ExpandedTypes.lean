import RectangleCLTArxivV1.PairedIntrinsicBennett
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.gaussian_smallerEnvelope_intrinsic,
    ``RectangleCLTArxivV1.gaussianMaximumMean_slepian_scale_div,
    ``RectangleCLTArxivV1.intrinsic_gaussian_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_gaussian_hessian_contraction,
    ``RectangleCLTArxivV1.intrinsic_weighted_gaussian_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_weighted_gaussian_hessian_contraction,
    ``RectangleCLTArxivV1.intrinsic_slepian_weighted_gradient_contraction,
    ``RectangleCLTArxivV1.intrinsic_slepian_weighted_hessian_contraction,
    ``RectangleCLTArxivV1.gaussian_integral_sum_fourthLocalMajorant_intrinsic,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_contraction,
    ``RectangleCLTArxivV1.intrinsic_gaussian_common_point_fourth_random_data,
    ``RectangleCLTArxivV1.intrinsic_gaussian_trapezoidal_sum_bound,
    ``RectangleCLTArxivV1.intrinsic_pairedGaussianRemainder_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementHessianTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementGradientTerm_le,
    ``RectangleCLTArxivV1.intrinsic_abs_largeIncrementRemainderTerm_le,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison_conditional,
    ``RectangleCLTArxivV1.intrinsic_largeIncrement_smooth_expectation_comparison,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison_bandwidth,
    ``RectangleCLTArxivV1.intrinsic_largeIncrementGaussianComparison,
    ``RectangleCLTArxivV1.intrinsic_gaussianComparisonWithLargeIncrementRemainders,
    ``RectangleCLTArxivV1.lemma_E1_intrinsic_comparison,
    ``RectangleCLTArxivV1.lemma_E3_paired_slepian,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_small_regime,
    ``RectangleCLTArxivV1.intrinsic_bennett_polynomial_large_regime,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT,
    ``RectangleCLTArxivV1.intrinsic_bennett_normalized_width_identity,
    ``RectangleCLTArxivV1.intrinsic_bennettPolynomialCLT_observations,
    ``RectangleCLTArxivV1.theorem_2_ii_intrinsic,
    ``RectangleCLTArxivV1.lemma_E4_truncated_bennett_maximum,
    ``RectangleCLTArxivV1.lemma_E4_truncated_bennett_maximum_zero_variance]
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
    ("scope", toJson "Actual intrinsic paired comparison and Theorem2(ii) Bennett transfer"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
