import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Kernel-derived direct project dependencies and the expanded endpoint types.
Mathlib has no dependencies on the later project namespaces, so omitting its
internal nodes cannot hide a project-to-project proof dependency. -/
open Lean Elab Command in
run_cmd do
  let targets := #[``GenericChaining.dirksen_expectation,
    ``GenericChaining.gamma2_le_gaussianWidth,
    ``RectangleCLTArxivV1.signedIndex_card,
    ``RectangleCLTArxivV1.signedMaximum_eq_norm,
    ``RectangleCLTArxivV1.signedAbsMaximum_eq_norm,
    ``RectangleCLTArxivV1.signed_incrementMaximum_eq_norm,
    ``RectangleCLTArxivV1.signedGaussianLinear,
    ``RectangleCLTArxivV1.signedDiscreteMetric_self,
    ``RectangleCLTArxivV1.signedDiscreteMetric_symm,
    ``RectangleCLTArxivV1.signedDiscreteMetric_triangle,
    ``RectangleCLTArxivV1.signedContrast_observation_measurable,
    ``RectangleCLTArxivV1.signedContrast_independent,
    ``RectangleCLTArxivV1.integral_signedContrast_zero,
    ``RectangleCLTArxivV1.signedContrast_discrete_bound,
    ``RectangleCLTArxivV1.sum_variance_signedContrast,
    ``RectangleCLTArxivV1.signedProcess_hasMixedTail,
    ``RectangleCLTArxivV1.bounded_sum_upper_tail,
    ``RectangleCLTArxivV1.bounded_sum_abs_tail,
    ``RectangleCLTArxivV1.signedVarianceMetric_eq_canonicalDist,
    ``RectangleCLTArxivV1.gamma1_eq_admissible_subsets,
    ``RectangleCLTArxivV1.gamma2_eq_admissible_subsets,
    ``RectangleCLTArxivV1.admissible_first_card,
    ``RectangleCLTArxivV1.gaussian_level_weight,
    ``RectangleCLTArxivV1.gamma1_metric_homogeneity,
    ``RectangleCLTArxivV1.gamma2_metric_homogeneity,
    ``RectangleCLTArxivV1.signed_dirksen_expectation,
    ``RectangleCLTArxivV1.signed_dirksen_expectation_log,
    ``RectangleCLTArxivV1.integral_sum_coordinate_sq,
    ``RectangleCLTArxivV1.integral_abs_le_one_of_second_moment,
    ``RectangleCLTArxivV1.signed_first_absolute_moment_le_one,
    ``RectangleCLTArxivV1.discreteCutoff_le_iff,
    ``RectangleCLTArxivV1.discreteCutoff_pos,
    ``RectangleCLTArxivV1.discreteCutoff_weight_le_log,
    ``RectangleCLTArxivV1.signedDiscreteNets_initial,
    ``RectangleCLTArxivV1.signedDiscreteNets_terminal,
    ``RectangleCLTArxivV1.signed_gamma1_discrete_le,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows,
    ``RectangleCLTArxivV1.gaussianLaw_ae_mem_factor_range,
    ``RectangleCLTArxivV1.gaussian_factor_exists,
    ``RectangleCLTArxivV1.signed_factorRows_norm_sq,
    ``RectangleCLTArxivV1.gaussianLaw_integral_signedContrast_sq,
    ``RectangleCLTArxivV1.gaussianLaw_signedCoordinate_ae_eq_of_zero_dist,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_ne_top,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_le,
    ``RectangleCLTArxivV1.gamma2_signedFactorRows_eq_range,
    ``RectangleCLTArxivV1.gaussianMaximum_signedFactorRows_ae_eq_range,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows_eq_range,
    ``RectangleCLTArxivV1.gaussianWidth_signedFactorRows_range,
    ``RectangleCLTArxivV1.gaussianMaximumMean_eq_of_covariance,
    ``RectangleCLTArxivV1.standardNormal_integral_abs,
    ``RectangleCLTArxivV1.sqrt_two_div_pi_le_gaussianMaximumMean,
    ``RectangleCLTArxivV1.expectedMaximumConstant_pos,
    ``RectangleCLTArxivV1.bounded_sum_expected_maximum,
    ``RectangleCLTArxivV1.bounded_sum_expected_maximum_factor_exists,
    ``RectangleCLTArxivV1.boundedIndependent_of_raw,
    ``RectangleCLTArxivV1.lemma_C2_expected_maximum,
    ``RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf]
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
    ("scope", toJson "Lemma C.2 endpoints and project proof dependencies"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
