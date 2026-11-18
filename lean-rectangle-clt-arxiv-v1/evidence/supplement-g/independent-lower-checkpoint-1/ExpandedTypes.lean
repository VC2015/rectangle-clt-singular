import RectangleCLTArxivV1.SupplementalGMinimalFactor
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_posSemidef_minimal_factor,
    ``RectangleCLTArxivV1.cap_covariance_minimal_factor,
    ``RectangleCLTArxivV1.cap_covariance_rank_pos,
    ``RectangleCLTArxivV1.cap_covariance_rank_le_dimension,
    ``RectangleCLTArxivV1.cap_convolutionFourthTensor_intrinsic_single_pair,
    ``RectangleCLTArxivV1.cap_array_fourth_expectation_product_single_pair,
    ``RectangleCLTArxivV1.cap_seeded_fourth_pattern_decomposition,
    ``RectangleCLTArxivV1.cap_pair_coefficient_integral_abs_le,
    ``RectangleCLTArxivV1.capSoftFaceSecond_abs_le,
    ``RectangleCLTArxivV1.cap_seeded_small_angle_pattern_bound,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_eq_second,
    ``RectangleCLTArxivV1.capMatrix_translated_copy_bound_numeric,
    ``RectangleCLTArxivV1.capThirdHermite_conditional_mass_bound_ae,
    ``RectangleCLTArxivV1.capSecondHermite_conditional_mass_bound_ae,
    ``RectangleCLTArxivV1.cap_seeded_single_pattern_bound,
    ``RectangleCLTArxivV1.cap_seeded_pair_pattern_bound,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_bound,
    ``RectangleCLTArxivV1.cap_seeded_single_sum_bound,
    ``RectangleCLTArxivV1.cap_seeded_pair_parallel_zero,
    ``RectangleCLTArxivV1.cap_seeded_fourth_pattern_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_sigma_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthArrayExperiment_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandA_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandB_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandC_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_patterns,
    ``RectangleCLTArxivV1.capWhitenedCopy_quadratic_budget,
    ``RectangleCLTArxivV1.capWhitenedCopy_reconstruct,
    ``RectangleCLTArxivV1.capWhitenedSlot_quadratic_budget,
    ``RectangleCLTArxivV1.cap_seeded_projection_hypotheses,
    ``RectangleCLTArxivV1.cap_seededSplit_mixed_covariance,
    ``RectangleCLTArxivV1.cap_seededWhole_mixed_covariance,
    ``RectangleCLTArxivV1.capSeededTestIntegral_eq_seededLaw,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_measurable_expression,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_aestronglyMeasurable,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_pair_geometric_mean,
    ``RectangleCLTArxivV1.capSecondHermite_integral_nuclear_le,
    ``RectangleCLTArxivV1.capThirdHermite_integral_nuclear_le]
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
    ("scope", toJson "Independent G3 review: literal actual rank covariance complementary remainder and genuine time integrability"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
