import RectangleCLTArxivV1.SupplementalGMinimalFactor
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_complementary_bound,
    ``RectangleCLTArxivV1.cap_covariance_minimal_factor,
    ``RectangleCLTArxivV1.cap_posSemidef_minimal_factor,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_sigma_bound,
    ``RectangleCLTArxivV1.cap_seeded_fourth_pattern_complementary_bound,
    ``RectangleCLTArxivV1.cap_seeded_single_sum_bound,
    ``RectangleCLTArxivV1.cap_seeded_single_pattern_bound,
    ``RectangleCLTArxivV1.cap_seededSplit_mixed_covariance,
    ``RectangleCLTArxivV1.capThirdHermite_conditional_mass_bound_ae,
    ``RectangleCLTArxivV1.capThirdHermite_integral_nuclear_le,
    ``RectangleCLTArxivV1.capWhitenedCopy_quadratic_budget,
    ``RectangleCLTArxivV1.cap_seeded_projection_hypotheses,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_bound,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_eq_second,
    ``RectangleCLTArxivV1.capWhitenedCopy_reconstruct,
    ``RectangleCLTArxivV1.capSoftFaceSecond_abs_le,
    ``RectangleCLTArxivV1.cap_seeded_small_angle_pattern_bound,
    ``RectangleCLTArxivV1.cap_seededWhole_mixed_covariance,
    ``RectangleCLTArxivV1.cap_pair_coefficient_integral_abs_le,
    ``RectangleCLTArxivV1.capWhitenedSlot_quadratic_budget,
    ``RectangleCLTArxivV1.cap_seeded_pair_pattern_bound,
    ``RectangleCLTArxivV1.capSecondHermite_conditional_mass_bound_ae,
    ``RectangleCLTArxivV1.capMatrix_translated_copy_bound_numeric,
    ``RectangleCLTArxivV1.capSecondHermite_integral_nuclear_le,
    ``RectangleCLTArxivV1.cap_pair_geometric_mean,
    ``RectangleCLTArxivV1.cap_seeded_pair_parallel_zero,
    ``RectangleCLTArxivV1.cap_seeded_fourth_pattern_decomposition,
    ``RectangleCLTArxivV1.cap_array_fourth_expectation_product_single_pair,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_patterns,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandA_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_seededFourthArrayExperiment_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandB_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_variableFourthPathIntegrandC_eq_rectangular_pattern,
    ``RectangleCLTArxivV1.cap_covariance_rank_pos,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_aestronglyMeasurable,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_measurable_expression,
    ``RectangleCLTArxivV1.capSeededTestIntegral_eq_seededLaw,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.cap_covariance_rank_le_dimension,
    ``RectangleCLTArxivV1.cap_convolutionFourthTensor_intrinsic_single_pair,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axs.toList}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_complementary_bound).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_posSemidef_minimal_factor do
    throwError "Missing actual proof step cap_posSemidef_minimal_factor"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_covariance_rank_pos do
    throwError "Missing actual proof step cap_covariance_rank_pos"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_patterns do
    throwError "Missing actual proof step cap_seededFourthRemainder_eq_patterns"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_array_fourth_expectation_product_single_pair do
    throwError "Missing actual proof step cap_array_fourth_expectation_product_single_pair"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_small_angle_pattern_bound do
    throwError "Missing actual proof step cap_seeded_small_angle_pattern_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_pair_pattern_bound do
    throwError "Missing actual proof step cap_seeded_pair_pattern_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_single_pattern_bound do
    throwError "Missing actual proof step cap_seeded_single_pattern_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.capMatrix_translated_copy_bound_numeric do
    throwError "Missing actual proof step capMatrix_translated_copy_bound_numeric"
  unless deps.visited.contains ``RectangleCLTArxivV1.capThirdHermite_conditional_mass_bound_ae do
    throwError "Missing actual proof step capThirdHermite_conditional_mass_bound_ae"
  unless deps.visited.contains ``RectangleCLTArxivV1.capSecondHermite_conditional_mass_bound_ae do
    throwError "Missing actual proof step capSecondHermite_conditional_mass_bound_ae"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_pair_contribution_eq_second do
    throwError "Missing actual proof step cap_seeded_pair_contribution_eq_second"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_pair_geometric_mean do
    throwError "Missing actual proof step cap_pair_geometric_mean"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_pair_parallel_zero do
    throwError "Missing actual proof step cap_seeded_pair_parallel_zero"
  unless deps.visited.contains ``RectangleCLTArxivV1.capWhitenedCopy_quadratic_budget do
    throwError "Missing actual proof step capWhitenedCopy_quadratic_budget"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seeded_projection_hypotheses do
    throwError "Missing actual proof step cap_seeded_projection_hypotheses"
  logInfo "PASS required actual route cap_seededFourthRemainder_rank_complementary_bound"
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_posSemidef_minimal_factor do
    throwError "Missing actual proof step cap_posSemidef_minimal_factor"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_aestronglyMeasurable do
    throwError "Missing actual proof step cap_seededFourthRemainder_aestronglyMeasurable"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_eq_measurable_expression do
    throwError "Missing actual proof step cap_seededFourthRemainder_eq_measurable_expression"
  unless deps.visited.contains ``RectangleCLTArxivV1.capSeededTestIntegral_measurable do
    throwError "Missing actual proof step capSeededTestIntegral_measurable"
  unless deps.visited.contains ``RectangleCLTArxivV1.capSeededTestIntegral_eq_seededLaw do
    throwError "Missing actual proof step capSeededTestIntegral_eq_seededLaw"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_intervalIntegrable do
    throwError "Missing actual proof step cap_seededFourthRemainder_intervalIntegrable"
  logInfo "PASS required actual route cap_seededFourthRemainder_rank_abs_intervalIntegrable"
