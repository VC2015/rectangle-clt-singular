import RectangleCLTArxivV1.IntrinsicMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.relativeFourthMatrix_eq_printed,
    ``RectangleCLTArxivV1.relativeFreshFourthMatrix_eq_printed,
    ``RectangleCLTArxivV1.IntrinsicFourthBounds.relativeMomentBounds,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_logarithmic,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_maximum,
    ``RectangleCLTArxivV1.one_le_intrinsicBoundaryCoefficient,
    ``RectangleCLTArxivV1.intrinsicRelativeRate_nonneg,
    ``RectangleCLTArxivV1.intrinsicGaussianCoefficientConstant_pos,
    ``RectangleCLTArxivV1.intrinsicBoundaryCoefficient_le_gaussian,
    ``RectangleCLTArxivV1.intrinsicBandwidth_admissible,
    ``RectangleCLTArxivV1.intrinsicBandwidth_pos,
    ``RectangleCLTArxivV1.intrinsicBandwidth_le_sum,
    ``RectangleCLTArxivV1.intrinsic_log_one_add_square,
    ``RectangleCLTArxivV1.intrinsicComparisonLog_le_D_L,
    ``RectangleCLTArxivV1.intrinsicBandwidth_fourth_cost_le,
    ``RectangleCLTArxivV1.intrinsicBandwidth_total_cost_le,
    ``RectangleCLTArxivV1.large_intrinsicBandwidth_rate,
    ``RectangleCLTArxivV1.intrinsic_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.intrinsic_trivial_large_envelope,
    ``RectangleCLTArxivV1.intrinsic_min_one_mul_le,
    ``RectangleCLTArxivV1.intrinsicRelativeRate_le_coefficient,
    ``RectangleCLTArxivV1.intrinsicRelativeRate_capped_le_coefficient,
    ``RectangleCLTArxivV1.intrinsic_capped_of_le_one_and_mul,
    ``RectangleCLTArxivV1.intrinsicRelativeRate_envelope_le,
    ``RectangleCLTArxivV1.intrinsicRestorationConstant_pos,
    ``RectangleCLTArxivV1.intrinsic_seeded_matrix_estimate_with_copies,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_bound,
    ``RectangleCLTArxivV1.abs_directSlepianCubicTerm_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.directSlepian_fourth_copy_data_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.abs_directSlepianCopyFourthIntegrand_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.abs_directSlepianFourthPathIntegrand_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.abs_directSlepianFourthRemainder_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.abs_directSlepianDerivative_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.directSlepian_increment_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.direct_initialization_intrinsic_of_envelope,
    ``RectangleCLTArxivV1.intrinsicSeededDerivativeConstant_pos,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_cubic_product_rate,
    ``RectangleCLTArxivV1.intrinsic_seeded_relative_fourth_product_rate,
    ``RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound,
    ``RectangleCLTArxivV1.intrinsic_seeded_derivative_bounds,
    ``RectangleCLTArxivV1.intrinsic_seeded_time_comparison_bound,
    ``RectangleCLTArxivV1.intrinsicComparisonConstant_pos,
    ``RectangleCLTArxivV1.intrinsic_smooth_comparison_of_boundary_suppliers,
    ``RectangleCLTArxivV1.intrinsicCLT_of_uniform_boundary_suppliers,
    ``RectangleCLTArxivV1.one_le_intrinsicBoundaryRateConstant,
    ``RectangleCLTArxivV1.one_le_intrinsicCoreConstant,
    ``RectangleCLTArxivV1.intrinsicUniversalConstant_pos,
    ``RectangleCLTArxivV1.intrinsicBoundaryCLT,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_core,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_of_quadratic_bounds,
    ``RectangleCLTArxivV1.intrinsicEnvelopeCLT,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_factor_exists,
    ``RectangleCLTArxivV1.theorem_1_intrinsic,
    ``RectangleCLTArxivV1.theorem_1_intrinsic_clt]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
