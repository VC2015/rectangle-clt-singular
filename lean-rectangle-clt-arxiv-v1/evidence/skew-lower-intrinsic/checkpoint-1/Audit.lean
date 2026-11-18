import RectangleCLTArxivV1.SkewLowerIntrinsic
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianMaximumMean_le_sqrt_two_log,
    ``RectangleCLTArxivV1.independentAbsGaussianMean_ge_positiveMean,
    ``RectangleCLTArxivV1.sqrt_two_log_two_mul_div_tendsto,
    ``RectangleCLTArxivV1.tendsto_independentAbsGaussianMean_div_sqrt_two_log,
    ``RectangleCLTArxivV1.skewIntrinsicRate_eq_gaussianWidth,
    ``RectangleCLTArxivV1.skewIntrinsicRate_pos,
    ``RectangleCLTArxivV1.skewIntrinsicRate_div_old_tendsto,
    ``RectangleCLTArxivV1.old_skew_rate_tendsto_zero_of_intrinsic,
    ``RectangleCLTArxivV1.skew_intrinsic_distance_liminf,
    ``RectangleCLTArxivV1.skew_intrinsic_construction_properties,
    ``RectangleCLTArxivV1.theorem_3_intrinsic_canonical,
    ``RectangleCLTArxivV1.lowerNormalizedRows_sum_eq_raw_normalized,
    ``RectangleCLTArxivV1.theorem_3_intrinsic,
    ``RectangleCLTArxivV1.theorem_3_intrinsic_positive_dimensions,
    ``RectangleCLT.Companion.lowerConstructionProperties,
    ``RectangleCLT.Companion.lowerRawRows_attains_envelope,
    ``RectangleCLT.Companion.lowerRawRows_independent_coordinates,
    ``RectangleCLT.Companion.lowerRawRows_covariance,
    ``RectangleCLT.Companion.lowerTwoPointLaw_third_ge,
    ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_eventual_lower_from_F1,
    ``RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
  logInfo m!"PASS: {targets.size} strict transitive audits."
