import RectangleCLTArxivV1.LowerBoundedCalibration
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.tendsto_lowerFamily_scale,
    ``RectangleCLTArxivV1.observationShift_amplitude_ratio_identity,
    ``RectangleCLTArxivV1.lowerFamily_theta_of_count,
    ``RectangleCLTArxivV1.tendsto_unmasked_observationShift_amplitude_ratio,
    ``RectangleCLTArxivV1.gaussianShift_amplitude_ratio_identity,
    ``RectangleCLTArxivV1.tendsto_unmasked_gaussianShift_amplitude_ratio,
    ``RectangleCLTArxivV1.tendsto_unmasked_shiftMeanDifference_amplitude_ratio,
    ``RectangleCLTArxivV1.lowerFamily_scale_ge_half,
    ``RectangleCLTArxivV1.lowerFamily_unmasked_shift_second_moment_budget,
    ``RectangleCLTArxivV1.eventually_lowerFamily_unmasked_shift_second_moment_budget,
    ``RectangleCLTArxivV1.lowerFamilyWidthScale_pos,
    ``RectangleCLTArxivV1.exists_lowerFamily_unmasked_signed_detection_constant,
    ``RectangleCLTArxivV1.lower_dimensionLog_le_twice_rare_log,
    ``RectangleCLTArxivV1.lowerFamilyMasterRemainder_nonneg,
    ``RectangleCLTArxivV1.lowerFamilyMasterRemainder_width_bound,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMasterRemainder_div_width,
    ``RectangleCLTArxivV1.tendsto_lowerFamily_dimensionLog_div_sqrt,
    ``RectangleCLTArxivV1.eventually_lowerFamily_leading_range,
    ``RectangleCLTArxivV1.exists_lowerFamily_unmasked_width_detection_constant,
    ``RectangleCLTArxivV1.lowerUnmaskedParameters_pi,
    ``RectangleCLTArxivV1.lowerUnmaskedParameters_theta,
    ``RectangleCLTArxivV1.lowerUnmaskedParameters_amplitude,
    ``RectangleCLTArxivV1.lowerUnmaskedSequence_pi,
    ``RectangleCLTArxivV1.lowerFamilyGaussianMaximumMean_width_profile,
    ``RectangleCLTArxivV1.lowerFamilyGaussianMaximumMean_one_tendsto,
    ``RectangleCLTArxivV1.lower_dimensionLog_product,
    ``RectangleCLTArxivV1.lower_rareLog_le_dimensionLog,
    ``RectangleCLTArxivV1.lower_dimensionLog_le_three_rareLog,
    ``RectangleCLTArxivV1.tendsto_lower_bounded_raw_width_scale,
    ``RectangleCLTArxivV1.lower_bounded_target_le_twelve_scale]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
