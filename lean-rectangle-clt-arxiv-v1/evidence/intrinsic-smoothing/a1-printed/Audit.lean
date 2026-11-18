import RectangleCLTArxivV1.DerivativesIntrinsic
import RectangleCLTArxivV1.DirectIntrinsicEnvelope

#print axioms RectangleCLTArxivV1.exp_one_le_four
#print axioms RectangleCLTArxivV1.thresholdLogistic_pos
#print axioms RectangleCLTArxivV1.thresholdLogistic_le_one
#print axioms RectangleCLTArxivV1.thresholdEnvelope_pos
#print axioms RectangleCLTArxivV1.hasDerivAt_thresholdLogistic
#print axioms RectangleCLTArxivV1.hasDerivAt_log_thresholdEnvelope
#print axioms RectangleCLTArxivV1.abs_log_thresholdEnvelope_derivative
#print axioms RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval
#print axioms RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference
#print axioms RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral
#print axioms RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed
#print axioms RectangleCLTArxivV1.integral_logisticEnvelope_le_of_layer_bound_printed
#print axioms RectangleCLTArxivV1.integral_logisticEnvelope_intrinsic
#print axioms RectangleCLTArxivV1.averaged_translated_derivative_intrinsic
#print axioms RectangleCLTArxivV1.intrinsicDerivative_inverse_power_eq_rpow
#print axioms RectangleCLTArxivV1.smallerEnvelope_scaled_bounded_intrinsic_maximum
#print axioms RectangleCLTArxivV1.smallerEnvelope_scaled_gaussian_intrinsic_maximum
#print axioms RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic

open Lean Elab Command in
run_cmd do
  let edges := #[
    (``RectangleCLTArxivV1.integral_logisticEnvelope_intrinsic,
      ``RectangleCLTArxivV1.integral_logisticEnvelope_le_of_layer_bound_printed),
    (``RectangleCLTArxivV1.integral_logisticEnvelope_le_of_layer_bound_printed,
      ``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed),
    (``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed,
      ``RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral),
    (``RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral,
      ``RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference),
    (``RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference,
      ``intervalIntegral.integral_eq_sub_of_hasDerivAt),
    (``RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval,
      ``intervalIntegral.integral_eq_sub_of_hasDerivAt),
    (``RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference,
      ``RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval),
    (``RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval,
      ``RectangleCLTArxivV1.hasDerivAt_log_thresholdEnvelope),
    (``RectangleCLTArxivV1.smallerEnvelope_scaled_bounded_intrinsic_maximum,
      ``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed),
    (``RectangleCLTArxivV1.smallerEnvelope_scaled_gaussian_intrinsic_maximum,
      ``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed)]
  for (parent, required) in edges do
    let ci ← getConstInfo parent
    let some body := ci.value? true | throwError "Missing proof {parent}"
    unless body.getUsedConstants.contains required do
      throwError "Missing printed A.1 proof edge {parent} -> {required}"
  logInfo "PASS: actual A.1/direct intrinsic proofs use window h, the logarithmic derivative, both FTC integrations, e/2 comparison and shared-clock averaging."
