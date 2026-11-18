import RectangleCLTArxivV1.SupplementalHCubicWeights
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.entropy_term_le_reference,
    ``RectangleCLTArxivV1.entropy_term_nonneg,
    ``RectangleCLTArxivV1.integrable_entropy_term,
    ``RectangleCLTArxivV1.entropy_term_common_factor,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_fixed_scale,
    ``RectangleCLTArxivV1.integral_sum_entropy_le_log_ratio,
    ``RectangleCLTArxivV1.sum_face_tuples_cons,
    ``RectangleCLTArxivV1.sum_face_probability_products,
    ``RectangleCLTArxivV1.sum_selector_first_weight,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight,
    ``RectangleCLTArxivV1.sum_selector_first_weight_le,
    ``RectangleCLTArxivV1.sum_selector_first_pair_weight_le,
    ``RectangleCLTArxivV1.selector_extra_factors_binomial,
    ``RectangleCLTArxivV1.supplementalHSelectorMass,
    ``RectangleCLTArxivV1.supplementalHSelectorProjection,
    ``RectangleCLTArxivV1.supplementalHSelectorEntropy,
    ``RectangleCLTArxivV1.supplementalHSelectorRadialTrace,
    ``RectangleCLTArxivV1.supplementalH_selector_projected_reduction,
    ``RectangleCLTArxivV1.supplementalH_sum_weighted_selector_reduction,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_nonneg,
    ``RectangleCLTArxivV1.supplementalH_nonnegative_logConcave_mul,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_logConcave,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_logConcave,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_sub,
    ``RectangleCLTArxivV1.supplementalHPositiveDirection_add]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
