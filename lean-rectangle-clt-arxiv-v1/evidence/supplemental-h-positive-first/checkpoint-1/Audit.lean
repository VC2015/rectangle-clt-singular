import RectangleCLTArxivV1.SupplementalHWeightedGammaPrimitive
import RectangleCLTArxivV1.PositiveFirstCoarea
import RectangleCLTArxivV1.PositiveFirstCoareaBounds
import RectangleCLTArxivV1.PositiveFirstCoareaDerivative
import RectangleCLTArxivV1.PositiveGammaFirstCoarea
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.measurable_gaussianFiniteWeightedThreshold,
    ``RectangleCLTArxivV1.abs_gaussianFiniteWeightedThreshold_le,
    ``RectangleCLTArxivV1.weighted_logistic_power_eq_gamma_weighted_threshold,
    ``RectangleCLTArxivV1.positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.measurable_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.integrable_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.integral_positiveGaussianPlaneTest,
    ``RectangleCLTArxivV1.positiveGaussianPlaneTest_eq_actual_projection,
    ``RectangleCLTArxivV1.gaussianFiniteWeightedSection_planeTest_eq,
    ``RectangleCLTArxivV1.continuousAt_gaussianFiniteWeightedSection_planeTest_of_slack,
    ``RectangleCLTArxivV1.hasDerivAt_positivePlaneThreshold_update_of_slack,
    ``RectangleCLTArxivV1.norm_positivePlaneThreshold_le_two,
    ``RectangleCLTArxivV1.norm_positiveMassThreshold_le_one,
    ``RectangleCLTArxivV1.norm_positivePlaneFirstSection_density_le,
    ``RectangleCLTArxivV1.norm_positiveMassFirstSection_density_le,
    ``RectangleCLTArxivV1.lipschitzWith_weightedThreshold_update_of_section_bound,
    ``RectangleCLTArxivV1.lipschitzWith_positivePlaneThreshold_update,
    ``RectangleCLTArxivV1.lipschitzWith_positiveMassThreshold_update,
    ``RectangleCLTArxivV1.hasDerivAt_positiveMassThreshold_update_of_slack,
    ``RectangleCLTArxivV1.ae_hasDerivAt_positiveMassThreshold_update,
    ``RectangleCLTArxivV1.ae_hasDerivAt_positivePlaneThreshold_update,
    ``RectangleCLTArxivV1.weighted_first_soft_coarea_of_hard_derivative,
    ``RectangleCLTArxivV1.positiveMass_soft_first_coarea,
    ``RectangleCLTArxivV1.positivePlane_soft_first_coarea]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
