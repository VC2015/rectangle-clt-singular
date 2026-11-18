import RectangleCLTArxivV1.SupplementalHFourthTubes
import RectangleCLTArxivV1.SupplementalHFourthFiberBounds
import RectangleCLTArxivV1.SupplementalHFacetPairing
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.adaptive_facet_gaussian_integral_lower_fourth,
    ``RectangleCLTArxivV1.adaptive_ridge_gaussian_integral_lower_fourth,
    ``RectangleCLTArxivV1.adaptive_weighted_ridge_pair_fourth_bound,
    ``RectangleCLTArxivV1.abs_weighted_facet_coefficient_le,
    ``RectangleCLTArxivV1.adaptive_weighted_facet_fourth_bound,
    ``RectangleCLTArxivV1.sum_erase_eq_full_sub_diagonal,
    ``RectangleCLTArxivV1.sum_erase_transpose,
    ``RectangleCLTArxivV1.sum_erase_pairing,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_pairing,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_pairing_of_slack,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedFacetIntegral_pairing]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
