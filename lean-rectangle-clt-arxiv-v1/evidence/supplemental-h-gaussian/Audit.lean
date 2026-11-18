import RectangleCLTArxivV1.SupplementalHLinearGrowth
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.NonnegativeLogConcave_min_const,
    ``RectangleCLTArxivV1.gaussianWeightCap_tendsto,
    ``RectangleCLTArxivV1.weightMass_gaussianWeightCap_pos,
    ``RectangleCLTArxivV1.integral_mul_gaussianWeightCap_tendsto,
    ``RectangleCLTArxivV1.gaussian_logConcave_matrix_reduction_of_moments,
    ``RectangleCLTArxivV1.gaussian_weighted_coordinate_moments,
    ``RectangleCLTArxivV1.weightCovariance_const_mul,
    ``RectangleCLTArxivV1.gaussian_logConcave_covariance_contraction_of_bound,
    ``RectangleCLTArxivV1.gaussian_logConcave_covariance_contraction_of_moments,
    ``RectangleCLTArxivV1.lemma_H2_gaussian_matrix,
    ``RectangleCLTArxivV1.lemma_H2_projected_reference]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
