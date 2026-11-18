import RectangleCLTArxivV1.SupplementalHTripleIncidenceAtoms
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceFrame_span
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceNormalPoint_supporting_levels
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidence_independent_of_third_residual_ne_zero
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidence_mass_eq_common
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_common_vector
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent
set_option pp.all true in
#check @RectangleCLTArxivV1.ae_hardGaussianRidgeThirdIncidenceGroup_classification

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.tripleIncidence_pair_nondegenerate,
    ``RectangleCLTArxivV1.tripleIncidence_pair_geometry,
    ``RectangleCLTArxivV1.tripleIncidence_third_residual_ne_zero,
    ``RectangleCLTArxivV1.tripleIncidenceFrame_orthonormal,
    ``RectangleCLTArxivV1.tripleIncidenceFrame_span,
    ``RectangleCLTArxivV1.tripleIncidenceNormalPoint_native,
    ``RectangleCLTArxivV1.tripleIncidenceNormalPoint_supporting_levels,
    ``RectangleCLTArxivV1.tripleIncidenceNormalPoint_mem_span,
    ``RectangleCLTArxivV1.tripleIncidenceNormalPoint_eq,
    ``RectangleCLTArxivV1.tripleIncidence_independent_of_third_residual_ne_zero,
    ``RectangleCLTArxivV1.tripleIncidence_remaining_eq,
    ``RectangleCLTArxivV1.tripleIncidence_third_mem_pairFaces,
    ``RectangleCLTArxivV1.tripleIncidenceCommonMass_nonneg,
    ``RectangleCLTArxivV1.tripleIncidence_mass_eq_common,
    ``RectangleCLTArxivV1.ae_tripleIncidenceRegularity,
    ``RectangleCLTArxivV1.tripleIncidence_scaled_density_eq_common,
    ``RectangleCLTArxivV1.tripleIncidence_weighted_density_eq_common,
    ``RectangleCLTArxivV1.tripleIncidence_normal_distance_pairing,
    ``RectangleCLTArxivV1.tripleIncidence_signed_grouping,
    ``RectangleCLTArxivV1.ae_tripleIncidence_scaled_densities_common,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_eq_tripleIncidence,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_eq_tripleIncidence_of_independent,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdAtom_zero_of_dependent,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_tuple_sum,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_common_vector,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent,
    ``RectangleCLTArxivV1.ae_hardGaussianRidgeThirdIncidenceGroup_classification]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
