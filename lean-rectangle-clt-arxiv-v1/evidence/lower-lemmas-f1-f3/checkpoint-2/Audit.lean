import RectangleCLTArxivV1.LowerLemmaF1Support
import RectangleCLTArxivV1.LowerLemmaF2
import RectangleCLTArxivV1.LowerLemmaF3
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.scalarModerateTailRadius_pos,
    ``RectangleCLTArxivV1.scalarModerateTailErrorConstant_pos,
    ``RectangleCLTArxivV1.lemma_F_1_bound,
    ``RectangleCLTArxivV1.lemma_F_1_uniform_scalar_moderate_tail,
    ``RectangleCLTArxivV1.lemma_F_2_independent_conditioning,
    ``RectangleCLTArxivV1.lemma_F_2_signed_taylor,
    ``RectangleCLTArxivV1.lemma_F_2_independently_shifted_variables,
    ``RectangleCLTArxivV1.lemma_F_3_raw_covariance,
    ``RectangleCLTArxivV1.lemma_F_3_gaussian_covariance,
    ``RectangleCLTArxivV1.lemma_F_3_properties_of_parameters,
    ``RectangleCLTArxivV1.lemma_F_3_common_symmetric_construction,
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_log_derivative,
    ``RectangleCLTArxivV1.lemma_F_1_weighted_normal_derivative]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.lemma_F_1_uniform_scalar_moderate_tail).run env).run {}
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.Printed.moderateTiltVariance_printed_copy_bounds"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.Printed.moderateArray_local_taylor_printed"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_nonneg_printed do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.Printed.moderateProductTail_nonneg_printed"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_eq_withDensity do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.genericTiltedProduct_eq_withDensity"
  if deps.visited.contains ``RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds then
    throwError "Forbidden shortcut RectangleCLT.Companion.SplitV4.moderateTiltVariance_exp_bounds"
  if deps.visited.contains ``RectangleCLT.Companion.SplitV4.moderateArray_local_taylor then
    throwError "Forbidden shortcut RectangleCLT.Companion.SplitV4.moderateArray_local_taylor"
  if deps.visited.contains ``RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold then
    throwError "Forbidden shortcut RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold"
  if deps.visited.contains ``RectangleCLT.Companion.SplitV4.moderateScalarTail_bound then
    throwError "Forbidden shortcut RectangleCLT.Companion.SplitV4.moderateScalarTail_bound"
  logInfo "PASS actual route RectangleCLTArxivV1.lemma_F_1_uniform_scalar_moderate_tail"
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.lemma_F_2_independently_shifted_variables).run env).run {}
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.independent_shift_cdf do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.independent_shift_cdf"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.shifted_taylor_bound do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.shifted_taylor_bound"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.independent_shift_comparison do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.independent_shift_comparison"
  logInfo "PASS actual route RectangleCLTArxivV1.lemma_F_2_independently_shifted_variables"
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.lemma_F_3_common_symmetric_construction).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyArrayLaw do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyArrayLaw"
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyObservation do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyObservation"
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyCovariance_rank do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyCovariance_rank"
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyCovariance_pairGap do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyCovariance_pairGap"
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyRawObservations_Lq_envelope do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyRawObservations_Lq_envelope"
  unless deps.visited.contains ``RectangleCLTArxivV1.lowerFamilyGaussian_width_bounds do
    throwError "Missing actual proof step RectangleCLTArxivV1.lowerFamilyGaussian_width_bounds"
  unless deps.visited.contains ``RectangleCLTArxivV1.covariance_lowerGridGaussianLaw do
    throwError "Missing actual proof step RectangleCLTArxivV1.covariance_lowerGridGaussianLaw"
  unless deps.visited.contains ``RectangleCLTArxivV1.lemma_lower_family_properties do
    throwError "Missing actual proof step RectangleCLTArxivV1.lemma_lower_family_properties"
  logInfo "PASS actual route RectangleCLTArxivV1.lemma_F_3_common_symmetric_construction"
