import RectangleCLTCompanion.SplitV4.GenericProductTilt
import Lean.Util.CollectAxioms

/-! Exact nonidentical product-tilt contracts and complete transitive axiom audit. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.generic_pi_withDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.generic_integrable_exp_of_bounded

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.generic_interior_integrableExpSet_of_bounded

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedMarginal_isProbability

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_isProbability

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_eq_withDensity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_iIndepFun

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltMean

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltTotalVariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltMean_eq_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltVariance_eq_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedMarginal_bounded

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltMean_abs_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_map_eval

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedRawRows

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedRawRows_measurable

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedRawRows_boundedIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedRawRows_second

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltNormalization

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows_boundedIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows_covariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_measurable

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_eq

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_cdf

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_cdf_of_variance_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericProduct_mgf_sum

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericProduct_cgf_sum

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_integrable_iff

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_inverse_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericTiltedProduct_inverse_integrable_iff

set_option pp.all true in
#check RectangleCLT.scalarBerryEsseenCDF

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.generic_pi_withDensity,
    ``RectangleCLT.Companion.SplitV4.generic_integrable_exp_of_bounded,
    ``RectangleCLT.Companion.SplitV4.generic_interior_integrableExpSet_of_bounded,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct,
    ``RectangleCLT.Companion.SplitV4.genericTiltedMarginal_isProbability,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_isProbability,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_eq_withDensity,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_iIndepFun,
    ``RectangleCLT.Companion.SplitV4.genericTiltMean,
    ``RectangleCLT.Companion.SplitV4.genericTiltVariance,
    ``RectangleCLT.Companion.SplitV4.genericTiltTotalVariance,
    ``RectangleCLT.Companion.SplitV4.genericTiltMean_eq_integral,
    ``RectangleCLT.Companion.SplitV4.genericTiltVariance_eq_integral,
    ``RectangleCLT.Companion.SplitV4.genericTiltedMarginal_bounded,
    ``RectangleCLT.Companion.SplitV4.genericTiltMean_abs_le,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_map_eval,
    ``RectangleCLT.Companion.SplitV4.genericTiltedRawRows,
    ``RectangleCLT.Companion.SplitV4.genericTiltedRawRows_measurable,
    ``RectangleCLT.Companion.SplitV4.genericTiltedRawRows_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.genericTiltedRawRows_second,
    ``RectangleCLT.Companion.SplitV4.genericTiltNormalization,
    ``RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows,
    ``RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows_boundedIndependent,
    ``RectangleCLT.Companion.SplitV4.genericTiltedNormalizedRows_covariance,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_measurable,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_eq,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_cdf,
    ``RectangleCLT.Companion.SplitV4.genericTiltedStandardizedSum_cdf_of_variance_lower,
    ``RectangleCLT.Companion.SplitV4.genericProduct_mgf_sum,
    ``RectangleCLT.Companion.SplitV4.genericProduct_cgf_sum,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_integral,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_integrable_iff,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_inverse_integral,
    ``RectangleCLT.Companion.SplitV4.genericTiltedProduct_inverse_integrable_iff]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in nonidentical product tilt or scalar Berry--Esseen"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited genuine nonidentical finite-product tilt, density normalizer, centered standardized array, unit covariance, actual tilted CDF Berry--Esseen, and integrable inverse change of measure."
