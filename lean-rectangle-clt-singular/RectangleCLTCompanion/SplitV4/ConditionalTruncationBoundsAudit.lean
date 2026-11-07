import RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds
import Lean.Util.CollectAxioms

/-! Strict audit for actual conditional covariance and exceptional-shift
moment bounds. Threshold comparison and optimization are separate endpoints. -/

#print RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses
#print RectangleCLT.Companion.SplitV4.truncationVarianceBudget
#print RectangleCLT.Companion.SplitV4.conditionalCovarianceForMask
#print RectangleCLT.Companion.SplitV4.originalAverageCovariance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.norm_mean_le_polynomial_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.abs_good_covariance_bias_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_conditional_covariance_deviation_actual
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.integral_exceptionalPart_q_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lintegral_tagged_product_eq_mask_bad_good

#print axioms RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.norm_mean_le_polynomial_tail
#print axioms RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.abs_good_covariance_bias_le
#print axioms RectangleCLT.Companion.SplitV4.expected_conditional_covariance_deviation_actual
#print axioms RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses.integral_exceptionalPart_q_le
#print axioms RectangleCLT.Companion.SplitV4.lintegral_tagged_product_eq_mask_bad_good

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.ConditionalTruncationBounds" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional-truncation numeric closure"
  logInfo m!"Audited {names.size} conditional-truncation numeric theorem declarations; only the permitted three axioms."
  logInfo "Actual expected conditional covariance discrepancy is at most 6*v_T; the covariance route uses C0<=2*T^2 and the actual Markov tail budget."
  logInfo "The polynomial threshold endpoint and optimization require separate assembly."
