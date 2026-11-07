import RectangleCLTCompanion.SplitV4.ConditionalPolynomial
import Lean.Util.CollectAxioms

/-! Actual Appendix E threshold transfer: concrete exceptional-data kernel,
singular Gaussian comparison, expected covariance deviation, and original
nonidentical independent observations with genuine envelope moments. -/

#print RectangleCLT.Companion.SplitV4.conditionalPolynomialConstant
#print RectangleCLT.Companion.SplitV4.conditionalPolynomialThresholdRate
#print RectangleCLT.Companion.SplitV4.truncationVarianceBudget
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeV
#print RectangleCLT.Companion.SplitV4.conditionalNormalizedShift
#print RectangleCLT.Companion.SplitV4.ConditionalTruncationMomentHypotheses

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.boundedRectangleDistanceCLT_of_marginal_lower_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalGoodKernel_rectangle_error_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_conditionalKernel_probability
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditionalPolynomial_threshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelope_threshold
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialEnvelope_threshold_of_average_variances

#print axioms RectangleCLT.Companion.SplitV4.polynomialEnvelope_threshold_of_average_variances

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.ConditionalPolynomial then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional polynomial threshold closure"
  logInfo m!"Audited {names.size} conditional polynomial threshold declarations."
