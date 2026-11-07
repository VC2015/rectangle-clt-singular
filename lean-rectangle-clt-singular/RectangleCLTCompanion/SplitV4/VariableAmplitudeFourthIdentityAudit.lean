import RectangleCLTCompanion.SplitV4.VariableAmplitudeFourthIdentity
import Lean.Util.CollectAxioms

/-! Strict audit of actual general-amplitude fourth-order identities.
The current endpoint is for the face smoother; the arbitrary smooth-test
extension of the whole manuscript Lemma B.1 remains separate. -/

set_option pp.all true in
#check RectangleCLT.FaceSmoother.variableRow_commonPoint_identity

set_option pp.all true in
#check RectangleCLT.FaceSmoother.variableSelectorOperator_fourth_identity

set_option pp.all true in
#check RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw_manuscript

#print axioms RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw_manuscript

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.FaceSmoother.variableBernoulliSecond,
    ``RectangleCLT.FaceSmoother.variableBernoulliThird,
    ``RectangleCLT.FaceSmoother.variableFourthRowB,
    ``RectangleCLT.FaceSmoother.variableFourthRowC,
    ``RectangleCLT.FaceSmoother.variableFourthRowB_eq_correction,
    ``RectangleCLT.FaceSmoother.variableFourthRowC_eq_correction,
    ``RectangleCLT.FaceSmoother.variable_second_bernoulli_contraction,
    ``RectangleCLT.FaceSmoother.variable_third_bernoulli_contraction,
    ``RectangleCLT.FaceSmoother.variableRow_commonPoint_identity,
    ``RectangleCLT.FaceSmoother.variableRowOperator,
    ``RectangleCLT.FaceSmoother.integrable_variableBernoulliSecond_base,
    ``RectangleCLT.FaceSmoother.integrable_variableBernoulliThird_base,
    ``RectangleCLT.FaceSmoother.integrable_variableFourthRows_base,
    ``RectangleCLT.FaceSmoother.integral_variableRow_commonPoint_identity,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthRemainder,
    ``RectangleCLT.FaceSmoother.variable_row_mask_commonPoint_identity,
    ``RectangleCLT.FaceSmoother.variableHeatShiftExpectation_eq_convolution,
    ``RectangleCLT.FaceSmoother.variableHeatShiftDerivative_eq_spatial_add_heat,
    ``RectangleCLT.FaceSmoother.variableSelectorOperator,
    ``RectangleCLT.FaceSmoother.variableSelectorHeatDerivative_eq_operator,
    ``RectangleCLT.FaceSmoother.variable_forced_increment_eq_rowOperator,
    ``RectangleCLT.FaceSmoother.variableSignedCubicPathTerm,
    ``RectangleCLT.FaceSmoother.variableSelectorOperator_fourth_identity,
    ``RectangleCLT.FaceSmoother.variableSelectorHeatDerivative_fourth_identity,
    ``RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw_fourth_identity,
    ``RectangleCLT.FaceSmoother.variableFourthRowB_freshPair,
    ``RectangleCLT.FaceSmoother.variableFourthRowC_freshPair,
    ``RectangleCLT.FaceSmoother.variableFourthRowB_eq_freshPair,
    ``RectangleCLT.FaceSmoother.variableFourthRowC_eq_freshPair,
    ``RectangleCLT.FaceSmoother.variableFourthPathIntegrandA,
    ``RectangleCLT.FaceSmoother.variableFourthPathIntegrandB,
    ``RectangleCLT.FaceSmoother.variableFourthPathIntegrandC,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthA,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthB,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthC,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthRemainder_eq_add,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthA_eq_interval_integral,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthB_eq_interval_integral,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthC_eq_interval_integral,
    ``RectangleCLT.Companion.SplitV4.variable_same_copy_fourth_kernel,
    ``RectangleCLT.Companion.SplitV4.variable_pair_fourth_kernel,
    ``RectangleCLT.FaceSmoother.variableSelectorFourthRemainder_eq_manuscript,
    ``RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw_manuscript]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in general-amplitude fourth identity"
  logInfo "Audited 43 VariableAmplitudeFourthIdentity declarations with genuine integrability and actual product-law copies."
  logInfo "Signed cubic aggregation precedes any absolute value. Generic smooth-test B.1 remains separate."
