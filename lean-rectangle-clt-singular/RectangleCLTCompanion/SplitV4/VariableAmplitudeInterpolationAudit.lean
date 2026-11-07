import RectangleCLTCompanion.SplitV4.VariableAmplitudeInterpolation
import Lean.Util.CollectAxioms

/-! Strict audit of the actual C¹-amplitude finite-mask differentiation
and its scalar coefficients. Fourth-order restoration remains separate. -/

#print RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw
set_option pp.all true in
#check RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw
set_option pp.all true in
#check RectangleCLT.FaceSmoother.variableHeatShiftDerivative_eq_heat

#print axioms RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw
#print axioms RectangleCLT.FaceSmoother.variableHeatShiftDerivative_eq_heat
#print axioms RectangleCLT.Companion.SplitV4.variable_signed_hessian_coefficient

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.variableRetention,
    ``RectangleCLT.Companion.SplitV4.variableRetentionDerivative,
    ``RectangleCLT.Companion.SplitV4.variableEta,
    ``RectangleCLT.Companion.SplitV4.variable_covariance_calibration,
    ``RectangleCLT.Companion.SplitV4.variable_third_moment_calibration,
    ``RectangleCLT.Companion.SplitV4.variable_signed_hessian_coefficient,
    ``RectangleCLT.Companion.SplitV4.variable_cubic_coefficient,
    ``RectangleCLT.Companion.SplitV4.variable_independent_copy_cubic_coefficient,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_variableRetention,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_maskWeight_curve,
    ``RectangleCLT.Companion.SplitV4.variableMaskPoint,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.measurable_variableMaskPoint,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_isProbability,
    ``RectangleCLT.FaceSmoother.abs_variableDirectionalSum_le,
    ``RectangleCLT.FaceSmoother.gaussian_raw_velocity_integral_eq,
    ``RectangleCLT.FaceSmoother.variableHeatShiftExpectation,
    ``RectangleCLT.FaceSmoother.variableHeatShiftDerivative,
    ``RectangleCLT.FaceSmoother.integrable_variableGradientKernel,
    ``RectangleCLT.FaceSmoother.variableHeatShiftDerivative_eq_heat,
    ``RectangleCLT.FaceSmoother.hasDerivAt_variableHeatShiftExpectation,
    ``RectangleCLT.FaceSmoother.variableSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.variableSelectorHeatDerivative,
    ``RectangleCLT.FaceSmoother.hasDerivAt_variableSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.integral_variableSeededInterpolationLaw_eq_variableSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.hasDerivAt_integral_variableSeededInterpolationLaw]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in variable-amplitude interpolation calculus"
  logInfo "Audited 26 variable-amplitude interpolation declarations, including actual independent finite-mask law differentiation, genuine domination, Gaussian integration by parts and signed scalar coefficients."
  logInfo "The general-amplitude signed-Hessian/Taylor fourth-order restoration and Appendix B analytic budgets remain separate."
