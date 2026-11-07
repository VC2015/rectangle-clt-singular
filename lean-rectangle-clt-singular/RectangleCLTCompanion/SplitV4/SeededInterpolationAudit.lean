import RectangleCLTCompanion.SplitV4.SeededInterpolation
import Lean.Util.CollectAxioms

/-! Strict audit of the actual calibrated seeded path. This is not a
certificate of the arbitrary-C¹-amplitude version of Lemma B.1. -/

#print RectangleCLT.Companion.SplitV4.seededInterpolationLaw
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededInterpolationLaw_eq_shifted_heat
set_option pp.all true in
#check RectangleCLT.FaceSmoother.hasDerivAt_seededSelectorHeatExpectation
set_option pp.all true in
#check RectangleCLT.FaceSmoother.hasDerivAt_integral_seededInterpolationLaw_fourthTerms
set_option pp.all true in
#check RectangleCLT.FaceSmoother.integrable_seededFourthTerms

#print axioms RectangleCLT.Companion.SplitV4.seededInterpolationLaw_eq_shifted_heat
#print axioms RectangleCLT.FaceSmoother.hasDerivAt_integral_seededInterpolationLaw_fourthTerms
#print axioms RectangleCLT.FaceSmoother.convolutionFourthDerivative_gaussian_seed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.abs_selectorWeightDerivative_le,
    ``RectangleCLT.Companion.SplitV4.abs_calibrated_probability_derivative_le,
    ``RectangleCLT.Companion.SplitV4.seededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.gaussian_seed_conv,
    ``RectangleCLT.Companion.SplitV4.interpolationLaw_eq_conv_arraySum,
    ``RectangleCLT.Companion.SplitV4.seededInterpolationLaw_eq_shifted_heat,
    ``RectangleCLT.Companion.SplitV4.seededInterpolationLaw_isProbability,
    ``RectangleCLT.Companion.SplitV4.shiftIntegral_gaussian_seed,
    ``RectangleCLT.FaceSmoother.seededSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.seededSelectorHeatDerivative,
    ``RectangleCLT.FaceSmoother.measurable_heatShiftExpectation_x,
    ``RectangleCLT.FaceSmoother.measurable_heatShiftDerivative_x,
    ``RectangleCLT.FaceSmoother.seedDominationHeatConstant,
    ``RectangleCLT.FaceSmoother.norm_heatShiftDerivative_le_seedDominationHeatConstant,
    ``RectangleCLT.FaceSmoother.norm_heatShiftExpectation_le_one,
    ``RectangleCLT.FaceSmoother.measurable_selectorHeatExpectation_x,
    ``RectangleCLT.FaceSmoother.measurable_selectorHeatDerivative_x,
    ``RectangleCLT.FaceSmoother.norm_selectorHeatExpectation_le_one,
    ``RectangleCLT.FaceSmoother.seedDominationConstant,
    ``RectangleCLT.FaceSmoother.norm_selectorHeatDerivative_le_seedDominationConstant,
    ``RectangleCLT.FaceSmoother.hasDerivAt_seededSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.integral_interpolationLaw_translate_eq_selectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.integral_seededInterpolationLaw_eq_seededSelectorHeatExpectation,
    ``RectangleCLT.FaceSmoother.seededSelectorHeatDerivative_eq_fourthTerms,
    ``RectangleCLT.FaceSmoother.hasDerivAt_integral_seededInterpolationLaw_fourthTerms,
    ``RectangleCLT.FaceSmoother.integrable_seededSelectorHeatDerivative,
    ``RectangleCLT.FaceSmoother.integrable_seededFourthTerms,
    ``RectangleCLT.FaceSmoother.convolutionFirstDerivative_gaussian_seed,
    ``RectangleCLT.FaceSmoother.convolutionSecondDerivative_gaussian_seed,
    ``RectangleCLT.FaceSmoother.convolutionThirdDerivative_gaussian_seed,
    ``RectangleCLT.FaceSmoother.convolutionFourthDerivative_gaussian_seed]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in calibrated seeded interpolation closure"
  logInfo "Audited 31 calibrated seeded interpolation declarations: actual independent seed law, variance t+ε, dominated differentiation, signed common cubic −t/3 and three actual fourth rows."
  logInfo "The arbitrary C¹ amplitude version, Slepian initialization and Appendix B analytic derivative budgets remain separate."
