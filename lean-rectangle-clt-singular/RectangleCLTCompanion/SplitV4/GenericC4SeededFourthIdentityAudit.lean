import RectangleCLTCompanion.SplitV4.GenericC4SeededFourthIdentity
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_manuscript

#print axioms RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_manuscript

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_genericThirdMomentMultiplier,
    ``RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.genericManuscriptFourthCombination,
    ``RectangleCLT.Companion.SplitV4.genericFourthCombination_variable_eq_manuscript,
    ``RectangleCLT.Companion.SplitV4.genericManuscriptFourthPathIntegrand,
    ``RectangleCLT.Companion.SplitV4.genericFourthPathIntegrand_variable_eq_manuscript,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_manuscript,
    ``RectangleCLT.Companion.SplitV4.intervalIntegrable_genericManuscriptFourthPathIntegrand]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 9 GenericC4SeededFourthIdentity declarations; only the three standard axioms are permitted."
