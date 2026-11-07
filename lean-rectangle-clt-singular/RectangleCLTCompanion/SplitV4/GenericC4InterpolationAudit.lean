import RectangleCLTCompanion.SplitV4.GenericC4Interpolation
import Lean.Util.CollectAxioms

/-! Strict audit of generic smooth-test helpers. These declarations do
not by themselves assert the full arbitrary-test Lemma B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_integral_variableSeededInterpolationLaw

#print axioms RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_integral_variableSeededInterpolationLaw

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.integrable_variablePointNorm,
    ``RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.genericVariableHeatDerivative,
    ``RectangleCLT.Companion.SplitV4.C4Test.integrable_genericVariableHeatValue,
    ``RectangleCLT.Companion.SplitV4.C4Test.integrable_genericVariableHeatVelocity,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableHeatExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.genericVariableSelectorExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.genericVariableSelectorDerivative,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableSelectorExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_variableSeededInterpolationLaw_eq_genericVariableSelectorExpectation,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_integral_variableSeededInterpolationLaw]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 helper closure"
  logInfo "Audited 11 GenericC4Interpolation declarations, with genuine integrability and canonical derivatives."
