import RectangleCLTCompanion.SplitV4.SlepianLaw
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_directSlepianExpectation

#print axioms RectangleCLT.Companion.SplitV4.hasDerivAt_directSlepianExpectation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.slepianAmplitudeDerivative,
    ``RectangleCLT.Companion.SplitV4.slepianAmplitude_pos,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.continuousAt_slepianAmplitudeDerivative,
    ``RectangleCLT.Companion.SplitV4.variableRetention_slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.variableEta_slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.variableRetentionDerivative_slepianAmplitude,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_eq_directSlepian,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_eq_directSlepian_one,
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw_eq_directSlepian_of_le,
    ``RectangleCLT.Companion.SplitV4.directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.integrable_directSlepianExpectation_kernel,
    ``RectangleCLT.Companion.SplitV4.continuous_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.continuousOn_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.directSlepianExpectation_eq_seededLaw,
    ``RectangleCLT.Companion.SplitV4.directSlepianExpectation_zero,
    ``RectangleCLT.Companion.SplitV4.directSlepianExpectation_one,
    ``RectangleCLT.Companion.SplitV4.directSlepianFourthRemainder,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.intervalIntegrable_directSlepianFourthRemainder_kernel]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in actual Slepian law closure"
  logInfo "Audited 21 SlepianLaw declarations; only the three standard axioms are permitted."
