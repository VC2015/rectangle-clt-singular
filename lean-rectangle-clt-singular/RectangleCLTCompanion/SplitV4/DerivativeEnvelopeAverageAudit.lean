import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage34
import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeStability
import Lean.Util.CollectAxioms

/-! Strict audit of actual smaller-envelope averaging and canonical D3/D4
translated-supremum specializations. The arbitrary-positive-order A.1
assertion needs its separate all-order derivative proof. -/

#print RectangleCLT.Companion.SplitV4.DerivativeEnvelopeComponent
#print RectangleCLT.Companion.SplitV4.translatedFaceDerivativeSupremum
#print RectangleCLT.Companion.SplitV4.derivativeEnvelopeAverageConstant
#print RectangleCLT.Companion.SplitV4.derivativeEnvelopeSignedAverageConstant
#print RectangleCLT.Companion.SplitV4.thirdDerivativeEnvelopeConstant
#print RectangleCLT.Companion.SplitV4.fourthDerivativeEnvelopeConstant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.logistic_smallerEnvelope_shift_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_bounded_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_gaussian_component
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_logisticEnvelope_component_signed_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_translated_third_derivative_signed_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.averaged_translated_fourth_derivative_signed_faces
#print axioms RectangleCLT.Companion.SplitV4.averaged_translated_third_derivative_signed_faces
#print axioms RectangleCLT.Companion.SplitV4.averaged_translated_fourth_derivative_signed_faces

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mods : Array Name := #[
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverageBase,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeSupremum,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeModels,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeLocal34,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage34,
    `RectangleCLTCompanion.SplitV4.DerivativeEnvelopeStability]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if mods.contains env.header.moduleNames[idx.toNat]! then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in derivative-envelope averaging closure"
  logInfo m!"Audited {names.size} actual envelope-averaging and translated D3/D4 theorems."
