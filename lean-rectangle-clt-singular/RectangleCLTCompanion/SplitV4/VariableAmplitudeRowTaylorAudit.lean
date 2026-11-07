import RectangleCLTCompanion.SplitV4.VariableAmplitudeRowTaylor
import Lean.Util.CollectAxioms

/-! Strict audit of actual general-amplitude fourth-order identities.
The current endpoint is for the face smoother; the arbitrary smooth-test
extension of the whole manuscript Lemma B.1 remains separate. -/

set_option pp.all true in
#check RectangleCLT.FaceSmoother.variableRowTranslation_identity

#print axioms RectangleCLT.FaceSmoother.variableRowTranslation_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.FaceSmoother.variableRowTaylorRemainder,
    ``RectangleCLT.FaceSmoother.variableFourthRowA,
    ``RectangleCLT.FaceSmoother.integrable_variableRowTaylor_remainders,
    ``RectangleCLT.FaceSmoother.variableRowTaylorRemainder_eq_fourthRowA,
    ``RectangleCLT.FaceSmoother.variableRowTranslation_identity]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in general-amplitude fourth identity"
  logInfo "Audited 5 VariableAmplitudeRowTaylor declarations with genuine integrability and actual product-law copies."
  logInfo "Signed cubic aggregation precedes any absolute value. Generic smooth-test B.1 remains separate."
