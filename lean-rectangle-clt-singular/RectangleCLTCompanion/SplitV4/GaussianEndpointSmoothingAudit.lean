import RectangleCLTCompanion.SplitV4.GaussianEndpointSmoothing
import Lean.Util.CollectAxioms

/-! Fresh audit of the full Gaussian-endpoint smoothing theorem (G.2).
The proof includes the actual logistic mixture, clock probabilities,
Gaussian shells, and absorption of the full rectangle distance. -/

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.gaussianSmoothingConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussianEndpointSmoothing

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleError_le_gaussianEndpointSmoothing

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.gaussianSmoothingConstant_ge_two,
    ``RectangleCLT.Companion.SplitV4.gaussianEndpointSmoothing,
    ``RectangleCLT.Companion.SplitV4.rectangleError_le_gaussianEndpointSmoothing]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in Gaussian-endpoint smoothing {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited full Lemma G.2, its global constant, and its all-rectangle consequence."
