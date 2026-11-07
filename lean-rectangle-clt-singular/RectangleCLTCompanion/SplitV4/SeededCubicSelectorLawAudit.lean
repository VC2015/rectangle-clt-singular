import RectangleCLTCompanion.SplitV4.SeededCubicSelectorLaw
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectorThirdDerivativeAverage_eq_seeded_integral
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeThirdMatrix_eq_coordinate_third_moment
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableSignedCubicPathTerm_eq_seeded_integral

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.selectorThirdDerivativeAverage_eq_seeded_integral,
    ``RectangleCLT.Companion.SplitV4.relativeThirdMatrix_eq_coordinate_third_moment,
    ``RectangleCLT.Companion.SplitV4.variableSignedCubicPathTerm_eq_seeded_integral]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in the actual seeded signed cubic selector law"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited exact calibrated selector cubic expectation under the genuine seeded interpolation law, retaining signed third moments and both time endpoints without covariance premises."
