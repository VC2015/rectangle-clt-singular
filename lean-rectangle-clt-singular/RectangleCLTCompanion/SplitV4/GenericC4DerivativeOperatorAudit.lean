import RectangleCLTCompanion.SplitV4.GenericC4DerivativeOperator
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_eq_operator

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := ``RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_eq_operator
  let action : CollectAxioms.M Unit := CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in genuine general-C4 derivative/operator identity"
  logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited the actual general-C4 seeded interpolation derivative as its Gaussian-averaged finite selector operator, with genuine product integrability and singular Gaussian factors."
