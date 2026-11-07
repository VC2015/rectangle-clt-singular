import RectangleCLTCompanion.SplitV4.GenericC4RowIntegrability
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_genericRow_commonPoint_identity

#print axioms RectangleCLT.Companion.SplitV4.integral_genericRow_commonPoint_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_diagonal,
    ``RectangleCLT.Companion.SplitV4.integrable_genericFourthRows_base,
    ``RectangleCLT.Companion.SplitV4.integrable_genericBernoulliMoment_base,
    ``RectangleCLT.Companion.SplitV4.genericRowOperator,
    ``RectangleCLT.Companion.SplitV4.genericRowFourthTotal,
    ``RectangleCLT.Companion.SplitV4.integral_genericRow_commonPoint_identity]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 6 GenericC4RowIntegrability declarations; only the three standard axioms are permitted."
