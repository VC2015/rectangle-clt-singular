import RectangleCLTCompanion.SplitV4.GenericC4SelectorAlgebra
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericSelectorOperator

#print axioms RectangleCLT.Companion.SplitV4.genericSelectorOperator

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.C4Test.integrable_value_sum_prod,
    ``RectangleCLT.Companion.SplitV4.genericFixedValue,
    ``RectangleCLT.Companion.SplitV4.genericFixedGradient,
    ``RectangleCLT.Companion.SplitV4.canonicalHessianCoordinate,
    ``RectangleCLT.Companion.SplitV4.genericFixedHeat,
    ``RectangleCLT.Companion.SplitV4.ofContDiff_gradient_eq_canonicalDiagonal,
    ``RectangleCLT.Companion.SplitV4.ofContDiff_hessianCoordinate_eq_canonicalHessianCoordinate,
    ``RectangleCLT.Companion.SplitV4.generic_forced_increment_eq_rowOperator,
    ``RectangleCLT.Companion.SplitV4.genericSelectorOperator]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 9 GenericC4SelectorAlgebra declarations; only the three standard axioms are permitted."
