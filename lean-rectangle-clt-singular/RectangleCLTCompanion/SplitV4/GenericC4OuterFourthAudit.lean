import RectangleCLTCompanion.SplitV4.GenericC4OuterFourth
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericSelectorFourthRemainder_outer_interval

#print axioms RectangleCLT.Companion.SplitV4.genericSelectorFourthRemainder_outer_interval

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.genericFourthPathIntegrand,
    ``RectangleCLT.Companion.SplitV4.genericFourthPath_row_data,
    ``RectangleCLT.Companion.SplitV4.genericSelectorFourthRemainder_outer_interval]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 3 GenericC4OuterFourth declarations; only the three standard axioms are permitted."
