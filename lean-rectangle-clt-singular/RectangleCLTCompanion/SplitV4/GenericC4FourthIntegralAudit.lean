import RectangleCLTCompanion.SplitV4.GenericC4FourthIntegral
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_genericRowFourthTotal_eq_interval

#print axioms RectangleCLT.Companion.SplitV4.integral_genericRowFourthTotal_eq_interval

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.genericFourthCombination,
    ``RectangleCLT.Companion.SplitV4.integrable_genericFourthCombination_interval_prod,
    ``RectangleCLT.Companion.SplitV4.genericFourthCombination_interval_data,
    ``RectangleCLT.Companion.SplitV4.genericRowFourthTotal_eq_pair_interval,
    ``RectangleCLT.Companion.SplitV4.integral_genericRowFourthTotal_eq_interval]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 5 GenericC4FourthIntegral declarations; only the three standard axioms are permitted."
