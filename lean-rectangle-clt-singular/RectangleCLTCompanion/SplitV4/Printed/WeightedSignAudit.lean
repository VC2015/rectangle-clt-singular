import RectangleCLTCompanion.SplitV4.Printed.WeightedSignProduct
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.relativeRate_le_of_fourth_cost
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.weighted_sign_fourth_matrices
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_weight_normalization
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_sign_actual_model
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_envelope_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_fourth_asymptotic
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.exceptional_capped_logarithmic_gain

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["WeightedSignExample", "WeightedSignRates", "WeightedSignProduct"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed weighted-sign example"
  logInfo m!"Audited {names.size} actual weighted-sign product-law, exact fourth matrices, exceptional weights and capped logarithmic gain declarations; only the three permitted axioms."
