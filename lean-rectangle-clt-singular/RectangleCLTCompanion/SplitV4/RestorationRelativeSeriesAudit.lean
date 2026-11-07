import RectangleCLTCompanion.SplitV4.RestorationRelativeSeries
import Lean.Util.CollectAxioms

/-! Relative M1/M2 coefficient profiles and actual score-restoration cap.
All profiles are derived from genuine conditional matrix moments; the
coarse directional envelope is used only for integrability. -/

#print RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_pair
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_signed_zero_shift
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration_of_budget
#print axioms RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_pair
#print axioms RectangleCLT.Companion.SplitV4.ConditionalTranslatedCoefficientBudget.relative_signed_zero_shift
#print axioms RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration_of_budget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationRelativeSeries" then
          names := names.push n
  unless names.size > 0 do
    throwError "No relative restoration series declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative restoration series closure"
  logInfo m!"Audited all {names.size} relative restoration series theorem declarations."
