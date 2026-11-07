import RectangleCLTCompanion.SplitV4.RestorationConditionalBudgets
import Lean.Util.CollectAxioms

/-! Actual conditional-moment budgets used by Lemma B.2. This audits
coefficient helpers; the analytic Stein/series restoration conclusion is
separate until the actual B.4 matrix estimate has been connected. -/

#print RectangleCLT.Companion.SplitV4.conditionalMatrixAverage
#print RectangleCLT.Companion.SplitV4.conditionalRestorationCoefficient
#print RectangleCLT.Companion.SplitV4.conditionalTranslatedRestorationCoefficient
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_baseline
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_relative_pair
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_restoration_coefficient_relative_signed_zero_shift
#print axioms RectangleCLT.Companion.SplitV4.ae_forall_matrixQuadratic_bound
#print axioms RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_baseline
#print axioms RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_relative_pair
#print axioms RectangleCLT.Companion.SplitV4.conditional_restoration_coefficient_relative_signed_zero_shift

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalBudgets" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional restoration budget declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional restoration budget closure"
  logInfo m!"Audited all {names.size} conditional restoration budget theorem declarations."
