import RectangleCLTCompanion.SplitV4.BennettTruncation
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the genuine truncation, omitted-tail, and
zero-second-moment inputs to Lemma G.4. These inputs do not by themselves
certify the Bennett maximum conclusion. -/

#print RectangleCLT.Companion.SplitV4.bennettTruncate
#check RectangleCLT.Companion.SplitV4.measurable_bennettTruncate
#check RectangleCLT.Companion.SplitV4.identDistrib_bennettTruncate_neg
#check RectangleCLT.Companion.SplitV4.integrable_bennettTruncate_coordinate
#check RectangleCLT.Companion.SplitV4.integrable_bennettTruncate_coordinate_sq
#check RectangleCLT.Companion.SplitV4.integral_bennettTruncate_coordinate_sq_le
#check RectangleCLT.Companion.SplitV4.iIndepFun_bennettTruncate
#check RectangleCLT.Companion.SplitV4.integrable_of_bennett_norm_moment

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_bennettTruncate_coordinate_eq_zero

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_sum_bennettRemainder_le_budget

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sum_ae_eq_zero_of_coordinate_second_moment_budget_zero

#print axioms RectangleCLT.Companion.SplitV4.integral_bennettTruncate_coordinate_eq_zero
#print axioms RectangleCLT.Companion.SplitV4.integral_norm_sum_bennettRemainder_le_budget
#print axioms RectangleCLT.Companion.SplitV4.sum_ae_eq_zero_of_coordinate_second_moment_budget_zero

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.BennettTruncation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Bennett truncation dependency closure"
  logInfo m!"Audited {names.size} Bennett truncation theorem declarations; only propext, Classical.choice and Quot.sound."
