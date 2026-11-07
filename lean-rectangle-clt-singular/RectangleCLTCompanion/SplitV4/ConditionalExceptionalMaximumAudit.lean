import RectangleCLTCompanion.SplitV4.ConditionalExceptionalMaximum
import Lean.Util.CollectAxioms

/-! Strict audit for the actual exceptional sum's Appendix E shift bound. -/

#print RectangleCLT.Companion.SplitV4.exceptionalArray
#print RectangleCLT.Companion.SplitV4.exceptionalMomentScale
#print RectangleCLT.Companion.SplitV4.polynomialEnvelopeV

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exceptionalArray_raw_maximum_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exceptional_normalized_norm_integrable
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.observed_exceptional_shift_maximum_le

#print axioms RectangleCLT.Companion.SplitV4.exceptionalArray_raw_maximum_le
#print axioms RectangleCLT.Companion.SplitV4.exceptional_normalized_maximum_le
#print axioms RectangleCLT.Companion.SplitV4.observed_exceptional_shift_maximum_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]!.toString == "RectangleCLTCompanion.SplitV4.ConditionalExceptionalMaximum" then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in actual exceptional-maximum closure"
  logInfo m!"Audited {names.size} actual exceptional-maximum theorem declarations; only the permitted three axioms."
  logInfo "The observed exceptional shift satisfies sqrt(L)*E||R|| <= 2*C_E*(L*sqrt(v_T)+V_q)."
