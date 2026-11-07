import RectangleCLTCompanion.SplitV4.ClockCutoff
import Lean.Util.CollectAxioms

/-! Actual clock-law, cutoff-probability, and displacement audit. -/

#print RectangleCLT.Companion.SplitV4.clockGood
#print RectangleCLT.Companion.SplitV4.clockRadius
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.clockGood_compl_probability_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.clockGood_shift_abs_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.clockRadius_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! == `RectangleCLTCompanion.SplitV4.ClockCutoff then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in clock cutoff dependency closure"
  logInfo m!"Audited {names.size} actual exponential clock cutoff theorem declarations."
