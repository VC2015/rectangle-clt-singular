import RectangleCLTCompanion.SplitV4.Printed.ClockMarkov
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.Printed.clockLogVector
#print RectangleCLT.Companion.SplitV4.Printed.clockLogMaximum
#print RectangleCLT.Companion.SplitV4.Printed.randomThresholdRadius
#print RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.clock_abs_log_ratio_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_le_log_add_one_of_exponential_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.integral_randomThresholdRadius_le_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.expectedClockCutoff_bad_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["RectangleCLTCompanion.SplitV4.Printed.ClockTails", "RectangleCLTCompanion.SplitV4.Printed.ClockMean", "RectangleCLTCompanion.SplitV4.Printed.ClockMarkov"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed clock expectation route"
  logInfo m!"Audited {names.size} printed exponential-clock tail, expected-width and Markov declarations; only permitted axioms."
