import RectangleCLTCompanion.SplitV4.SparseMaskLogAsymptotics
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMaskPi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMaskLog

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMaskLog_rpow_div_rpow

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMask_loglog_ratio

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMaskPi_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMaskPi_log_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMaskPi_log

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMaskPi

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMask_log_inverse_identity

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseMask_log_inverse_ratio

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.sparseMaskPi,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMaskLog,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMaskLog_rpow_div_rpow,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMask_loglog_ratio,
    ``RectangleCLT.Companion.SplitV4.sparseMaskPi_pos,
    ``RectangleCLT.Companion.SplitV4.sparseMaskPi_log_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMaskPi_log,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMaskPi,
    ``RectangleCLT.Companion.SplitV4.sparseMask_log_inverse_identity,
    ``RectangleCLT.Companion.SplitV4.tendsto_sparseMask_log_inverse_ratio]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual sparse lower numerical calibration"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited genuine scalar sparse-mask calibration: exact powers, logarithmic probability asymptotics, original rounded-count coverage, valid probabilities and negligible genuine comparison costs."
