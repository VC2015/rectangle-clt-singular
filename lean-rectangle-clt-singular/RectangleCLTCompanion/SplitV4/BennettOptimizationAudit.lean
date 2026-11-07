import RectangleCLTCompanion.SplitV4.BennettOptimization
import Lean.Util.CollectAxioms

/-! Genuine scalar Bennett optimizer inequalities. These are helpers for
the polynomial proposition, rather than a probability bound on their own. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_log_power_div_rpow_bound

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exists_bennett_log_denominator_lower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bennett_large_regime_ratio_bounds

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.bennettParameterLog_ge_one,
    ``RectangleCLT.Companion.SplitV4.exists_log_power_div_rpow_bound,
    ``RectangleCLT.Companion.SplitV4.exists_bennett_log_denominator_lower,
    ``RectangleCLT.Companion.SplitV4.bennett_large_regime_ratio_bounds]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in Bennett optimizer {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited global Bennett logarithmic denominator and power-ratio bounds."
