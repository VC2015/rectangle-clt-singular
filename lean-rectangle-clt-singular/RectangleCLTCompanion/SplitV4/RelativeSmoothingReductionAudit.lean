import RectangleCLTCompanion.SplitV4.RelativeSmoothingReduction
import Lean.Util.CollectAxioms

/-! This audits a conditional smoothing reduction, not the whole CLT. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeCLT_of_uniform_smooth_comparison

#print axioms RectangleCLT.Companion.SplitV4.relativeCLT_of_uniform_smooth_comparison

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.relativeComparisonLog_one_le,
    ``RectangleCLT.Companion.SplitV4.relativeCLT_of_uniform_smooth_comparison]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative smoothing reduction closure"
  logInfo "Audited 2 RelativeSmoothingReduction declarations; only the three standard axioms are permitted."
