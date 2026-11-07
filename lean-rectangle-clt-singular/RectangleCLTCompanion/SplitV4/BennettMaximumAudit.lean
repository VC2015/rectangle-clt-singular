import RectangleCLTCompanion.SplitV4.BennettMaximum
import Lean.Util.CollectAxioms

/-! Expanded G.4 contracts and strict transitive axiom checks, including
the actual MGF, optimization, truncation and zero-variance dependencies. -/

#print RectangleCLT.Companion.SplitV4.bennettCorrection
#print RectangleCLT.Companion.SplitV4.bennettKernel
#print RectangleCLT.Companion.SplitV4.bennettTruncate
#print RectangleCLT.dimensionLog
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_centered_bennett_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_sum_bennett_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.truncated_bennett_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.truncated_bennett_maximum_zero_variance
#print axioms RectangleCLT.Companion.SplitV4.truncated_bennett_maximum
#print axioms RectangleCLT.Companion.SplitV4.truncated_bennett_maximum_zero_variance

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod == `RectangleCLTCompanion.SplitV4.BennettMaximum ||
            mod == `RectangleCLTCompanion.SplitV4.BennettTruncation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in G.4 Bennett maximum dependency closure"
  logInfo m!"Audited {names.size} G.4 Bennett/truncation theorem declarations; only propext, Classical.choice and Quot.sound."
