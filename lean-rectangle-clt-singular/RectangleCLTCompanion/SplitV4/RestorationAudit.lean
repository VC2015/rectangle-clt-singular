import RectangleCLTCompanion.SplitV4.Restoration
import Lean.Util.CollectAxioms

/-! Whole Lemma B.2: universal constants for every model, baseline
paired derivatives, signed unshifted M1, and both-face M2 refinement. -/

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.PairedRestorationContract
set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.PairedRestorationConclusion
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.lemma_paired_restoration
#print axioms RectangleCLT.Companion.SplitV4.lemma_paired_restoration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.Restoration" then
          names := names.push n
  unless names.size > 0 do
    throwError "No full restoration declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in full restoration closure"
  logInfo m!"Audited all {names.size} full restoration theorem declarations."
