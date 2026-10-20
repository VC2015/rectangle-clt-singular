import RectangleCLTCompanion
import Lean.Util.CollectAxioms

/-! Audit every theorem in every imported companion module, including
private helper theorems and the vendored Prékopa development. A shared
visited set audits the transitive dependency closure once, including
the final unconditional CLT theorems. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString.startsWith "RectangleCLTCompanion." then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in companion dependency closure"
  logInfo m!"Audited {names.size} companion theorem declarations; only propext, Classical.choice and Quot.sound."
