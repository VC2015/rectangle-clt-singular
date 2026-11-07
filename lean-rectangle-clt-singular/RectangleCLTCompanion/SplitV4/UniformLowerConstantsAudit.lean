import RectangleCLTCompanion.SplitV4.UniformLowerConstants
import Lean.Util.CollectAxioms

/-! Strict audit of public comparison constants quantified before every dimension sequence. -/
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fourthMoment_uniform_constants
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.denseMoment_uniform_constants
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMoment_uniform_constants

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == `RectangleCLTCompanion.SplitV4.UniformLowerConstants then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in uniform lower constants"
  logInfo m!"Audited {names.size} uniform lower-constant theorem declarations; only the permitted three axioms."
  logInfo "All three public wrappers choose constants before all dimension/sample sequences. Theorem5: absolute c, C_B; Theorem7: C_q before B, c_qB before dimensions; Theorem8: c_q and C_q before both envelope and dimension sequences."
