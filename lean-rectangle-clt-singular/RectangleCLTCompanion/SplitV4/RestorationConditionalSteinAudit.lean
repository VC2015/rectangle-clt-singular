import RectangleCLTCompanion.SplitV4.RestorationConditionalStein
import Lean.Util.CollectAxioms

/-! Actual third/fourth Fréchet derivatives, rectangular support factors,
two Gaussian Stein identities, and all random-array moment justifications. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_restorationThirdDerivative_stein
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.array_restorationFourthDerivative_stein
#print axioms RectangleCLT.Companion.SplitV4.array_restorationThirdDerivative_stein
#print axioms RectangleCLT.Companion.SplitV4.array_restorationFourthDerivative_stein

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationConditionalStein" then
          names := names.push n
  unless names.size > 0 do
    throwError "No conditional restoration Stein declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in conditional restoration Stein closure"
  logInfo m!"Audited all {names.size} conditional restoration Stein theorem declarations."
