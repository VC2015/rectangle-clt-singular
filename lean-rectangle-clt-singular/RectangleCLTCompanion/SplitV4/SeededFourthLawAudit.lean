import RectangleCLTCompanion.SplitV4.SeededFourthLaw
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandA_eq_seeded_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandB_eq_seeded_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandC_eq_seeded_product
#print axioms RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandA_eq_seeded_product
#print axioms RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandB_eq_seeded_product
#print axioms RectangleCLT.Companion.SplitV4.variableFourthPathIntegrandC_eq_seeded_product

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.SeededFourthLaw" then
          names := names.push n
  unless names.size > 0 do
    throwError "No seeded fourth law declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in seeded fourth law closure"
  logInfo m!"Audited all {names.size} seeded fourth law theorem declarations."
