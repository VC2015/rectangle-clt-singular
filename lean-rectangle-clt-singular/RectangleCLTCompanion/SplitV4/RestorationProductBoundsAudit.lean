import RectangleCLTCompanion.SplitV4.RestorationProductBounds
import Lean.Util.CollectAxioms

/-! B.2 source-scale constants on the actual Gaussian product law,
including all zero-scale cases and both relative refinements. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_paired_baseline_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_third_relative_product
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restoration_fourth_relative_product
#print axioms RectangleCLT.Companion.SplitV4.restoration_paired_baseline_product
#print axioms RectangleCLT.Companion.SplitV4.restoration_third_relative_product
#print axioms RectangleCLT.Companion.SplitV4.restoration_fourth_relative_product

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationProductBounds" then
          names := names.push n
  unless names.size > 0 do
    throwError "No product restoration bounds found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in product restoration bounds closure"
  logInfo m!"Audited all {names.size} product restoration bound theorem declarations."
