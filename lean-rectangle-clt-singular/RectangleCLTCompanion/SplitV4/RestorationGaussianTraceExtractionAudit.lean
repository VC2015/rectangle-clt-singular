import RectangleCLTCompanion.SplitV4.RestorationGaussianTraceExtraction
import Lean.Util.CollectAxioms

/-! Actual Gaussian coefficient extraction and complete common-base weight
restoration, with B.4's averaged matrix estimate explicit. This is a B.2
analytic reduction, before the two Stein identities/derivative partitions. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration
#print axioms RectangleCLT.Companion.SplitV4.gaussian_restoration_order_eq_integral
#print axioms RectangleCLT.Companion.SplitV4.translated_score_hasSum_expected_orders
#print axioms RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.RestorationGaussianTraceExtraction" then
          names := names.push n
  unless names.size > 0 do
    throwError "No Gaussian restoration coefficient extraction declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Gaussian restoration extraction closure"
  logInfo m!"Audited all {names.size} Gaussian restoration extraction theorem declarations."
