import RectangleCLTCompanion.SplitV4.RareFamilyComparison
import Lean.Util.CollectAxioms

/-! Actual sparse masked mean/comparison contracts and strict transitive axiom audit. -/
#print RectangleCLT.Companion.SplitV4.familyRareShiftScale
#print RectangleCLT.Companion.SplitV4.familyRareLowerScale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyRare_observation_mean_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyRare_gaussian_mean_ratio
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_familyRare_discrepancy_div_scale

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTCompanion.SplitV4.RareFamilyShifts", "RectangleCLTCompanion.SplitV4.RareFamilyComparison"]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in actual masked sparse comparison"
  logInfo m!"Audited {names.size} actual masked sparse comparison declarations; only the permitted three axioms."
  logInfo "This is a reusable actual probability comparison under explicit numerical limits of primitive family parameters; it is not yet a complete standalone theorem6 or8 until those parameter limits are instantiated."
