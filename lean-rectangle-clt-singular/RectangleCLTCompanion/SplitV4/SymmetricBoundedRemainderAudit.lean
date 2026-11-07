import RectangleCLTCompanion.SplitV4.SymmetricBoundedRemainder
import Lean.Util.CollectAxioms

/-! Strict audit of the actual local Taylor remainder calibration. -/

#print RectangleCLT.Companion.SplitV4.boundedLocalDensityConstant
#print RectangleCLT.Companion.SplitV4.boundedLocalShiftCostConstant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_normalMaximumDensity_at_threshold_abs_le_sqrt_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_localShiftComparisonCost_le_log
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_boundedFamily_shift_second_moment_budget
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_local_shift_remainder_ratio
#print axioms RectangleCLT.Companion.SplitV4.tendsto_boundedFamily_local_shift_remainder_ratio

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let modName := env.header.moduleNames[idx.toNat]!
        if modName == `RectangleCLTCompanion.SplitV4.SymmetricBoundedRemainder ||
            modName == `RectangleCLTCompanion.SplitV4.SymmetricBoundedMoments then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in symmetric bounded remainder closure"
  logInfo m!"Audited {names.size} symmetric bounded shift-moment and Taylor-remainder theorems."
