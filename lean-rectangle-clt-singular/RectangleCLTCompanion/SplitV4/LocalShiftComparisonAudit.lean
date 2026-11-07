import RectangleCLTCompanion.SplitV4.LocalShiftComparison
import Lean.Util.CollectAxioms

/-! Strict dependency audit for the local signed-shift comparison.
The local CDF error and local curvature are visible helper inputs; actual
lower-bound callers must discharge them using their concrete laws. -/

#print RectangleCLT.Companion.SplitV4.realCDF
#print RectangleCLT.Companion.SplitV4.localRealCDFDistance
#print RectangleCLT.Companion.SplitV4.localShiftTaylorCost
#print RectangleCLT.Companion.SplitV4.localShiftComparisonCost

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.localRealCDFDistance_le_iff
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.shifted_taylor_bound_local_global
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.local_shift_convolution_error_bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_cdf_shift_taylor_error_local
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_local_shift_comparison
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.independent_local_shift_comparison_of_local_distance

#print axioms RectangleCLT.Companion.SplitV4.independent_local_shift_comparison
#print axioms RectangleCLT.Companion.SplitV4.independent_local_shift_comparison_of_local_distance

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let modName := env.header.moduleNames[idx.toNat]!
        if modName == `RectangleCLTCompanion.SplitV4.LocalShiftComparison ||
            modName == `RectangleCLTCompanion.SplitV4.LocalizedShiftComparison then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in local signed-shift comparison closure"
  logInfo m!"Audited {names.size} local signed-shift comparison theorems."
