import RectangleCLTCompanion.SplitV4.RelativeMomentTransfer
import Lean.Util.CollectAxioms

/-! Exact moment-transfer endpoint and strict permitted-axiom audit.
This audit does not assert the full polyhedral CLT corollary. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativeMomentBounds_projected
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.covariance_projected_sum

#print axioms RectangleCLT.Companion.SplitV4.relativeMomentBounds_projected
#print axioms RectangleCLT.Companion.SplitV4.projected_relativeThirdMatrix_quadratic
#print axioms RectangleCLT.Companion.SplitV4.projected_relativeFourthMatrix_quadratic_le
#print axioms RectangleCLT.Companion.SplitV4.projected_relativeFreshFourthMatrix_quadratic_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.RelativeMomentTransfer then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative-moment transfer closure"
  logInfo m!"Audited {names.size} relative-moment transfer helpers; full Corollary 3 remains open."
