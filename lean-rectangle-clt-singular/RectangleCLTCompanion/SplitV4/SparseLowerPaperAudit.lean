import RectangleCLTCompanion.SplitV4.SparseCoordinateNegligible
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerLog_div_ell
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerRate_div_scale
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLowerScale_of_paperRate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseLower_coordinate_div_rate

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["RectangleCLTCompanion.SplitV4.SparseLowerLogScales", "RectangleCLTCompanion.SplitV4.SparseLowerPaperRate", "RectangleCLTCompanion.SplitV4.SparseCoordinateNegligible"].contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sparse paper scale conversions"
  logInfo m!"Audited {names.size} sparse paper scale conversion declarations; only the three permitted axioms."
