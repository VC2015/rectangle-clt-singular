import RectangleCLTArxivV1.SeededIntrinsicConcentration
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLTArxivV1.boundedRectangleFaceLayer_min
set_option pp.all true in
#check RectangleCLTArxivV1.integral_norm_bernoulliArraySum_le
set_option pp.all true in
#check RectangleCLTArxivV1.intrinsicRectangleConcentration_bounded_endpoint
set_option pp.all true in
#check RectangleCLTArxivV1.intrinsicRectangleConcentration_gaussian_endpoint
set_option pp.all true in
#check RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["RectangleCLTArxivV1.IntrinsicBoundedConcentration",
    "RectangleCLTArxivV1.ActiveFaceCoordinates", "RectangleCLTArxivV1.BoundedRectangleIntrinsic",
    "RectangleCLTArxivV1.ThinnedMaximum", "RectangleCLTArxivV1.SeededIntrinsicConcentration"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push n
  unless names.size > 0 do throwError "No bounded intrinsic theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in bounded intrinsic dependency closure"
  logInfo m!"Audited {names.size} bounded intrinsic theorem declarations; only propext, Classical.choice and Quot.sound."
