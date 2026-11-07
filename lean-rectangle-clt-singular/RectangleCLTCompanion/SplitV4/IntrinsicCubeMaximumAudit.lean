import RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum
import Lean.Util.CollectAxioms

#print RectangleCLT.Companion.SplitV4.cubeSign
#print RectangleCLT.Companion.SplitV4.cubeLinear
#print RectangleCLT.Companion.SplitV4.positiveLinearMaximum
#print RectangleCLT.Companion.SplitV4.intrinsicCubeMean
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.avg_exp_cubeLinear_le
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsicCubeMean_le_sqrt_log

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if mod == "RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum" ||
            mod == "RectangleCLTCompanion.SplitV4.IntrinsicCubeData" then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sign-cube maximum dependency closure"
  logInfo m!"Audited {names.size} sign-cube data and maximum theorem declarations."
  logInfo "The intrinsic cube boundary probability estimate is a separate endpoint."
