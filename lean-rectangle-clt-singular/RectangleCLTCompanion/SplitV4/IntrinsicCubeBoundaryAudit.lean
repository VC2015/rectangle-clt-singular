import RectangleCLTCompanion.SplitV4.IntrinsicCubeBoundary
import Lean.Util.CollectAxioms

/-! Whole-statement audit of Lemma C.1 (`appx-lem:cube-boundary`). The
probability law, affine maximum, and positive maximum are printed. The
intrinsic estimate retains the actual expected maximum; its logarithmic
specialization is an additional conclusion. Active supporting branches
handle ties directly, without assuming unique maximizers. -/

#print RectangleCLT.Companion.SplitV4.cubeUniformLaw
#print RectangleCLT.Companion.SplitV4.cubeSign
#print RectangleCLT.Companion.SplitV4.cubeLinear
#print RectangleCLT.Companion.SplitV4.affineCubeMaximum
#print RectangleCLT.Companion.SplitV4.positiveLinearMaximum
#print RectangleCLT.Companion.SplitV4.activeCubeBranch
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsic_cube_boundary
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.intrinsic_cube_mean_le_sqrt_log

#print axioms RectangleCLT.Companion.SplitV4.cube_avg_signed_coordinate
#print axioms RectangleCLT.Companion.SplitV4.affineCube_edge_support
#print axioms RectangleCLT.Companion.SplitV4.cubeEdgeFlux_controls_squares
#print axioms RectangleCLT.Companion.SplitV4.intrinsic_cube_boundary
#print axioms RectangleCLT.Companion.SplitV4.intrinsic_cube_mean_le_sqrt_log

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.IntrinsicCubeBoundary" ||
            mod.toString == "RectangleCLTCompanion.SplitV4.IntrinsicCubeData" ||
            mod.toString == "RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum" then
          names := names.push n
  unless names.size > 0 do
    throwError "No intrinsic-cube theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Lemma C.1 dependency closure"
  logInfo m!"Audited all {names.size} intrinsic-cube theorem declarations; only the three permitted axioms."
