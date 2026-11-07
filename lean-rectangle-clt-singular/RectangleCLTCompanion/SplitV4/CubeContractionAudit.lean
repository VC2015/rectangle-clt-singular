import RectangleCLTCompanion.SplitV4.CubeContraction
import Lean.Util.CollectAxioms

/-! Strict audit of the actual square-contraction step in Appendix C. -/

#print RectangleCLT.Companion.SplitV4.absoluteLinearMaximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.finiteMaximum_pair_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cube_average_contraction
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_cube_square_contraction
#print axioms RectangleCLT.Companion.SplitV4.cube_average_contraction
#print axioms RectangleCLT.Companion.SplitV4.cube_square_contraction_intrinsic
#print axioms RectangleCLT.Companion.SplitV4.integral_cube_square_contraction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod.toString == "RectangleCLTCompanion.SplitV4.CubeContraction" then
          names := names.push n
  unless names.size > 0 do
    throwError "No cube-contraction theorem declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in cube-contraction dependency closure"
  logInfo m!"Audited all {names.size} cube-contraction theorem declarations; only the three permitted axioms."
