import RectangleCLTCompanion.SplitV4.SmootherC4
import Lean.Util.CollectAxioms

/-! The actual face-smoother C4 constructor, including its proof fields and
the exact identification of the paired fourth-derivative contraction. -/

#print RectangleCLT.Companion.SplitV4.C4Test
#print RectangleCLT.Companion.SplitV4.smootherC4Bound
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smootherC4Test
#check RectangleCLT.Companion.SplitV4.multilinear_norm_le_coordinate_bound
#check RectangleCLT.Companion.SplitV4.smoother_iteratedFDeriv_norm_le
#check RectangleCLT.Companion.SplitV4.smootherC4Test_value
#check RectangleCLT.Companion.SplitV4.smootherC4Test_gradient_eq_translationD1
#check RectangleCLT.Companion.SplitV4.smootherC4Test_secondDiagonal_eq_translationD2
#check RectangleCLT.Companion.SplitV4.smootherC4Test_thirdDiagonal_eq_translationD3
#check RectangleCLT.Companion.SplitV4.smootherC4Test_fourthDiagonal_eq_translationD4
#check RectangleCLT.Companion.SplitV4.smootherC4Test_fourthDiagonal_eq_diagonalFourth
#print axioms RectangleCLT.Companion.SplitV4.smootherC4Test
#print axioms RectangleCLT.Companion.SplitV4.smootherC4Test_fourthDiagonal_eq_diagonalFourth

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[``RectangleCLT.Companion.SplitV4.smootherC4Test]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! == `RectangleCLTCompanion.SplitV4.SmootherC4 then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in actual smoother C4 dependency closure"
  logInfo m!"Audited the actual smoother C4 constructor and {names.size - 1} theorem declarations; only propext, Classical.choice and Quot.sound."
