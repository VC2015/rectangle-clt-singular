import RectangleCLTCompanion.SplitV4.RestorationDerivativeIdentification
import Lean.Util.CollectAxioms

/-! Strict dependency audit of exact rank-three and rank-four
identifications for the actual rational logistic smoother. -/

#print RectangleCLT.Companion.SplitV4.restorationThirdDerivative
#print RectangleCLT.Companion.SplitV4.restorationFourthDerivative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.multilinear_eq_sum_coordinate_directions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationThirdDerivative_eq_coordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.restorationFourthDerivative_eq_coordinate
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smootherC4Test_third_eq_restorationThirdDerivative
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smootherC4Test_fourth_eq_restorationFourthDerivative
#print axioms RectangleCLT.Companion.SplitV4.restorationThirdDerivative_eq_coordinate
#print axioms RectangleCLT.Companion.SplitV4.restorationFourthDerivative_eq_coordinate

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.RestorationDerivativeIdentification then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in restoration derivative identification closure"
  logInfo m!"Audited {names.size} exact restoration derivative identification theorems."
