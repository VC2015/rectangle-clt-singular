import RectangleCLTCompanion.SplitV4.RelativePathJoin
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoother_gap_le_actual_two_stage_gaps

#print axioms RectangleCLT.Companion.SplitV4.smoother_gap_le_actual_two_stage_gaps

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integral_normalizedSeeded_zero_eq_directSlepianExpectation,
    ``RectangleCLT.Companion.SplitV4.integral_normalizedSeeded_one_eq_gaussian,
    ``RectangleCLT.Companion.SplitV4.smoother_gap_le_actual_two_stage_gaps]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative path/face helper closure"
  logInfo "Audited 3 RelativePathJoin declarations; only the three standard axioms are permitted."
