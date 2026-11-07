import RectangleCLTCompanion.SplitV4.MomentIntegrability
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_vector_of_coordinate_fourth_moments
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_vector_eq_zero_of_coordinate_centered
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_and_centered_of_coordinate_fourths

#print axioms RectangleCLT.Companion.SplitV4.abs_le_one_add_fourth
#print axioms RectangleCLT.Companion.SplitV4.vector_norm_le_one_add_sum_fourths
#print axioms RectangleCLT.Companion.SplitV4.integrable_vector_of_coordinate_fourth_moments
#print axioms RectangleCLT.Companion.SplitV4.integral_vector_eq_zero_of_coordinate_centered
#print axioms RectangleCLT.Companion.SplitV4.integrable_and_centered_of_coordinate_fourths

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.abs_le_one_add_fourth,
    ``RectangleCLT.Companion.SplitV4.vector_norm_le_one_add_sum_fourths,
    ``RectangleCLT.Companion.SplitV4.integrable_vector_of_coordinate_fourth_moments,
    ``RectangleCLT.Companion.SplitV4.integral_vector_eq_zero_of_coordinate_centered,
    ``RectangleCLT.Companion.SplitV4.integrable_and_centered_of_coordinate_fourths]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in fourth-moment integrability closure"
  logInfo "Audited all five fourth-moment integrability and centering helpers."
