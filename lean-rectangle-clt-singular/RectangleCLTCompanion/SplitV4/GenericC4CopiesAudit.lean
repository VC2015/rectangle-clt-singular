import RectangleCLTCompanion.SplitV4.GenericC4Copies
import Lean.Util.CollectAxioms

/-! Strict audit of generic smooth-test helpers. These declarations do
not by themselves assert the full arbitrary-test Lemma B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.C4Test.integral_value_independent_copy

#print axioms RectangleCLT.Companion.SplitV4.C4Test.integral_value_independent_copy

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integral_independent_copy_of_integrable,
    ``RectangleCLT.Companion.SplitV4.indepFun_first_and_deleted_product_base,
    ``RectangleCLT.Companion.SplitV4.indepFun_row_deleted_gaussian_base,
    ``RectangleCLT.Companion.SplitV4.integral_canonical_independent_copy,
    ``RectangleCLT.Companion.SplitV4.C4Test.integral_value_independent_copy]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 helper closure"
  logInfo "Audited 5 GenericC4Copies declarations, with genuine integrability and canonical derivatives."
