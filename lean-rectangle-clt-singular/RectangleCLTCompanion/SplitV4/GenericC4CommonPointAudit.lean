import RectangleCLTCompanion.SplitV4.GenericC4CommonPoint
import Lean.Util.CollectAxioms

/-! Strict audit of generic smooth-test helpers. These declarations do
not by themselves assert the full arbitrary-test Lemma B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_canonical_third_shift_sub

#print axioms RectangleCLT.Companion.SplitV4.integral_canonical_third_shift_sub

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integral_linear_centered_zero,
    ``RectangleCLT.Companion.SplitV4.canonical_mixed_cubic_integral_zero,
    ``RectangleCLT.Companion.SplitV4.integral_canonical_hessian_shift_sub,
    ``RectangleCLT.Companion.SplitV4.integral_canonical_third_shift_sub]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 helper closure"
  logInfo "Audited 4 GenericC4CommonPoint declarations, with genuine integrability and canonical derivatives."
