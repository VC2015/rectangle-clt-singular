import RectangleCLTCompanion.SplitV4.GenericC4Taylor
import Lean.Util.CollectAxioms

/-! Strict audit of generic smooth-test helpers. These declarations do
not by themselves assert the full arbitrary-test Lemma B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.canonical_third_taylor_one

#print axioms RectangleCLT.Companion.SplitV4.canonical_third_taylor_one

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_iteratedFDeriv_segment,
    ``RectangleCLT.Companion.SplitV4.canonicalDiagonal,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_canonicalDiagonal_segment,
    ``RectangleCLT.Companion.SplitV4.canonical_value_taylor_four,
    ``RectangleCLT.Companion.SplitV4.canonical_gradient_taylor_three,
    ``RectangleCLT.Companion.SplitV4.canonical_hessian_taylor_two,
    ``RectangleCLT.Companion.SplitV4.canonical_third_taylor_one]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 helper closure"
  logInfo "Audited 7 GenericC4Taylor declarations, with genuine integrability and canonical derivatives."
