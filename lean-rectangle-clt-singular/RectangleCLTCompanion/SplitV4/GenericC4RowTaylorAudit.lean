import RectangleCLTCompanion.SplitV4.GenericC4RowTaylor
import Lean.Util.CollectAxioms

/-! Strict audit of generic smooth-test helpers. These declarations do
not by themselves assert the full arbitrary-test Lemma B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericRowTranslation_identity

#print axioms RectangleCLT.Companion.SplitV4.genericRowTranslation_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integrable_canonical_derivative_eval,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalDiagonal_bounded,
    ``RectangleCLT.Companion.SplitV4.integral_canonicalLinear_zero,
    ``RectangleCLT.Companion.SplitV4.genericValueTaylorPolynomial,
    ``RectangleCLT.Companion.SplitV4.genericGradientTaylorPolynomial,
    ``RectangleCLT.Companion.SplitV4.genericRowFourthRemainder,
    ``RectangleCLT.Companion.SplitV4.generic_row_remainder_pointwise,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalValue_shifted_bounded,
    ``RectangleCLT.Companion.SplitV4.genericRowTranslation_identity]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 helper closure"
  logInfo "Audited 9 GenericC4RowTaylor declarations, with genuine integrability and canonical derivatives."
