import RectangleCLTCompanion.SplitV4.GenericC4FourthIdentity
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericSelectorOperator_fourth_identity

#print axioms RectangleCLT.Companion.SplitV4.genericSelectorOperator_fourth_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.canonicalDiagonal_two_eq_coordinates,
    ``RectangleCLT.Companion.SplitV4.integral_canonicalDiagonal_two_eq_coordinates,
    ``RectangleCLT.Companion.SplitV4.canonical_hessianTrace_covariance_eq_moments,
    ``RectangleCLT.Companion.SplitV4.genericFixedHeat_eq_half_sum_moments,
    ``RectangleCLT.Companion.SplitV4.genericFullMoment,
    ``RectangleCLT.Companion.SplitV4.genericCommonCubic,
    ``RectangleCLT.Companion.SplitV4.genericSelectorFourthRemainder,
    ``RectangleCLT.Companion.SplitV4.generic_row_mask_commonPoint_identity,
    ``RectangleCLT.Companion.SplitV4.genericSelectorOperator_fourth_identity]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 9 GenericC4FourthIdentity declarations; only the three standard axioms are permitted."
