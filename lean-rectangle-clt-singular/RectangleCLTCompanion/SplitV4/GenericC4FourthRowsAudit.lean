import RectangleCLTCompanion.SplitV4.GenericC4FourthRows
import Lean.Util.CollectAxioms

/-! Strict axiom audit of the actual generic C4 interpolation declarations. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericRow_commonPoint_identity

#print axioms RectangleCLT.Companion.SplitV4.genericRow_commonPoint_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor,
    ``RectangleCLT.Companion.SplitV4.norm_canonicalFourthTensor_le,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalFourthTensor_interval_prod,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_interval_fubini_data,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_pair_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_triple_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowB,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowC,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowB_eq_correction,
    ``RectangleCLT.Companion.SplitV4.genericFourthRowC_eq_correction,
    ``RectangleCLT.Companion.SplitV4.genericBernoulliMoment,
    ``RectangleCLT.Companion.SplitV4.genericRow_commonPoint_identity]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic C4 interpolation closure"
  logInfo "Audited 12 GenericC4FourthRows declarations; only the three standard axioms are permitted."
