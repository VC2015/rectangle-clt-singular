import RectangleCLTCompanion.SplitV4.PairedExchange
import Lean.Util.CollectAxioms

/-! This audit covers proof ingredients of Lemma G.3, rather than its still
open full analytic interpolation contract. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_trapezoidal

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_integral_exchange

#print axioms RectangleCLT.Companion.SplitV4.integral_trapezoidal
#print axioms RectangleCLT.Companion.SplitV4.truncation_event_swap
#print axioms RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_swap
#print axioms RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_mul_exchange
#print axioms RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_integral_exchange
#print axioms RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_even_exchange
#print axioms RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_integral_even_exchange
#print axioms RectangleCLT.Companion.SplitV4.paired_fourth_remainder_coefficient

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integral_trapezoidal,
    ``RectangleCLT.Companion.SplitV4.truncation_event_swap,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_swap,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_mul_exchange,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_integral_exchange,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_even_exchange,
    ``RectangleCLT.Companion.SplitV4.pairedTruncatedIncrement_integral_even_exchange,
    ``RectangleCLT.Companion.SplitV4.paired_fourth_remainder_coefficient]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in paired-exchange dependency closure"
  logInfo "Audited eight split-V4 paired-exchange/trapezoidal proof ingredients."
