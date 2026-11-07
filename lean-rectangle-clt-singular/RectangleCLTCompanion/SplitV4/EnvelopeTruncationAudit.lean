import RectangleCLTCompanion.SplitV4.EnvelopeTruncation
import Lean.Util.CollectAxioms

/-! Strict audit of the centered vector truncation and its actual expected-
norm transfer, used in the Appendix E envelope-maximum proof. -/

#print RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation
#check RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_boundedHypotheses
#check RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_second_moment_le
#check RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_second_moment_sum_le
#check RectangleCLT.Companion.SplitV4.truncationMean_eq_integral
#check RectangleCLT.Companion.SplitV4.integral_vector_eq_zero_of_coordinate_centering
#check RectangleCLT.Companion.SplitV4.norm_truncationMean_le_integral_remainder

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail

#print axioms RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_boundedHypotheses
#print axioms RectangleCLT.Companion.SplitV4.envelopeCenteredTruncation_second_moment_sum_le
#print axioms RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.EnvelopeTruncation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in centered envelope truncation dependency closure"
  logInfo m!"Audited {names.size} centered envelope truncation theorems; only propext, Classical.choice and Quot.sound."
