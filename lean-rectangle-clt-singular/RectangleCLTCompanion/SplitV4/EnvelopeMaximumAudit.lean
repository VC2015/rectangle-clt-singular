import RectangleCLTCompanion.SplitV4.EnvelopeMaximum
import Lean.Util.CollectAxioms

/-! The actual expected maximum and its centered-truncation proof chain.
The audit rejects every nonstandard axiom in the transitive closure. -/

#print RectangleCLT.Companion.SplitV4.envelopeMaximumConstant
#check RectangleCLT.Companion.SplitV4.bennettCorrection_le_exp_one_mul_sq
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.bounded_vector_bernstein_maximum
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.envelope_cutoff_rate_identities
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sumVector_ae_zero_of_envelope_budget_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.expected_maximum_under_envelope_moment
#print axioms RectangleCLT.Companion.SplitV4.expected_maximum_under_envelope_moment

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!
        if mod == `RectangleCLTCompanion.SplitV4.EnvelopeMaximum ||
            mod == `RectangleCLTCompanion.SplitV4.EnvelopeTruncation then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in Appendix E maximum dependency closure"
  logInfo m!"Audited {names.size} Appendix E maximum/truncation theorem declarations; only propext, Classical.choice and Quot.sound."
