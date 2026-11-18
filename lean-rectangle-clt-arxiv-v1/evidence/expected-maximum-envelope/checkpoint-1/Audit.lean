import RectangleCLTArxivV1.EnvelopeExpectedMaximum
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.expectedMaximum_negative_budget_obstruction,
    ``RectangleCLTArxivV1.coordinate_sq_integrable_of_envelope_moment,
    ``RectangleCLTArxivV1.integrable_norm_sum_of_envelope_moment,
    ``RectangleCLTArxivV1.expected_maximum_under_envelope_moment,
    ``RectangleCLTArxivV1.lemma_E1_expected_maximum,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_maximum_under_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.Printed.bounded_vector_bernstein_maximum_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.Printed.expected_le_exp_moment_by_tail_integration,
    ``RectangleCLT.Companion.SplitV4.integral_norm_sum_le_centeredTruncation_add_tail,
    ``RectangleCLT.Companion.SplitV4.sumVector_ae_zero_of_envelope_budget_zero]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{target} depends on {axiomName}"
    logInfo m!"{target} uses {axioms.toList}"
  logInfo m!"PASS: {targets.size} strict transitive audits."
