import RectangleCLTCompanion.SplitV4.Smoothing
import RectangleCLTCompanion.GaussianEntropy
import Lean.Util.CollectAxioms

/-! Current Lemma 2 and its actual supremum contract. The single-face
Gaussian mean estimate is printed separately as Appendix B.3 reuse evidence.
This audit does not assert that the remaining Appendix B or C routes pass. -/

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.closedBoxSmoothingGap

set_option pp.all true in
#print RectangleCLT.Companion.SplitV4.smoothingDiscrepancy

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_le_smoothingDiscrepancy_add_endpoint

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.smoothingLemma2

set_option pp.all true in
#check RectangleCLT.Companion.gaussian_mean_relative_to_one_face

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.integrable_smoother_comp,
    ``RectangleCLT.Companion.SplitV4.smoother_mean_mem_Icc,
    ``RectangleCLT.Companion.SplitV4.closedBoxSmoothingGap_le_one,
    ``RectangleCLT.Companion.SplitV4.smoothingGaps_bddAbove,
    ``RectangleCLT.Companion.SplitV4.smoothingGaps_nonempty,
    ``RectangleCLT.Companion.SplitV4.closedBoxSmoothingGap_le_smoothingDiscrepancy,
    ``RectangleCLT.Companion.SplitV4.smoothingDiscrepancy_nonneg,
    ``RectangleCLT.Companion.SplitV4.smoothingDiscrepancy_le_one,
    ``RectangleCLT.Companion.SplitV4.smoothingDiscrepancy_le_iff,
    ``RectangleCLT.Companion.SplitV4.rectangleError_le_uniform_smoothing_add_endpoint,
    ``RectangleCLT.Companion.SplitV4.rectangleDistance_le_smoothingDiscrepancy_add_endpoint,
    ``RectangleCLT.Companion.SplitV4.smoothingLemma2,
    ``RectangleCLT.Companion.gaussian_mean_relative_to_one_face]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in smoothing/reuse endpoint {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited current Lemma 2 without extra bandwidth positivity, eleven smoothing helpers, and the B.3 reuse candidate."
