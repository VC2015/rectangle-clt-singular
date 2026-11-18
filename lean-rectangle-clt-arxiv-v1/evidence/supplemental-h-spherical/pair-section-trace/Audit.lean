import RectangleCLTArxivV1.SupplementalHPairSectionTrace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSignedSection_integrable
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSignedSection_eq_residual_trace
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSection_Green_of_slack
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairSection_Green_weighted_of_slack

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.hardPairResidualNormal_orthogonal,
    ``RectangleCLTArxivV1.gaussianPairSectionPoint_faceDot_residual,
    ``RectangleCLTArxivV1.vectorNormSq_gaussianPairSectionPoint,
    ``RectangleCLTArxivV1.gaussianPairSectionPoint_mem_event_iff,
    ``RectangleCLTArxivV1.hardGaussianPairSectionProbability_eq_residual_CDF,
    ``RectangleCLTArxivV1.hardGaussianPairSignedSection_integrable,
    ``RectangleCLTArxivV1.hardGaussianPairSignedSection_eq_residual_trace,
    ``RectangleCLTArxivV1.hardGaussianPairSection_Green_of_slack,
    ``RectangleCLTArxivV1.hardGaussianPairSection_Green_weighted_of_slack]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
