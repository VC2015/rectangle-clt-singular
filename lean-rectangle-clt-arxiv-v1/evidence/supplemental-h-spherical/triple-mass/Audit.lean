import RectangleCLTArxivV1.SupplementalHTripleMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.hardPairThirdFrame_span
set_option pp.all true in
#check @RectangleCLTArxivV1.hardPairThirdSection_selected_levels
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_scale_eq_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_weight_eq_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianFrameHardMass_three_choices_of_supporting_levels

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianFrameHardMass_nonneg,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_frame_independent,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_native_triple,
    ``RectangleCLTArxivV1.nativeTripleFrame_orthonormal,
    ``RectangleCLTArxivV1.hardPairThirdScale_pos,
    ``RectangleCLTArxivV1.hardPairThirdDirection_geometry,
    ``RectangleCLTArxivV1.hardPairThirdFrame_orthonormal,
    ``RectangleCLTArxivV1.hardPairResidualNormal_eq_sub,
    ``RectangleCLTArxivV1.hardPairThirdFrame_span,
    ``RectangleCLTArxivV1.hardPairThirdSection_selected_levels,
    ``RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_nonneg,
    ``RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_zero_of_zero_residual,
    ``RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_scale_eq_mass,
    ``RectangleCLTArxivV1.hardGaussianPairThirdBoundaryDensity_weight_eq_mass,
    ``RectangleCLTArxivV1.hardPairThirdDirection_own_pairing,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_three_incident_choices,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_of_spanning_levels,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_three_choices_of_supporting_levels]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
