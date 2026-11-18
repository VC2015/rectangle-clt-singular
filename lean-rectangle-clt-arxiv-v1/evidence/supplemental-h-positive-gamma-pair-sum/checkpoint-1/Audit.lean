import RectangleCLTArxivV1.PositiveGammaPairSum
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaMixedMassKernel_eq_ridgeDensity
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGamma_angle_mul_massKernel
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGamma_angle_mul_planeKernel
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaMixedMassKernel_norm_le
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaMixedPlaneKernel_norm_le
set_option pp.all true in
#check @RectangleCLTArxivV1.integrable_gamma_positiveEdge_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.integrable_gamma_positiveEdge_projection
set_option pp.all true in
#check @RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_projection
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGamma_mass_angle_soft_coarea
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGamma_projection_angle_soft_coarea
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_coarea_scaled
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_coarea_scaled
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_eq_gamma
set_option pp.all true in
#check @RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_eq_gamma

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection,
    ``RectangleCLTArxivV1.positiveGammaMixedMassKernel_eq_ridgeDensity,
    ``RectangleCLTArxivV1.positiveGamma_angle_mul_massKernel,
    ``RectangleCLTArxivV1.positiveGamma_angle_mul_planeKernel,
    ``RectangleCLTArxivV1.positiveGammaMixedMassKernel_norm_le,
    ``RectangleCLTArxivV1.positiveGammaMixedPlaneKernel_norm_le,
    ``RectangleCLTArxivV1.integrable_gamma_positiveEdge_mass,
    ``RectangleCLTArxivV1.integrable_gamma_positiveEdge_projection,
    ``RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_mass,
    ``RectangleCLTArxivV1.integrable_gaussian_positive_soft_pair_projection,
    ``RectangleCLTArxivV1.positiveGamma_mass_angle_soft_coarea,
    ``RectangleCLTArxivV1.positiveGamma_projection_angle_soft_coarea,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_coarea_scaled,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_coarea_scaled,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairMass_eq_gamma,
    ``RectangleCLTArxivV1.positiveGammaSoftOrderedPairProjection_eq_gamma]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
