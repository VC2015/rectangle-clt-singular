import RectangleCLTArxivV1.SupplementalHFourthTransportFacetSum
import RectangleCLTArxivV1.SupplementalHFourthTransportRegularity
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.fourthRidgeNormalPoint_supporting_levels,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_coefficient_identity,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_off_diagonal,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_coefficient_sum,
    ``RectangleCLTArxivV1.abs_hardGaussianWeightedFacetIntegral_le_threeFace_tube,
    ``RectangleCLTArxivV1.residualThresholdRegularity_isOpen,
    ``RectangleCLTArxivV1.measurableSet_all_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_affine_residualThresholdRegularity,
    ``RectangleCLTArxivV1.ae_threshold_ae_base_residualThresholdRegularity,
    ``RectangleCLTArxivV1.measurable_thresholdSignedSection_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianWeightedFacetIntegral,
    ``RectangleCLTArxivV1.fourthTransport_measurableSet_gaussianOutwardVariableTube,
    ``RectangleCLTArxivV1.hardGaussianWeightedFacetIntegral_base_tube_bound,
    ``RectangleCLTArxivV1.ae_hardGaussianWeightedFacetIntegral_concentrated_base]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
