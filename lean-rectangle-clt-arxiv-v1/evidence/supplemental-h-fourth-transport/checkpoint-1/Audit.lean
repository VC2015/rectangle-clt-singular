import RectangleCLTArxivV1.SupplementalHFourthTransportData
import RectangleCLTArxivV1.SupplementalHFourthTransportFacet
import RectangleCLTArxivV1.SupplementalHFourthTransportRidge
import RectangleCLTArxivV1.SupplementalHFourthTransportSlack
import RectangleCLTArxivV1.SupplementalHFourthTransportGeometry
import RectangleCLTArxivV1.SupplementalHFourthTransportSum
import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.fourthTransportRadius,
    ``RectangleCLTArxivV1.continuous_fourthTransportRadius,
    ``RectangleCLTArxivV1.fourthFacetEvent,
    ``RectangleCLTArxivV1.fourthPairEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthFacetEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthPairEvent,
    ``RectangleCLTArxivV1.fourthFacetEvent_section,
    ``RectangleCLTArxivV1.gaussianThresholdSectionProbability_eq_strict_of_slack,
    ``RectangleCLTArxivV1.fourthFacet_fiber_coefficient_bound,
    ``RectangleCLTArxivV1.hard_facet_coefficient_le_fourth_event,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint,
    ``RectangleCLTArxivV1.fourthRidge_fiber_coefficient_bound,
    ``RectangleCLTArxivV1.fourthPairEvent_section,
    ``RectangleCLTArxivV1.hard_ridge_coefficient_le_fourth_event_strict,
    ``RectangleCLTArxivV1.gaussianPairBase_ae_no_boundary_of_slack,
    ``RectangleCLTArxivV1.gaussianPairBase_probability_le_eq_lt_of_slack,
    ``RectangleCLTArxivV1.hardGaussianRidgeDensity_eq_strict_of_slack,
    ``RectangleCLTArxivV1.hard_ridge_density_coefficient_le_fourth_event,
    ``RectangleCLTArxivV1.fourthFacetEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthPairEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthStratumEvent,
    ``RectangleCLTArxivV1.measurableSet_fourthStratumEvent,
    ``RectangleCLTArxivV1.fourthStratumEvent_mem_tube,
    ``RectangleCLTArxivV1.fourthStratumEvent_shared_point,
    ``RectangleCLTArxivV1.fourthOuterLayer,
    ``RectangleCLTArxivV1.measurableSet_fourthOuterLayer,
    ``RectangleCLTArxivV1.fourthStratumEvent_mem_outerLayer,
    ``RectangleCLTArxivV1.fourthStratumEvent_indicator_sum_le,
    ``RectangleCLTArxivV1.fourthStratumEvent_integral_sum_le,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_sum_le,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius,
    ``RectangleCLTArxivV1.continuous_fourthThreeFaceRadius,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_ge_one,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_add_le,
    ``RectangleCLTArxivV1.fourthThreeFaceRadius_fourth_integrable,
    ``RectangleCLTArxivV1.supplementalHRadius_abs_inner_small_span_le,
    ``RectangleCLTArxivV1.supplementalHRadius_face_abs_le,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_norm_le_threeFaceRadius,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_sum_le_threeFaceRadius,
    ``RectangleCLTArxivV1.fourthOuterLayer_shift_threshold,
    ``RectangleCLTArxivV1.fourthGreenTubeCoefficient_affine_sum_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
