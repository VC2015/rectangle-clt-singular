import RectangleCLTArxivV1.GapMain
import RectangleCLTArxivV1.HFourthOriginalBound
import RectangleCLTArxivV1.HFourthSeededScales
import RectangleCLTArxivV1.HFourthPhysicalMatrixTransport
import RectangleCLTArxivV1.HFourthPairIndexTransport
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.GapNormalizedMatrixEstimates,
    ``RectangleCLTArxivV1.positiveGapComparisonConstant,
    ``RectangleCLTArxivV1.positiveGapComparisonConstant_pos,
    ``RectangleCLTArxivV1.positiveGap_normalized_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGap_normalized_remainder_majorant_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGap_normalized_time_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapSmoothComparisonConstant,
    ``RectangleCLTArxivV1.positiveGapSmoothComparisonConstant_pos,
    ``RectangleCLTArxivV1.positiveGap_smooth_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapBandwidthConstant,
    ``RectangleCLTArxivV1.positiveGapBandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGapBoundaryConstant,
    ``RectangleCLTArxivV1.positiveGapBoundaryConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGap_boundary_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.positiveGapCoreConstant,
    ``RectangleCLTArxivV1.positiveGapCoreConstant_ge_one,
    ``RectangleCLTArxivV1.positiveGap_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_original_expectation_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_seed_scale_range,
    ``RectangleCLTArxivV1.hFourth_normalized_seed_scale_range,
    ``RectangleCLTArxivV1.hFourthCubicGaussianScore_eq_selectorScore,
    ``RectangleCLTArxivV1.measurable_hFourthCubicGaussianScore_nuclear,
    ``RectangleCLTArxivV1.hFourth_cubic_matrix_sum_physical_transport,
    ``RectangleCLTArxivV1.hFourth_pair_matrix_sum_physical_transport,
    ``RectangleCLTArxivV1.hFourth_pair_nuclear_integral_add_comm,
    ``RectangleCLTArxivV1.hFourth_pair_supplier_of_angle_weighted_front]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
