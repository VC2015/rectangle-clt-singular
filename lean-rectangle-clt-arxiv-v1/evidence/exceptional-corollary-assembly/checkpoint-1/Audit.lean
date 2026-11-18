import RectangleCLTArxivV1.ExceptionalFourthBound
import RectangleCLTArxivV1.ExceptionalMatrixSuppliers
import RectangleCLTArxivV1.ExceptionalSeededTensor
import RectangleCLTArxivV1.ExceptionalSeededModel
import RectangleCLTArxivV1.ExceptionalSeededRemainder
import RectangleCLTArxivV1.ExceptionalComparison
import RectangleCLTArxivV1.ExceptionalSeededComparison
import RectangleCLTArxivV1.ExceptionalMain
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.exceptionalFourthCutoffExpectation,
    ``RectangleCLTArxivV1.exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates,
    ``RectangleCLTArxivV1.exceptional_seeded_matrix_estimates_of_angle,
    ``RectangleCLTArxivV1.ExceptionalNormalizedMatrixEstimates,
    ``RectangleCLTArxivV1.exceptional_copy_gaussian_outer_sum_eq_product,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_eq_cutoff_product,
    ``RectangleCLTArxivV1.exceptional_seeded_cutoff_product_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_pattern_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_remainder_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_separated_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_seeded_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_early_late_additive_bound,
    ``RectangleCLTArxivV1.exceptional_integral_majorant_bound,
    ``RectangleCLTArxivV1.exceptionalComparisonConstant,
    ``RectangleCLTArxivV1.exceptionalComparisonConstant_pos,
    ``RectangleCLTArxivV1.exceptional_normalized_remainder_late_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_normalized_remainder_majorant_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_normalized_time_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalSmoothComparisonConstant,
    ``RectangleCLTArxivV1.exceptionalSmoothComparisonConstant_pos,
    ``RectangleCLTArxivV1.exceptional_smooth_comparison_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalBandwidthConstant,
    ``RectangleCLTArxivV1.exceptionalBandwidthConstant_ge_one,
    ``RectangleCLTArxivV1.exceptionalBoundaryConstant,
    ``RectangleCLTArxivV1.exceptionalBoundaryConstant_ge_one,
    ``RectangleCLTArxivV1.exceptional_boundary_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptionalCoreConstant,
    ``RectangleCLTArxivV1.exceptionalCoreConstant_ge_one,
    ``RectangleCLTArxivV1.exceptional_CLT_of_matrix_suppliers,
    ``RectangleCLTArxivV1.exceptional_CLT_printed_of_matrix_suppliers,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.mk,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.cubic,
    ``RectangleCLTArxivV1.ExceptionalSeededAngleMatrixEstimates.pair]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
