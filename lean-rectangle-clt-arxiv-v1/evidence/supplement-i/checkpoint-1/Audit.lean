import RectangleCLTArxivV1.SupplementalIRestriction
import RectangleCLTArxivV1.SupplementalIBudget
import RectangleCLTArxivV1.SupplementalIExceptional
import RectangleCLTArxivV1.SupplementalIIntegration
import RectangleCLTArxivV1.SupplementalIOptimization
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.exceptionalCutoffDet,
    ``RectangleCLTArxivV1.correlationAngleWeight,
    ``RectangleCLTArxivV1.separatedFirstPair,
    ``RectangleCLTArxivV1.separatedSelectorTuples,
    ``RectangleCLTArxivV1.exceptionalCutoffDet_bounds,
    ``RectangleCLTArxivV1.correlationAngleWeight_nonneg,
    ``RectangleCLTArxivV1.correlationAngleWeight_ge_det,
    ``RectangleCLTArxivV1.exceptionalCutoffDet_le_angle,
    ``RectangleCLTArxivV1.separatedFirstPair_congr,
    ``RectangleCLTArxivV1.separated_nonnegative_sum_le_angle_weighted,
    ``RectangleCLTArxivV1.separated_selector_nuclear_integral_le_angle_weighted,
    ``RectangleCLTArxivV1.correlationGap,
    ``RectangleCLTArxivV1.exceptionalCoordinateWeight,
    ``RectangleCLTArxivV1.exceptionalCorrelationBudget,
    ``RectangleCLTArxivV1.exceptionalFaceSine,
    ``RectangleCLTArxivV1.exceptionalCoordinateWeight_nonneg,
    ``RectangleCLTArxivV1.exceptionalCorrelationBudget_nonneg,
    ``RectangleCLTArxivV1.ordered_sum_eq_twice_upper,
    ``RectangleCLTArxivV1.exceptional_ordered_coordinate_sum,
    ``RectangleCLTArxivV1.cap_signed_correlation_abs,
    ``RectangleCLTArxivV1.exceptional_sine_le_gap_weight,
    ``RectangleCLTArxivV1.exceptional_signed_face_sine_sum_le_budget,
    ``RectangleCLTArxivV1.cap_seeded_pair_contribution_sine_bound,
    ``RectangleCLTArxivV1.capSeededExceptionalPattern,
    ``RectangleCLTArxivV1.cap_seeded_exceptional_pattern_bound,
    ``RectangleCLTArxivV1.capSeededSeparatedPattern,
    ``RectangleCLTArxivV1.cap_seeded_fourth_pattern_exceptional_split,
    ``RectangleCLTArxivV1.exceptionalCutoffLog,
    ``RectangleCLTArxivV1.one_le_exceptionalCutoffLog,
    ``RectangleCLTArxivV1.exceptionalCutoff_crossing_log_le,
    ``RectangleCLTArxivV1.exceptional_integral_separated_minimum,
    ``RectangleCLTArxivV1.exceptional_integral_minimum_add_constant,
    ``RectangleCLTArxivV1.exceptionalBudgetRoot,
    ``RectangleCLTArxivV1.exceptionalBudgetBandwidth,
    ``RectangleCLTArxivV1.exceptionalBudgetRate,
    ``RectangleCLTArxivV1.exceptionalBudgetRoot_nonneg,
    ``RectangleCLTArxivV1.exceptionalBudgetRoot_cube,
    ``RectangleCLTArxivV1.exceptionalBudgetBandwidth_admissible,
    ``RectangleCLTArxivV1.exceptionalBudgetBandwidth_pos,
    ``RectangleCLTArxivV1.exceptionalBudgetBandwidth_inverse_costs,
    ``RectangleCLTArxivV1.exceptionalBudgetBandwidth_total_cost,
    ``RectangleCLTArxivV1.exceptionalBudget_large_bandwidth_rate,
    ``RectangleCLTArxivV1.exceptionalBudgetOptimizationConstant,
    ``RectangleCLTArxivV1.exceptionalBudget_rate_of_small_bandwidth_estimate,
    ``RectangleCLTArxivV1.exceptionalBudgetRoot_scaled,
    ``RectangleCLTArxivV1.exceptionalBudgetRate_eq_printed,
    ``RectangleCLTArxivV1.exceptionalBudgetRate_le_coefficient,
    ``RectangleCLTArxivV1.exceptionalBudget_trivial_large_envelope]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
