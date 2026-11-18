import RectangleCLTArxivV1.ActualMatrixConstant
import RectangleCLTArxivV1.ActualMatrixTransport
import RectangleCLTArxivV1.ActualSeededMatrixBase
import RectangleCLTArxivV1.ActualPairMatrixTransport
import RectangleCLTArxivV1.ActualNormalizedMatrices
import RectangleCLTArxivV1.ActualHFourth
import RectangleCLTArxivV1.ActualCorollaries
import RectangleCLTArxivV1.ActualRemainderIntegral
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.actualMatrixConstant,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_one,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_cubic,
    ``RectangleCLTArxivV1.actualMatrixConstant_ge_pair,
    ``RectangleCLTArxivV1.actualMatrix_cubic_power_le,
    ``RectangleCLTArxivV1.actualMatrix_pair_power_le,
    ``RectangleCLTArxivV1.actualMatrix_factorNormal_eq_selectorFaceNormal,
    ``RectangleCLTArxivV1.actualMatrix_physical_pushforward,
    ``RectangleCLTArxivV1.actualMatrix_cubic_supplier_of_physical,
    ``RectangleCLTArxivV1.actual_seededSplitBase_map_eq,
    ``RectangleCLTArxivV1.actual_seeded_physical_concentration,
    ``RectangleCLTArxivV1.actual_normalized_cubic_supplier,
    ``RectangleCLTArxivV1.actualMatrix_pair_supplier_of_physical,
    ``RectangleCLTArxivV1.actual_normalized_matrix_estimates,
    ``RectangleCLTArxivV1.actual_normalized_gap_matrix_estimates,
    ``RectangleCLTArxivV1.theoremH3Constant,
    ``RectangleCLTArxivV1.theoremH3Constant_pos,
    ``RectangleCLTArxivV1.theorem_H3_fourth_derivative,
    ``RectangleCLTArxivV1.corollary4Constant,
    ``RectangleCLTArxivV1.corollary4Constant_ge_one,
    ``RectangleCLTArxivV1.corollary4Constant_pos,
    ``RectangleCLTArxivV1.corollary5Constant,
    ``RectangleCLTArxivV1.corollary5Constant_ge_one,
    ``RectangleCLTArxivV1.corollary5Constant_pos,
    ``RectangleCLTArxivV1.corollary4_positive_correlation_gap,
    ``RectangleCLTArxivV1.corollary5_exceptional_correlation_budget,
    ``RectangleCLTArxivV1.corollary5RemainderConstant,
    ``RectangleCLTArxivV1.corollary5RemainderConstant_pos,
    ``RectangleCLTArxivV1.corollary5_normalized_remainder_abs_intervalIntegrable,
    ``RectangleCLTArxivV1.corollary5_normalized_remainder_integral]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
