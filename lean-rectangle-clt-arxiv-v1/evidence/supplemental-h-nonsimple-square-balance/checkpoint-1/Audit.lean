import RectangleCLTArxivV1.SupplementalHNonsimpleSquareBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleSquareEdgeLeft, ``RectangleCLTArxivV1.nonsimpleSquareEdgeRight, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale_pos, ``RectangleCLTArxivV1.nonsimpleSquareConormalScale_sq, ``RectangleCLTArxivV1.nonsimpleSquareRawConormals, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_unit, ``RectangleCLTArxivV1.nonsimpleSquareEdge_distinct, ``RectangleCLTArxivV1.nonsimpleSquareEdge_pair_injective, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_inner, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_zero, ``RectangleCLTArxivV1.nonsimpleSquareInwardConormals_strict, ``RectangleCLTArxivV1.nonsimpleSquareEdge_sum_ne_zero, ``RectangleCLTArxivV1.nonsimpleSquareEdge_sub_ne_zero, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects_nonneg, ``RectangleCLTArxivV1.nonsimpleSquarePolarDefects_zero, ``RectangleCLTArxivV1.nonsimpleSquare_polar_third_nonpos, ``RectangleCLTArxivV1.nonsimpleSquare_polar_third_zero, ``RectangleCLTArxivV1.nonsimpleSquare_polar_zero_pair_is_edge, ``RectangleCLTArxivV1.nonsimpleSquare_polar_edge_multiple, ``RectangleCLTArxivV1.nonsimpleSquare_nonzero_polar_incident_coverage, ``RectangleCLTArxivV1.nonsimpleSquare_normal_span_eq_top, ``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance, ``RectangleCLTArxivV1.nonsimpleSquare_four_edge_spherical_balance_norm_le]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
