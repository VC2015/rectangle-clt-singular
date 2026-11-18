import RectangleCLTArxivV1.HFourthSeededRemainder
import RectangleCLTArxivV1.HFourthSeededPhysicalBase
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.hFourth_gap_or_parallel,
    ``RectangleCLTArxivV1.hFourth_copy_pair_zero_outside_gap,
    ``RectangleCLTArxivV1.hFourth_seeded_pattern_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.HFourthSeededMatrixEstimates,
    ``RectangleCLTArxivV1.hFourth_seeded_remainder_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourth_seeded_remainder_late_bound_of_matrix_suppliers,
    ``RectangleCLTArxivV1.hFourthRetainedSupportCoordinates,
    ``RectangleCLTArxivV1.hFourthPhysicalSeededBase,
    ``RectangleCLTArxivV1.hFourthRetainedSupportCoordinates_continuous,
    ``RectangleCLTArxivV1.hFourthPhysicalSeededBase_continuous,
    ``RectangleCLTArxivV1.hFourth_retained_support_reconstruct,
    ``RectangleCLTArxivV1.hFourth_seeded_base_eq_physical]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
