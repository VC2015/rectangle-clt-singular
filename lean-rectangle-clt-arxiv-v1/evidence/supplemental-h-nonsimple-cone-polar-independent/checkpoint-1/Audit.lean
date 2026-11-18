import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCone
import RectangleCLTArxivV1.SupplementalHNonsimpleFacePolarLine
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.zero_mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.generator_mem_nonsimpleGeneratedCone,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_innerDual,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_coefficient_bound,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_isClosed,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_bipolar,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_mem_iff_polar,
    ``RectangleCLTArxivV1.nonsimpleGeneratedCone_no_cancellation,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_isClosed,
    ``RectangleCLTArxivV1.nonsimpleActiveGeneratedCone_mem_iff_polar,
    ``RectangleCLTArxivV1.nonsimple_polar_positive_endpoint,
    ``RectangleCLTArxivV1.nonsimple_polar_negative_endpoint,
    ``RectangleCLTArxivV1.nonsimple_polar_line_split,
    ``RectangleCLTArxivV1.nonsimple_polar_line_vector_decomposition,
    ``RectangleCLTArxivV1.nonsimple_zero_sum_slopes_both_signs,
    ``RectangleCLTArxivV1.nonsimple_polar_inner_slopes_both_signs,
    ``RectangleCLTArxivV1.nonsimple_polar_inner_line_split]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
