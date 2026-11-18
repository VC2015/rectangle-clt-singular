import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartProduct
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv,
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv_apply,
    ``RectangleCLTArxivV1.nonsimpleChartAppendEquiv_gaussian_preserving,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_measurable,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_append,
    ``RectangleCLTArxivV1.nonsimpleChartPrefix_gaussian_map,
    ``RectangleCLTArxivV1.nonsimpleChartDensity_append,
    ``RectangleCLTArxivV1.nonsimpleChartDensity_rotation,
    ``RectangleCLTArxivV1.nonsimpleChart_gaussian_map_of_rotated_prefix,
    ``RectangleCLTArxivV1.nonsimpleFrameSection_measurable,
    ``RectangleCLTArxivV1.nonsimpleFrameSection_chart_gaussian_map,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_density,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_tangentChart_integral,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_density_integrable,
    ``RectangleCLTArxivV1.nonsimpleFaceChart_supporting_level,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_measurable,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_isometry,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_covers_closedFace,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_active_level,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_mem_closedFace_iff,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_closedFace_chart_integral,
    ``RectangleCLTArxivV1.nonsimpleActualFaceChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualFaceEuclideanChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_surface_integral]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
