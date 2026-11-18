import RectangleCLTArxivV1.SupplementalHNonsimpleFiniteFrameChartMass
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.nonsimpleFiniteFrameSection_measurable,
    ``RectangleCLTArxivV1.nonsimpleFiniteFrameSection_chart_gaussian_map,
    ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_density,
    ``RectangleCLTArxivV1.gaussianFrameHardMass_eq_finiteTangentChart_integral,
    ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_density_integrable,
    ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_supporting_level,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceChart,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceChart_measurable,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceEuclideanChart,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceEuclideanChart_isometry,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceEuclideanChart_covers_closedFace,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceChart_active_level,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceChart_mem_closedFace_iff,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_closedFace_finiteChart_integral,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualFiniteFaceEuclideanChart_surface_integrable,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_eq_finite_surface_integral,
    ``RectangleCLTArxivV1.nonsimpleActualGaussianMass_ridge_surface_integral]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
