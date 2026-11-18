import RectangleCLTArxivV1.SupplementalHNonsimpleFiniteFrameChartGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_exists, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_normal, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartBasis_normal_coordinate, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_range, ``RectangleCLTArxivV1.nonsimpleFiniteFrame_vectorNormSq_append, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_normalSum_eq_rotation, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_rotated_inner, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_rotated_section, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_measurable, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanAppend, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanAppend_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameTangentAppend, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartTangentIsometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartAffineIsometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChartAffineIsometry_apply, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_isometry, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_range, ``RectangleCLTArxivV1.nonsimpleFiniteFrameEuclideanChart_normSq, ``RectangleCLTArxivV1.nonsimpleFiniteFrameChart_gaussianKernel]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
