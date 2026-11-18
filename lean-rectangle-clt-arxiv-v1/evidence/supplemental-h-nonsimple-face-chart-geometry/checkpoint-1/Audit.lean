import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartGeometry
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleFaceChartBasis_exists, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis_normal, ``RectangleCLTArxivV1.nonsimpleFaceChartBasis_normal_coordinate, ``RectangleCLTArxivV1.nonsimpleFaceChart, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart, ``RectangleCLTArxivV1.nonsimpleFaceChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFaceChart_range, ``RectangleCLTArxivV1.nonsimple_vectorNormSq_append, ``RectangleCLTArxivV1.nonsimpleFaceChart_normSq, ``RectangleCLTArxivV1.nonsimpleFaceChart_normalSum_eq_rotation, ``RectangleCLTArxivV1.nonsimpleFaceChart_rotated_inner, ``RectangleCLTArxivV1.nonsimpleFaceChart_rotated_section, ``RectangleCLTArxivV1.nonsimpleFaceChart_measurable, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanAppend, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanAppend_normSq, ``RectangleCLTArxivV1.nonsimpleFaceTangentAppend, ``RectangleCLTArxivV1.nonsimpleFaceChartTangentIsometry, ``RectangleCLTArxivV1.nonsimpleFaceChartAffineIsometry, ``RectangleCLTArxivV1.nonsimpleFaceChartAffineIsometry_apply, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_isometry, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_normal_equations, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_range, ``RectangleCLTArxivV1.nonsimpleFaceEuclideanChart_normSq, ``RectangleCLTArxivV1.nonsimpleFaceChart_gaussianKernel]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
