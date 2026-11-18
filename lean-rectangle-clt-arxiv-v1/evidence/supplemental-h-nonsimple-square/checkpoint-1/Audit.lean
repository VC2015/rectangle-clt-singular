import RectangleCLTArxivV1.SupplementalHNonsimpleExample
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.nonsimpleSquareScale, ``RectangleCLTArxivV1.nonsimpleSquareScale_pos, ``RectangleCLTArxivV1.nonsimpleSquareScale_sq, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals, ``RectangleCLTArxivV1.nonsimpleSquareNormals, ``RectangleCLTArxivV1.nonsimpleSquareDefect, ``RectangleCLTArxivV1.nonsimpleSquareNormals_dot, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals_normSq, ``RectangleCLTArxivV1.nonsimpleSquareNormals_unit, ``RectangleCLTArxivV1.nonsimpleSquare_four_normal_relation, ``RectangleCLTArxivV1.nonsimpleSquareCone, ``RectangleCLTArxivV1.nonsimpleSquareCone_eq_thresholdEvent, ``RectangleCLTArxivV1.nonsimpleSquare_strictInterior, ``RectangleCLTArxivV1.nonsimpleSquareDeletionWitness, ``RectangleCLTArxivV1.nonsimpleSquare_irredundant, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanRawNormals, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals_inner, ``RectangleCLTArxivV1.nonsimpleSquareEuclideanNormals_unit, ``RectangleCLTArxivV1.nonsimpleSquare_euclidean_strictInterior, ``RectangleCLTArxivV1.nonsimpleSquare_euclidean_irredundant, ``RectangleCLTArxivV1.nonsimpleSquareRawNormals_mem_normalSpace, ``RectangleCLTArxivV1.nonsimpleSquare_normalSpace_eq_top, ``RectangleCLTArxivV1.nonsimpleSquare_normal_rank_three, ``RectangleCLTArxivV1.nonsimpleSquare_origin_exactStratum, ``RectangleCLTArxivV1.nonsimpleSquare_exactStratum_eq_singleton, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex_card, ``RectangleCLTArxivV1.nonsimpleSquareActualVertex_is_nonsimple]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
