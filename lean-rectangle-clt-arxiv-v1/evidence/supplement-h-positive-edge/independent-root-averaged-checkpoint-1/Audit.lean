import RectangleCLTArxivV1.SupplementalHPositiveEdgeAveraged
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLTArxivV1.continuous_fourthRidgeNormalPoint_threshold,
    ``RectangleCLTArxivV1.measurable_hardGaussianRidgeDensity,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_nonneg,
    ``RectangleCLTArxivV1.measurable_positiveEdgeTubeCoefficient_threshold,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_abs_le,
    ``RectangleCLTArxivV1.positiveEdge_outer_affine_integral_eq,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_second_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_fourth_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeTubeCoefficient_second_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeTubeCoefficient_fourth_concentrated_base,
    ``RectangleCLTArxivV1.ae_positiveEdgeLeadingTerm_concentrated_base,
    ``RectangleCLTArxivV1.positiveEdge_pairSectionProbability_eq,
    ``RectangleCLTArxivV1.fourthRidgeNormalPoint_norm_sq_eq,
    ``RectangleCLTArxivV1.positiveEdgeTubeCoefficient_sub_eq_ridgeLeading,
    ``RectangleCLTArxivV1.positiveEdgeLeadingTerm_eq_hardGaussianRidgeLeadingIntegral,
    ``RectangleCLTArxivV1.ae_hardGaussianRidgeLeadingIntegral_concentrated_base]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
