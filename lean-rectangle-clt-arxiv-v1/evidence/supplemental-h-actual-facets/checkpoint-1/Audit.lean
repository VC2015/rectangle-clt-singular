import RectangleCLTArxivV1.SupplementalHActualFacetGeometry
import RectangleCLTArxivV1.SupplementalHActualFacetRegularity
import RectangleCLTArxivV1.SupplementalHActualFacetSelection
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.HasStrictFacetInterior,
    ``RectangleCLTArxivV1.HasIrredundantFacetWitnesses,
    ``RectangleCLTArxivV1.actualFacet_pair_affine_inconsistent,
    ``RectangleCLTArxivV1.actualFacet_triple_affine_inconsistent,
    ``RectangleCLTArxivV1.actualFacet_pair_residual_slack,
    ``RectangleCLTArxivV1.actualFacet_triple_residual_slack,
    ``RectangleCLTArxivV1.actualFacet_residualThresholdRegularity,
    ``RectangleCLTArxivV1.actualFacet_abs_weightedFacetIntegral_le_threeFace_tube,
    ``RectangleCLTArxivV1.FacetPresentationEquivalent,
    ``RectangleCLTArxivV1.exists_irredundant_facet_subfamily,
    ``RectangleCLTArxivV1.exists_actual_facet_presentation,
    ``RectangleCLTArxivV1.exists_actual_facet_weightedIntegral_bound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
