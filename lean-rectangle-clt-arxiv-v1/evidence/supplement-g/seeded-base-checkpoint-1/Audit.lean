import RectangleCLTArxivV1.SupplementalGSeededBase
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.capSignedFactor,
    ``RectangleCLTArxivV1.capSignedFactor_mulVec,
    ``RectangleCLTArxivV1.capSignedFactor_gram,
    ``RectangleCLTArxivV1.capSignedProjection_covariance_scaledGram,
    ``RectangleCLTArxivV1.cap_signed_mixed_covariance,
    ``RectangleCLTArxivV1.cap_signed_mixed_value,
    ``RectangleCLTArxivV1.cap_seeded_projection_hypotheses,
    ``RectangleCLTArxivV1.cap_thinned_mixed_covariance,
    ``RectangleCLTArxivV1.cap_seededSplit_mixed_covariance,
    ``RectangleCLTArxivV1.cap_seededWhole_mixed_covariance,
    ``RectangleCLTArxivV1.cap_seededSplit_variance_band,
    ``RectangleCLTArxivV1.cap_signed_mixed_projection_zero,
    ``RectangleCLTArxivV1.cap_signed_mixed_projection_one,
    ``RectangleCLTArxivV1.cap_thinned_single_face_mass,
    ``RectangleCLTArxivV1.cap_thinned_pair_face_mass,
    ``RectangleCLTArxivV1.cap_seededSplitBase_single_mass,
    ``RectangleCLTArxivV1.cap_seededSplitBase_pair_mass,
    ``RectangleCLTArxivV1.cap_seededWhole_map_law]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
