import RectangleCLTCompanion.SplitV4.ZeroVarianceFaces
import Lean.Util.CollectAxioms

/-! Strict audit of actual zero-variance face deletion under both laws. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.centered_linear_form_ae_zero_of_variance_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_linear_form_ae_zero_of_variance_zero
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polyhedralDistance_delete_zero_variance_faces
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT_delete_zero_variance_faces

#print axioms RectangleCLT.Companion.SplitV4.zero_variance_faces_probability_eq
#print axioms RectangleCLT.Companion.SplitV4.zero_variance_faces_negative_threshold
#print axioms RectangleCLT.Companion.SplitV4.polyhedralDistance_delete_zero_variance_faces
#print axioms RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT_delete_zero_variance_faces

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.centered_linear_form_ae_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.gaussian_linear_form_ae_zero_of_variance_zero,
    ``RectangleCLT.Companion.SplitV4.retainedFaceNormals,
    ``RectangleCLT.Companion.SplitV4.facePolyhedron_deleted_faces_iff,
    ``RectangleCLT.Companion.SplitV4.zero_variance_faces_ae_zero,
    ``RectangleCLT.Companion.SplitV4.zero_variance_faces_probability_eq,
    ``RectangleCLT.Companion.SplitV4.zero_variance_faces_negative_threshold,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_le_delete_zero_variance_faces,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_delete_zero_variance_faces,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_empty_faces,
    ``RectangleCLT.Companion.SplitV4.polyhedralDistance_zero_of_all_face_variances_zero,
    ``RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT_delete_zero_variance_faces]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in zero-variance face deletion closure"
  logInfo "Audited 12 zero-variance face declarations, including exact finite-subfamily deletion of the actual polyhedral distance and the polynomial CLT after deletion."
  logInfo "Both null projections follow from actual centered L2 moments and exact covariance; negative deleted thresholds give zero probabilities under both laws."
