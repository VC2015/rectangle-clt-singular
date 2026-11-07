import RectangleCLTCompanion.SplitV4.PolyhedralGeometry
import Lean.Util.CollectAxioms

/-! This audit covers only the deterministic Appendix D helpers. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.mem_facePolyhedron_iff_standardized

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.standardizedFaceMap_envelope

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.mulVec_sq_le_weighted_coordinate_squares

#print axioms RectangleCLT.Companion.SplitV4.mem_facePolyhedron_iff_standardized
#print axioms RectangleCLT.Companion.SplitV4.standardizedFaceMap_envelope
#print axioms RectangleCLT.Companion.SplitV4.mulVec_sq_le_weighted_coordinate_squares
#print axioms RectangleCLT.Companion.SplitV4.mulVec_fourth_le_weighted_coordinate_fourths
#print axioms RectangleCLT.Companion.SplitV4.boundedIndependent_projected
#print axioms RectangleCLT.Companion.SplitV4.standardizedFaceMap_covariance_unit_diagonal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.mem_lowerOrthant,
    ``RectangleCLT.Companion.SplitV4.standardizedFaceMap_apply,
    ``RectangleCLT.Companion.SplitV4.mem_facePolyhedron_iff_standardized,
    ``RectangleCLT.Companion.SplitV4.facePolyhedron_eq_preimage_standardized,
    ``RectangleCLT.Companion.SplitV4.standardizedFaceMap_row_l1_le,
    ``RectangleCLT.Companion.SplitV4.faceCovariance_diagonal,
    ``RectangleCLT.Companion.SplitV4.standardizedFaceMap_covariance_unit_diagonal,
    ``RectangleCLT.Companion.SplitV4.abs_mulVec_le_of_row_l1,
    ``RectangleCLT.Companion.SplitV4.norm_mulVec_le_of_row_l1,
    ``RectangleCLT.Companion.SplitV4.standardizedFaceMap_envelope,
    ``RectangleCLT.Companion.SplitV4.boundedIndependent_projected,
    ``RectangleCLT.Companion.SplitV4.mulVec_sq_le_weighted_coordinate_squares,
    ``RectangleCLT.Companion.SplitV4.mulVec_fourth_le_weighted_coordinate_fourths]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in polyhedral geometry helper closure"
  logInfo "Audited deterministic split-V4 polyhedral helpers; Corollary 3 remains pending."
