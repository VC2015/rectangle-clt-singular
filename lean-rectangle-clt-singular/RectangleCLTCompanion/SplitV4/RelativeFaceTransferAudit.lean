import RectangleCLTCompanion.SplitV4.RelativeFaceTransfer
import Lean.Util.CollectAxioms

/-! Strict audit of the actual relative CLT and face transfer closure. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.relativePolyhedralCLT_delete_zero_variance_faces

#print axioms RectangleCLT.Companion.SplitV4.relativePolyhedralCLT_delete_zero_variance_faces

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.relativeIndependent_standardizedFaces,
    ``RectangleCLT.Companion.SplitV4.bounded_sum_coordinate_memLp_two,
    ``RectangleCLT.Companion.SplitV4.bounded_sum_coordinate_centered,
    ``RectangleCLT.Companion.SplitV4.relativePolyhedralCLT,
    ``RectangleCLT.Companion.SplitV4.relativePolyhedralCLT_delete_zero_variance_faces,
    ``RectangleCLT.Companion.SplitV4.relativePolyhedralDistance_zero_of_all_face_variances_zero]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in relative CLT/face closure"
  logInfo "Audited 6 RelativeFaceTransfer declarations; only the three standard axioms are permitted."
