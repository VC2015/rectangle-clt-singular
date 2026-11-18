import RectangleCLTArxivV1.SupplementalHTrihedralResidualConormal
import RectangleCLTArxivV1.SupplementalHTrihedralFiberBound
import RectangleCLTArxivV1.SupplementalHSecondTubes
import RectangleCLTArxivV1.SupplementalHLocalizedMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.trihedral_other_pair_nondegenerate,
    ``RectangleCLTArxivV1.trihedralDoubleResidual_orthogonal_pair,
    ``RectangleCLTArxivV1.trihedralDoubleResidual_ne_zero,
    ``RectangleCLTArxivV1.trihedralResidualUnitNormal_eq_inward,
    ``RectangleCLTArxivV1.trihedral_residual_boundary_pairing,
    ``RectangleCLTArxivV1.adaptive_trihedral_boundary_fourth_bound,
    ``RectangleCLTArxivV1.adaptive_ridge_gaussian_integral_lower_second,
    ``RectangleCLTArxivV1.adaptive_angle_ridge_second_bound,
    ``RectangleCLTArxivV1.adaptive_angle_ridge_normSq_fourth_bound,
    ``RectangleCLTArxivV1.concentrated_base_gaussian_weighted_tube_power,
    ``RectangleCLTArxivV1.concentrated_base_gaussian_weighted_outward_tube_power,
    ``RectangleCLTArxivV1.concentrated_base_threeFace_second_outward_tube]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
