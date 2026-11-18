import RectangleCLTArxivV1.SupplementalHTrihedralBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.trihedralFacetCone_eq_positivePlanarWedge
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalHFacetAngle_trihedral
set_option pp.all true in
#check @RectangleCLTArxivV1.trihedral_spherical_balance
set_option pp.all true in
#check @RectangleCLTArxivV1.trihedral_spherical_balance_norm_le

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.trihedralOutwardNormals_dot,
    ``RectangleCLTArxivV1.trihedralOutwardNormals_unit,
    ``RectangleCLTArxivV1.trihedralOutwardNormals_nonparallel,
    ``RectangleCLTArxivV1.supplementalHPolyhedralCone_trihedral,
    ``RectangleCLTArxivV1.trihedralFacetCoordinates_map,
    ``RectangleCLTArxivV1.trihedralFacetCoordinates_norm,
    ``RectangleCLTArxivV1.trihedralFacetCoordinates_inner,
    ``RectangleCLTArxivV1.trihedralFacetChart_mem_iff,
    ``RectangleCLTArxivV1.trihedralFacetChart_orthogonal,
    ``RectangleCLTArxivV1.trihedralFacetCone_eq_positivePlanarWedge,
    ``RectangleCLTArxivV1.trihedralFacetCoordinates_nonparallel,
    ``RectangleCLTArxivV1.supplementalHFacetAngle_trihedral,
    ``RectangleCLTArxivV1.trihedralOutwardNormals_inward,
    ``RectangleCLTArxivV1.trihedral_spherical_balance,
    ``RectangleCLTArxivV1.trihedral_spherical_balance_norm_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
