import RectangleCLTArxivV1.SupplementalHPositiveWedge
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.positivePlanarWedge_canonical_polar_iff
set_option pp.all true in
#check @RectangleCLTArxivV1.positivePlanarWedge_complex_gaussian_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.positivePlanarWedge_complex_angular_area
set_option pp.all true in
#check @RectangleCLTArxivV1.positivePlanarWedge_angular_area_of_isometry
set_option pp.all true in
#check @RectangleCLTArxivV1.positivePlanarWedge_angular_area

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.positivePlanarWedge_dilation,
    ``RectangleCLTArxivV1.positivePlanarWedge_one_iff,
    ``RectangleCLTArxivV1.positivePlanarWedge_one_measurable,
    ``RectangleCLTArxivV1.positivePlanarWedge_canonical_polar_iff,
    ``RectangleCLTArxivV1.positivePlanarWedge_canonical_gaussian_mass,
    ``RectangleCLTArxivV1.positivePlanarWedge_canonical_angular_area,
    ``RectangleCLTArxivV1.positivePlanarWedge_isometry_image,
    ``RectangleCLTArxivV1.positivePlanarWedge_gaussian_mass_isometry,
    ``RectangleCLTArxivV1.exists_positive_wedge_complex_isometry,
    ``RectangleCLTArxivV1.positivePlanarWedge_complex_measurable,
    ``RectangleCLTArxivV1.positivePlanarWedge_complex_gaussian_mass,
    ``RectangleCLTArxivV1.positivePlanarWedge_complex_angular_area,
    ``RectangleCLTArxivV1.positivePlanarWedge_angular_area_of_isometry,
    ``RectangleCLTArxivV1.positivePlanarWedge_angular_area]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
