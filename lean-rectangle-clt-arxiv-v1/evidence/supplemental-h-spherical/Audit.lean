import RectangleCLTArxivV1.SupplementalHSphericalSectors
import RectangleCLTArxivV1.SupplementalHSphericalBalance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_integral_radial_three
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_integral_radial_two
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_planar_cone_gaussian_mass
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_circle_arc_area
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_circle_arccos_arc_area
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_facetKernel_eq_angle
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_spherical_balance_outward
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_spherical_balance_inward
set_option pp.all true in
#check @RectangleCLTArxivV1.supplementalH_spherical_balance_norm_le

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_integral_polar,
    ``RectangleCLTArxivV1.supplementalH_integral_radial_density,
    ``RectangleCLTArxivV1.supplementalH_integral_angular_radial,
    ``RectangleCLTArxivV1.supplementalH_integral_radial_three,
    ``RectangleCLTArxivV1.supplementalH_integral_radial_two,
    ``RectangleCLTArxivV1.supplementalH_cone_gaussian_firstMoment,
    ``RectangleCLTArxivV1.supplementalH_spherical_vectorIntegral_norm_le,
    ``RectangleCLTArxivV1.supplementalH_cone_gaussian_firstMoment_norm_le,
    ``RectangleCLTArxivV1.supplementalH_planar_cone_gaussian_mass,
    ``RectangleCLTArxivV1.supplementalH_gaussian_firstMoment_integrable,
    ``RectangleCLTArxivV1.supplementalH_spherical_vectorIntegral_apply,
    ``RectangleCLTArxivV1.supplementalHPlanarSector_measurable,
    ``RectangleCLTArxivV1.supplementalHPlanarSector_dilation,
    ``RectangleCLTArxivV1.supplementalH_planar_sector_gaussian,
    ``RectangleCLTArxivV1.supplementalH_planar_arccos_sector_gaussian,
    ``RectangleCLTArxivV1.supplementalH_circle_arc_area,
    ``RectangleCLTArxivV1.supplementalH_circle_arccos_arc_area,
    ``RectangleCLTArxivV1.supplementalH_vectorNormSq_equiv,
    ``RectangleCLTArxivV1.supplementalH_normalSectionChart_smul,
    ``RectangleCLTArxivV1.supplementalH_thresholdCone_dilation,
    ``RectangleCLTArxivV1.supplementalHPolyhedralCone_measurable,
    ``RectangleCLTArxivV1.supplementalHPolyhedralCone_dilation,
    ``RectangleCLTArxivV1.supplementalHFacetCone_measurable,
    ``RectangleCLTArxivV1.supplementalHFacetCone_dilation,
    ``RectangleCLTArxivV1.supplementalH_facetKernel_eq_angle,
    ``RectangleCLTArxivV1.supplementalH_cone_coordinate_moment,
    ``RectangleCLTArxivV1.supplementalH_spherical_balance_outward,
    ``RectangleCLTArxivV1.supplementalH_spherical_balance_inward,
    ``RectangleCLTArxivV1.supplementalH_spherical_balance_norm_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
