import RectangleCLTArxivV1.SupplementalHTripleIncidenceTransport
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceTransportIsometry_pair
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceTransportIsometry_doubleResidual
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceTransportIsometry_conormal
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceTransportBasis_angle
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidenceTransportIsometry_weighted_conormals
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidence_shift_scale_eq_conormal_pairing
set_option pp.all true in
#check @RectangleCLTArxivV1.tripleIncidence_signed_coefficient_fourth_bound
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_trihedral_vector
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_spherical_vector

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_pair,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_doubleResidual,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_conormal,
    ``RectangleCLTArxivV1.tripleIncidenceTransportBasis_angle,
    ``RectangleCLTArxivV1.tripleIncidenceTransportIsometry_weighted_conormals,
    ``RectangleCLTArxivV1.tripleIncidence_shift_scale_eq_conormal_pairing,
    ``RectangleCLTArxivV1.tripleIncidence_signed_coefficient_fourth_bound,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_trihedral_vector,
    ``RectangleCLTArxivV1.hardGaussianRidgeThirdIncidenceGroup_eq_spherical_vector]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
