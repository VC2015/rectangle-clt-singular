import RectangleCLTArxivV1.SupplementalHMixedCoareaCoordinates
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPairConditionalDirection_geometry_nonparallel
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalPairSection_eq_pairSection
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalPairSignedSection_eq_pairSection
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalPairSignedSection_integrable
set_option pp.all true in
#check @RectangleCLTArxivV1.gaussianPair_conditional_density_jacobian_eq
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalMixedSignedSection_eq_pairSection
set_option pp.all true in
#check @RectangleCLTArxivV1.hardGaussianConditionalMixedSignedSection_nested_eq_pairSection

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.gaussianPairConditionalDirection_geometry_nonparallel,
    ``RectangleCLTArxivV1.hardGaussianConditionalPairSection_eq_pairSection,
    ``RectangleCLTArxivV1.hardGaussianConditionalPairSignedSection_eq_pairSection,
    ``RectangleCLTArxivV1.hardGaussianConditionalPairSignedSection_integrable,
    ``RectangleCLTArxivV1.gaussianPair_conditional_density_jacobian_eq,
    ``RectangleCLTArxivV1.hardGaussianConditionalMixedSignedSection_eq_pairSection,
    ``RectangleCLTArxivV1.hardGaussianConditionalMixedSignedSection_nested_eq_pairSection]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
