import RectangleCLTArxivV1.SupplementalHCubicMoments
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_integrable_abs_linear_normSq,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_moments,
    ``RectangleCLTArxivV1.supplementalH_standardNormal_positive_halfline,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_mass_pos,
    ``RectangleCLTArxivV1.supplementalH_positive_selector_matrix_reduction]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
