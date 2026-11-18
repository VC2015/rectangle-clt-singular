import RectangleCLTArxivV1.SupplementalHQuantitativeEntropy
import RectangleCLTArxivV1.SupplementalHCubicMatrix
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.supplementalH_entropy_cardinality_budget,
    ``RectangleCLTArxivV1.supplementalH_integral_entropy_cardinality_bound,
    ``RectangleCLTArxivV1.supplementalHCubicSelectorScore,
    ``RectangleCLTArxivV1.supplementalH_cross_nuclear_le,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_decomposition,
    ``RectangleCLTArxivV1.supplementalHCubicMeanEnergy,
    ``RectangleCLTArxivV1.supplementalH_cubic_selector_nuclear_reduction]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target}: {axioms.toList}"
