import RectangleCLTArxivV1.LowerBoundedOne
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.independentAbsGaussianMean_one_eq_density,
    ``RectangleCLTArxivV1.lowerBoundedOne_widthScale_eq,
    ``RectangleCLTArxivV1.tendsto_lowerBoundedOne_signed_div_widthScale,
    ``RectangleCLTArxivV1.lowerBoundedOneTarget_pos,
    ``RectangleCLTArxivV1.tendsto_lowerBoundedOne_target_div_widthScale,
    ``RectangleCLTArxivV1.tendsto_lowerBoundedOne_signed_div_target,
    ``RectangleCLTArxivV1.lowerBoundedOne_distance_ereal_liminf,
    ``RectangleCLTArxivV1.bounded_width_example_one_eighth,
    ``RectangleCLTArxivV1.bounded_width_example_one_eighth_from_main_regime]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
