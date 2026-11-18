import RectangleCLTArxivV1.BoundedCharacteristicFunction
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.norm_unitPhase,
    ``RectangleCLTArxivV1.re_unitPhase,
    ``RectangleCLTArxivV1.unitPhase_sub,
    ``RectangleCLTArxivV1.unitPhase_sum,
    ``RectangleCLTArxivV1.integrable_unitPhase,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_sq,
    ``RectangleCLTArxivV1.integrable_bounded_half,
    ``RectangleCLTArxivV1.integrable_sq_bounded_half,
    ``RectangleCLTArxivV1.integral_independent_copy_contrast_sq,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_le,
    ``RectangleCLTArxivV1.integral_unitPhase_sum_eq_prod,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_sum_le,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_gaussian_linear,
    ``RectangleCLTArxivV1.two_div_pi_sq_le_half,
    ``RectangleCLTArxivV1.norm_integral_unitPhase_gaussian_linear_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
