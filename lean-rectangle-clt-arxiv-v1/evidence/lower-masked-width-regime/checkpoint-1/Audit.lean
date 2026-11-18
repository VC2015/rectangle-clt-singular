import RectangleCLTArxivV1.LowerMaskedProfile
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.lowerFamilyEffectiveAmplitude_widthScale,
    ``RectangleCLTArxivV1.lowerFamilyEffectiveAmplitude_square,
    ``RectangleCLTArxivV1.lowerFamilyRareWidthScale_pos,
    ``RectangleCLTArxivV1.lowerFamily_masked_shift_second_moment_budget,
    ``RectangleCLTArxivV1.lowerFamilyMaskedMasterRemainder_width_bound,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMaskedMasterRemainder_div_width,
    ``RectangleCLTArxivV1.eventually_lowerFamily_masked_leading_range,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMasked_reverse_mean_ratio,
    ``RectangleCLTArxivV1.exists_lowerFamily_masked_width_detection_constant,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyRare_shiftScale,
    ``RectangleCLTArxivV1.tendsto_lowerFamilyMasked_rare_width,
    ``RectangleCLTArxivV1.lowerFamilyMasked_width_profile]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
