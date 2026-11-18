import RectangleCLTArxivV1.LowerMaskedFourthTheorem
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.lowerMaskedFourth_log_bounds,
    ``RectangleCLTArxivV1.lowerMaskedFourthRawWidth_eq,
    ``RectangleCLTArxivV1.lowerMaskedFourthRawWidth_fourth,
    ``RectangleCLTArxivV1.lowerMaskedFourthIntrinsicRate_fourth,
    ``RectangleCLTArxivV1.lowerMaskedFourthRawWidth_le_intrinsicRate,
    ``RectangleCLTArxivV1.lowerMaskedFourthRawWidth_fourth_count,
    ``RectangleCLTArxivV1.lowerMaskedFourthTheta_le_raw_fourth,
    ``RectangleCLTArxivV1.lowerMaskedFourthIntrinsicRate_le_raw,
    ``RectangleCLTArxivV1.tendsto_lowerMaskedFourthRawWidth,
    ``RectangleCLTArxivV1.tendsto_lowerMaskedFourthLog_div_rareLog,
    ``RectangleCLTArxivV1.tendsto_lowerMaskedFourthTheta,
    ``RectangleCLTArxivV1.tendsto_lowerMaskedFourthVariance,
    ``RectangleCLTArxivV1.tendsto_lowerMaskedFourthEffectiveAmplitude,
    ``RectangleCLTArxivV1.eventually_lowerMaskedFourthSequence_fields,
    ``RectangleCLTArxivV1.lowerMaskedFourthCalibration,
    ``RectangleCLTArxivV1.eventually_lowerMaskedFourth_membership,
    ``RectangleCLTArxivV1.theorem_6_growing_fourth_moment_lower]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
