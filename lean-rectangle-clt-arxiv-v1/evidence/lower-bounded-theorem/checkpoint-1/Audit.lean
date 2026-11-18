import RectangleCLTArxivV1.LowerBoundedTheorem
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.lowerUnmasked_count_identity,
    ``RectangleCLTArxivV1.tendsto_lowerUnmasked_raw_variance,
    ``RectangleCLTArxivV1.eventually_lowerUnmaskedSequence_fields,
    ``RectangleCLTArxivV1.tendsto_lowerUnmaskedSequence_variance,
    ``RectangleCLTArxivV1.tendsto_lowerUnmaskedSequence_widthScale,
    ``RectangleCLTArxivV1.tendsto_lowerUnmaskedSequence_rare_width,
    ``RectangleCLTArxivV1.eventually_lowerUnmaskedSequence_count,
    ``RectangleCLTArxivV1.lowerUnmaskedSequence_width_profile,
    ``RectangleCLTArxivV1.lowerUnmaskedSequence_one_width_tendsto,
    ``RectangleCLTArxivV1.eventually_lowerUnmaskedSequence_properties,
    ``RectangleCLTArxivV1.exists_lowerUnmaskedSequence_detection_constant,
    ``RectangleCLTArxivV1.theorem4_bounded_symmetric_lower]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
