import RectangleCLTArxivV1.LowerSparseReadingOrder
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.lowerSparseIntrinsicK_four,
    ``RectangleCLTArxivV1.lowerSparseIntrinsicRate_four,
    ``RectangleCLTArxivV1.lowerSparseSequence_four,
    ``RectangleCLTArxivV1.lowerSparse_cube_dimension_sq_le_coordinateWidth_fourth,
    ``RectangleCLTArxivV1.tendsto_lowerSparseEll_cube_dimensionLog_sq_div,
    ``RectangleCLTArxivV1.lowerSparseCalibration_from_headline]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
