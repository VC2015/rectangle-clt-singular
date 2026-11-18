import RectangleCLTArxivV1.SupplementalGCapNormalizedRemainder
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_integral_bound,
    ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_bounded_integral_bound,
    ``RectangleCLTArxivV1.proposition_G1_dimension_log_cap_normalized]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_bounded_integral_bound).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_majorant do
    throwError "Missing actual normalized R4 proof step RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_majorant"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable do
    throwError "Missing actual normalized R4 proof step RectangleCLTArxivV1.cap_seededFourthRemainder_rank_abs_intervalIntegrable"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_integral_majorant_bound do
    throwError "Missing actual normalized R4 proof step RectangleCLTArxivV1.cap_integral_majorant_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase do
    throwError "Missing actual normalized R4 proof step RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.seededRescaledSmoother do
    throwError "Missing actual normalized R4 proof step RectangleCLT.Companion.SplitV4.seededRescaledSmoother"
  logInfo "PASS exact printed normalized R4, actual rank time-integrability, original bandwidth and discharged concentration route"
