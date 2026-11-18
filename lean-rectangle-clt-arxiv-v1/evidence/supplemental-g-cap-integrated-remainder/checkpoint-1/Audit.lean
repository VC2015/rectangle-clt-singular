import RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.cap_seededFourthRemainder_majorant,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_integral_bound,
    ``RectangleCLTArxivV1.capBoundedIntegratedRemainderConstant_pos,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_seededFourthRemainder_bounded_integral_bound).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound do
    throwError "Missing actual proof step RectangleCLTArxivV1.intrinsic_seeded_fourth_remainder_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_abs_le_split_min do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_abs_le_split_min"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_integral_majorant_bound do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_integral_majorant_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_seededFourthRemainder_abs_intervalIntegrable"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase do
    throwError "Missing actual proof step RectangleCLTArxivV1.intrinsicRectangleConcentration_seededSplitBase"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope"
  if deps.visited.contains ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_majorant then
    throwError "Used normalized remainder rather than proving raw R4 bound"
  logInfo "PASS literal raw R4, actual time integrability, capped integral, and discharged concentration route"
