import RectangleCLTArxivV1.SupplementalGCapSeededComparison
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.capSeededComparisonConstant_pos,
    ``RectangleCLTArxivV1.capSeededTimeComparisonConstant_pos,
    ``RectangleCLTArxivV1.cap_normalizedSeededFourthRemainder_majorant,
    ``RectangleCLTArxivV1.cap_normalizedSeeded_time_comparison_bound]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axioms.toList}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_,deps) := ((CollectAxioms.collect ``RectangleCLTArxivV1.cap_normalizedSeeded_time_comparison_bound).run env).run {}
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_seededFourthRemainder_complementary_bound"
  unless deps.visited.contains ``RectangleCLTArxivV1.intrinsic_seeded_derivative_bounds do
    throwError "Missing actual proof step RectangleCLTArxivV1.intrinsic_seeded_derivative_bounds"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_abs_le_split_min do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_abs_le_split_min"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_time_increment_le do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_time_increment_le"
  unless deps.visited.contains ``RectangleCLTArxivV1.cap_integral_majorant_bound do
    throwError "Missing actual proof step RectangleCLTArxivV1.cap_integral_majorant_bound"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.hasDerivAt_normalizedSeededExpectation"
  unless deps.visited.contains ``RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope do
    throwError "Missing actual proof step RectangleCLT.Companion.SplitV4.relativeMomentBounds_of_envelope"
  if deps.visited.contains ``RectangleCLTArxivV1.intrinsic_seeded_time_comparison_bound then
    throwError "Used uncapped time comparison instead of proved actual cap"
  logInfo "PASS actual normalized seeded R4/derivative/FTC/capped-integration route"
