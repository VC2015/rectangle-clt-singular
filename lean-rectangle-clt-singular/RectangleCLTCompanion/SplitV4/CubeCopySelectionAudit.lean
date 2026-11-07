import RectangleCLTCompanion.SplitV4.CubeCopySelection
import Lean.Util.CollectAxioms

/-! Exact actual-copy/sign law contracts and their complete transitive axiom audit. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.randomCubeSelectedArray

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cubePairMidpoint

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.cubePairDifference

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_randomCubeSelectedArray

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurePreserving_random_countable_selector

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fixedCubeSelectedArray_measurePreserving

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fixedCubeSelectedArray_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fixedCubeSelectedPair_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.randomCubeSelectedArray_measurePreserving

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.randomCubeSelectedArray_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedArray_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectedArray_eq_midpoint_add_signed_difference

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.selectedSum_eq_midpoint_add_signed_difference

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.measurable_cubeArraySum

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.fixedCubeSignedDifference_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.randomCubeSignedDifference_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.identDistrib_prod_independent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_with_independent_shift_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_test_transport

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSignedDifference_test_transport

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSignedDifference_iterated_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeMidpointSignedSum_identDistrib

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_with_independent_shift_test_transport

set_option pp.all true in
#print RectangleCLT.selectedArray_law_eq_original

set_option pp.all true in
#print RectangleCLT.selectedPair_law_eq_original

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.randomCubeSelectedArray,
    ``RectangleCLT.Companion.SplitV4.cubePairMidpoint,
    ``RectangleCLT.Companion.SplitV4.cubePairDifference,
    ``RectangleCLT.Companion.SplitV4.measurable_randomCubeSelectedArray,
    ``RectangleCLT.Companion.SplitV4.measurePreserving_random_countable_selector,
    ``RectangleCLT.Companion.SplitV4.fixedCubeSelectedArray_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.fixedCubeSelectedArray_identDistrib,
    ``RectangleCLT.Companion.SplitV4.fixedCubeSelectedPair_identDistrib,
    ``RectangleCLT.Companion.SplitV4.randomCubeSelectedArray_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.randomCubeSelectedArray_identDistrib,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedArray_identDistrib,
    ``RectangleCLT.Companion.SplitV4.selectedArray_eq_midpoint_add_signed_difference,
    ``RectangleCLT.Companion.SplitV4.selectedSum_eq_midpoint_add_signed_difference,
    ``RectangleCLT.Companion.SplitV4.measurable_cubeArraySum,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_identDistrib,
    ``RectangleCLT.Companion.SplitV4.fixedCubeSignedDifference_identDistrib,
    ``RectangleCLT.Companion.SplitV4.randomCubeSignedDifference_identDistrib,
    ``RectangleCLT.Companion.SplitV4.identDistrib_prod_independent,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_with_independent_shift_identDistrib,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_test_transport,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSignedDifference_test_transport,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSignedDifference_iterated_integral,
    ``RectangleCLT.Companion.SplitV4.uniformCubeMidpointSignedSum_identDistrib,
    ``RectangleCLT.Companion.SplitV4.uniformCubeSelectedSum_with_independent_shift_test_transport]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in independent-copy/sign selection law"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual product-law selection, independent copy swaps, signed differences, midpoint representation, and integrable-test transports."
