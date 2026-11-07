import RectangleCLTCompanion.SplitV4.SymmetricPolynomialUniform
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.zero_mem_polynomialSymmetricClassDistances

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances_subset

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances_bddAbove

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_nonneg

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_le_one

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_mem_polynomialSymmetricClassDistances

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.rectangleDistance_le_polynomialSymmetricWorstDistance

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses.mono_envelope

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialFourthUniformConstant

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialFourthUniformConstant_pos

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialBennettObservationRate_four_factor

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialWorstDistance_four_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_four_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance,
    ``RectangleCLT.Companion.SplitV4.zero_mem_polynomialSymmetricClassDistances,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances_subset,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricClassDistances_bddAbove,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_nonneg,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_le,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_le_one,
    ``RectangleCLT.Companion.SplitV4.rectangleDistance_mem_polynomialSymmetricClassDistances,
    ``RectangleCLT.Companion.SplitV4.rectangleDistance_le_polynomialSymmetricWorstDistance,
    ``RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses.mono_envelope,
    ``RectangleCLT.Companion.SplitV4.polynomialFourthUniformConstant,
    ``RectangleCLT.Companion.SplitV4.polynomialFourthUniformConstant_pos,
    ``RectangleCLT.Companion.SplitV4.polynomialBennettObservationRate_four_factor,
    ``RectangleCLT.Companion.SplitV4.polynomialWorstDistance_four_le,
    ``RectangleCLT.Companion.SplitV4.polynomialSymmetricWorstDistance_four_le]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual symmetric polynomial uniform class"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited literal centrally symmetric polynomial-model supremum, class inclusion, model domination, monotone envelope transfer and genuine q=4 all-model uniform rate."
