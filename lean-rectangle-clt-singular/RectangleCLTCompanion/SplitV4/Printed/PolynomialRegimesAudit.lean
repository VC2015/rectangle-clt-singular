import RectangleCLTCompanion.SplitV4.Printed.PolynomialRegimes
import Lean.Util.CollectAxioms

#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_atTop_below_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_dominates_coordinate_below_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialMoment_four_uniform_bound
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseParameter_tendsto_zero_above_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialSparseRate_negligible_to_coordinate_above_four
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelopeTransferRate_isBigO_polylog
#check RectangleCLT.Companion.SplitV4.Printed.polynomialEnvelope_rates_six
#check RectangleCLT.Companion.SplitV4.Printed.sparse_log_dimension_condition_of_log_n
#check RectangleCLT.Companion.SplitV4.Printed.sparse_regime_four_iff
#check RectangleCLT.Companion.SplitV4.Printed.envelope_tendsto_atTop_under_sparse_conditions_above_four

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]! ==
            `RectangleCLTCompanion.SplitV4.Printed.PolynomialRegimes then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in the printed polynomial regime arithmetic"
  logInfo m!"Audited {names.size} printed polynomial regime theorem declarations transitively; only propext, Classical.choice and Quot.sound."
