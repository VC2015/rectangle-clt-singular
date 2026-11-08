import RectangleCLTCompanion.SplitV4.Printed.MatrixSectorPaper
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if #["MatrixSectorBound", "MatrixSectorRegularized", "MatrixSectorPaper"].any
            (fun suffix => env.header.moduleNames[idx.toNat]!.toString ==
              "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sector-derived printed B4 route"
  let forbidden := #[
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_succ,
    ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound_of_log_le_two,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
    ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
    ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_estimate,
    ``RectangleCLT.Companion.SplitV4.logistic_matrix_bound_unit_independent,
    ``RectangleCLT.Companion.SplitV4.exists_logistic_matrix_paper_constant,
    ``RectangleCLT.Companion.SplitV4.Printed.sector_logistic_matrix_estimate]
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.sector_exists_logistic_matrix_paper_constant]
  let mut offset := 0
  while offset < pending.size do
    let n := pending[offset]!
    offset := offset + 1
    unless visited.contains n do
      visited := visited.insert n
      if forbidden.contains n then
        throwError "Printed matrix endpoint bypassed sector/full-Fatou route through {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  logInfo m!"Audited {names.size} sector-derived printed B4 theorem declarations; only permitted axioms. Final full-padding/Fatou-before-compression endpoint closure checked across {visited.size} constants without old B4/B5 bounds, old MGF radius moments or block-first sector endpoint."
