import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorAveraging
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #["FacetRadius", "RidgeSectorThreshold", "RidgeSectorBound", "RidgeSectorAveraging"]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if modules.any (fun m => env.header.moduleNames[idx.toNat]!.toString ==
            "RectangleCLTCompanion.SplitV4.Printed." ++ m) then
          names := names.push n
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed sector assembly"
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.averagedGaussianThresholdDerivative_sector_bound_of_log_le_two]
  let mut index := 0
  while index < pending.size do
    let n := pending[index]!
    index := index + 1
    unless visited.contains n do
      visited := visited.insert n
      if #[``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_moment,
          ``RectangleCLT.Companion.SplitV4.thresholdProjectionRadius_second_third_moments,
          ``RectangleCLT.Companion.SplitV4.gaussianThresholdDerivative_le_adaptiveLayer,
          ``RectangleCLT.Companion.SplitV4.averagedGaussianThresholdDerivative_bound].contains n then
        throwError "Printed sector route unexpectedly uses bypass {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  logInfo m!"Audited {names.size} printed facet/sector assembly declarations; only permitted axioms."
  logInfo m!"Checked {visited.size} constants in the sector endpoint closure; old coordinate-MGF radius and rectangular-layer endpoints are absent."
